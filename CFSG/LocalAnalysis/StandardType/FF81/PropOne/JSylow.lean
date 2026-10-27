module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JStruct
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalOrders
import CFSG.Adapters.StatedSLTwoField
import CFSG.LocalAnalysis.StandardType.GGFFSLSylow
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.StandardType.GGFF
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)

private theorem card_J_cases {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G} (hJ : JData n L z J) :
    Nat.card J = 20160 ∨ Nat.card J = 9999360 := by
  rcases h.hypA.n_cases with rfl | rfl
  · left
    have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (X := ↥J) (k := 4) (p := 2)
      (e := 1) (by norm_num) hJ.model
    rw [hc]
    decide
  · right
    have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (X := ↥J) (k := 5) (p := 2)
      (e := 1) (by norm_num) hJ.model
    rw [hc]
    decide

private theorem mulAut_congr_conj {A B : Type} [Group A] [Group B] (e : A ≃* B) (k : A) :
    MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  ext x
  simp [MulAut.congr, MulAut.conj_apply, MulEquiv.trans_apply]

theorem center_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G} (hJ : JData n L z J) :
    ∀ x ∈ J, (∀ y ∈ J, x * y = y * x) → x = 1 := by
  intro x hxJ hx
  have : IsSimpleGroup ↥J :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hJ.model
  have hcen : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with hb | ht
    · exact hb
    · exfalso
      let : CommGroup ↥J := { (inferInstance : Group ↥J) with mul_comm := fun a b =>
        (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top a) b).symm }
      have hprime : (Nat.card ↥J).Prime :=
        (CommGroup.is_simple_iff_prime_card (α := ↥J)).mp inferInstance
      rcases card_J_cases h hJ with hc | hc <;> rw [hc] at hprime <;> norm_num at hprime
  have hmem : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hx g.1 g.2).symm
  rw [hcen] at hmem
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)

theorem inner_odd_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G} (hJ : JData n L z J) :
    ∀ α : MulAut ↥J, ∀ m : ℕ, Odd m → α ^ m = 1 → ∃ k : ↥J, α = MulAut.conj k := by
  intro α m hm hα
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hJ.model
  have hm' : 3 ≤ n - 1 := by rcases h.hypA.n_cases with rfl | rfl <;> norm_num
  have hα' : (MulAut.congr e α) ^ m = 1 := by
    rw [← map_pow, hα, map_one]
  obtain ⟨k, hk⟩ :=
    CFSG.StandardType.GGFF.inner_odd_SL hm' (MulAut.congr e α) m hm hα'
  refine ⟨e.symm k, ?_⟩
  apply (MulAut.congr e).injective
  rw [hk, mulAut_congr_conj e (e.symm k), e.apply_symm_apply]

private theorem vecElt_mem_J_of_zero {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G}
    (hJ : JData n L z J) {v : Fin 3 → ZMod 3} (hv : v 0 = 0) :
    vecElt (GGFF.zs z) v ∈ J := by
  have hS := h.settingCore
  have hdecomp : v = Pi.single 1 (v 1) + Pi.single 2 (v 2) := by
    funext i
    fin_cases i <;> simp [Pi.single, hv]
  rw [hdecomp, vecElt_add hS.zs_pow hS.zs_comm, vecElt_single, vecElt_single]
  exact J.mul_mem (J.pow_mem hJ.z₁ _) (J.pow_mem hJ.z₂ _)

private theorem zero_of_vecElt_mem_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G}
    (hJ : JData n L z J) {v : Fin 3 → ZMod 3} (hv : vecElt (GGFF.zs z) v ∈ J) :
    v 0 = 0 := by
  have hS := h.settingCore
  have hdecomp : v = Pi.single 0 (v 0) + Function.update v 0 0 := by
    funext i
    fin_cases i <;> simp [Pi.single, Function.update]
  have hv'mem : vecElt (GGFF.zs z) (Function.update v 0 0) ∈ J :=
    vecElt_mem_J_of_zero h hJ (by simp)
  have hsplit : vecElt (GGFF.zs z) v = vecElt (GGFF.zs z) (Pi.single 0 (v 0)) *
      vecElt (GGFF.zs z) (Function.update v 0 0) := by
    conv_lhs => rw [hdecomp]
    rw [vecElt_add hS.zs_pow hS.zs_comm, vecElt_single]
  have hsing : vecElt (GGFF.zs z) (Pi.single 0 (v 0)) ∈ J := by
    have heq : vecElt (GGFF.zs z) (Pi.single 0 (v 0)) =
        vecElt (GGFF.zs z) v * (vecElt (GGFF.zs z) (Function.update v 0 0))⁻¹ := by
      rw [hsplit]; group
    rw [heq]
    exact J.mul_mem hv (J.inv_mem hv'mem)
  have hmem_inf : vecElt (GGFF.zs z) (Pi.single 0 (v 0)) ∈
      (Subgroup.zpowers (GGFF.zs z 0) ⊓ J : Subgroup G) := by
    refine ⟨?_, hsing⟩
    rw [vecElt_single]
    exact (Subgroup.zpowers (GGFF.zs z 0)).pow_mem (Subgroup.mem_zpowers _) _
  rw [hJ.inf] at hmem_inf
  have hone : vecElt (GGFF.zs z) (Pi.single 0 (v 0)) = 1 := Subgroup.mem_bot.mp hmem_inf
  have hsingle0 : (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 3) = 0 :=
    hS.inj' (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 3) hone
  have := congrFun hsingle0 0
  simpa using this

private theorem card_inf_J_eq_nine {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G}
    (hJ : JData n L z J) : Nat.card (bOne z ⊓ J : Subgroup G) = 9 := by
  have hS := h.settingCore
  let ins : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3) :=
    Fin.insertNth (α := fun _ : Fin 3 => ZMod 3) 0 0
  have hins0 : ∀ w, ins w 0 = 0 := fun w => by simp [ins]
  have hrem : ∀ w, Fin.removeNth 0 (ins w) = w := fun w => by simp [ins]
  have hinsrem : ∀ v : Fin 3 → ZMod 3, v 0 = 0 → ins (Fin.removeNth 0 v) = v := by
    intro v hv0
    rw [show ins (Fin.removeNth 0 v) =
      Fin.insertNth (α := fun _ : Fin 3 => ZMod 3) 0 (0 : ZMod 3) (Fin.removeNth 0 v) from rfl]
    rw [Fin.insertNth_eq_iff]
    exact ⟨hv0.symm, rfl⟩
  let f : (Fin 2 → ZMod 3) → (bOne z ⊓ J : Subgroup G) := fun w =>
    ⟨vecElt (GGFF.zs z) (ins w),
      ⟨vecElt_mem_tor (GGFF.zs z) (ins w), vecElt_mem_J_of_zero h hJ (hins0 w)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro w1 w2 hw
      have h1 : vecElt (GGFF.zs z) (ins w1) = vecElt (GGFF.zs z) (ins w2) := by
        simpa [f] using congrArg Subtype.val hw
      have h2 := (vecElt_injective hS.zs_pow hS.zs_comm hS.inj') h1
      calc w1 = Fin.removeNth 0 (ins w1) := (hrem w1).symm
        _ = Fin.removeNth 0 (ins w2) := by rw [h2]
        _ = w2 := hrem w2
    · intro y
      obtain ⟨v, hv⟩ := (GGFF.SettingCore.mem_torG hS).mp y.2.1
      have hvJ : vecElt (GGFF.zs z) v ∈ J := hv ▸ y.2.2
      have hv0 : v 0 = 0 := zero_of_vecElt_mem_J h hJ hvJ
      refine ⟨Fin.removeNth 0 v, ?_⟩
      apply Subtype.ext
      change vecElt (GGFF.zs z) (ins (Fin.removeNth 0 v)) = y.1
      rw [hinsrem v hv0]
      exact hv.symm
  change Nat.card (bOne z ⊓ J : Subgroup G) = 9
  calc Nat.card (bOne z ⊓ J : Subgroup G)
      = Nat.card (Fin 2 → ZMod 3) := Nat.card_congr (Equiv.ofBijective f hf).symm
    _ = 9 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
      norm_num

private theorem card_le_nine_of_isPGroup_of_le {G : Type} [Group G] [Finite G]
    {J P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup 3 P) (h27 : ¬ (27 : ℕ) ∣ Nat.card J) :
    Nat.card P ≤ 9 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3) (G := P)).mp hP
  have hdvd : 3 ^ a ∣ Nat.card J := ha ▸ Subgroup.card_dvd_of_le hPJ
  by_contra hle
  rw [ha] at hle
  have ha3 : 3 ≤ a := by
    by_contra h
    have ha2 : a ≤ 2 := by omega
    exact hle (by
      calc 3 ^ a ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
        _ = 9 := by norm_num)
  exact h27 (by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact dvd_trans (pow_dvd_pow 3 ha3) hdvd)

theorem sylow_B₁_inf_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J : Subgroup G} (hJ : JData n L z J) :
    IsPGroup 3 (bOne z ⊓ J : Subgroup G) ∧ Nat.card (bOne z ⊓ J : Subgroup G) = 9 ∧
      ∀ P : Subgroup G, P ≤ J → IsPGroup 3 P → bOne z ⊓ J ≤ P → P = bOne z ⊓ J := by
  have hS := h.settingCore
  have hcardY := card_inf_J_eq_nine h hJ
  have h27 : ¬ (27 : ℕ) ∣ Nat.card J := by
    rcases card_J_cases h hJ with hc | hc <;> rw [hc] <;> norm_num
  refine ⟨?_, hcardY, ?_⟩
  · have hbOne : IsPGroup 3 (bOne z : Subgroup G) :=
      IsPGroup.of_card (n := 3) (by
        rw [show Nat.card (bOne z : Subgroup G) = 27 from GGFF.SettingCore.card_torG hS]
        norm_num)
    exact hbOne.to_le inf_le_left
  · intro P hPJ hP hYP
    exact (Subgroup.eq_of_le_of_card_ge hYP (by
      rw [hcardY]
      exact card_le_nine_of_isPGroup_of_le hPJ hP h27)).symm

end CFSG.StandardType.FF81.PropOne

end
