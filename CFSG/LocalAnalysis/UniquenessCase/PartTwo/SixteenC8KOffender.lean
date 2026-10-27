module

import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OffenderB10
import CFSG.RankThree.PartTwo.Sec15.SimsBaumannTransvection
import CFSG.Quasithin.Background.DicksonPerfectSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma c8k_pCore_le_sylow {Γ : Type} [Group Γ] {S : Subgroup Γ}
    (hS : IsSylowIn 2 S ⊤) : CFSG.pCore 2 Γ ≤ S :=
  IsSylowIn.le_of_normal hS le_top ((CFSG.pCore_normal (p := 2) (G := Γ)).subgroupOf ⊤)
    (CFSG.pCore_isPGroup (p := 2) (G := Γ))

private lemma c8k_inf_ker_le_pCore {Γ : Type} [Group Γ] [Finite Γ] {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (nat : C8KNat Γ d ρ O Z)
    (hker : ρ.ker = O) {A : Subgroup Γ} (hA2 : ∀ x ∈ A, x ^ 2 = 1) :
    A ⊓ ρ.ker ≤ CFSG.pCore 2 Γ := by
  intro x hx
  obtain ⟨hxA, hxker⟩ := Subgroup.mem_inf.mp hx
  have hxO : x ∈ O := hker ▸ hxker
  obtain ⟨n, hn⟩ := nat.seven x hxO
  have hodd : Odd (7 ^ n) := Odd.pow (n := n) ⟨3, by norm_num⟩
  obtain ⟨k, hk⟩ := hodd
  have hxeq : x ^ 7 ^ n = x := by
    rw [hk, pow_add, pow_mul, hA2 x hxA, one_pow, one_mul, pow_one]
  rwa [hxeq] at hn

private lemma c8k_card_map_rho_le_two {Γ : Type} [Group Γ]
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {A : Subgroup Γ} (hA2 : ∀ x ∈ A, x ^ 2 = 1) :
    Nat.card (A.map ρ) ≤ 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) ≃* ↥(StatedSL 2 (ZMod 7)) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 7)
  set c : ↥(StatedSL 2 (ZMod 7)) := e (CFSG.Quasithin.A1c.sl2NegOne 7) with hc_def
  have hc1 : c ≠ 1 := by
    rw [hc_def]
    intro h
    exact CFSG.Quasithin.A1c.sl2NegOne_ne_one (p := 7) (by norm_num) (by
      have := congrArg e.symm h
      rwa [e.symm_apply_apply, map_one] at this)
  have hsub : (A.map ρ : Set ↥(StatedSL 2 (ZMod 7))) ⊆ ({1, c} : Set _) := by
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hy
    have hxx : x * x = 1 := by rw [← pow_two]; exact hA2 x hxA
    have hyy : ρ x * ρ x = 1 := by rw [← map_mul, hxx, map_one]
    have hg : e.symm (ρ x) * e.symm (ρ x) = 1 := by rw [← map_mul, hyy, map_one]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases CFSG.Quasithin.Dickson.sl2_eq_one_or_negOne_of_mul_self (p := 7)
      (by norm_num) hg with h | h
    · left
      exact e.symm.injective (by rw [h, map_one])
    · right
      calc ρ x = e (e.symm (ρ x)) := (e.apply_symm_apply (ρ x)).symm
        _ = e (CFSG.Quasithin.A1c.sl2NegOne 7) := by rw [h]
        _ = c := hc_def.symm
  have hinj : Function.Injective (fun y : A.map ρ =>
      if (y : ↥(StatedSL 2 (ZMod 7))) = 1 then (0 : Fin 2) else 1) := by
    intro y z hyz
    have hy1 := hsub y.2
    have hz1 := hsub z.2
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy1 hz1
    rcases hy1 with hy1 | hy1 <;> rcases hz1 with hz1 | hz1
    · exact Subtype.ext (hy1.trans hz1.symm)
    · exfalso
      change (if (y : ↥(StatedSL 2 (ZMod 7))) = 1 then (0 : Fin 2) else 1) =
        (if (z : ↥(StatedSL 2 (ZMod 7))) = 1 then (0 : Fin 2) else 1) at hyz
      rw [if_pos hy1, if_neg (by rw [hz1]; exact hc1)] at hyz
      exact Fin.zero_ne_one hyz
    · exfalso
      change (if (y : ↥(StatedSL 2 (ZMod 7))) = 1 then (0 : Fin 2) else 1) =
        (if (z : ↥(StatedSL 2 (ZMod 7))) = 1 then (0 : Fin 2) else 1) at hyz
      rw [if_neg (by rw [hy1]; exact hc1), if_pos hz1] at hyz
      exact Fin.zero_ne_one hyz.symm
    · exact Subtype.ext (hy1.trans hz1.symm)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

private lemma c8k_relIndex_ne_zero {Γ : Type} [Group Γ] [Finite Γ] (H K : Subgroup Γ) :
    H.relIndex K ≠ 0 := by
  haveI : H.IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.2 (by infer_instance)
  exact Subgroup.relIndex_ne_zero

private lemma c8k_centralizer_conj {Γ : Type} [Group Γ] (g a : Γ) :
    (Subgroup.centralizer ({a} : Set Γ)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹} : Set Γ) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change (g * a * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * a * g⁻¹)
    calc (g * a * g⁻¹) * (g * y * g⁻¹)
        = g * (a * y) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by rw [hy a (by simp)]
      _ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      calc a * (g⁻¹ * x * g)
          = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [hx (g * a * g⁻¹) (by simp)]
        _ = (g⁻¹ * x * g) * a := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem c8k_offender_index {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) (hker : ρ.ker = O) {W : Subgroup Γ} (hWn : W.Normal)
    (hWe : IsElemAbelian 2 W) (hWq : W ≤ CFSG.pCore 2 Γ)
    (hWc : ∀ x ∈ W, ∀ q ∈ CFSG.pCore 2 Γ, x * q = q * x) {A : Subgroup Γ}
    (hA : IsMaxElemAbelian S A) {a : Γ} (ha : a ∈ A) (g : Γ) :
    (W ⊓ centralizer ({g⁻¹ * a * g} : Set Γ)).relIndex W ≤ 2 := by
  have hA2 : ∀ x ∈ A, x ^ 2 = 1 := fun x hx => hA.2.1.2 x hx
  have hWS : W ≤ S := hWq.trans (c8k_pCore_le_sylow conf.sylow)
  open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs in
  have hoff := offender_index_le_of_isMaxElemAbelian hA hWS hWe
  have hK_le : A ⊓ ρ.ker ≤ A ⊓ Subgroup.centralizer (W : Set Γ) := by
    intro x hx
    obtain ⟨hxA, hxker⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxA, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hWc w hw x (c8k_inf_ker_le_pCore nat hker hA2 ⟨hxA, hxker⟩)
  have hrel : (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A ≤
      (A ⊓ ρ.ker).relIndex A :=
    Subgroup.relIndex_le_of_le_left hK_le (c8k_relIndex_ne_zero (A ⊓ ρ.ker) A)
  have hkerrel : (A ⊓ ρ.ker).relIndex A = Nat.card (A.map ρ) := by
    rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_ker]
  have hcard : Nat.card (A.map ρ) ≤ 2 := c8k_card_map_rho_le_two hA2
  have hAK_le_two : (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A ≤ 2 := by
    calc (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A
        ≤ (A ⊓ ρ.ker).relIndex A := hrel
      _ = Nat.card (A.map ρ) := hkerrel
      _ ≤ 2 := hcard
  have hWA : (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W ≤ 2 :=
    le_trans hoff hAK_le_two
  have hcent_le : Subgroup.centralizer (A : Set Γ) ≤
      Subgroup.centralizer ({a} : Set Γ) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha)
  have hinf_le : W ⊓ Subgroup.centralizer (A : Set Γ) ≤
      W ⊓ Subgroup.centralizer ({a} : Set Γ) := inf_le_inf le_rfl hcent_le
  have hWa : (W ⊓ Subgroup.centralizer ({a} : Set Γ)).relIndex W ≤
      (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W :=
    Subgroup.relIndex_le_of_le_left hinf_le
      (c8k_relIndex_ne_zero (W ⊓ Subgroup.centralizer (A : Set Γ)) W)
  have hWa2 : (W ⊓ Subgroup.centralizer ({a} : Set Γ)).relIndex W ≤ 2 :=
    le_trans hWa hWA
  have hconj : (W ⊓ Subgroup.centralizer ({a} : Set Γ)).map
        (MulAut.conj g⁻¹).toMonoidHom =
      W ⊓ Subgroup.centralizer ({g⁻¹ * a * g} : Set Γ) := by
    rw [Subgroup.map_inf W (Subgroup.centralizer ({a} : Set Γ))
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    congr 1
    · exact Subgroup.normal_iff_map_conj_eq.mp hWn g⁻¹
    · simpa only [inv_inv] using c8k_centralizer_conj (g := g⁻¹) (a := a)
  have hWmap : W.map (MulAut.conj g⁻¹).toMonoidHom = W :=
    Subgroup.normal_iff_map_conj_eq.mp hWn g⁻¹
  have hrelconj := Subgroup.relIndex_map_map_of_injective
    (f := (MulAut.conj g⁻¹).toMonoidHom)
    (W ⊓ Subgroup.centralizer ({a} : Set Γ)) W (MulAut.conj g⁻¹).injective
  rw [hconj, hWmap] at hrelconj
  rw [hrelconj]
  exact hWa2

theorem c8k_transvection_product {Γ : Type} [Group Γ] [Finite Γ] {W : Subgroup Γ}
    (hW : IsElemAbelian 2 W) {a b : Γ} (ha : ∀ w ∈ W, a * w * a⁻¹ ∈ W)
    (hb : ∀ w ∈ W, b * w * b⁻¹ ∈ W) (hia : (W ⊓ centralizer ({a} : Set Γ)).relIndex W ≤ 2)
    (hib : (W ⊓ centralizer ({b} : Set Γ)).relIndex W ≤ 2) :
    ∀ w ∈ W, (a * b) ^ 12 * w * ((a * b) ^ 12)⁻¹ = w := by
  have hxa : a ∈ Subgroup.normalizer (W : Set Γ) :=
    Subgroup.mem_normalizer_fintype (S := (W : Set Γ)) (fun n hn => ha n hn)
  have hxb : b ∈ Subgroup.normalizer (W : Set Γ) :=
    Subgroup.mem_normalizer_fintype (S := (W : Set Γ)) (fun n hn => hb n hn)
  have hcent :=
    CFSG.RankThree.PartTwo.Sec15.SimsBaumann.pow_twelve_mem_centralizer hW hxa hxb hia hib
  intro w hw
  have hcomm := Subgroup.mem_centralizer_iff.1 hcent w hw
  rw [← hcomm]
  group

theorem c8k_x12_not_mem_z {Γ : Type} [Group Γ] [Finite Γ] {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (nat : C8KNat Γ d ρ O Z) {a e : Γ}
    (ha : a ^ 2 = 1) (haρ : ρ a ≠ 1) (he : e ∈ O) (hez : e ∉ Z) :
    (a * (e⁻¹ * a * e)) ^ 12 ∉ Z := by
  intro hx
  haveI : Z.Normal := nat.z_normal
  let π : Γ →* Γ ⧸ Z := QuotientGroup.mk' Z
  have ha_inv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (b := a) (by rw [← pow_two]; exact ha)
  have ha2 : ρ a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hinv : a * e⁻¹ * a⁻¹ * e⁻¹ ∈ Z := nat.inv a haρ ha2 e⁻¹ (O.inv_mem he)
  have hπinv : π (a * e⁻¹ * a⁻¹) = π e := by
    have h1 : π (a * e⁻¹ * a⁻¹) * (π e)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff (N := Z) _).2 hinv
    exact mul_inv_eq_one.mp h1
  have hxeq : π (a * (e⁻¹ * a * e)) = (π e) ^ 2 := by
    have h2 : a * (e⁻¹ * a * e) = (a * e⁻¹ * a⁻¹) * e := by
      rw [ha_inv]
      group
    rw [h2, map_mul, hπinv, pow_two]
  have hx12 : π ((a * (e⁻¹ * a * e)) ^ 12) = (π e) ^ 24 := by
    rw [map_pow, hxeq, ← pow_mul]
  have h24 : (π e) ^ 24 = 1 := by
    rw [← hx12]
    exact (QuotientGroup.eq_one_iff (N := Z) _).2 hx
  have h7 : (π e) ^ 7 = 1 := by
    have he7 : e ^ 7 ∈ Z := nat.pow e he
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := Z) _).2 he7
  have hge : π e = 1 := by
    have := (pow_gcd_eq_one (a := π e) (m := 24) (n := 7)).2 ⟨h24, h7⟩
    rwa [show Nat.gcd 24 7 = 1 by norm_num, pow_one] at this
  exact hez ((QuotientGroup.eq_one_iff (N := Z) e).1 (by simpa [π] using hge))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
