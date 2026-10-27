module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.EmptyFaithful.S146zYFPSp4Borel
public import CFSG.Quasithin.Vol2.F134LieSp4

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin.F134.Sp4

theorem normalizes_of_mulEquiv_five {A : Type*} [Group A] [Finite A] {L U P : Subgroup A}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (ψ₀ : ↥L ≃* StatedSp 2 K)
    (hU : IsSylowTwoOf U L) (hPL : P ≤ L) (hP25 : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1)
    (hmul : ∀ u ∈ U, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ U, u * x = y * s) :
    (∀ y ∈ P, ∀ u ∈ U, y * u * y⁻¹ ∈ U) ∧ 5 ∣ Nat.card K - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₁ := (U.subgroupOf L).map ψ₀.toMonoidHom with hU₁def
  have hU₁ : IsSylowTwoOf U₁ (⊤ : Subgroup (StatedSp 2 K)) := by
    refine ⟨le_top, (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, hU₁def]
    erw [Subgroup.index_map_equiv]
    exact hU.2.2
  obtain ⟨g, -, hg⟩ := IsSylowTwoOf.exists_conj hU₁ (isSylowTwoOf_unipotent (K := K))
  set ψ : ↥L ≃* StatedSp 2 K := ψ₀.trans (MulAut.conj g) with hψ
  have hψU : ∀ l : L, ψ l ∈ unipotent 2 K ↔ (l : A) ∈ U := by
    intro l
    rw [hg, Subgroup.mem_map_equiv, hU₁def, Subgroup.mem_map_equiv, hψ, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  set P₁ := (P.subgroupOf L).map ψ.toMonoidHom with hP₁
  have hP₁25 : Nat.card P₁ = 25 := by
    rw [hP₁, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, ← hP25]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hP₁exp : ∀ x ∈ P₁, x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ 5 = 1 := Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
    rw [this, map_one]
  have hP₁U : ∀ u ∈ unipotent 2 K, ∀ x ∈ P₁, ∃ y ∈ P₁, ∃ s ∈ unipotent 2 K,
      u * x = y * s := by
    intro u hu x hx
    obtain ⟨x', hx', rfl⟩ := hx
    set u' := ψ.symm u with hu'
    have hu'U : (u' : A) ∈ U := (hψU u').mp (by rw [hu', MulEquiv.apply_symm_apply]; exact hu)
    obtain ⟨y, hy, s, hs, hys⟩ := hmul _ hu'U _ (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨ψ ⟨y, hPL hy⟩, ⟨⟨y, hPL hy⟩, hy, rfl⟩, ψ ⟨s, hU.1 hs⟩, (hψU _).mpr hs, ?_⟩
    rw [← MulEquiv.apply_symm_apply ψ u, ← hu']
    change ψ u' * ψ x' = _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hys
  obtain ⟨hB, h5⟩ := le_borelSubgroup_of_mul_five hK hP₁U hP₁25 hP₁exp
  refine ⟨fun y hy u hu => ?_, h5⟩
  have hyB : ψ ⟨y, hPL hy⟩ ∈ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    rw [normalizer_unipotent]
    exact hB ⟨⟨y, hPL hy⟩, hy, rfl⟩
  have huU : ψ ⟨u, hU.1 hu⟩ ∈ unipotent 2 K := (hψU _).mpr hu
  have h1 := (Subgroup.mem_normalizer_iff.mp hyB _).mp huU
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  exact (hψU _).mp h1

theorem conj_eq_of_conjNormal_eq_conj_five {A : Type*} [Group A] [Finite A] {L U P : Subgroup A}
    [L.Normal] (hZ : Subgroup.center L = ⊥) (hU : IsSylowTwoOf U L) (hPL : P ≤ L)
    (hP5 : IsPGroup 5 P) (hPU : ∀ y ∈ P, ∀ u ∈ U, y * u * y⁻¹ ∈ U) {t : A}
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htU : t ∈ Subgroup.normalizer (U : Set A))
    (htP : t ∈ Subgroup.normalizer (P : Set A)) {x : L}
    (htx : MulAut.conjNormal t = MulAut.conj x) {y : A} (hy : y ∈ P) :
    t * y * t⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hconj : ∀ l : L, t * (l : A) * t⁻¹ = (x : A) * l * (x : A)⁻¹ := by
    intro l
    have h := congrArg (fun α : MulAut L => ((α l : L) : A)) htx
    simpa [MulAut.conjNormal_apply] using h
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp ht2) ⟨t, Subgroup.mem_zpowers t⟩
  have hta : t ^ 2 ^ a = 1 := by
    have := pow_orderOf_eq_one (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t)
    rw [ha] at this
    exact congrArg Subtype.val this
  have hxa : x ^ 2 ^ a = 1 := by
    have h1 : MulAut.conj (x ^ 2 ^ a) = 1 := by
      rw [map_pow, ← htx, ← map_pow, hta, map_one]
    have hmem : x ^ 2 ^ a ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      have := congrArg (fun α : MulAut L => α l) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc l * x ^ 2 ^ a = x ^ 2 ^ a * l * (x ^ 2 ^ a)⁻¹ * x ^ 2 ^ a := by rw [this]
        _ = x ^ 2 ^ a * l := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hxU : (x : A) ∈ Subgroup.normalizer (U : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hconj ⟨h, hU.1 hh⟩]
      exact (Subgroup.mem_normalizer_iff.mp htU h).mp hh
    · intro hh
      have hL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem x.2) (hU.1 hh)) x.2
        rwa [show (x : A)⁻¹ * ((x : A) * h * (x : A)⁻¹) * x = h by group] at this
      rw [← hconj ⟨h, hL⟩] at hh
      exact (Subgroup.mem_normalizer_iff.mp htU h).mpr hh
  have hx2 : IsPGroup 2 (Subgroup.zpowers (x : A)) := by
    have hxa' : (x : A) ^ 2 ^ a = 1 := by
      rw [← SubgroupClass.coe_pow, hxa, OneMemClass.coe_one]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxa')
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hsup := CFSG.Quasithin.P134.le_of_isSylowTwoOf hU le_sup_right
    (sup_le (Subgroup.zpowers_le.mpr x.2) hU.1)
    (hx2.to_sup_of_normal_right' hU.2.1 (Subgroup.zpowers_le.mpr hxU))
  have hxU' : (x : A) ∈ U := hsup (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hyL : y ∈ L := hPL hy
  have hc1 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ P := by
    rw [← hconj ⟨y, hyL⟩]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp htP y).mp hy) (P.inv_mem hy)
  have hc2 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ U := by
    rw [show (x : A) * y * (x : A)⁻¹ * y⁻¹ = x * (y * (x : A)⁻¹ * y⁻¹) by group]
    exact U.mul_mem hxU' (hPU y hy _ (U.inv_mem hxU'))
  have hdisj := IsPGroup.disjoint_of_ne 5 2 (by norm_num) P U hP5 hU.2.1
  have hc : (x : A) * y * (x : A)⁻¹ * y⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hdisj hc1 hc2
  rw [hconj ⟨y, hyL⟩]
  calc (x : A) * y * (x : A)⁻¹ = (x : A) * y * (x : A)⁻¹ * y⁻¹ * y := by group
    _ = y := by rw [hc, one_mul]

open CFSG.Quasithin.EmptyFaithfulMultiple in
theorem facts134Five_psp4Even : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A),
    StatedClassicalModel ↥L .PSp 2 2 n → E25Config L P T → AutCyclic T P := by
  intro n A _ _ L P T hL h
  obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have hn : 2 ≤ n := by
    by_contra h'
    have : n = 1 := by omega
    subst this
    exact hne rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := h.normal
  have hU := E25Config.isSylowTwoOf_inf h
  obtain ⟨hPU, -⟩ := normalizes_of_mulEquiv_five hK4 (e.trans (Lin2.Five.projEquiv K).symm) hU
    h.le h.card h.exp (E25Config.mul_inf h)
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 2) (by rw [h.card]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_forall_eq_conj_mul_pow e
  refine autCyclic_of_forall hτ fun s hs x hsx y hy => ?_
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    h.sylow.2.1.to_le (Subgroup.zpowers_le.mpr hs.1)
  have hsU : s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup A) : Set A) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs.1,
      (Subgroup.normalizer_eq_top_iff.mpr h.normal).symm ▸ Subgroup.mem_top s⟩
  exact conj_eq_of_conjNormal_eq_conj_five (Lin2.Five.center_eq_bot_of_equiv e) hU h.le hP5 hPU
    hs2 hsU hs.2 hsx hy

end CFSG.Quasithin.S146zY
