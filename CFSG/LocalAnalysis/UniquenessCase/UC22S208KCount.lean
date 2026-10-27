module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208KCommon
import CFSG.LargeExtraspecial.Bender
import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem s208k_card_sylow_eq_index {G : Type} [Group G] [Finite G] {B R : Subgroup G} [R.Normal]
    (U : Sylow 2 G) (hBU : B ≤ normalizer ((U : Subgroup G) : Set G))
    (hR : ¬ Group.IsSolvable ↥R) (hRB : ¬ R ≤ B)
    (hdc : ∀ g, g ∉ B → ∀ y, y ∉ B → ∃ b₁ ∈ B, ∃ b₂ ∈ B, y = b₁ * g * b₂) :
    Nat.card (Sylow 2 ↥R) = B.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrR, hrB⟩ := SetLike.not_le_iff_exists.mp hRB
  have hsup : B ⊔ R = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    by_cases hy : y ∈ B
    · exact Subgroup.mem_sup_left hy
    · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hdc r hrB y hy
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right hrR))
        (Subgroup.mem_sup_left hb₂)
  obtain ⟨T, hT⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq R U
  have hmemT : ∀ t : ↥R, t ∈ (T : Subgroup ↥R) ↔ (t : G) ∈ (U : Subgroup G) := fun t => by
    rw [hT, Subgroup.mem_subgroupOf]
  have hconjB : ∀ b ∈ B, ∀ t : G, t ∈ (U : Subgroup G) ↔ b * t * b⁻¹ ∈ (U : Subgroup G) :=
    fun b hb => mem_normalizer_iff.mp (hBU hb)
  have hN : normalizer ((T : Subgroup ↥R) : Set ↥R) = B.subgroupOf R := by
    ext x
    rw [mem_normalizer_iff, Subgroup.mem_subgroupOf]
    simp only [hmemT, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨fun hx => ?_, fun hx t => hconjB _ hx t⟩
    by_contra hxB
    have hmul : ∀ g h : G,
        (∀ t ∈ R, t ∈ (U : Subgroup G) → g * t * g⁻¹ ∈ (U : Subgroup G)) →
        (∀ t ∈ R, t ∈ (U : Subgroup G) → h * t * h⁻¹ ∈ (U : Subgroup G)) →
        ∀ t ∈ R, t ∈ (U : Subgroup G) → g * h * t * (g * h)⁻¹ ∈ (U : Subgroup G) := by
      intro g h hg hh t ht htU
      have e : g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
      rw [e]
      exact hg _ (‹R.Normal›.conj_mem t ht h) (hh t ht htU)
    have hB' : ∀ b ∈ B, ∀ t ∈ R, t ∈ (U : Subgroup G) → b * t * b⁻¹ ∈ (U : Subgroup G) :=
      fun b hb t _ htU => (hconjB b hb t).mp htU
    have hx' : ∀ t ∈ R, t ∈ (U : Subgroup G) → (x : G) * t * (x : G)⁻¹ ∈ (U : Subgroup G) :=
      fun t ht htU => (hx ⟨t, ht⟩).mp htU
    have hall : ∀ y : G, ∀ t ∈ R, t ∈ (U : Subgroup G) → y * t * y⁻¹ ∈ (U : Subgroup G) := by
      intro y
      by_cases hy : y ∈ B
      · exact hB' y hy
      · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hdc x hxB y hy
        exact hmul _ _ (hmul _ _ (hB' b₁ hb₁) hx') (hB' b₂ hb₂)
    have hTn : (T : Subgroup ↥R).Normal :=
      ⟨fun t ht y => (hmemT _).mpr (hall y t t.2 ((hmemT t).mp ht))⟩
    have hsol : Group.IsSolvable ↥(normalizer ((T : Subgroup ↥R) : Set ↥R)) :=
      CFSG.ComponentClassification.AS76b.isSolvable_normalizer_sylow_two T
    rw [normalizer_eq_top_iff.mpr hTn] at hsol
    exact hR (Group.isSolvable_of_surjective (f := (⊤ : Subgroup ↥R).subtype)
      fun z => ⟨⟨z, Subgroup.mem_top z⟩, rfl⟩)
  have hc : Nat.card (Sylow 2 ↥R) = (normalizer ((T : Subgroup ↥R) : Set ↥R)).index :=
    T.card_eq_index_normalizer
  rw [hc, hN]
  change B.relIndex R = B.index
  have h1 : R.relIndex B = R.index := by
    rw [← relIndex_sup_right B R, hsup, relIndex_top_right]
  have h2 := relIndex_mul_index (inf_le_left : B ⊓ R ≤ B)
  have h3 := relIndex_mul_index (inf_le_right : B ⊓ R ≤ R)
  rw [inf_relIndex_left, h1] at h2
  rw [inf_relIndex_right] at h3
  have hR0 : 0 < R.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hR0 ?_
  rw [h3, ← h2, mul_comm]

theorem s208k_card_sylow_quotient {R : Type} [Group R] [Finite R] :
    Nat.card (Sylow 2 R) = Nat.card (Sylow 2 (R ⧸ CFSG.pCore 2 R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := QuotientGroup.mk'_surjective (CFSG.pCore 2 R)
  refine Nat.card_eq_of_bijective (Sylow.mapSurjective hsurj)
    ⟨fun S T hST => ?_, Sylow.mapSurjective_surjective hsurj 2⟩
  have hS := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := R)) S
  have hT := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := R)) T
  have h := congrArg (fun V : Sylow 2 (R ⧸ CFSG.pCore 2 R) =>
    (V : Subgroup (R ⧸ CFSG.pCore 2 R)).comap (QuotientGroup.mk' (CFSG.pCore 2 R))) hST
  simp only [Sylow.coe_mapSurjective, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  rw [sup_eq_left.mpr hS, sup_eq_left.mpr hT] at h
  exact Sylow.ext h

private theorem s208k_normalizer_prod {A C : Type} [Group A] [Group C] (H : Subgroup A)
    (K : Subgroup C) :
    normalizer ((H.prod K : Subgroup (A × C)) : Set (A × C)) =
      (normalizer (H : Set A)).prod (normalizer (K : Set C)) := by
  ext ⟨g₁, g₂⟩
  simp only [Subgroup.mem_prod, mem_normalizer_iff, Prod.forall, Prod.mk_mul_mk, Prod.inv_mk]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun c => ?_⟩
    · simpa using h a 1
    · simpa using h 1 c
  · rintro ⟨h₁, h₂⟩ a c
    exact and_congr (h₁ a) (h₂ c)

theorem s208k_card_sylow_prod {A C : Type} [Group A] [Group C] [Finite A] [Finite C] :
    Nat.card (Sylow 2 (A × C)) = Nat.card (Sylow 2 A) * Nat.card (Sylow 2 C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SA⟩ : Nonempty (Sylow 2 A) := inferInstance
  obtain ⟨SC⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hSA : Nat.card ↥(SA : Subgroup A) = 2 ^ (Nat.card A).factorization 2 :=
    SA.card_eq_multiplicity
  have hSC : Nat.card ↥(SC : Subgroup C) = 2 ^ (Nat.card C).factorization 2 :=
    SC.card_eq_multiplicity
  have hfac : (Nat.card (A × C)).factorization 2 =
      (Nat.card A).factorization 2 + (Nat.card C).factorization 2 := by
    rw [Nat.card_prod, Nat.factorization_mul hA0 hC0]
    rfl
  have hcard : Nat.card ((SA : Subgroup A).prod (SC : Subgroup C)) =
      2 ^ (Nat.card (A × C)).factorization 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hSA, hSC, hfac, pow_add]
  have hS : Nat.card (Sylow 2 (A × C)) =
      (normalizer (((SA : Subgroup A).prod (SC : Subgroup C) : Subgroup (A × C)) :
        Set (A × C))).index :=
    (Sylow.ofCard _ hcard).card_eq_index_normalizer
  have hA : Nat.card (Sylow 2 A) = (normalizer ((SA : Subgroup A) : Set A)).index :=
    SA.card_eq_index_normalizer
  have hC : Nat.card (Sylow 2 C) = (normalizer ((SC : Subgroup C) : Set C)).index :=
    SC.card_eq_index_normalizer
  rw [hS, hA, hC, s208k_normalizer_prod, Subgroup.index_prod]

theorem s208k_two_pow_add_one_mul_ne {a b k : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (2 ^ a + 1) * (2 ^ b + 1) ≠ 2 ^ k + 1 := by
  wlog hab : a ≤ b generalizing a b
  · rw [mul_comm]
    exact this (a := b) (b := a) hb ha (by omega)
  intro h
  have hsum : 2 ^ a * 2 ^ b + 2 ^ a + 2 ^ b = 2 ^ k := by
    have e : (2 ^ a + 1) * (2 ^ b + 1) = 2 ^ a * 2 ^ b + 2 ^ a + 2 ^ b + 1 := by ring
    rw [e] at h
    exact Nat.add_right_cancel h
  have hx : 0 < 2 ^ a := by positivity
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · have hy : 0 < 2 ^ b := by positivity
    have hd : 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    have h2 : 2 ^ (a + 1) ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    have h1 : 2 ^ (a + 1) ∣ 2 ^ a * 2 ^ b := h2.mul_left _
    have hk : k ≤ a := by
      by_contra hka
      have h3 : 2 ^ (a + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have h4 := Nat.dvd_sub (Nat.dvd_sub h3 h1) h2
      rw [hd] at h4
      generalize 2 ^ a * 2 ^ b = xy at hsum h4
      generalize 2 ^ a = x at hsum h4 hx
      generalize 2 ^ b = y at hsum h4
      generalize 2 ^ k = z at hsum h4
      have e : z - xy - y = x := by omega
      rw [e] at h4
      have := Nat.le_of_dvd hx h4
      omega
    have h5 : 2 ^ k ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hk
    generalize 2 ^ a * 2 ^ b = xy at hsum
    generalize 2 ^ a = x at hsum h5
    generalize 2 ^ b = y at hsum hy
    generalize 2 ^ k = z at hsum h5
    omega
  · rw [← heq] at hsum
    have hd : 2 ^ (a + 2) = 2 ^ a * 4 := by ring
    have h4 : 4 ∣ 2 ^ a := by
      have h22 : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
      norm_num at h22
      exact h22
    have h1 : 2 ^ a * 4 ∣ 2 ^ a * 2 ^ a := Nat.mul_dvd_mul (dvd_refl _) h4
    have hk : k ≤ a + 1 := by
      by_contra hka
      have h3 : 2 ^ a * 4 ∣ 2 ^ k := by
        rw [← hd]
        exact Nat.pow_dvd_pow 2 (by omega)
      have h5 := Nat.dvd_sub h3 h1
      generalize 2 ^ a * 2 ^ a = xx at hsum h5
      generalize 2 ^ a = x at hsum h5 hx
      generalize 2 ^ k = z at hsum h5
      have e : z - xx = x * 2 := by omega
      rw [e] at h5
      have := Nat.le_of_dvd (by omega) h5
      omega
    have h5 : 2 ^ k ≤ 2 ^ a * 2 :=
      (Nat.pow_le_pow_right (by norm_num) hk).trans (pow_succ 2 a).le
    have h6 : 0 < 2 ^ a * 2 ^ a := by positivity
    generalize 2 ^ a * 2 ^ a = xx at hsum h6
    generalize 2 ^ a = x at hsum h5
    generalize 2 ^ k = z at hsum h5
    omega

theorem s208k_card_sylow_factor {A : Type} [Group A] [Finite A]
    {n : ℕ} (hA : IsSz A n ∨ IsL2 A n) : ∃ a : ℕ, n ≤ a ∧ Nat.card (Sylow 2 A) = 2 ^ a + 1 := by
  rcases hA with hA | hA
  · exact ⟨2 * n, by omega, CFSG.LargeExtraspecial.Bender.card_sylow_of_suzuki A n hA⟩
  · exact ⟨n, le_rfl, CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 A 2 n
      (CFSG.Blueprint.LieModel.statedClassicalModel hA (by decide))⟩

theorem s208k_not_isSzL2Product {X : Type} [Group X] [Finite X]
    {P : Subgroup X} {n k : ℕ} (S : Sylow 2 X) (hSP : normalizer (S : Set X) ≤ P)
    (hdc : ∀ x ∈ P, x ∉ normalizer (S : Set X) → ∀ y ∈ P, y ∉ normalizer (S : Set X) →
      ∃ b₁ ∈ normalizer (S : Set X), ∃ b₂ ∈ normalizer (S : Set X), y = b₁ * x * b₂)
    (hidx : (normalizer (S : Set X)).relIndex P = 2 ^ k + 1) (hn : 2 ≤ n)
    (hQ : IsSzL2Product (Bar2 (Hinf P)) n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eR : ↥(CFSG.perfectResidual ↥P) ≃* ↥(Hinf P) :=
    (CFSG.perfectResidual ↥P).equivMapOfInjective P.subtype P.subtype_injective
  have hR : ¬ Group.IsSolvable ↥(CFSG.perfectResidual ↥P) := fun h =>
    s208k_hinf_not_isSolvable (Or.inr (Or.inr hQ))
      (Group.isSolvable_of_surjective (f := eR.toMonoidHom) eR.surjective)
  have hNsol : Group.IsSolvable ↥(normalizer (S : Set X)) :=
    CFSG.ComponentClassification.AS76b.isSolvable_normalizer_sylow_two S
  have hBsol : Group.IsSolvable ↥((normalizer (S : Set X)).subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hSP).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSP).injective
  have hRB : ¬ CFSG.perfectResidual ↥P ≤ (normalizer (S : Set X)).subgroupOf P := fun hle =>
    hR (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  have hSP' : (S : Subgroup X) ≤ P := Subgroup.le_normalizer.trans hSP
  obtain ⟨U, hU⟩ : ∃ U : Sylow 2 ↥P, (U : Subgroup ↥P) = (S : Subgroup X).subgroupOf P :=
    ⟨S.subtype hSP', rfl⟩
  have hBU : (normalizer (S : Set X)).subgroupOf P ≤ normalizer ((U : Subgroup ↥P) : Set ↥P) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    rw [mem_normalizer_iff]
    intro h
    rw [hU, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.mp hb h
  have hdc' : ∀ g : ↥P, g ∉ (normalizer (S : Set X)).subgroupOf P →
      ∀ y : ↥P, y ∉ (normalizer (S : Set X)).subgroupOf P →
        ∃ b₁ ∈ (normalizer (S : Set X)).subgroupOf P,
          ∃ b₂ ∈ (normalizer (S : Set X)).subgroupOf P, y = b₁ * g * b₂ := by
    intro g hg y hy
    rw [Subgroup.mem_subgroupOf] at hg hy
    obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hdc g g.2 hg y y.2 hy
    exact ⟨⟨b₁, hSP hb₁⟩, Subgroup.mem_subgroupOf.mpr hb₁, ⟨b₂, hSP hb₂⟩,
      Subgroup.mem_subgroupOf.mpr hb₂, Subtype.ext he⟩
  have hK1 := s208k_card_sylow_eq_index U hBU hR hRB hdc'
  obtain ⟨A, C, _, _, ⟨e⟩, hA, hC⟩ := hQ
  have : Finite (A × C) := Finite.of_equiv _ e.toEquiv
  have : Finite A := Finite.prod_left C
  have : Finite C := Finite.prod_right A
  obtain ⟨a, hna, ha⟩ := s208k_card_sylow_factor hA
  obtain ⟨c, hnc, hc⟩ := s208k_card_sylow_factor hC
  have hcount : Nat.card (Sylow 2 ↥(CFSG.perfectResidual ↥P)) = (2 ^ a + 1) * (2 ^ c + 1) := by
    rw [CFSG.LargeExtraspecial.Bender.card_sylow_congr eR 2, s208k_card_sylow_quotient,
      CFSG.LargeExtraspecial.Bender.card_sylow_congr e 2, s208k_card_sylow_prod, ha, hc]
  exact s208k_two_pow_add_one_mul_ne (by omega) (by omega) (hcount.symm.trans (hK1.trans hidx))

end CFSG.LocalAnalysis.UniquenessCase.UC22
