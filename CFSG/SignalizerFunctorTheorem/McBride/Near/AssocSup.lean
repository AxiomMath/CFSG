module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Glauberman

public section

open CFSG.Open
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

namespace AssocSup

theorem normal_subgroupOf_sup {P Q : Subgroup G} (hQP : Admits Q P) :
    (P.subgroupOf (P ⊔ Q)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer hQP)

theorem mk'_comp_inclusion_surjective {P Q : Subgroup G} (hQP : Admits Q P)
    [(P.subgroupOf (P ⊔ Q)).Normal] :
    Function.Surjective ((QuotientGroup.mk' (P.subgroupOf (P ⊔ Q))).comp
      (Subgroup.inclusion (le_sup_right : Q ≤ P ⊔ Q))) := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf (P ⊔ Q)) z
  have hy' : y ∈ (P : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P Q hQP]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have h := (Subgroup.mem_normalizer_iff''.mp (hQP hv) u).mp hu
  simpa [mul_assoc] using h

theorem card_sup_dvd_mul {P Q : Subgroup G} (hQP : Admits Q P) :
    Nat.card ↥(P ⊔ Q) ∣ Nat.card ↥P * Nat.card ↥Q := by
  have := normal_subgroupOf_sup hQP
  have h1 := Subgroup.card_ker_mul_card_of_surjective
    (QuotientGroup.mk'_surjective (P.subgroupOf (P ⊔ Q)))
  rw [QuotientGroup.ker_mk',
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ P ⊔ Q)).toEquiv] at h1
  have h3 : Nat.card (↥(P ⊔ Q) ⧸ P.subgroupOf (P ⊔ Q)) ∣ Nat.card ↥Q :=
    Subgroup.card_dvd_of_surjective (mk'_comp_inclusion_surjective hQP)
  rw [← h1]
  exact Nat.mul_dvd_mul_left _ h3

theorem coprime_card_sup {P Q : Subgroup G} (hQP : Admits Q P)
    (hP : Nat.Coprime p (Nat.card ↥P)) (hQ : Nat.Coprime p (Nat.card ↥Q)) :
    Nat.Coprime p (Nat.card ↥(P ⊔ Q)) :=
  (Nat.Coprime.mul_right hP hQ).coprime_dvd_right (card_sup_dvd_mul hQP)

theorem isSectionOf_sup {P Q : Subgroup G} (hQP : Admits Q P) {S : Type*} [Group S]
    [IsSimpleGroup S] (hS : IsSectionOf S ↥(P ⊔ Q)) :
    IsSectionOf S ↥P ∨ IsSectionOf S ↥Q := by
  have := normal_subgroupOf_sup hQP
  rcases hS.of_hom (QuotientGroup.mk' (P.subgroupOf (P ⊔ Q))) with h | h
  · rw [QuotientGroup.ker_mk'] at h
    exact Or.inl (h.trans (IsSectionOf.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ P ⊔ Q)).symm))
  · exact Or.inr (h.trans (IsSectionOf.of_surjective _ (mk'_comp_inclusion_surjective hQP)))

theorem cenIn_sup_le_sup_of_isPGroup [Finite G] (hp : p.Prime) {E P Q : Subgroup G}
    (hE : IsPGroup p E) (hEP : Admits E P) (hEQ : Admits E Q) (hQP : Admits Q P)
    (hcop : Nat.Coprime p (Nat.card (P ⊔ Q : Subgroup G))) :
    cenIn (P ⊔ Q) (E : Set G) ≤ cenIn P (E : Set G) ⊔ cenIn Q (E : Set G) := by
  intro x hx
  obtain ⟨hxPQ, hxE⟩ := Subgroup.mem_inf.mp hx
  have hx' : x ∈ (P : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P Q hQP]
    exact hxPQ
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_centralizer hp hE
    (hcop.coprime_dvd_right (Subgroup.card_dvd_of_le le_sup_left)) hEP hEQ hx' hxE
  exact Subgroup.mul_mem_sup ha hb

theorem isSolvable_sup {X D : Subgroup G} (hDX : Admits D X) (hD : Group.IsSolvable ↥D)
    (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥(X ⊔ D) := by
  have hn := normal_subgroupOf_sup hDX
  have := hX
  have := hD
  have h1 : Group.IsSolvable ↥(X.subgroupOf (X ⊔ D)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ X ⊔ D)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : X ≤ X ⊔ D)).injective
  have h2 : Group.IsSolvable (↥(X ⊔ D) ⧸ X.subgroupOf (X ⊔ D)) :=
    Group.isSolvable_of_surjective (mk'_comp_inclusion_surjective hDX)
  exact Group.isSolvable_of_ker_le_range (X.subgroupOf (X ⊔ D)).subtype
    (QuotientGroup.mk' (X.subgroupOf (X ⊔ D))) (by simp)

end AssocSup

theorem signalizerNearPSolvable_sup [Finite G] {P Q : Subgroup G} (hQP : Admits Q P)
    (hP : signalizerNearPSolvable p ↥P) (hQ : signalizerNearPSolvable p ↥Q) :
    signalizerNearPSolvable p ↥(P ⊔ Q) := by
  obtain ⟨hcopP, hP'⟩ := signalizerNearPSolvable_iff.mp hP
  obtain ⟨hcopQ, hQ'⟩ := signalizerNearPSolvable_iff.mp hQ
  refine signalizerNearPSolvable_iff.mpr ⟨AssocSup.coprime_card_sup hQP hcopP hcopQ, ?_⟩
  intro S _ _ hS hnc
  rcases AssocSup.isSectionOf_sup hQP hS with h | h
  · exact hP' S h hnc
  · exact hQ' S h hnc

theorem cenIn_sup_le_sup [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A) {P Q : Subgroup G}
    (hAP : Admits A P) (hAQ : Admits A Q) (hQP : Admits Q P)
    (hcop : Nat.Coprime p (Nat.card (P ⊔ Q : Subgroup G))) {a : G} (ha : a ∈ A) :
    cenIn (P ⊔ Q) {a} ≤ cenIn P {a} ⊔ cenIn Q {a} := by
  have hz : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hpA := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA
  have h := AssocSup.cenIn_sup_le_sup_of_isPGroup hp (hpA.to_le hz) (hz.trans hAP)
    (hz.trans hAQ) hQP hcop
  unfold cenIn at h ⊢
  rwa [centralizer_zpowers_eq_singleton] at h

theorem cenIn_sup_le_sup_of_subgroup [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {P Q : Subgroup G} (hAP : Admits A P) (hAQ : Admits A Q) (hQP : Admits Q P)
    (hcop : Nat.Coprime p (Nat.card (P ⊔ Q : Subgroup G))) :
    cenIn (P ⊔ Q) (A : Set G) ≤ cenIn P (A : Set G) ⊔ cenIn Q (A : Set G) :=
  AssocSup.cenIn_sup_le_sup_of_isPGroup hp
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA) hAP hAQ hQP hcop

theorem sup_mem_assoc [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A) {P Q : Subgroup G}
    (hP : P ∈ assoc p A θ) (hQ : Q ∈ assoc p A θ) (hQP : Admits Q P) :
    P ⊔ Q ∈ assoc p A θ := by
  obtain ⟨hAP, hcopP, hθP, hnearP, hsolP⟩ := mem_assoc_iff.mp hP
  obtain ⟨hAQ, hcopQ, hθQ, hnearQ, hsolQ⟩ := mem_assoc_iff.mp hQ
  have hcop := AssocSup.coprime_card_sup hQP hcopP hcopQ
  refine mem_assoc_iff.mpr ⟨Admits.sup hAP hAQ, hcop, fun a ha ha1 => ?_,
    signalizerNearPSolvable_sup hQP hnearP hnearQ, ?_⟩
  · exact (cenIn_sup_le_sup hp hA hAP hAQ hQP hcop ha).trans (sup_le (hθP a ha ha1) (hθQ a ha ha1))
  · have hadm : Admits (cenIn Q (A : Set G)) (cenIn P (A : Set G)) := by
      refine Subgroup.le_normalizer_iff.mpr fun q hq x hx => ?_
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
      obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hQP q hqQ x hxP,
        mul_mem (mul_mem hqC hxC) (inv_mem hqC)⟩
    have hs : Group.IsSolvable ↥(cenIn P (A : Set G) ⊔ cenIn Q (A : Set G)) :=
      AssocSup.isSolvable_sup hadm hsolQ hsolP
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (cenIn_sup_le_sup_of_subgroup hp hA hAP hAQ hQP hcop))

theorem sup_dsub_mem_mtil [Finite G] (hθ : NearFunctor p A θ) {X : Subgroup G}
    (hX : X ∈ mhat p A θ) : X ⊔ dsub A θ ∈ mtil p A θ :=
  ⟨sup_mem_assoc hθ.prime hθ.elemAbelian hX.1 (dsub_mem_assoc hθ) hX.2, le_sup_right⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
