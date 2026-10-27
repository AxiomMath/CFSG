module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux69
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux610

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma67a
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    cenIn (thetaOf θ B) (dOne p A θ) =
        CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) ∧
      IsMulCommutative (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) :=
  ⟨Sec6S31.cenIn_dOne_eq h hB, (Sec6S31.fitting_eq_cenIn_kOf h hB).2⟩

theorem lemma67b
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    ssol p A θ ⊓ kOf (thetaOf θ B) ≤ thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dTwo p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ∧
      thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dTwo p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ≤
        khat (thetaOf θ B) :=
  Sec6S31.sectionCentralizer_d2 h hB

theorem lemma67c
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    thetaOf θ B ⊓ sectionCentralizer
        (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
        (dZero p A θ ⊔ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) ≤
      ssol p A θ ⊓ kOf (thetaOf θ B) :=
  Sec6S31.sectionCentralizer_d0 h hB

theorem lemma68a
    (h : Counterexample p A θ) {B J : Subgroup G} (hB : B ∈ rSet p A θ)
    (hJ : J ∈ lcal (thetaOf θ B)) (hJ3 : ¬ IsPSL3 p J) :
    ∃ t ∈ dZero p A θ, orderOf t = 2 ∧
      ∀ x ∈ dOne p A θ, x ≠ 1 → t * x * t⁻¹ ≠ x := by
  have H := Sec6S31.hyp h hB
  have hK := H.semisimpleAction
  have hJ' : J ∈ lcal (kOf (thetaOf θ B)) := H.lcal_kOf ▸ hJ
  have hall : ∀ J' ∈ lcal (kOf (thetaOf θ B)), ¬ IsPSL3 p J' := fun J' hJ'' ⟨e⟩ =>
    hJ3 (by
      obtain ⟨e'⟩ := Sec6S31.nonempty_mulEquiv h hB hJ' hJ''
      exact ⟨e'.trans e⟩)
  obtain ⟨t, ht, ht2, htz⟩ := Sec6S31.exists_involution_fpf hK hall
  rw [Sec6S31.cenIn_kOf_eq h hB] at ht htz
  exact ⟨t, ht, ht2, htz⟩

theorem lemma68b
    (h : Counterexample p A θ) {B J : Subgroup G} (hB : B ∈ rSet p A θ)
    (_hJ : J ∈ lcal (thetaOf θ B)) (_hJ3 : ¬ IsPSL3 p J) {t : G} (ht : t ∈ dZero p A θ)
    (_ht2 : orderOf t = 2) (htD : ∀ x ∈ dOne p A θ, x ≠ 1 → t * x * t⁻¹ ≠ x) :
    ∀ x ∈ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)), x ≠ 1 →
      t * x * t⁻¹ ≠ x := by
  have hK := (Sec6S31.hyp h hB).semisimpleAction
  have ht' : t ∈ cenIn (kOf (thetaOf θ B)) A := by
    rw [Sec6S31.cenIn_kOf_eq h hB]
    exact ht
  have htD' : ∀ w ∈ CFSG.fittingSubgroupOf (cenIn (kOf (thetaOf θ B)) A), w ≠ 1 →
      t * w * t⁻¹ ≠ w := by
    rw [Sec6S31.cenIn_kOf_eq h hB]
    exact htD
  intro x hx hx1
  exact Sec6S31.fpf_fProd hK ht' htD' x ((Sec6S31.fProd_eq h hB).symm ▸ hx) hx1

theorem lemma69
    (h : Counterexample p A θ) {B J : Subgroup G} (hB : B ∈ rSet p A θ)
    (hJ : J ∈ lcal (thetaOf θ B)) (hJ3 : IsPSL3 p J) :
    IsChiefFactorOf ((thetaOf θ B ⊓ ssol p A θ) ⊔ A)
        (CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ)) ⊥ ∧
      ∀ M : Subgroup G, IsChiefFactorOf ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) M ⊥ →
        M ≤ kOf (thetaOf θ B) →
        M = CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ) := by
  rw [inf_comm (kOf (thetaOf θ B))]
  refine ⟨⟨⟨bot_le, ?_⟩, ⟨Sec6S31.fitting_le_gamma _ _, Sec6S31.admits_fitting h hB⟩,
    bot_lt_iff_ne_bot.mpr (Sec6S31.fitting_ne_bot h hB hJ), ?_⟩, ?_⟩
  · exact le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  · intro N hN _ hle
    by_cases hN1 : N = ⊥
    · exact Or.inl hN1
    · exact Or.inr (Sec6S31.fitting_minimal h hB hJ hJ3 hle hN.2 hN1)
  · intro M hM hMK
    exact Sec6S31.eq_fitting_of_minimal h hB hJ hJ3 hMK hM.2.1
      (bot_lt_iff_ne_bot.mp hM.2.2.1)
      (fun N' hN' hle => hM.2.2.2 N' hN' bot_le hle)

theorem lemma610
    (h : Counterexample p A θ) {E F J K : Subgroup G} (hE : E ∈ rSet p A θ)
    (hF : F ∈ rSet p A θ) (hJ : J ∈ lcal (thetaOf θ E)) (hK : K ∈ lcal (thetaOf θ F)) :
    Nonempty (↥J ≃* ↥K) :=
  Sec6S31.nonempty_mulEquiv_of_mem_rSet h hE hF hJ hK

theorem lemma611
    (h : Counterexample p A θ) {E : Subgroup G} (hE : E ∈ rSet p A θ) :
    sOne p A θ ⊓ thetaOf θ E =
      CFSG.fittingSubgroupOf (kOf (thetaOf θ E) ⊓ ssol p A θ) := by
  rw [Sec6S31.sOne_inf_eq h hE, Sec6S31.cenIn_dOne_eq h hE, inf_comm]

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
