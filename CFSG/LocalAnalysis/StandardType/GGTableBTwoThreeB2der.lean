module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagSp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA TwoThree

namespace TwoThree

section MatConj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem finite_GL : Finite (GL ι K) :=
  Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) Units.val_injective

theorem card_dvd_of_subset_matConjImage {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K))) {X : Subgroup (MulAut (LargeEvenProj H))}
    (hX : (X : Set (MulAut (LargeEvenProj H))) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S) :
    Nat.card X ∣ Nat.card (GL ι K) := by
  have := finite_GL (ι := ι) (K := K)
  have hXr : X ≤ (projConj H).range := by
    intro φ hφ
    obtain ⟨A, hA, rfl⟩ := exists_eq_projConj hS (hX hφ)
    exact ⟨_, rfl⟩
  have : Finite (Subgroup.normalizer (H : Set (GL ι K))) := inferInstance
  have h1 : Nat.card X ∣ Nat.card (projConj H).range := Subgroup.card_dvd_of_le hXr
  have h2 : Nat.card (projConj H).range ∣ Nat.card (Subgroup.normalizer (H : Set (GL ι K))) :=
    Subgroup.card_dvd_of_surjective (projConj H).rangeRestrict_surjective
  exact h1.trans (h2.trans (Subgroup.card_subgroup_dvd_card _))

theorem card_lt_of_not_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K))) (hGL : ¬ p ^ 3 ∣ Nat.card (GL ι K))
    {X : Subgroup (MulAut (LargeEvenProj H))} (hXA : IsElemAbelian p X)
    (hX : (X : Set (MulAut (LargeEvenProj H))) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S) :
    Nat.card X < p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_GL (ι := ι) (K := K)
  have hdvd := card_dvd_of_subset_matConjImage hS hX
  have : Finite X := by
    have hpos : 0 < Nat.card (GL ι K) := Nat.card_pos
    exact Nat.finite_of_card_ne_zero (fun h => by rw [h] at hdvd; omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hXA)
  rw [hk] at hdvd ⊢
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    exact hlt (Nat.pow_lt_pow_right hp.one_lt (by omega))
  exact hGL ((pow_dvd_pow p hk3).trans hdvd)

theorem ggBstarBound_of_not_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K))) (hGL : ¬ p ^ 3 ∣ Nat.card (GL ι K)) :
    GGBstarBound p 0 (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) :=
  ggBstarBound_of_card_lt fun _ hXI hX => card_lt_of_not_dvd hp hS hGL hX hXI

theorem ggEndNode_of_not_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup (GL ι K)} {S : Set (GL ι K)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K))) (hGL : ¬ p ^ 3 ∣ Nat.card (GL ι K)) :
    GGEndNode p 0 (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (LargeEvenProj H))) :
      Set (MulAut (LargeEvenProj H))) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hlt := card_lt_of_not_dvd hp hS hGL hX hXI
  rw [hcard] at hlt
  omega

end MatConj

section B2der

variable {K : Type} [Field K] [Finite K]

theorem card_GL_four (hK : Nat.card K = 2) : Nat.card (GL (Fin 2 ⊕ Fin 2) K) = 20160 := by
  have : Fintype K := Fintype.ofFinite K
  let e : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 4) K :=
    Units.mapEquiv (Matrix.reindexAlgEquiv K K (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).toMulEquiv
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [hq, Fin.prod_univ_four]
  norm_num

theorem not_dvd_card_GL_four (hK : Nat.card K = 2) : ¬ 3 ^ 3 ∣ Nat.card (GL (Fin 2 ⊕ Fin 2) K) := by
  rw [card_GL_four hK]
  norm_num

theorem largeEvenScalars_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] (hK : Nat.card K = 2) :
    LargeEvenScalars ι K = ⊥ :=
  CFSG.StandardType.largeEvenScalars_eq_bot hK

theorem two_dvd_card_b2der (hK : Nat.card K = 2) :
    2 ∣ Nat.card (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) := by
  obtain ⟨e⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK
  have h1 : Nat.card (LargeEvenSpGroup K 2) = 720 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulEquiv.ofBijective
      CFSG.ComponentClassification.PresentationLocal.omegaPerm
      ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
        CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h2 : Nat.card (commutator (LargeEvenSpGroup K 2)) = 360 := by
    have := Subgroup.card_mul_index (commutator (LargeEvenSpGroup K 2))
    rw [index_commutator_largeEvenSpGroup hK, h1] at this
    omega
  have h3 : Nat.card (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup _) = 360 := by
    rw [← Subgroup.map_subtype_commutator,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact h2
  have hN : Nat.card ((LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
      ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) = 1 := by
    rw [largeEvenScalars_eq_bot hK, Subgroup.bot_subgroupOf, Subgroup.card_bot]
  have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
  rw [hN, mul_one, h3] at h5
  change 2 ∣ Nat.card (↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ⧸
    (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
  rw [← h5]
  norm_num

theorem gsp_subset_normalizer (hK : Nat.card K = 2) :
    LargeEvenGSpSet K 2 ⊆ Subgroup.normalizer
      ((⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup _) : Set (GL (Fin 2 ⊕ Fin 2) K)) :=
  fun _ hA => mem_normalizer_commutator (mem_largeEvenSpGroup_of_gsp hK hA)

end B2der

end TwoThree

theorem recipeB2der_tableB_three {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic 2 2 true Q) :
    LargeEvenRecipeSymplectic 2 2 true fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I ∧ GGEndNode 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact ⟨0, ggTorusLift_zero (two_dvd_card_b2der hK),
    ggBstarBound_of_not_dvd Nat.prime_three (gsp_subset_normalizer hK) (not_dvd_card_GL_four hK),
    ggEndNode_of_not_dvd Nat.prime_three (gsp_subset_normalizer hK) (not_dvd_card_GL_four hK)⟩

@[expose] def GGB2derThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.tag = .B2der

theorem largeEvenLabelAll_b2derThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGB2derThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, ht⟩ := h
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeB2der_tableB_three hQ

theorem largeEvenLabelAll_outdiag_b2der {lab : LargeEvenLabel} (h : lab.tag = .B2der) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  subst h
  intro Q hQ
  exact recipeB2der_outdiag hQ

theorem ggBstarInputOn_b2der : GGBstarInputOn GGB2derThreeLabel := by
  intro G _ _ p B x L hT hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hnc := (ggLNoncyclicInputOn_of_labels (S := fun lab => lab.tag = .B2der)
    fun _ _ h => largeEvenLabelAll_outdiag_b2der h) G p B x L hT
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hM)
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => GGB2derThreeLabel p lab)
    (fun lab _ hs => largeEvenLabelAll_b2derThree hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_ggBstar_of_marking hT hnc
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
      ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, (hP.2.imp fun _ h => ⟨h.1, h.2.1⟩)⟩) hM')

theorem ggStdSubPreInputOn_b2der : GGStdSubPreInputOn GGB2derThreeLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ _ _ h =>
    (largeEvenLabelAll_b2derThree h).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end CFSG.StandardType
