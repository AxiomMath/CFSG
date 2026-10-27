module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup TauCeti
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr
  glCongr_statedSp glCongr_statedSU)
open CFSG.ClassicalInvolution.Upgrade (fieldIsoOfCard map_statedOmega statedQuadOdd_comp
  statedQuadPlus_comp statedQuadMinus_comp irreducible_map)

section Index

private theorem uc22p20w_equiv_of_fixedField_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (K : Type) → [Field K] → Subgroup (GL ι K))
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    (d : ValidLieTypeIndex) (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) : Nonempty (G ≃* d.Group) := by
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let φ : K ≃+* ↥d.fixedField :=
    fieldIsoOfCard (hK.trans (ValidLieTypeIndex.card_fixedField d).symm)
  exact ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans eT.symm⟩

theorem uc22p20w_index_psl {P : Type} [Group P] {m p f : ℕ} (h : StatedClassicalModel P .PSL m p f)
    (hdup : ¬ ((m = 2 ∧ (p ^ f = 4 ∨ p ^ f = 5 ∨ p ^ f = 9)) ∨ (m = 3 ∧ p ^ f = 2) ∨
      (m = 4 ∧ p ^ f = 2))) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.A (m - 1) q).Valid), q.p = p ∧ q.card = p ^ f ∧
      Nonempty (P ≃* (CFSGIndex.lie ⟨LieTypeIndex.A (m - 1) q, hv⟩).Group) := by
  have hp : p.Prime := h.1.1
  have hf : 1 ≤ f := h.1.2.1
  have hm : 2 ≤ m := h.1.2.2.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hdup' : ¬ (LieTypeIndex.A (m - 1) q).IsDuplicateRepresentative := by
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def, q]
    intro hd
    apply hdup
    omega
  have hv := CFSG.ClassicalModels.linearCatalog_index_valid m p f h.1 hdup'
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K m p f (by omega) hKcard
  have hdim : m - 1 + 1 = m := by omega
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (m - 1) q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A (m - 1) q, hv⟩) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField p f) := by
    rw [hdim] at eC
    exact eC
  exact ⟨q, hv, rfl, rfl, ⟨(e.trans eK).trans eC'.symm⟩⟩

private theorem uc22p20w_unitary_index_valid (m p f : ℕ) (h : StatedLieAdmissible .PSU m p f) :
    (LieTypeIndex.twistedA (m - 1) ⟨p, f, h.1, by have hf := h.2.1; omega⟩).Valid := by
  obtain ⟨hp, hf, hm, h32⟩ := h
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def, not_false_eq_true, and_true]
  refine ⟨by omega, fun hr => ?_⟩
  have hm3 : m = 3 := by omega
  have hq2 : p ^ f ≠ 2 := fun hq => h32 (by rw [hm3, hq])
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  omega

theorem uc22p20w_index_psu {P : Type} [Group P] {m p f : ℕ} (h : StatedClassicalModel P .PSU m p f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA (m - 1) q).Valid), q.p = p ∧ q.card = p ^ f ∧
      Nonempty (P ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA (m - 1) q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hm : 3 ≤ m := hadm.2.2.1
  have hv := uc22p20w_unitary_index_valid m p f hadm
  let _ : Fact p.Prime := ⟨hp⟩
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin m) φ) (glCongr_statedSU φ m (p ^ f))
    (glCongr_statedScalars φ)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hv' : (LieTypeIndex.twistedA m' q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m' q hv'
  exact ⟨q, hv', rfl, rfl, ⟨(e.trans e1).trans eT.symm⟩⟩

theorem uc22p20w_index_psp {P : Type} [Group P] {m f : ℕ} (h : StatedClassicalModel P .PSp m 2 f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B m q).Valid), q.p = 2 ∧ q.card = 2 ^ f ∧
      Nonempty (P ≃* (CFSGIndex.lie ⟨LieTypeIndex.B m q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hf : 1 ≤ f := hadm.2.1
  have hm : 2 ≤ m := hadm.2.2.1
  let q : PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · have hq2 : 2 ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
    have hq3 : 2 ^ f ≠ 3 := by
      intro h3
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    have hv : (LieTypeIndex.B 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def, true_and, le_refl]
      exact ⟨hq2, hq3⟩
    obtain ⟨e⟩ := uc22p20w_equiv_of_fixedField_model (fun K _ => StatedSp 2 K)
      (fun φ => glCongr_statedSp φ 2) ⟨.B 2 q, hv⟩
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
    exact ⟨q, hv, rfl, rfl, ⟨e⟩⟩
  · have hv : (LieTypeIndex.B m q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
    obtain ⟨e⟩ := uc22p20w_equiv_of_fixedField_model (fun K _ => StatedSp m K)
      (fun φ => glCongr_statedSp φ m) ⟨.B m q, hv⟩
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj m q hv rfl hm3)
      (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
    exact ⟨q, hv, rfl, rfl, ⟨e⟩⟩

theorem uc22p20w_index_pomegaPlus {P : Type} [Group P] {m p f : ℕ}
    (h : StatedClassicalModel P .POmegaPlus m p f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.D m q).Valid), q.p = p ∧ q.card = p ^ f ∧
      Nonempty (P ≃* (CFSGIndex.lie ⟨LieTypeIndex.D m q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hm⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.D m q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  obtain ⟨e⟩ := uc22p20w_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus m K))
    (fun φ => map_statedOmega φ (statedQuadPlus_comp φ)) ⟨.D m q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid m q hv)
    (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact ⟨q, hv, rfl, rfl, ⟨e⟩⟩

theorem uc22p20w_index_pomegaMinus {P : Type} [Group P] {m p f : ℕ}
    (h : StatedClassicalModel P .POmegaMinus m p f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD m q).Valid), q.p = p ∧ q.card = p ^ f ∧
      Nonempty (P ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedD m q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hm⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.twistedD m q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      m q hv
  obtain ⟨φ⟩ : Nonempty (K ≃+* ↥(ValidLieTypeIndex.fixedField ⟨.twistedD m q, hv⟩)) := by
    have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD m q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact ⟨fieldIsoOfCard (by
      rw [ValidLieTypeIndex.card_fixedField]
      simp [ValidLieTypeIndex.fieldOrder, q, hK])⟩
  have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD m q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := m) (by omega)
    (irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (map_statedOmega φ (statedQuadMinus_comp (n := m) (b := b) (c := c) φ rfl rfl))
    (glCongr_statedScalars φ)
  exact ⟨q, hv, rfl, rfl, ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

end Index

section Rank

theorem uc22p20w_pRank_psl (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ} (hS : StatedClassicalModel (K ⧸ center K) .PSL m 2 n)
    (hm : 3 ≤ m) (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkLin m true (2 ^ n) r (Nat.card (center K)) := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdup : ¬ ((m = 2 ∧ (2 ^ n = 4 ∨ 2 ^ n = 5 ∨ 2 ^ n = 9)) ∨ (m = 3 ∧ 2 ^ n = 2) ∨
      (m = 4 ∧ 2 ^ n = 2)) := by
    rintro (⟨h2, -⟩ | ⟨-, h⟩ | ⟨-, h⟩) <;> omega
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_psl hS hdup
  have := hT K hq ⟨.A (m - 1) q, hv⟩ hqp ⟨e⟩ r hr hr2
  rw [this]
  show rkLin (m - 1 + 1) true q.card r (Nat.card (center K)) = _
  rw [hqc, Nat.sub_add_cancel (by omega)]

theorem uc22p20w_pRank_psu (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ} (hS : StatedClassicalModel (K ⧸ center K) .PSU m 2 n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkLin m false (2 ^ n) r (Nat.card (center K)) := by
  have hm : 3 ≤ m := hS.1.2.2.1
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_psu hS
  have := hT K hq ⟨.twistedA (m - 1) q, hv⟩ hqp ⟨e⟩ r hr hr2
  rw [this]
  show rkLin (m - 1 + 1) false q.card r (Nat.card (center K)) = _
  rw [hqc, Nat.sub_add_cancel (by omega)]

theorem uc22p20w_pRank_psp (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ} (hS : StatedClassicalModel (K ⧸ center K) .PSp m 2 n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkSp m (2 ^ n) r := by
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_psp hS
  have := hT K hq ⟨.B m q, hv⟩ hqp ⟨e⟩ r hr hr2
  rw [this]
  show rkSp m q.card r = _
  rw [hqc]

theorem uc22p20w_pRank_pomegaPlus (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hS : StatedClassicalModel (K ⧸ center K) .POmegaPlus m 2 n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkOmPlus m (2 ^ n) r := by
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_pomegaPlus hS
  have := hT K hq ⟨.D m q, hv⟩ hqp ⟨e⟩ r hr hr2
  rw [this]
  show rkOmPlus m q.card r = _
  rw [hqc]

theorem uc22p20w_pRank_pomegaMinus (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {m n : ℕ}
    (hS : StatedClassicalModel (K ⧸ center K) .POmegaMinus m 2 n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkOmMinus m (2 ^ n) r := by
  obtain ⟨q, hv, hqp, hqc, ⟨e⟩⟩ := uc22p20w_index_pomegaMinus hS
  have := hT K hq ⟨.twistedD m q, hv⟩ hqp ⟨e⟩ r hr hr2
  rw [this]
  show rkOmMinus m q.card r = _
  rw [hqc]

end Rank

section Exceptional


theorem uc22p20w_pRank_g2 (hT : LieOddRankChev) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {n : ℕ} (hn : 2 ≤ n)
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ center K) .G2 2 n) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : CFSG.Open.pRank r (⊤ : Subgroup K) = rkG2 (2 ^ n) r := by
  obtain ⟨K', _, _, hK'card, ⟨eK⟩⟩ := hM.2
  let q : PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hv : (LieTypeIndex.G2 q).Valid :=
    ⟨show 3 ≤ q.card from by simp only [PrimePower.card_def, q]; omega, fun h => h⟩
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv rfl K'
    (by simpa [PrimePower.card_def, q] using hK'card)
  have := hT K hq ⟨.G2 q, hv⟩ rfl ⟨eK.trans b⟩ r hr hr2
  rw [this]
  rfl

theorem uc22p20w_four_le_pRank_three_exc {K : Type} [Group K] [Finite K] (hZ : center K = ⊥)
    {t : StatedLieTag} {m n : ℕ} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hn : 1 ≤ n) (hM : LieModel (K ⧸ center K) t m 2 n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have e : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (Or.inl rfl)
      (uc22p20v_exc_model hM (by decide)).2.2
  · exact CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (Or.inr (Or.inl rfl))
      (uc22p20v_exc_model hM (by decide)).2.2
  · exact CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (Or.inr (Or.inr (Or.inl rfl)))
      (uc22p20v_exc_model hM (by decide)).2.2
  · exact CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (Or.inr (Or.inr (Or.inr rfl)))
      (uc22p20v_exc_model hM (by decide)).2.2
  · exact CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two hn
      (uc22p20v_exc_model hM (by decide)).2.2

end Exceptional

end CFSG.LocalAnalysis.UniquenessCase.UC22
