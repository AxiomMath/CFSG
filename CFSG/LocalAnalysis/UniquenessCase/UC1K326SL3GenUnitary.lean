module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenCore
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenFrame
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenField
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenZeta
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldAut
public import CFSG.LieType.SeitzGeneration.HeisTorusU84
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3)

namespace SL3G

section FrameUnitary

variable {K : Type} [Field K]

private theorem frame_unitary_exists {p f : ℕ} (h : UnitaryFieldData p f K) (hq3 : p ^ f % 3 = 2)
    (T Q : Subgroup (GL (Fin 3) K))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hQn : ∀ s ∈ T, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    {u : GL (Fin 3) K} (hu : u ∈ Q) (huU : u ∈ unitarySU p f K 3) (hu3 : u ^ 3 = 1)
    (hnsc : ∀ c : K, (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    ∃ (θ : GL (Fin 3) K) (ε : Fin 3 → K), θ ∈ unitaryIsom3 h ∧ IsFrame T Q u θ ε := by
  obtain ⟨hdet, hU⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp huU
  have hmem : u ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hU
  let G : Subgroup (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3)) := Subgroup.zpowers ⟨u, hmem⟩
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact (Commute.zpow_zpow_self _ m n).eq
  have hpow : ∀ x ∈ G, x ^ 3 = 1 := by
    rintro x ⟨m, rfl⟩
    have h3 : (⟨u, hmem⟩ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 3)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hu3)
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h3,
      _root_.one_zpow]
  have h3dvd : 3 ∣ p ^ f + 1 := by omega
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three h3dvd G hcomm hpow
  have hdiag := hP ⟨u, hmem⟩ (Subgroup.mem_zpowers _)
  have hθ : (((P : GL (Fin 3) K)⁻¹ * u * (P : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := hdiag
  obtain ⟨ε, hε, hinj, hone⟩ := diag_eigenvalues hθ hu3 hdet hnsc
  refine ⟨(P : GL (Fin 3) K), ε, ?_, frame_of_diag T Q hQab hQn hu hε hinj hone⟩
  have hPmem := P.2
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hPmem
  refine CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.mpr ?_
  simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hPmem

end FrameUnitary

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

private theorem classify_unitary (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (α : MulAut ↥(unitarySU p f K 3)) (hα : α ^ 3 = 1) :
    ∃ (σ : K ≃+* K) (B : GL (Fin 3) K), (σ = 1 ∨ orderOf σ = 3) ∧
      ActsAs (unitarySU p f K 3).subtype α σ B := by
  have key : ∀ (σ : K ≃+* K) (B : GL (Fin 3) K),
      (∀ g : unitarySU p f K 3, ((α g : unitarySU p f K 3) : GL (Fin 3) K) =
        B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ (g : GL (Fin 3) K) * B⁻¹) →
      ActsAs (unitarySU p f K 3).subtype α σ B := by
    intro σ B hB g
    have := congrArg Units.val (hB g)
    simpa [Units.val_mul, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut] using this
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.exists_suConj_or_conj_suField
      h hq hα with ⟨B, hB⟩ | ⟨σ, H, hσ, hθ⟩
  · refine ⟨1, (B : GL (Fin 3) K), Or.inl rfl, key 1 _ fun g => ?_⟩
    rw [hB, CFSG.RankThree.PartTwo.KFacts.coe_suConj]
    simp
  · refine ⟨σ, (H : GL (Fin 3) K) *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ (H : GL (Fin 3) K)⁻¹,
      Or.inr hσ, key σ _ fun g => ?_⟩
    rw [hθ]
    simp only [MulAut.mul_apply]
    rw [← map_inv, CFSG.RankThree.PartTwo.KFacts.coe_suConj,
      CFSG.RankThree.PartTwo.KFacts.coe_suField, CFSG.RankThree.PartTwo.KFacts.coe_suConj]
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Subgroup.coe_inv]
    group

private theorem unitary_conj (h : UnitaryFieldData p f K) :
    ConjProp (unitarySU p f K 3).subtype (unitaryIsom3 h) := by
  intro θ hθ
  refine ⟨CFSG.RankThree.PartTwo.KFacts.suConj h ⟨θ⁻¹, inv_mem hθ⟩, fun g => ?_⟩
  change ((CFSG.RankThree.PartTwo.KFacts.suConj h ⟨θ⁻¹, inv_mem hθ⟩ g : unitarySU p f K 3) :
    GL (Fin 3) K) = _
  rw [CFSG.RankThree.PartTwo.KFacts.coe_suConj]
  simp

private theorem unitary_frame (h : UnitaryFieldData p f K) (hq3 : p ^ f % 3 = 2) :
    FrameProp (unitarySU p f K 3).subtype (unitaryIsom3 h) := by
  intro T Q u hQab hQn hu huR hu3 hnsc
  obtain ⟨g, rfl⟩ := huR
  obtain ⟨θ, ε, hθ, hfr⟩ := frame_unitary_exists h hq3 T Q hQab hQn hu g.2 hu3 hnsc
  exact ⟨θ, hθ, ε, hfr⟩

private theorem unitary_block (h : UnitaryFieldData p f K) (hq3 : p ^ f % 3 = 2) (hq : 2 < p ^ f) :
    BlockProp (unitarySU p f K 3).subtype := by
  intro H hH
  have hq4 : 4 ≤ p ^ f := by omega
  have hle := CFSG.LieType.SeitzGeneration.unitarySU_le_of_blocks h hq4 (by norm_num)
    (H.map (unitarySU p f K 3).subtype)
    (fun a b hab g hg hblk => ⟨⟨g, hg⟩, hH a b hab ⟨g, hg⟩ hblk, rfl⟩)
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp (hle g.2)
  have hg'g : g' = g := Subtype.ext hgg'
  exact hg'g ▸ hg'

private theorem unitary_field (h : UnitaryFieldData p f K) (hq3 : p ^ f % 3 = 2) :
    FieldProp (unitarySU p f K 3).subtype := by
  haveI := h.finite
  intro α T σ B hH hσ hα hmono hdiag
  obtain ⟨ζ, hζq, hζ, h1, h2, h3⟩ := exists_zeta_unitary h hq3 hσ
  refine field_false (Subgroup.subtype_injective _) hH hα hmono hdiag hζ ?_ h1 h2 h3
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
  exact ⟨⟨_, CFSG.Open.StatedCenterThree.diagGL_mem hq0 hζq⟩, rfl⟩

theorem unitaryModelGen (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (hq3 : p ^ f % 3 = 2) :
    ModelGen ↥(unitarySU p f K 3) := by
  haveI := h.finite
  exact model_generic (Subgroup.subtype_injective _) (unitary_conj h) (unitary_frame h hq3)
    (classify_unitary h hq) (unitary_block h hq3 hq) (unitary_field h hq3)

end Unitary

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
