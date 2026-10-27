module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagCoatom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointActionTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Blueprint.LieModelAPI

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Blueprint CFSG.BenderSuzuki.MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem isCoatom_normalizer_sylow_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) :
    ∀ U : Sylow 2 (SuzukiMatrixGroup m),
      IsCoatom (Subgroup.normalizer ((U : Subgroup (SuzukiMatrixGroup m)) :
        Set (SuzukiMatrixGroup m))) := by
  have h2tr : MulAction.IsMultiplyPretransitive (SuzukiMatrixGroup m)
      (Sylow 2 (SuzukiMatrixGroup m)) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) a c
    have hb : g • b ≠ c := by
      intro h
      apply hab
      apply MulAction.injective g
      change g • a = g • b
      rw [hg, h]
    obtain ⟨u, hu, -⟩ := SzPointModel.regular_sylow m hm c (g • b) d hb hcd.symm
    refine ⟨(u : SuzukiMatrixGroup m) * g, ?_, ?_⟩
    · rw [mul_smul, hg]
      exact (Sylow.smul_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer u.2)
    · rw [mul_smul]
      exact hu
  haveI : MulAction.IsPreprimitive (SuzukiMatrixGroup m)
      (Sylow 2 (SuzukiMatrixGroup m)) :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2tr
  have hcard : Nat.card (Sylow 2 (SuzukiMatrixGroup m)) =
      (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [(suzukiTorusData_suzukiMatrixGroup m hm).card_points]
  haveI : Finite (Sylow 2 (SuzukiMatrixGroup m)) :=
    CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  haveI : Nontrivial (Sylow 2 (SuzukiMatrixGroup m)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    have : 0 < (2 ^ (2 * m + 1)) ^ 2 := by positivity
    omega
  intro U
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (SuzukiMatrixGroup m) U
  rwa [Sylow.stabilizer_eq_normalizer] at hco

theorem isCoatom_normalizer_sylow_suzukiGroup {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ S : Sylow 2 (suzukiGroup a K),
      IsCoatom (Subgroup.normalizer ((S : Subgroup (suzukiGroup a K)) :
        Set (suzukiGroup a K))) := by
  let e := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK
  intro S
  let S' : Sylow 2 (SuzukiMatrixGroup a) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup (SuzukiMatrixGroup a)) =
      (S : Subgroup (suzukiGroup a K)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hN : Subgroup.normalizer ((S' : Subgroup (SuzukiMatrixGroup a)) :
        Set (SuzukiMatrixGroup a)) =
      (Subgroup.normalizer ((S : Subgroup (suzukiGroup a K)) :
        Set (suzukiGroup a K))).map e.toMonoidHom := by
    rw [hS']
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup (suzukiGroup a K)) e).symm
  have hco := isCoatom_normalizer_sylow_suzukiMatrixGroup a (by omega) S'
  rw [hN] at hco
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e)
    (Subgroup.normalizer ((S : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)))).1 hco

theorem isCoatom_normalizer_sylow_of_mulEquiv {Y : Type} [Group Y]
    (e : X ≃* Y)
    (hY : ∀ S : Sylow 2 Y,
      IsCoatom (Subgroup.normalizer ((S : Subgroup Y) : Set Y))) :
    ∀ S : Sylow 2 X,
      IsCoatom (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  let S' : Sylow 2 Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hN : Subgroup.normalizer ((S' : Subgroup Y) : Set Y) =
      (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom := by
    rw [hS']
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e).symm
  have hco := hY S'
  rw [hN] at hco
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e)
    (Subgroup.normalizer ((S : Subgroup X) : Set X))).1 hco

theorem kDiag_of_isSz {n : ℕ} (hX : IsSz X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hSuz : CFSG.Blueprint.SuzukiModel X 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hX).2
  obtain ⟨-, a, ha, K, hfield, hfinite, rfl, hcard, ⟨e⟩⟩ := hSuz
  letI : Field K := hfield
  letI : Finite K := hfinite
  exact kDiag_of_sylow_normalizer_coatom
    (isCoatom_normalizer_sylow_of_mulEquiv e
      (isCoatom_normalizer_sylow_suzukiGroup ha hcard))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
