module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUni
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryRankThreeCover
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LocalAnalysis.ComponentInitial


theorem GGSecFiveBCoordBUniCell.exists_frames_of_diag (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hBB : B = Bs)
    {m : ℕ} (hm : 3 ≤ m) {f : ℕ} {K : Subgroup G} {i0 : Fin (m + 1)}
    (hcell : GGSecFiveBCoordBUniCell p Bs L 𝒦 (m + 1) f K i0)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (φ : ↥(unitarySU 2 f F (m + 1)) →* K)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (m + 1) → F, LineU.ActsDiagU φ a t) :
    ∃ eta' : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)),
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull (m + 1) p ∧
      x ∈ Bs ∧ CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) ∧
      ∃ (_ : Algebra (GaloisField 2 f) F)
        (E : QuadExt (GaloisField 2 f) F (unitaryInvolution F 2 f)),
        UnitaryFieldData 2 f F ∧ ∃ π : Equiv.Perm (Fin (m + 1)), π (Fin.last m) = i0 ∧
          (∃ (κ : normOmega E m →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermOmKFrame E Bs L eta' π κ χ) ∧
          ∃ (σ : ↥(unitarySU 2 f F (m + 1)) →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermUniLFrame Bs K eta' π σ χ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, hEv, hpq, hK𝒦, -, ⟨eLs⟩, eta', -, hAL', hAK'⟩ := hcell
  have hmo : Odd m := by
    obtain ⟨j, hj⟩ := hEv
    exact ⟨j - 1, by omega⟩
  have hUF : UnitaryFieldData 2 f F := hM.field
  let _ : Algebra (GaloisField 2 f) F := galoisAlgebra hUF
  have E : QuadExt (GaloisField 2 f) F (unitaryInvolution F 2 f) := galoisQuadExt hUF
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  obtain ⟨-, hBsE, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hCK := hR.card_inf_centralizer_nbr_le hBB hNy
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      ((hR.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.2.2.1)
  obtain ⟨eS⟩ := nonempty_spinMinus_mulEquiv_normOmega E hmo (by omega)
    (CFSG.LieType.Universal.minusCoeffs_irr 2 f)
  obtain ⟨π, hπ, κ, χK, hκ⟩ := ggSecFiveBPermOmK_exists_frame hMp hp2 E hUF hpq hm rfl
    hR.1.1.2.1 hR.1.2.2.1.1 (eLs.trans eS) eta' hAL'
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC hCK (by omega) eta' hAK'
    hN φ hM hdiag π
  exact ⟨eta', hAK', hxBs, hLc, inferInstance, E, hUF, π, hπ, ⟨κ, χK, hκ⟩, σ, χ, hLF⟩

theorem GGSecFiveBCoordBUniCell.exists_frames
    (hMp : GGInnerDiagMpInput) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hBB : B = Bs)
    {m : ℕ} (hm : 3 ≤ m) {f : ℕ} {K : Subgroup G} {i0 : Fin (m + 1)}
    (hcell : GGSecFiveBCoordBUniCell p Bs L 𝒦 (m + 1) f K i0) :
    ∃ eta' : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)),
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull (m + 1) p ∧
      x ∈ Bs ∧ CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (_ : Algebra (GaloisField 2 f) F)
        (E : QuadExt (GaloisField 2 f) F (unitaryInvolution F 2 f)),
        UnitaryFieldData 2 f F ∧ ∃ π : Equiv.Perm (Fin (m + 1)), π (Fin.last m) = i0 ∧
          (∃ (κ : normOmega E m →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermOmKFrame E Bs L eta' π κ χ) ∧
          ∃ (σ : ↥(unitarySU 2 f F (m + 1)) →* G) (χ : Multiplicative (ZMod p) →* Fˣ),
            GGSecFiveBPermUniLFrame Bs K eta' π σ χ := by
  classical
  have hcellKeep := hcell
  obtain ⟨hf2, -, hpq, hK𝒦, hsu, -, ⟨etaCell, -⟩⟩ := hcell
  obtain ⟨hψ, hψker, hψrange⟩ := hsu
  have hp : p.Prime := (GGConfig.tableB_facts hR.1.1).1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hf1 : 1 ≤ f := by omega
  have hn4 : 4 ≤ m + 1 := by omega
  obtain ⟨φ, hM⟩ := exists_unitTBModel_of_su_centralImage hf1 hn4 hψ hψker hψrange
  have hLab : GGHasLabel ⟨.twA, m, f⟩ (↥K ⧸ Subgroup.center ↥K) := by
    have h := ggHasLabel_of_unitaryModel (X := K) (n := f) (d := m + 1) hM (by omega) (by
      intro hc
      have h1 := congrArg Prod.fst hc
      simp at h1
      omega)
    simpa using h
  have hΛ : LargeEvenInLambda2 ⟨.twA, m, f⟩ := by
    simp only [LargeEvenInLambda2]
    exact ⟨by omega, by omega, fun h => by omega⟩
  have hcover : ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : ↥(unitarySU 2 f F (m + 1)) →* K),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (m + 1) → F, LineU.ActsDiagU φ a t := by
    by_cases hm3 : m = 3
    · subst m
      obtain ⟨F, hField, hFinite, hChar, hN, φ, hcard, hM, hdiag⟩ :=
        exists_diagonal_cover_of_unitary_four hRig (GGConfig.tableB_facts hR.1.1).2.1
          (hR.1.2.2.1.2 y K hNy) hf2 hpq hLab hΛ
      exact ⟨F, hField, hFinite, hChar, hN, φ, hcard, hM, hdiag⟩
    · have hm4 : 4 ≤ m := by omega
      by_cases hpd : p ∣ m + 1
      · refine exists_diagonal_cover_of_large_unitary_side_of_cfg_of_rank hRig hR.1.1 hR.1.2.2.1
          (Or.inr ⟨y, hNy⟩) hm4 (Or.inr ⟨by omega, fun hN => ?_⟩) hpq hpd hLab hΛ
        have hb := hR.pow_le_card_range_ggGamma_nbr hBB hNy etaCell hN
        have hm1 : m + 1 - 1 = m := by omega
        rw [hm1] at hb
        exact (Nat.pow_le_pow_right hp.pos hm4).trans hb
      · exact exists_diagonal_cover_of_large_unitary_coprime_of_inner hRig
          (GGConfig.tableB_facts hR.1.1).2.1 (hR.1.2.2.1.2 y K hNy) hm4 (Or.inr (by omega))
          hpq hpd hLab hΛ
  obtain ⟨F, _, _, _, hN, φ, -, hM, hdiag⟩ := hcover
  obtain ⟨eta', hauto, hxB, hcomp, hAlg, E, hUFD, π, hπ, hom, huni⟩ :=
    exists_frames_of_diag hMp hR hBB (by omega) hcellKeep hN φ hM hdiag
  exact ⟨eta', hauto, hxB, hcomp, F, inferInstance, inferInstance, inferInstance, hAlg, E, hUFD,
    π, hπ, hom, huni⟩

end CFSG.StandardType

end
