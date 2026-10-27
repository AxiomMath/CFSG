module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Transport
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.ClassicalGroups.Unitary.IsotropicPerp
import CFSG.ClassicalGroups.Unitary.Elements
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove

open CFSG.Open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

private theorem exists_tv_fix_moves {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) {n : ℕ}
    {e u : Fin n → K} (he : herm σ e e = 0)
    (h : ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a u = 0 ∧ herm σ a e ≠ 0) :
    ∃ g : SUid σ n, g • u = u ∧ ∀ c : K, g • e ≠ c • e := by
  obtain ⟨a, haa, hau, hae⟩ := h
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  refine ⟨tv hσ.invol haa hτ, ?_, ?_⟩
  · rw [tv_smul, hau, mul_zero, zero_smul, add_zero]
  · intro c hc
    have hsplit : (τ * herm σ a e) • a = (c - 1) • e := by
      have h1 : (τ * herm σ a e) • a = c • e - e := by
        rw [← hc, tv_smul]
        abel
      simpa [sub_smul] using h1
    have hzero : herm σ a e = 0 := by
      have h2 := congrArg (fun x => herm σ x e) hsplit
      simp only [herm_smul_left, he, mul_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero σ).mpr (mul_ne_zero hτ0 hae))
    exact hae hzero

theorem centMove_statedSU (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) {e : Fin n → K}
    (he : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution K p f) e e
      = 0) (he0 : e ≠ 0) :
    CentMove (StatedSU n (p ^ f) K) e := by
  classical
  intro u hu
  have hσ : IsUnitaryInvolution (CFSG.LieType.BorelTits.unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨a, haa, hau, hae⟩ := exists_isotropic_herm_eq_zero_herm_ne_zero hσ hn he he0 hu
  obtain ⟨g, hgu, hge⟩ := exists_tv_fix_moves hσ he ⟨a, haa, hau, hae⟩
  refine ⟨(g : GL (Fin n) K), ?_, ?_, ?_⟩
  · rw [← SUid_eq_statedSU hK n]
    exact g.2
  · simpa only [smul_def] using hgu
  · intro c
    simpa only [smul_def] using hge c

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove
