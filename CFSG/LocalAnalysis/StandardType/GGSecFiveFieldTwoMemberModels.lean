module

public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSLChart
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
import CFSG.LocalAnalysis.StandardType.GGSelectedPSUModel
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTorus
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
import CFSG.LieType.Steinberg.Classical.SpinPlus.Weyl
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.PsiDiag
  CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer


theorem exists_selectedSL2Model_PSL_long {m : ℕ} (hm : 2 ≤ m) :
    ∃ δ : Fin (ggU .PSL (m + 1) 1).D.rank → ℤ, δ ∈ (ggU .PSL (m + 1) 1).D.roots ∧
      GGLongRoot (ggU .PSL (m + 1) 1).D δ ∧
      Nonempty (SelectedSL2Model (ggU .PSL (m + 1) 1).D (GaloisField 2 1) δ) := by
  obtain ⟨γ, model, -⟩ :=
    FieldTwoPSL.exists_selectedModel_PSL_chart (F := GaloisField 2 1) (m := m) (by omega)
  exact ⟨γ, model.root_mem,
    LieKnownR2.PSL.ggLongRoot_of_mem_roots (by omega) model.root_mem, ⟨model⟩⟩

theorem exists_selectedSL2Model_PSU_long {n : ℕ} (hn : 4 ≤ n) :
    ∃ δ : Fin (ggU .PSU n 1).D.rank → ℤ, δ ∈ (ggU .PSU n 1).D.roots ∧
      GGLongRoot (ggU .PSU n 1).D δ ∧
      Nonempty (SelectedSL2Model (ggU .PSU n 1).D (GaloisField 2 1) δ) := by
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 :=
    card_galoisField_two_mul 2 1 le_rfl
  obtain ⟨model, -⟩ := exists_selectedModel_PSU_chart_twoWt hF hn
  have hk : Nat.card (fixedSubfield (GaloisField 2 (2 * 1)) 2 1) = 2 ^ 1 :=
    card_fixedSubfield hF
  have hG1 : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  let e₁ : GaloisField 2 1 ≃+* fixedSubfield (GaloisField 2 (2 * 1)) 2 1 :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hG1.trans hk.symm)
  have hne : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have h' : (0 : ℕ) = n - (0 + 1) := congrArg Fin.val h
    omega
  exact ⟨_, model.root_mem,
    LieKnownR2.Geo.ggLongRoot_of_two_smul_weight hF (InnerDiagSU.twoWtRoot_mem_roots hne) hne
      (InnerDiagSU.toStd_twoWtRoot _),
    ⟨model.congrField e₁⟩⟩

theorem exists_selectedSL2Model_POmegaPlus_long {n : ℕ} (hn : 4 ≤ n) :
    ∃ δ : Fin (ggU .POmegaPlus n 1).D.rank → ℤ, δ ∈ (ggU .POmegaPlus n 1).D.roots ∧
      GGLongRoot (ggU .POmegaPlus n 1).D δ ∧
      Nonempty (SelectedSL2Model (ggU .POmegaPlus n 1).D (GaloisField 2 1) δ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hn3 : 3 ≤ m + 4 := by omega
  let k : Fin (m + 4) := ⟨0, by omega⟩
  obtain ⟨phi, hinj, hup, -⟩ := SpinPlus.rankOne (K := GaloisField 2 1) hn3 k
  have hroot : (Pi.single k 1 : Fin (m + 4) → ℤ) ∈
      (Spin.plusDatum (m + 4) (GaloisField 2 1) hn3).roots :=
    Or.inl ⟨1, k, by simp; rfl⟩
  have hpar := (SpinPlus.isParametrization (n := m + 4) (K := GaloisField 2 1) hn3)
    (Pi.single k 1) hroot
  have hupper : (sl2UpperUniSub (GaloisField 2 1)).map phi =
      (Spin.plusDatum (m + 4) (GaloisField 2 1) hn3).rootGroup (Pi.single k 1) := by
    ext g
    constructor
    · rintro ⟨M, ⟨c, rfl⟩, rfl⟩
      rw [hup c]
      exact (hpar.1 _).mpr ⟨c, rfl⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (hpar.1 g).mp hg
      exact ⟨sl2Upper c, ⟨c, rfl⟩, hup c⟩
  have hlong : GGLongRoot (Spin.plusDatum (m + 4) (GaloisField 2 1) hn3) (Pi.single k 1) :=
    ggLongRoot_of_symmetric (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
      (fun i j => by
        rw [show (Spin.plusDatum (m + 4) (GaloisField 2 1) hn3).cartan =
          Spin.cartanD (m + 4) from rfl, Spin.cartanD_eq]
        exact (CartanMatrix.D_isSymm (m + 4)).apply j i)
      rfl hroot
  exact ⟨_, hroot, hlong,
    ⟨SelectedSL2Model.ofGF2Upper _ _ hroot phi hinj hupper⟩⟩

end CFSG.StandardType.SelectedRoot

end
