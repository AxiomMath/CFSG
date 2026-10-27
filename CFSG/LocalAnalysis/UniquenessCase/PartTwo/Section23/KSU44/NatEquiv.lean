module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.B4Models

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
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
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin CFSG.Open

theorem exists_hypNatEquiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ 2) K)).Realizes H ⊤ ⊥) :
    ∃ (π : ↥(hypSU hK 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K)),
      ∀ (γ : ↥(hypSU hK 2 0)) (w : W),
        Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
            Multiplicative.toAdd (e w) := by
  obtain ⟨π₀, e₀, he₀⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv hreal
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) hK
  let φ : (Fin (2 * 2 + 0) → K) ≃+ (HypIndex 2 0 → K) :=
    { toFun := fun v => transportInv hK R *ᵥ v
      invFun := fun v => R *ᵥ v
      left_inv := fun v => by
        simp only []
        rw [Matrix.mulVec_mulVec, mul_transportInv hR, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only []
        rw [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]
      map_add' := fun v w => by rw [Matrix.mulVec_add] }
  refine ⟨(hypTransport hK hR).trans π₀, e₀.trans (AddEquiv.toMultiplicative φ), ?_⟩
  intro γ w
  show transportInv hK R *ᵥ Multiplicative.toAdd
      (e₀ (((π₀ (hypTransport hK hR γ) : ↥H) : MulAut W) w)) =
    ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (transportInv hK R *ᵥ Multiplicative.toAdd (e₀ w))
  have hmat : transportInv hK R *
      (((hypTransport hK hR γ : unitarySU 2 2 K (2 * 2 + 0)) : GL (Fin (2 * 2 + 0)) K) :
        Matrix (Fin (2 * 2 + 0)) (Fin (2 * 2 + 0)) K) =
      ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        transportInv hK R := by
    rw [coe_hypTransport hR γ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, transportInv_mul hR, Matrix.one_mul]
  rw [he₀ (hypTransport hK hR γ) w]
  simp only [Matrix.mulVec_mulVec]
  rw [hmat]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

end
