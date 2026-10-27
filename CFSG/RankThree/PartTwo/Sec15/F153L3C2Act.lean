module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

variable {G : Type} [Group G]

@[expose] noncomputable def descendPCore (Y : Type) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.characteristic_iff_map_eq.1 inferInstance σ)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' σ τ := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H z => rfl

@[expose] noncomputable def rho (Y : Subgroup G) :
    ↥(Subgroup.normalizer (Y : Set G)) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  (descendPCore ↥Y).comp (Subgroup.normalizerMonoidHom Y)

@[expose] def innQ (Y : Subgroup G) : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
  (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)).range

theorem rho_mk (Y : Subgroup G) (n : ↥(Subgroup.normalizer (Y : Set G))) (y : ↥Y) :
    rho Y n (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨(n : G) * y * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 y).mp y.2⟩ :=
  rfl

theorem rho_inner (Y : Subgroup G) (y : ↥Y) :
    rho Y ⟨(y : G), Subgroup.le_normalizer y.2⟩ = MulAut.conj (QuotientGroup.mk y) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z => rfl

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
