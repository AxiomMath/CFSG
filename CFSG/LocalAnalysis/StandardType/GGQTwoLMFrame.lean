module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

structure QTwoFrame {G : Type} [Group G] (m : ℕ) (V VT : Type) [Group V] [Group VT]
    (Bs L : Subgroup G) (x : G) where
  hN : Bs ≤ Subgroup.normalizer (L : Set G)
  hx : x ∈ Bs
  hord : orderOf x = 3
  elemAb : IsElemAbelian 3 Bs
  permV : Equiv.Perm (Fin m) →* MulAut V
  permVT : Equiv.Perm (Fin m) →* MulAut VT
  ker : ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x
  link : ∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
    ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ MulAut.conj n' = MulAut.conj n
  theta : V ≃* ↥(ggGamma L hN).range
  norm_perm : ∀ (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
    ∃ π : Equiv.Perm (Fin m), ggConjAut (ggGamma L hN).range hn = MulAut.congr theta (permV π)
  perm_ind : ∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
    ggConjAut (ggGamma L hN).range hn = MulAut.congr theta (permV σ)
  thetaT : VT ≃* ↥(Bs ⊓ L)
  normT : ∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
    ∃ π : Equiv.Perm (Fin m), ∀ v : VT,
      (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ = ((thetaT (permVT π v) : ↥(Bs ⊓ L)) : G)
  indT : ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
    (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : VT,
      (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ = ((thetaT (permVT σ v) : ↥(Bs ⊓ L)) : G)

structure QTwoUnitaryModel {G : Type} [Group G] [Finite G] (m : ℕ) (L : Subgroup G) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  centerBot : Subgroup.center L = ⊥
  perfect : commutator L = ⊤
  theta : L ⧸ Subgroup.center L ≃* R
  centerPrime : GGCenterPrime 3 R
  torusPerm : GGTorusPermEltSC 3 m R

end CFSG.StandardType.QTwo

end
