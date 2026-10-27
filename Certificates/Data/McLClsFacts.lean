module

public import Certificates.Data.McLCls
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.SectionRank.QTK.Insp443.McLCls

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Quasithin.KGC31

namespace F

noncomputable abbrev t0 : Equiv.Perm (Fin 275) := tp 275 (mclCentTbl 4)

noncomputable abbrev H : Subgroup (Equiv.Perm (Fin 275)) := mclP ⊓ centralizer ({t0} : Set _)

noncomputable abbrev v (i : Fin 4) : Equiv.Perm (Fin 275) := tp 275 (eB.getD i (idT 275))

noncomputable abbrev W : Subgroup (Equiv.Perm (Fin 275)) := closure (Set.range v)

noncomputable abbrev M : Subgroup (Equiv.Perm (Fin 275)) := genOf 275 mGens

noncomputable abbrev S : Subgroup (Equiv.Perm (Fin 275)) := genOf 275 sGens

noncomputable abbrev r : Equiv.Perm (Fin 275) := tp 275 gT * mclU

@[expose] def O : Finset (Fin 275) := Finset.univ.filter fun i => i.val ∈ oPts

end F

structure Facts : Prop where
  tbls : (∀ T ∈ allTbls, Rep 275 T (tp 275 T) ∧ tp 275 T ∈ mclP) ∧ Rep 275 mclOuterTbl mclU
  basis : EBasis F.v
  mOne : F.W ≤ F.M ∧ F.M ≤ normalizer (F.W : Set (Equiv.Perm (Fin 275))) ∧
    Nat.card F.M = 40320 ∧ F.M ≤ setStab F.O ∧ (∀ w ∈ F.W, ∀ i ∈ F.O, w i = i) ∧
    ∀ g ∈ F.M, (∀ i ∈ F.O, g i = i) → g ∈ F.W
  cent : (∀ g ∈ mclP, (∀ w ∈ F.W, g * w = w * g) → g ∈ F.W) ∧
    Nat.card ↥(F.H ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275)))) ≤ 2688
  sTwo : F.S ≤ F.H ∧ Nat.card F.S = 128
  cls : ∀ x ∈ F.S, x * x = 1 → x ∈ F.W ∨ x ∈ F.W.map (MulAut.conj F.r).toMonoidHom ∨
    Nat.card ↥{g : Equiv.Perm (Fin 275) | g ∈ F.S ∧ g * g = 1 ∧ g * x = x * g} < 16
  e8 : ∀ x ∈ F.H, ∀ a ∈ F.H, ∀ b ∈ F.H, x ≠ 1 → (∃ p ∈ [3, 5, 7], x ^ p = 1) →
    a * a = 1 → a ≠ 1 → a ≠ F.t0 → b * b = 1 → b ≠ 1 → b ≠ F.t0 → x * a = a * x →
    x * b = b * x → a * b = b * a → b = a ∨ b = a * F.t0

end CFSG.SectionRank.QTK.Insp443.McLCls

end
