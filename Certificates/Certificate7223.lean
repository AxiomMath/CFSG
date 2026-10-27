
module

public import CFSG.Quasithin.Vol2.KGFactC31HeElt
import Certificates.Kernel.He7223.GlueFinal
import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.HeldB.InnerCheckInputs
meta import CFSG.Sporadic.HeldB.InnerData
meta import CFSG.Sporadic.HeldB.Common
meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import CFSG.Sporadic.HeldB.InnerClassCheckInputs
meta import CFSG.Sporadic.HeldB.HeBlocks
meta import CFSG.Sporadic.HeldB.InnerCheck
meta import Certificates.Data.CFSGNative.HeldB.Tests
meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Sporadic.HeldB.OuterArithCheckInputs
meta import CFSG.Sporadic.HeldB.AutData
meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.HeldB.HeBlocks
import CFSG.Sporadic.HeldB.OuterArithCheck
import Certificates.Data.CFSGNative.HeldB.Tests
meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
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
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB

public section

namespace Certificates

open CertificateChecks.KernelHe7223

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Sporadic.HeldB in
theorem certificate7223 :
    ((∀ w ∈ eW ++ qW ++ lsGenW ++ njW, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) ∧ w5W = eW.take 4 ∧
      w7W = qW.take 3 ∧ eW.length = 6 ∧ qW.length = 4) ∧
    (EBasis (fun i : Fin 6 => elt (eW.getD i [])) ∧ EBasis (fun i : Fin 4 => elt (qW.getD i []))) ∧
    ((∀ x ∈ heAutGroup, (∀ i : Fin 4, x * elt (eW.getD i []) = elt (eW.getD i []) * x) →
        x ∈ heE) ∧
      ∀ x ∈ heAutGroup, (∀ i : Fin 3, x * elt (qW.getD i []) = elt (qW.getD i []) * x) →
        x ∈ heQ) ∧
    (Nat.card nsGrp = 138240 ∧ Nat.card lGrp = 69120 ∧ Nat.card n7Grp = 21504 ∧
      nsGrp ≤ heP ⊓ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) ∧
      n7Grp ≤ heP ⊓ Subgroup.normalizer (heQ : Set (Equiv.Perm (Fin 8330))) ∧
      lGrp ≤ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) ∧
      (∀ n ∈ njW, elt n ∈ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330)))) ∧
      orderOf (elt y5W) = 5 ∧ heE ≤ lGrp) ∧
    (∀ w ∈ lsGenW, ∀ p : Fin 8330, (p : ℕ) ∈ CFSG.Quasithin.KGC31.He.bB → ((elt w p : Fin 8330) : ℕ) ∈ CFSG.Quasithin.KGC31.He.bB) ∧
    (∀ i : Fin 6, ∀ p : Fin 8330, (p : ℕ) ∈ CFSG.Quasithin.KGC31.He.bB → elt (eW.getD i []) p = p) ∧
    Nat.card {x : lGrp // ∀ p : Fin 8330, (p : ℕ) ∈ CFSG.Quasithin.KGC31.He.bB → (x : Equiv.Perm (Fin 8330)) p = p} = 192 :=
  ⟨⟨words_ok, w5W_eq, w7W_eq, eW_len, qW_len⟩, ⟨ebasis_E, ebasis_Q⟩, ⟨cent_heE, cent_heQ⟩,
    ⟨card_nsGrp, card_lGrp, card_n7Grp, nsGrp_le, n7Grp_le, lGrp_le, nj_le, orderOf_y5,
      heE_le_lGrp⟩, lsGen_maps_bB, E_fix, card_lFix⟩

end Certificates

end
