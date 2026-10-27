module

public import CFSG.RankThree.SubgroupLists.SymplecticThreeCount
public import CFSG.RankThree.SubgroupLists.TransvectionRecognition
public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate7023
public import Certificates.Certificate1022
public import Certificates.Certificate7059
public import CFSG.Fischer.NoF25.Local
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem le_card_ncImage_three (hSp : FischerSpCard) (hO : FischerOrthCard)
    (hU : FischerUnitaryCard) (hR : FischerReflectionCard) {G : Subgroup (GL V₄ (ZMod 3))}
    (hGS : G ≤ CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 3)) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod 3)) = 1 ∨ (z : GL V₄ (ZMod 3)) = -1)
    (hneg : (-1 : GL V₄ (ZMod 3)) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ (ZMod 3))) :
    45 ≤ Nat.card (ncImage G t) := by
  unfold FischerSpCard at hSp
  unfold FischerOrthCard at hO
  unfold FischerUnitaryCard at hU
  unfold FischerReflectionCard at hR
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have : Group.IsPerfect G := hq.1
  obtain ⟨⟨-, hclass, hinv, hprod, hgen⟩, hcenter, hsimple⟩ :=
    fischerHyp_ncImage h2 hGS hq hZ hneg ht fun _ => isThreePair_zmod_three _ _
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem (G ⧸ Subgroup.center G)
      (ncImage G t) hclass hinv hprod hgen hcenter hsimple with
    ⟨m, hm, φ, -⟩ | ⟨m, hm, b, halt, hnd, φ, hφ⟩ | ⟨m, hm, Q, hpol, -, φ, hφ⟩ | ⟨m, hm, φ, hφ⟩ |
      ⟨m, hm, f, hfs, hfn, φ, hφ⟩ | ⟨-, hD⟩ | ⟨-, hD⟩ | ⟨-, hD⟩
  · exact absurd (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective)
      (fischerSymNotPerfect m (by omega))
  · have h45 := hSp m hm b halt hnd (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom)
      φ.surjective)
    rwa [← Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv hφ)] at h45
  · have h45 := hO m hm Q hpol (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective)
    rwa [← Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv hφ)] at h45
  · have h45 := hU m hm
    rwa [← Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv hφ)] at h45
  · have h45 := hR m hm f hfs hfn (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom)
      φ.surjective)
    rwa [← Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv hφ)] at h45
  · rw [hD]; norm_num
  · rw [hD]; norm_num
  · rw [hD]; norm_num

theorem eq_statedSp_three_of_isNCInv (hSp : FischerSpCard) (hO : FischerOrthCard)
    (hU : FischerUnitaryCard) (hR : FischerReflectionCard) {G : Subgroup (GL V₄ (ZMod 3))}
    (hGS : G ≤ CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 3)) (hq : CFSG.IsQuasisimple G) (hirr : IsIrreducibleOn G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod 3)) = 1 ∨ (z : GL V₄ (ZMod 3)) = -1)
    (hneg : (-1 : GL V₄ (ZMod 3)) ∈ G) {t : GL V₄ (ZMod 3)} (htG : t ∈ G) (ht : IsNCInv t) :
    G = CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 3) := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h45 := le_card_ncImage_three hSp hO hU hR hGS hq hZ hneg (t := ⟨t, htG⟩) ht
  have h90 := two_mul_card_ncImage_le h2 hGS hZ hneg (t := ⟨t, htG⟩) ht
  have hT := spTrans_mem_of_card (G := G) (by omega)
  have : Group.IsPerfect G := hq.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine eq_statedSp_of_spTrans_mem (p := 3) (by decide) hGS hirr ?_ one_ne_zero hT
  intro h
  have := congrFun h (Sum.inr 1)
  simp at this

end CFSG.RankThree.SubgroupLists
