module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolK
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolS6
import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)

section Sp48


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem nonempty_projSp_two_mulEquiv_perm :
    Nonempty (projSp 2 (GaloisField 2 1) ≃* Equiv.Perm (Fin 6)) := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega)]
    norm_num
  obtain ⟨e⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hcard
  exact ⟨(KFacts.statedSpEquivProjSpOfCharTwo (GaloisField 2 1)).symm.trans e⟩

theorem exists_field_involution_sp48 (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hSp : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSp 2 (GaloisField 2 3)))
    (hcf : KFacts.InducesStdKind K c .field) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  classical
  obtain ⟨hcN, h3, h1, hP, hPq⟩ := exists_bridge_image h45 C
  have hout : InducesOuterTheta c K := KFacts.InducesStdKind.inducesOuterTheta K hcf (by decide)
  have hc3 : c ^ 3 = 1 := C.mem_S.1.1.2 c C.c_mem
  have hSp' : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
      projSp 2 (GaloisField 2 (3 * 1))) := by simpa using hSp
  obtain ⟨-, ⟨eC⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := 1) one_ne_zero hc3 hout hSp'
  have hbar : Sec8.barCentralizer (Subgroup.zpowers c) K =
      Item426.fixSub (Item426.thetaAut K hcN) := by
    ext y
    rw [KFacts.mem_barCentralizer_zpowers_iff hcN y]
    exact Iff.rfl
  obtain ⟨ePerm⟩ := nonempty_projSp_two_mulEquiv_perm
  set P := ((Sec11.sec11K L d).subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))
    with hPdef
  have hPC : P ≤ Item426.fixSub (Item426.thetaAut K hcN) := le_of_mem_thetaComponentsIn hP
  have hPperf : Group.IsPerfect P := isPerfect_of_mem_thetaComponentsIn hP
  obtain ⟨ePA⟩ := hPq
  have hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360 := by
    rw [Nat.card_congr ePA.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨t, htC, ht2, hS6⟩ := exists_s6act_of_perm (Item426.fixSub (Item426.thetaAut K hcN))
    ((MulEquiv.subgroupCongr hbar.symm).trans (eC.trans ePerm)) hPC hPperf hq
  exact exists_field_involution_fix h45 C ht2 htC hS6

end Sp48

end CFSG.RankThree.PartTwo.Sec8.Hering611
