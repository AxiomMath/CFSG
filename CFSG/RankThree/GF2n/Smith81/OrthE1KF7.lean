module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenTight
public import CFSG.CGT.PushingUpLit.STT.Printed

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG.CGT.Timmesfeld75 (ListGroup)

theorem kf7_alt_exists_noncomm (k : ℕ) (hk : 4 ≤ k) :
    ∃ a b : alternatingGroup (Fin k), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin k)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin k)).mp hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

theorem kf7_listGroup_exists_noncomm {D : Type} [Group D] [Finite D] (h : ListGroup D) :
    ∃ a b : D, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  rcases h with ⟨m, s, hm, -, h⟩ | ⟨s, hs, h⟩ | ⟨s, hodd, hs3, h⟩ | ⟨k, hk6, -, ⟨e⟩⟩ |
    hM22 | hM23 | hM24
  · exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_psl hm h hc
  · exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_stated_bender (Or.inr ⟨s, hs, h⟩) hc
  · exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_stated_bender
      (Or.inl ⟨s, hodd, hs3, h⟩) hc
  · exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_equiv e
      (kf7_alt_exists_noncomm k (by omega)) hc
  · obtain ⟨e⟩ : Nonempty (D ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := hM22
    exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_equiv e
      CFSG.CGT.PushingUpLit.STT.m22_noncomm hc
  · obtain ⟨e⟩ : Nonempty (D ≃* ↥CFSG.Blueprint.NativeSporadic.M23) := hM23
    exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_equiv e
      CFSG.CGT.PushingUpLit.STT.m23_noncomm hc
  · obtain ⟨e⟩ : Nonempty (D ≃* ↥CFSG.Blueprint.NativeSporadic.M24) := hM24
    exact CFSG.CGT.PushingUpLit.STT.not_forall_comm_of_equiv e
      CFSG.CGT.PushingUpLit.STT.m24_noncomm hc

section KF7Certificates

theorem listNoPerfectOut_holds : ListNoPerfectOutStatement := by
  intro D _ _ hD hsimp P hP
  have hnonab : ∃ a b : D, a * b ≠ b * a := kf7_listGroup_exists_noncomm hD
  have hcat : CFSG.Assembly.InCatalog D :=
    CFSG.RankThree.PartTwo.Sec19.SolSeven.inCatalog_of_listGroup hD
  have hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer D) :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds D hnonab hcat
  haveI : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  intro x hx
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    P.subtype (⟨x, hx⟩ : P)
  exact MonoidHom.mem_range.mpr ⟨g, hg.symm⟩

end KF7Certificates

end CFSG.RankThree.GF2n.Smith81.Smith23E1
