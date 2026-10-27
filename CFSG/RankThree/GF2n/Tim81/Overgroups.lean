module

public import CFSG.RankThree.GF2n.Tim81.Basic
public import CFSG.CGT.Timmesfeld75.ConjCentralizer

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

namespace Hyp

theorem le_of_isPGroup_of_Pc_le (h : Hyp M V) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hPS : Pc M V ≤ S) : S ≤ M := by
  have hSne : S ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (le_bot_iff.mp (h.le_Pc.trans (hPS.trans_eq hbot)))
  set Z : Subgroup G := S ⊓ Subgroup.centralizer (S : Set G) with hZdef
  have hZV : Z ≤ V := by
    intro z hz
    rw [← h.centralizer_Pc, Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp hz.2 p (hPS hp)
  have hZne : Z ≠ ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
    haveI : Nontrivial ↥(Subgroup.center ↥S) := hS.center_nontrivial
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥S)
    have hwZ : ((w : ↥S) : G) ∈ Z :=
      ⟨(w : ↥S).2, Subgroup.mem_centralizer_iff.mpr fun s hs =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩)⟩
    have hwne : ((w : ↥S) : G) ≠ 1 := by
      intro hw
      exact hw1 (Subtype.ext (Subtype.ext hw))
    intro hbot
    exact hwne (Subgroup.mem_bot.mp (hbot ▸ hwZ))
  have hSZ : S ≤ Subgroup.normalizer (Z : Set G) := fun s hs =>
    mem_normalizer_inf (Subgroup.le_normalizer (H := S) hs)
      (mem_normalizer_centralizer (Subgroup.le_normalizer (H := S) hs))
  exact hSZ.trans (h.normalizer_le_M hZV hZne)

theorem pCore_le_of_Pc_le (h : Hyp M V) {H : Subgroup G} (hPH : Pc M V ≤ H) :
    inSubgroup (pCore 2) H ≤ M := by
  have hP2 : IsPGroup 2 ↥(Pc M V) :=
    (inSubgroup_pCore_two M).1.to_le (show Pc M V ≤ inSubgroup (pCore 2) M from inf_le_left)
  have hQ2 : IsPGroup 2 ↥(inSubgroup (pCore 2) H) := (inSubgroup_pCore_two H).1
  have hPN : Pc M V ≤ Subgroup.normalizer ((inSubgroup (pCore 2) H : Subgroup G) : Set G) :=
    hPH.trans (inSubgroup_pCore_two H).2.2
  have hsup2 : IsPGroup 2 ↥(Pc M V ⊔ inSubgroup (pCore 2) H) :=
    hP2.to_sup_of_normal_right' hQ2 hPN
  exact le_sup_right.trans (le_of_isPGroup_of_Pc_le h hsup2 le_sup_left)

theorem centralizer_conj_Pc (h : Hyp M V) (g : G) :
    Subgroup.centralizer (conjSubgroup g (Pc M V) : Set G) = conjSubgroup g V := by
  rw [centralizer_conjSubgroup_eq, h.centralizer_Pc]

theorem pCore_le_conj_of_Pc_le (h : Hyp M V) {H : Subgroup G} (hPH : Pc M V ≤ H) {g : G}
    (hg : g ∈ H) : inSubgroup (pCore 2) H ≤ conjSubgroup g M := by
  have hO : conjSubgroup g (inSubgroup (pCore 2) H) = inSubgroup (pCore 2) H :=
    conjSubgroup_eq_self_iff.mpr ((inSubgroup_pCore_two H).2.2 hg)
  calc inSubgroup (pCore 2) H = conjSubgroup g (inSubgroup (pCore 2) H) := hO.symm
    _ ≤ conjSubgroup g M := Subgroup.map_mono (pCore_le_of_Pc_le h hPH)

end Hyp

end CFSG.RankThree.GF2n.Tim81
