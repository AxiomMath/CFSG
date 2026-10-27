module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.RankThree.GF2n.Stroth80.Sec311Cover

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n.Stroth80 Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem wac_eq_self {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hw : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) :
    WAC A = A := by
  apply le_antisymm
  · exact iSup₂_le fun g hg => (hw g hg).le
  · have h1 : conjSubgroup 1 A = A := by
      ext x
      simp [mem_conjSubgroup]
    have hle : conjSubgroup 1 A ≤ centralizer (A : Set G) := by
      rw [h1]
      intro y hy z hz
      exact (congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)).symm
    calc A = conjSubgroup 1 A := h1.symm
      _ ≤ WAC A := le_iSup₂_of_le 1 hle le_rfl

theorem isWC_of_weaklyClosed_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hTI : IsTI A)
    (hw : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) :
    IsWC A := by
  refine ⟨hA, fun t ht ht1 => ⟨fun a ha => ?_, fun g hg => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨y, ht⟩ ⟨a, ha⟩)
  · have hN : conjSubgroup g A ≤ normalizer (A : Set G) := by
      intro x hx
      have hxt : x * t = t * x := by
        have := Subgroup.mem_centralizer_iff.mp (hg hx) t (Set.mem_singleton t)
        exact this.symm
      exact mem_normalizer_of_commute_of_isTI hTI ht ht1 hxt
    have hel := tim77_2_3 hA hTI hN
    refine hw g fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have hx' : x ∈ A ⊔ conjSubgroup g A := Subgroup.mem_sup_right hx
    have ha' : a ∈ A ⊔ conjSubgroup g A := Subgroup.mem_sup_left ha
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha'⟩ ⟨x, hx'⟩)

theorem cor2One_of_weaklyClosed (hThA : TheoremAStmt) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hw : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) :
    WAC A = A ∧ ThmAConclusion A :=
  ⟨wac_eq_self hA hw, hThA G A (isWC_of_weaklyClosed_centralizer hA hTI hw)⟩

end CFSG.RankThree.GF2n.Tim77
