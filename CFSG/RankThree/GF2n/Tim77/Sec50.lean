module

public import CFSG.RankThree.GF2n.Tim77TI
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Tim77.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tim77Sec50_elemAbelian_of_le {A T : Subgroup G} (hA : IsElemAbelian 2 A)
    (hT : T ≤ A) : IsElemAbelian 2 T := by
  obtain ⟨hc, h2⟩ := hA
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h := congrArg Subtype.val (hc.is_comm.comm ⟨a.1, hT a.2⟩ ⟨b.1, hT b.2⟩)
    exact h
  · exact h2 x (hT hx)

theorem tim77Sec50_isTI {A T : Subgroup G} (hTI : IsTI A) (hTA : T ≤ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (T : Set G)) : IsTI T := by
  intro g
  by_cases hne : T ⊓ conjSubgroup g T = ⊥
  · exact Or.inl hne
  refine Or.inr ?_
  have hconj : conjSubgroup g T ≤ conjSubgroup g A := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    rw [mem_conjSubgroup]
    exact hTA hx
  have hle : T ⊓ conjSubgroup g T ≤ A ⊓ conjSubgroup g A :=
    le_inf (inf_le_left.trans hTA) (inf_le_right.trans hconj)
  have hA' : A ⊓ conjSubgroup g A ≠ ⊥ := fun h => hne (le_bot_iff.mp (hle.trans h.le))
  have hgA : conjSubgroup g A = A := conjSubgroup_eq_of_isTI hTI hA'
  have hgT : conjSubgroup g T = T :=
    conjSubgroup_eq_self_iff.mpr (hN (conjSubgroup_eq_self_iff.mp hgA))
  rw [hgT, inf_idem]

theorem tim77Sec50_le_center {A T : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hTA : T ≤ A) (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ (Subgroup.center (weakClosure T (Subgroup.normalizer (A : Set G)))).map
      (weakClosure T (Subgroup.normalizer (A : Set G))).subtype := by
  have hTel : IsElemAbelian 2 T := tim77Sec50_elemAbelian_of_le hA hTA
  have hTTI : IsTI T := tim77Sec50_isTI hTI hTA hN
  have hgen : ∀ x ∈ {x : G | ∃ g : G, conjSubgroup g T ≤ Subgroup.normalizer (A : Set G) ∧
      x ∈ conjSubgroup g T}, x ∈ Subgroup.centralizer (T : Set G) := by
    rintro x ⟨g, hg, hx⟩
    have hel := tim77_2_3 hTel hTTI (hg.trans hN)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ T := ha
    exact congrArg Subtype.val
      (hel.1.is_comm.comm ⟨a, Subgroup.mem_sup_left ha'⟩ ⟨x, Subgroup.mem_sup_right hx⟩)
  have hHc : weakClosure T (Subgroup.normalizer (A : Set G)) ≤
      Subgroup.centralizer (T : Set G) := by
    unfold weakClosure
    exact (Subgroup.closure_le _).mpr hgen
  intro a ha
  have haH : a ∈ weakClosure T (Subgroup.normalizer (A : Set G)) := by
    have hmem : a ∈ {x : G | ∃ g : G, conjSubgroup g T ≤ Subgroup.normalizer (A : Set G) ∧
        x ∈ conjSubgroup g T} :=
      ⟨1, by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact hTA.trans Subgroup.le_normalizer,
        by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact ha⟩
    unfold weakClosure
    exact Subgroup.subset_closure hmem
  refine Subgroup.mem_map.mpr ⟨⟨a, haH⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hHc k.2) a ha).symm

theorem tim77Sec50_holds : Tim77Sec50Statement := by
  intro G _ _ A Abar S₀ B h _ hnot
  by_contra hall
  apply hnot
  have hTA : Section3.A0 A Abar ≤ A := by
    unfold Section3.A0 normalizerIn
    exact inf_le_left
  have hN : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Section3.A0 A Abar : Set G) :=
    fun g hg => Classical.byContradiction fun hn => hall ⟨g, hg, hn⟩
  unfold Sec4A0LeCenterH Section5.H
  exact tim77Sec50_le_center h.hyp.elemAbelian h.hyp.ti hTA hN

end CFSG.RankThree.GF2n.Tim77
