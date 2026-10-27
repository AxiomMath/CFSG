module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ModA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans
public import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem c23_wTil_inf_conj_eq_bot {D : Data G} {V L : Subgroup G} (h : Hyp151 D ⊥ V L)
    (hV : IsElemAbelian 2 V) (hv1 : v1Sub D.M ⊥ V hV L = ⊥) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V hV L) :
    wTil ⊥ V hV L ⊓ wTil ⊥ V hV (conjSubgroup L x) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨w, rfl⟩ := mkTil_surjective ⊥ V hV u
  have hY : L ≤ stabTil ⊥ V :=
    le_stabTil (h.le.trans h.hyp125.pairFacts.le_normalizer)
      (h.le.trans h.hyp125.pairFacts.le_normalizer₀)
  have hfixmem : mkTil ⊥ V hV w ∈ fixV (barSub ⊥ V hV L) := by
    rw [mem_fixV]
    intro a ha
    exact c23_fix_wTil_conj h hV hx hxn a ha (mkTil ⊥ V hV w) hu2
  have hcomm : ∀ l ∈ L, l * w.val * l⁻¹ = w.val :=
    (s16c7_mem_fixV_barSub_iff V hV hY w).1 hfixmem
  have hcent : w.val ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := hcomm l hl
    calc l * w.val = l * w.val * l⁻¹ * l := by group
      _ = w.val * l := by rw [h2]
  have hwsub : w.val ∈ wSub ⊥ V hV L :=
    (mem_preTil ⊥ V hV (wTil ⊥ V hV L)).2 ⟨w, rfl, hu1⟩
  have hv1mem : w.val ∈ v1Sub D.M ⊥ V hV L := by
    rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    exact le_iSup (fun m : D.M =>
      conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) (m : G)) 1
      (by simpa only [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one] using
        (Subgroup.mem_inf.2 ⟨hwsub, hcent⟩))
  have hwval : w.val = 1 := by
    have hmem := hv1mem
    rw [hv1] at hmem
    simpa using hmem
  have hw : w = 1 := IntMod.val_injective (by simpa using hwval)
  rw [hw]
  simp

theorem c23_wTil_sup_conj_eq_top {D : Data G} (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2)
    (hL : barSub V₀ V hV L ≠ ⊥) {x : G} (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) :
    wTil V₀ V hV L ⊔ wTil V₀ V hV (conjSubgroup L x) = ⊤ := by
  refine le_antisymm le_top ?_
  have htop := s15_Two_iSup_commSub_eq_top D h1217 h hL
  rw [← htop]
  refine iSup_le fun m => ?_
  rcases c23_barSub_conj_cases D h hV hs hx hxn m.2 with hc | hc
  · rw [hc]
    exact le_sup_left
  · rw [hc]
    exact le_sup_right

theorem c23_core_of_case2 {D : Data G} (h1217 : R1217 D) {V L : Subgroup G} (h : Hyp151 D ⊥ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M ⊥ V hV L = 2) (hL3 : IsL3 ↥(barSub ⊥ V hV L) 1)
    (hnat : BinaryNaturalSL (barSub ⊥ V hV L) (wTil ⊥ V hV L) ⊥ 3 1)
    (hv1 : v1Sub D.M ⊥ V hV L = ⊥) {x : G} (hx : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V hV L) :
    C23Core (wTil ⊥ V hV L) (wTil ⊥ V hV (conjSubgroup L x)) (barSub ⊥ V hV L)
      (barSub ⊥ V hV (conjSubgroup L x)) (Mbar D.M ⊥ V hV) := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil ⊥ V := hMs hx
  have hL : barSub ⊥ V hV L ≠ ⊥ := by
    intro h0
    have := card_eq_of_isL3 hL3
    rw [h0, Subgroup.card_bot] at this
    omega
  have h8 := s15_T7_card_eight hnat
  have htr := c23_binaryNatural_transitive hnat
  exact ⟨h8, (c23_card_wTil_conj hV hxs L).trans h8,
    c23_wTil_inf_conj_eq_bot h hV hv1 hx hxn, c23_wTil_sup_conj_eq_top h1217 h hV hs hL hx hxn,
    card_eq_of_isL3 hL3, (c23_card_barSub_conjSubgroup hV hxs L).trans (card_eq_of_isL3 hL3),
    c23_fix_wTil_conj h hV hx hxn, c23_fix_wTil_of_nBar h hV hx hxn, htr,
    c23_exists_trans_conj hV hxs htr, barSub_mono ⊥ V hV h.le,
    c23_barSub_conjSubgroup_le_Mbar D h hV hx, c23_perm_wTil h hV hs hL hx hxn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
