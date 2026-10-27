module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB4
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4G
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4FAux1
import CFSG.Quasithin.Background.Asc81cPfTrans1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_stable_Wd (L : Subgroup (MulAut W)) : StableUnder L (Wd L) :=
  stableUnder_commSub (fun a ha b hb => L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha))
    (fun _ _ _ _ => Subgroup.mem_top _)

private theorem w1369_commSub_Wd_self {L : Subgroup (MulAut W)} (hLp : ⁅L, L⁆ = L) :
    commSub (Wd L) L = Wd L := by
  refine le_antisymm (commSub_le_of_invariant (w1369_stable_Wd L)) ?_
  exact s13_perfect_chain L hLp (commSub (Wd L) L) (Wd L) ⊤ le_rfl le_rfl

theorem case_two_of_swap (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} {g : MulAut W}
    (S : Swap136 Y t L g) : ∃ L' : Subgroup (MulAut W), Conc4_136W Y t L' := by
  classical
  obtain ⟨hWdX, hCd, hCdX, hStrong⟩ := swap_structure hw2 S
  have hWdX' : commSub (⊤ : Subgroup W) (Lc L g) = Wd L := hWdX
  have hT : SwapT Y L g := swap_T hw2 S hWdX hCd hStrong
  obtain ⟨hL3, hL3', hcard, -⟩ := swap_l3 hw2 S hWdX hCd hCdX hStrong hT
  have hLp : ⁅L, L⁆ = L :=
    CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple S.ctx.comp.2.2
  have hcomm : commSub (⊤ : Subgroup W) (L ⊔ Lc L g) = Wd L := by
    rw [CFSG.Quasithin.Asc81c.Pf.commSub_sup, hWdX']
    exact sup_idem (Wd L)
  have hWd_ne : Wd L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(Wd L) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  have hcompX : Lc L g ≠ L := (swap_comp S).2.1
  have hcommLX : ⁅L, Lc L g⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (swap_comp S).2.2.1
  have hKK' : ∀ a ∈ L, ∀ b ∈ Lc L g, a * b = b * a := by
    intro a ha b hb
    have hle : L ≤ Subgroup.centralizer (Lc L g : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLX
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hstabL : StableUnder L (Wd L) := w1369_stable_Wd L
  have hstabX : StableUnder (Lc L g) (Wd L) := by
    rw [← hWdX']
    exact w1369_stable_Wd (Lc L g)
  have hstab : StableUnder (L ⊔ Lc L g) (Wd L) := f4f_stableUnder_sup hstabL hstabX
  have hGL3 : GL3Case L (Lc L g) (Wd L) (Cd L) := hStrong.1
  have hIrr : IsIrrOn (L ⊔ Lc L g) (Wd L) ⊥ := by
    refine ⟨bot_lt_iff_ne_bot.mpr hWd_ne, hstab, ?_, ?_⟩
    · intro x _ u hu
      rw [Subgroup.mem_bot] at hu
      rw [hu, map_one]
      exact Subgroup.one_mem _
    · intro M hM hbotM hMW
      have hML : StableUnder L M := fun l hl m hm => hM l (Subgroup.mem_sup_left hl) m hm
      have hMX : StableUnder (Lc L g) M :=
        fun x hx m hm => hM x (Subgroup.mem_sup_right hx) m hm
      have h := hGL3.1 M (by rw [hCd]; exact hbotM) hMW hML hMX
      rw [hCd] at h
      exact h
  have hKnt : ¬ ∀ k ∈ L, ∀ r ∈ Wd L, k r = r := by
    intro hall
    have hfix : Wd L ≤ fixV L := fun r hr => mem_fixV.mpr fun k hk => hall k hk r hr
    have hbot : commSub (Wd L) L = ⊥ := commSub_eq_bot_iff.mpr hfix
    rw [w1369_commSub_Wd_self hLp] at hbot
    exact hWd_ne hbot
  have hK'nt : ¬ ∀ k ∈ Lc L g, ∀ r ∈ Wd L, k r = r := by
    intro hall
    apply S.nontriv
    rw [commSub_eq_bot_iff]
    exact fun r hr => mem_fixV.mpr fun k hk => hall k hk r hr
  refine ⟨L ⊔ Lc L g, ?_, ?_, Or.inr (Or.inl ?_)⟩
  · rw [hcomm]
    exact lemmaS S.ctx.comp.1 (comm_top_of_component S.ctx.std hw2 S.ctx.comp)
  · exact hT
  · refine ⟨L, S.ctx.comp, g, S.gY, ?_, rfl, Or.inl ⟨hL3, ?_⟩⟩
    · intro h
      exact hcompX h.symm
    · rw [hcomm]
      exact s134b_tensor_of_irr hw2 hKK' hL3 hL3' hcard hIrr hKnt hK'nt

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
