module

public import CFSG.Quasithin.Background.D36GluedFinal
public import CFSG.Quasithin.Background.D36GluedDim
import CFSG.Quasithin.Background.F918J2
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z7aTypes
import CFSG.Quasithin.Background.D36GluedL231
import CFSG.Quasithin.Background.D36GluedA5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def D36GluedDiagL27 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      ¬ A ≤ stabSub (commSub (orbSup T V) L) →
      GluedDiag L A (orbSup T V) (commSub (orbSup T V) L) →
      ¬ GluedL24 L (orbSup T V) (commSub (orbSup T V) L) →
      ¬ GluedL3 L (orbSup T V) (commSub (orbSup T V) L) →
      IsPSL 2 7 1 ↥L →
      CubicBound (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) →
      DiagShape (autSub A (orbSup T V)) (autSub L (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) → False

theorem d36GluedDiagOther_of_l27
    (hL38 : D3L38) (hres : D36GluedDiagL27) : D36GluedDiagOther := by
  intro W _ _ M Mp T L V t n hd A hA hQ hAU hdiag hn24 hn3 hcub hshape
  have hsw := d36_gluedSwap hL38 n hA hQ hAU
  obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have hsimple : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hA38
  have hLstab : L ≤ stabSub (orbSup T V) := (d36t_L_le_Mp n).trans (d36t_Mp_le_stab_orbSup n)
  have hLU : L ≤ stabSub (commSub (orbSup T V) L) := by
    intro l hl u
    constructor
    · intro h
      have := d36t_L_inv_U n l⁻¹ (L.inv_mem hl) _ h
      simpa using this
    · exact d36t_L_inv_U n l hl u
  have hnc : ¬ L ≤ centSub (orbSup T V) := by
    intro hLc
    have hgap := hsw.gap
    have hbot : commSub (orbSup T V) L = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro v hv l hl
      exact hLc hl v hv
    have h0 : rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V)) = 0 := by
      rw [hbot, Subgroup.bot_subgroupOf, rk_bot]
    rw [h0] at hgap
    omega
  have hfaith : L ⊓ centSub (orbSup T V) = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hsimple hLstab hnc
  let e : ↥L ≃* ↥(autSub L (orbSup T V)) := autSubEquivOfFaithful hLstab hfaith
  have hsimple₀ : IsSimpleGroup ↥(autSub L (orbSup T V)) := MulEquiv.isSimpleGroup e.symm
  have hnonab₀ : ∃ a b : ↥(autSub L (orbSup T V)), a * b ≠ b * a := by
    have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp n.std.hyp.comp
    by_contra hcon
    push Not at hcon
    apply hns
    refine Group.isSolvable_of_comm fun a b => ?_
    have h1 := hcon (e a) (e b)
    apply e.injective
    rw [map_mul, map_mul]
    exact h1
  have hA38₀ : A38Types ↥(autSub L (orbSup T V)) := a38Types_congr e hA38
  have hL₀U : autSub L (orbSup T V) ≤ stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) :=
    autSub_le_stabSub_subgroupOf hLU
  have hexp := d36_exp_VT n
  have hfix := d36_L_fix_Ut' hL38 n
  rcases Z7a.a38_cases hA38₀ with ⟨k, hk, hL⟩ | ⟨k, hk, hL⟩ | hL | ⟨p, hp, hp7, hL⟩
  · by_cases hk2 : k = 2
    · subst hk2
      exact hsw.false_of_psl2_four hexp (d36_L_le_X n) hfix hL₀U hdiag hsimple₀ hnonab₀ hL
    · exact hsw.false_of_psl2_two hexp (d36_L_le_X n) hfix hL₀U hdiag hsimple₀ hnonab₀
        (by omega) hL
  · exact hsw.false_of_sz hexp hfix hL₀U hdiag hsimple₀ hnonab₀ hk hL
  · exact hsw.false_of_j1 hexp hfix hL₀U hdiag hsimple₀ hnonab₀ hL
  · by_cases h7 : p = 7
    · subst h7
      exact hres W M Mp T L V t n hd A hA hQ hAU hdiag hn24 hn3
        (isPSL_congr e.symm hL) hcub hshape
    by_cases h31 : p = 31
    · subst h31
      exact hsw.false_of_psl2_31 hexp hfix hL₀U hdiag hsimple₀ hnonab₀ hL
    have h11 : 11 ≤ p := by
      by_contra hcon
      have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
      rcases this with rfl | rfl | rfl <;> norm_num at hp
    exact hsw.false_of_psl2_prime hexp hfix hL₀U hdiag hsimple₀ hnonab₀ hp h11 h31 hL

end CFSG.Quasithin
