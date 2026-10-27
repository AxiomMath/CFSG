module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.PairRankIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.PairRankComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiNe
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4FAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

private theorem inf_fixV_eq_bot_of_isIrrOn {W : Type} [CommGroup W]
    {H X : Subgroup (MulAut W)} {I : Subgroup W} (hI : IsIrrOn H I ⊥)
    (hn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hXI : commSub I X ≠ ⊥) :
    I ⊓ fixV X = ⊥ := by
  have hfix : StableUnder H (fixV X) := stableUnder_fixV hn
  have hstab : StableUnder H (I ⊓ fixV X) := stableUnder_inf hI.2.1 hfix
  rcases hI.2.2.2 (I ⊓ fixV X) hstab bot_le inf_le_left with h | h
  · exact h
  · exfalso
    refine hXI ?_
    rw [commSub_eq_bot_iff]
    exact h ▸ inf_le_right

private theorem eq_of_minimal_of_rank_le_sixteen {W : Type} [CommGroup W] [Finite W]
    {H X X' : Subgroup (MulAut W)} {I U : Subgroup W} (hI : IsIrrOn H I ⊥)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hX'n : ∀ h ∈ H, ∀ x ∈ X', h * x * h⁻¹ ∈ X')
    (hI16 : rk ↥I ≤ 16) (hUI : U ≤ I) (hUne : U ≠ ⊥)
    (hUirr : IsIrrOn (X ⊔ X') U ⊥) (hcardU : Nat.card ↥U = 2 ^ 9) :
    U = I := by
  have hpt : ∀ g ∈ H, ∀ n ∈ X ⊔ X', g * n * g⁻¹ ∈ X ⊔ X' := fun g hg n hn =>
    Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
      ⟨Subgroup.le_normalizer_iff.mpr hXn hg, Subgroup.le_normalizer_iff.mpr hX'n hg⟩ n hn
  have hpt' : ∀ g ∈ H, ∀ n ∈ X ⊔ X', g⁻¹ * n * g ∈ X ⊔ X' := fun g hg n hn => by
    simpa using hpt g⁻¹ (H.inv_mem hg) n hn
  have hmap_eq : ∀ h ∈ H, U.map h.toMonoidHom = U := by
    intro h hh
    by_contra hne
    have hirr : IsIrrOn (X ⊔ X') (U.map h.toMonoidHom) ⊥ :=
      s15_semi_isIrrOn_map (hpt' h hh) (hpt h hh) hUirr
    have hle : U.map h.toMonoidHom ≤ I := by
      rintro _ ⟨u, hu, rfl⟩
      exact hI.2.1 h hh u (hUI hu)
    have hdisj : U ⊓ U.map h.toMonoidHom = ⊥ :=
      f4f_inf_eq_bot_of_irr hUirr hirr (Ne.symm hne)
        (by rw [Subgroup.card_map_of_injective h.injective])
    have hrkU : rk ↥U = 9 := by
      rw [rk, hcardU, padicValNat.prime_pow]
    have h18 : rk ↥(U ⊔ U.map h.toMonoidHom) = 18 := by
      rw [f4f_rk_sup_of_inf_bot hdisj, f4f_rk_map h U, hrkU]
    have hle16 : rk ↥(U ⊔ U.map h.toMonoidHom) ≤ 16 :=
      le_trans (rk_mono (sup_le hUI hle)) hI16
    omega
  have hHU : StableUnder H U := by
    intro h hh u hu
    have hmem : h u ∈ U.map h.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [hmap_eq h hh] at hmem
  rcases hI.2.2.2 U hHU bot_le hUI with h | h
  · exact absurd h hUne
  · exact h

theorem kL32PairRank_holds : KL32PairRank := by
  intro W _ _ hW H X X' I hI hXH hX'H hXn hX'n hXX' hL3 hL3' hXI hX'I
  have hIX : StableUnder X I := fun x hx u hu => hI.2.1 x (hXH hx) u hu
  have hIX' : StableUnder X' I := fun x hx u hu => hI.2.1 x (hX'H hx) u hu
  have hIN : StableUnder (X ⊔ X') I := f4f_stableUnder_sup hIX hIX'
  have hIne : I ≠ ⊥ := hI.1.ne'
  have hIfixX : I ⊓ fixV X = ⊥ := inf_fixV_eq_bot_of_isIrrOn hI hXn hXI
  have hIfixX' : I ⊓ fixV X' = ⊥ := inf_fixV_eq_bot_of_isIrrOn hI hX'n hX'I
  obtain ⟨U, hUI, _hUstab, hUne, hUirr, -⟩ := f4f_exists_minimal hIne hIN
  have hnt : ∀ {Y : Subgroup (MulAut W)}, I ⊓ fixV Y = ⊥ →
      ¬ ∀ y ∈ Y, ∀ u ∈ U, (y : MulAut W) u = u := by
    intro Y hY htriv
    refine hUne (le_bot_iff.mp ?_)
    rw [← hY]
    exact le_inf hUI fun u hu => mem_fixV.mpr fun y hy => htriv y hy u hu
  have hXnt := hnt hIfixX
  have hX'nt := hnt hIfixX'
  obtain ⟨h9, hcard9⟩ := nine_le_rk_and_card_of_isIrrOn hW hXX' hL3 hL3' hUirr hXnt hX'nt
  refine ⟨le_trans h9 (rk_mono hUI), ?_⟩
  intro hI16
  have hcardU : Nat.card ↥U = 2 ^ 9 := hcard9 (le_trans (rk_mono hUI) hI16)
  have hUIeq : U = I :=
    eq_of_minimal_of_rank_le_sixteen hI hXn hX'n hI16 hUI hUne hUirr hcardU
  intro s hs hs2
  rw [← hUIeq]
  exact rk_commSub_zpowers_eq_three hW hXX' hL3 hL3' hcardU hUirr hXnt hX'nt hs hs2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
