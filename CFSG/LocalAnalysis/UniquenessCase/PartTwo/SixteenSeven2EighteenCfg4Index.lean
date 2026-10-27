module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_cfg4_card_aut_dvd {Y : Type} [Group Y] [Finite Y] (hc : Nat.card Y = 4)
    (hY : ∀ y : Y, y ^ 2 = 1) : Nat.card (MulAut Y) ∣ 6 := by
  classical
  have := Fintype.ofFinite Y
  let res : MulAut Y →* Equiv.Perm {y : Y // y ≠ 1} :=
    { toFun := fun σ => σ.toEquiv.subtypeEquiv fun y => by
        simp only [ne_eq, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.map_eq_one_iff]
      map_one' := by ext; rfl
      map_mul' := fun σ τ => by ext; rfl }
  have hinj : Function.Injective res := by
    intro σ τ h
    ext y
    by_cases hy : y = 1
    · rw [hy, map_one, map_one]
    · have := congrArg (fun f : Equiv.Perm {y : Y // y ≠ 1} => (f ⟨y, hy⟩ : Y)) h
      exact this
  have hcard : Nat.card (Equiv.Perm {y : Y // y ≠ 1}) = 6 := by
    rw [Nat.card_perm]
    have : Nat.card {y : Y // y ≠ 1} = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, hc]
    rw [this]
    rfl
  rw [← hcard]
  exact Subgroup.card_dvd_of_injective res hinj

theorem s16c167_cfg4_index {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z)
    {Y : Subgroup W} (hY : Y ∈ conjSubs X Z) : 9 ≤ Nat.card ↥(L ⊓ centSub Y) := by
  have hA : L ≤ stabSub Y := s16c167_cfg4_stab F hY
  have h27 : Nat.card ↥L = 27 := by
    obtain ⟨e⟩ := F.elem
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 3) ≃
        (Fin 3 → ZMod 3)),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hmul := card_autSub_mul hA
  rw [h27] at hmul
  have hY4 : Nat.card ↥Y = 4 := by
    rw [card_eq_two_pow F.sq Y, s16c167_cfg4_rk_mem hY, F.rk_eq]
    norm_num
  have hexp : ∀ y : ↥Y, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using F.sq (y : W))
  have hdvdAut : Nat.card (autSub L Y) ∣ Nat.card (MulAut ↥Y) :=
    Subgroup.card_subgroup_dvd_card (autSub L Y)
  have hdvd6 : Nat.card (MulAut ↥Y) ∣ 6 := s16c167_cfg4_card_aut_dvd hY4 hexp
  have hdvd27 : Nat.card (autSub L Y) ∣ 27 := ⟨_, hmul.symm⟩
  have hdvd3 : Nat.card (autSub L Y) ∣ 3 := by
    have h := Nat.dvd_gcd hdvd27 (hdvdAut.trans hdvd6)
    norm_num at h
    exact h
  have ha3 : Nat.card (autSub L Y) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
  have ha1 : 1 ≤ Nat.card (autSub L Y) := Nat.pos_of_dvd_of_pos hdvd3 (by norm_num)
  interval_cases ha : Nat.card (autSub L Y) <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
