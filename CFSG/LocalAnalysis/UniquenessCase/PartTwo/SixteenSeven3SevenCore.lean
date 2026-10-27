module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {M L : Subgroup (MulAut W)} {Z : Subgroup W}

theorem s16c167_card_le_four_of_sevenCfg (h : SevenCfg M L Z) {X : Subgroup (MulAut W)}
    (hXM : X ≤ M) (hX : IsElemAbelian2 X) : Nat.card X ≤ 4 := by
  classical
  have hsq : ∀ x : ↥X, (x : MulAut W) * (x : MulAut W) = 1 := fun x => by
    have h2 := hX.2 (x : MulAut W) x.2
    rwa [pow_two] at h2
  let ρ : ↥X →* Equiv.Perm ↥(conjSubs M Z) := (sevenPerm M Z).comp (Subgroup.inclusion hXM)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hstab : ∀ Y ∈ conjSubs M Z, Y.map (x : MulAut W).toMonoidHom = Y := by
      intro Y hY
      have h1 := congrArg
        (fun σ : Equiv.Perm ↥(conjSubs M Z) => ((σ ⟨Y, hY⟩ : ↥(conjSubs M Z)) : Subgroup W)) hx
      exact h1
    exact Subtype.ext (h.eq_one_of_stab (hXM x.2) (hsq x) hstab)
  have hcardS : Nat.card ↥(conjSubs M Z) = 4 := by
    rw [Nat.card_coe_set_eq]
    exact h.ncard
  haveI : Finite ↥(conjSubs M Z) :=
    Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have hrange : ∀ y ∈ ρ.range, y * y = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x), map_one]
  calc Nat.card X = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ≤ 4 := s16c167_card_le_four_of_perm_four hcardS hrange

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
