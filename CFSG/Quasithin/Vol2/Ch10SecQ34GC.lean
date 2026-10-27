module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {I : Subgroup V}
  {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}

theorem injective_of_realizes (hD : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H I ⊥ π) :
    Function.Injective π := by
  obtain ⟨e, he⟩ := B5.exists_linModel hD
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hact : ∀ v : Fin 3 → ZMod 2,
      (((γ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        v = v := by
    intro v
    set u : ↥I := e.symm (Multiplicative.ofAdd v) with hu
    have hπu : ((π γ : ↥H) : MulAut V) u ∈ I := by rw [hγ]; exact u.2
    have h := he γ u hπu
    have h2 : (⟨((π γ : ↥H) : MulAut V) u, hπu⟩ : ↥I) = u := Subtype.ext (by
      show ((π γ : ↥H) : MulAut V) (u : V) = u
      rw [hγ]
      rfl)
    rw [h2, hu, MulEquiv.apply_symm_apply] at h
    have h3 := congrArg Multiplicative.toAdd h
    exact h3.symm
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrFun (hact (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h
  rw [h]
  show (if i = j then (1 : ZMod 2) else 0) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j
  rw [Matrix.one_apply]

theorem card_eq_168 (hD : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H I ⊥ π) :
    Nat.card H = 168 := by
  rw [← card_statedSL_three_two]
  exact (Nat.card_congr (Equiv.ofBijective π ⟨injective_of_realizes hD, hD.1⟩)).symm

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
