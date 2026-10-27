module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion

public section

namespace CFSG.Quasithin.RonanG72

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem odd_card_center {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have h := CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hW
    (isIrrOn_toMulSub hirr).2
  rwa [← map_center_toMulSubEquiv L,
    Subgroup.card_map_of_injective (toMulSubEquiv L).injective] at h

theorem le_finrank_of_mulEquiv {L : Subgroup (GLV V)} {S : Type} [Group S] (e : ↥L ≃* S)
    {ρ : ℕ}
    (hDim : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : S →* MulAut W, Function.Injective σ → 2 ^ ρ ≤ Nat.card W) :
    ρ ≤ Module.finrank (ZMod 2) V := by
  let σ : S →* MulAut (Multiplicative V) :=
    (toMulSub L).subtype.comp ((toMulSubEquiv L).toMonoidHom.comp e.symm.toMonoidHom)
  have hσ : Function.Injective σ :=
    Subtype.val_injective.comp ((toMulSubEquiv L).injective.comp e.symm.injective)
  have hd := hDim (Multiplicative V) mul_self_eq_one_multiplicative σ hσ
  rw [natCard_multiplicative] at hd
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hd

theorem mulEquiv_of_cover {L : Subgroup (GLV V)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrr L ⊤)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Nonempty (↥L ≃* S) := by
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover ⟨hq.1.commutator_eq_top, hq.2.1⟩ hirr e hCover
  exact ⟨f⟩

theorem ord_two_eleven : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem ord_two_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem ten_le_of_eleven_dvd {L : Subgroup (GLV V)} {S : Type} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) (h : 11 ∣ Nat.card S) :
    10 ≤ Module.finrank (ZMod 2) V := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := orderOf_two_le_finrank_of_dvd_card_quotient e (p := 11) (by norm_num) h
  rwa [ord_two_eleven] at this

theorem twelve_le_of_thirteen_dvd {L : Subgroup (GLV V)} {S : Type} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) (h : 13 ∣ Nat.card S) :
    12 ≤ Module.finrank (ZMod 2) V := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have := orderOf_two_le_finrank_of_dvd_card_quotient e (p := 13) (by norm_num) h
  rwa [ord_two_thirteen] at this

end CFSG.Quasithin.RonanG72
