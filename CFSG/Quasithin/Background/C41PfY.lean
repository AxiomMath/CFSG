module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sl3Order_lt' {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := by
  have h1 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ha3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have ha2' : 0 < a ^ 2 - 1 := by
    have : 4 ≤ a ^ 2 := by nlinarith
    omega
  have h3 : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h4 : a ^ 3 - 1 < b ^ 3 - 1 := by omega
  exact Nat.mul_lt_mul'' h1 (Nat.mul_lt_mul'' h3 h4)

theorem card_statedSL_three' (F : Type) [Field F] [Fintype F] :
    Nat.card ↥(StatedSL 3 F) =
      Fintype.card F ^ 3 * ((Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1)) := by
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    Nat.card_eq_fintype_card]
  have : Finset.Icc 2 3 = {2, 3} := by decide
  rw [this, Finset.prod_pair (by norm_num)]

omit [Finite G] in
theorem card_eq_of_modO2Surj {K : Subgroup G} {F F' : Type} [Field F] [Fintype F] [Field F']
    [Fintype F'] {α : ↥K →* ↥(StatedSL 3 F)} {α' : ↥K →* ↥(StatedSL 3 F')}
    (hα : IsModO2Surj K α) (hα' : IsModO2Surj K α') : Fintype.card F = Fintype.card F' := by
  have e1 : Nat.card ↥(StatedSL 3 F) = Nat.card (ModO2 K) :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)).toEquiv).symm
  have e2 : Nat.card ↥(StatedSL 3 F') = Nat.card (ModO2 K) :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hα'.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α' hα'.1)).toEquiv).symm
  have h := e1.trans e2.symm
  rw [card_statedSL_three', card_statedSL_three'] at h
  have ha : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hb : 2 ≤ Fintype.card F' := Fintype.one_lt_card
  rcases lt_trichotomy (Fintype.card F) (Fintype.card F') with hlt | heq | hgt
  · exact absurd h (sl3Order_lt' ha hlt).ne
  · exact heq
  · exact absurd h (sl3Order_lt' hb hgt).ne'

omit [Finite G] in
theorem natWith_of_sumOne {K W : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : IsModO2Surj K α)
    (h : IsSumOfNaturalModulesVia K W ⊥ α false 1) :
    ∃ β : ↥W →* Multiplicative (Fin 3 → F),
      IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β := by
  obtain ⟨hA, -, β, hβ, hβker, hβeq⟩ := h
  let e : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  refine ⟨e.toMonoidHom.comp β, hA, hα.1, hα.2, e.surjective.comp hβ, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective β _ e.injective, hβker]
  · intro a u v huv
    have h0 := hβeq a u v huv 0
    simpa [moduleAct, e] using h0

end CFSG.Quasithin.C41Pf
