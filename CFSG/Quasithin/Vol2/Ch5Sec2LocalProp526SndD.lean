module

public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Centralizers
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

namespace Sec526

theorem isSolvable_of_card_eq_pow_mul_pow {X : Type*} [Group X] [Finite X] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card X = p ^ a * q ^ b) :
    Group.IsSolvable X := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Nat.primeFactors_pow _ ha, Nat.primeFactors_pow _ hb, hp.primeFactors, hq.primeFactors]
  exact (Finset.card_union_le _ _).trans (by simp)

theorem isSolvable_members_twoF4
    {Y : Type} [Group Y] (hY : IsTwistedF4Over 1 Y) {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) : Group.IsSolvable ↥M₁ ∧ Group.IsSolvable ↥M₂ := by
  obtain ⟨e⟩ : Nonempty (Y ≃* MulAut CFSG.Open.quasithinTits) := by
    rcases hY with ⟨-, h⟩ | ⟨h, -, -⟩
    · exact h
    · omega
  let φ : Y ≃* twoF4M := e.trans (twoF4AutEquiv titsOutBound)
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Y ≃* twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hH : Group.IsSolvable ↥twoF4H :=
    isSolvable_of_card_eq_pow_mul_pow (q := 5) (a := 12) (b := 1) Nat.prime_two (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [CFSG.LocalAnalysis.EvenBN.Tits.Model.card_twoF4H])
  have hN : Group.IsSolvable ↥twoF4N :=
    isSolvable_of_card_eq_pow_mul_pow (q := 3) (a := 12) (b := 1) Nat.prime_two (by norm_num)
      (by norm_num) (by norm_num)
      (by norm_num [(CFSG.LocalAnalysis.EvenBN.Tits.Model.card_twoF4N).1])
  have key : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) → Group.IsSolvable ↥M := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    have e1 : ↥M ≃* ↥(M.map f.toMonoidHom) := M.equivMapOfInjective f.toMonoidHom f.injective
    rcases twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm) with
      h1 | h1
    · rw [h1, twoF4Lattice_P₁] at e1
      have e2 := e1.trans (Subgroup.subgroupOfEquivOfLe twoF4H_le_twoF4M)
      exact Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective
    · rw [h1, twoF4Lattice_P₂] at e1
      have hNM : twoF4N ≤ twoF4M := extSub_mono titsN_le_titsD
      have e2 := e1.trans (Subgroup.subgroupOfEquivOfLe hNM)
      exact Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective
  exact ⟨key M₁ (Or.inl rfl), key M₂ (Or.inr rfl)⟩

end Sec526

end CFSG.Quasithin.H13
