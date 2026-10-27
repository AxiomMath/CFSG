module

public import CFSG.RankThree.PartTwo.Sec9.Statements
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.KFacts.K72Omega
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem isCyclic_sylow_of_mulEquiv_of_isCyclic {X Y : Type*} [Group X] [Group Y] [Finite X]
    {p : ℕ} [Fact p.Prime] (e : X ≃* Y) (hY : ∀ S : Sylow p Y, IsCyclic S) (S : Sylow p X) :
    IsCyclic S := by
  have h : IsCyclic ((S : Subgroup X).map e.toMonoidHom) :=
    hY (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact isCyclic_of_surjective
    ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem ringChar_ne_three_and_four_le {p n : ℕ} [Fact p.Prime] (hp : p ≠ 3) (hn : n ≠ 0)
    (h4 : 4 ≤ p ^ n) : ringChar (GaloisField p n) ≠ 3 ∧ 4 ≤ Nat.card (GaloisField p n) := by
  rw [ringChar.eq (GaloisField p n) p, GaloisField.card p n hn]
  exact ⟨hp, h4⟩

theorem exists_mulEquiv_psl2_of_isList1016 {X : Type} [Group X] (hX : Sec9.IsList1016 X)
    (hL3 : ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 3 ∧ 4 ≤ Nat.card K ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 K) := by
  rcases hX with ⟨p, e, _, hp, he, ⟨eq⟩⟩ | ⟨n, hn, ⟨eq⟩⟩ | hL
  · obtain ⟨h3, h4⟩ := ringChar_ne_three_and_four_le (p := p) (n := 3 * e) (by omega) (by omega)
      (le_trans (by omega) (Nat.le_self_pow (by omega) p))
    exact ⟨_, inferInstance, inferInstance, h3, h4, ⟨eq.trans (Sec4.projSLEquivPSL _)⟩⟩
  · obtain ⟨h3, h4⟩ := ringChar_ne_three_and_four_le (p := 2) (n := 3 * n) (by omega) (by omega)
      (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n)))
    exact ⟨_, inferInstance, inferInstance, h3, h4, ⟨eq.trans (Sec4.projSLEquivPSL _)⟩⟩
  · exact absurd hL hL3

theorem isCyclic_sylow_three_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) (S : Sylow 3 X) : IsCyclic S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hn hL S
  · obtain ⟨K, _, _, h3, h4, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact isCyclic_sylow_of_mulEquiv_of_isCyclic e (KFacts.isCyclic_sylow_three_psl2 h3 h4) S

theorem center_eq_bot_of_isList1016 {X : Type} [Group X] [Finite X] (hX : Sec9.IsList1016 X) :
    Subgroup.center X = ⊥ := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.center_eq_bot_of_isoLThreeMinusPi hn hL
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e
      (CFSG.GorensteinWalter.psl2_center_eq_bot K)

theorem exists_pow_mul_isInnerAut_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {σ τ : MulAut X}
    (hσP : σ ∈ P) (hτP : τ ∈ P) (hσ3 : σ ^ 3 = 1) (hσ : ¬ KFacts.IsInnerAut σ)
    (hτ3 : τ ^ 3 = 1) : ∃ i : ℕ, KFacts.IsInnerAut (σ ^ i * τ) := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.exists_pow_mul_isInnerAut_of_isoLThreeMinusPi hn hL hP hσP hτP hσ3 hσ hτ3
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact KFacts.exists_pow_mul_isInnerAut_of_mulEquiv_psl2 e hP hσP hτP hσ3 hσ hτ3

theorem commute_of_pow_three_eq_one_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {σ τ : MulAut X}
    (hσP : σ ∈ P) (hτP : τ ∈ P) (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) : σ * τ = τ * σ :=
  KFacts.commute_of_pow_three_eq_one_of_isPGroup (isCyclic_sylow_three_of_isList1016 hX) hP
    (fun _ hσP _ hτP hσ3 hτ3 hσ => exists_pow_mul_isInnerAut_of_isList1016 hX hP hσP hτP hσ3 hσ hτ3)
    hσP hτP hσ hτ

end CFSG.RankThree.PartTwo.Sec11
