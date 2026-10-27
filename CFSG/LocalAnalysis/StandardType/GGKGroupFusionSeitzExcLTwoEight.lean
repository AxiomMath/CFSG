module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcBasic
public import CFSG.CharacterTheory.Burnside
public import CFSG.Adapters.LinearCatalog
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggIsSolvable_of_card_eq_pow_mul_pow {G : Type} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  let := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem ggCard_dvd_factorial_index {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {X : Subgroup G} (hX : X ≠ ⊤) : Nat.card G ∣ X.index.factorial := by
  have hcore : X.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ X.normalCore_le)) hX
  have h := X.index_normalCore_dvd_factorial_index
  rwa [hcore, Subgroup.index_bot] at h

theorem ggIsSolvable_of_not_dvd_index_of_card_eq_504 {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 504) {X : Subgroup G} (hX : X ≠ ⊤)
    (h3 : ¬ 3 ∣ X.index) : Group.IsSolvable ↥X := by
  have hfac := ggCard_dvd_factorial_index hX
  rw [hG] at hfac
  have hmul := X.card_mul_index
  rw [hG] at hmul
  have hn1 : X.index ≠ 1 := fun h => hX (Subgroup.index_eq_one.mp h)
  have hdvd : X.index ∣ 504 := ⟨Nat.card X, by rw [← hmul, mul_comm]⟩
  have h56 : X.index ∣ 56 := by
    have hcop : Nat.Coprime X.index 9 :=
      Nat.Coprime.pow_right 2 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
        Nat.prime_three).mpr h3)))
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  have hmem : X.index ∈ Nat.divisors 56 := Nat.mem_divisors.mpr ⟨h56, by norm_num⟩
  have hd : Nat.divisors 56 = {1, 2, 4, 7, 8, 14, 28, 56} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> rw [h] at hmul hfac
  · exact absurd h hn1
  · exact absurd hfac (by decide)
  · exact absurd hfac (by decide)
  · exact ggIsSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by omega)
  · exact ggIsSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 1) Nat.prime_three
      (by norm_num : Nat.Prime 7) (by norm_num) (by omega)
  · exact ggIsSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by omega)
  · exact ggIsSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by omega)
  · exact ggIsSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by omega)

theorem ggCard_lTwoEight {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card K = 504 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e1 : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hF : Nat.card (GaloisField q.p q.exponent) = 2 ^ 3 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2, hq3]
  rw [Nat.card_congr e1.toEquiv,
    Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      _).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  decide

theorem ggKGroupFusionAt_lTwoEight
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) :
    GGKGroupFusionAt GGKFSeitzLTwoEight :=
  ggKGroupFusionAt_of_solvable hSch fun _ _ ⟨hp, d, q, hi, hq2, hq3, hd⟩ K _ _ _ ⟨e⟩ _ hX h3 => by
    subst hp hi
    exact ggIsSolvable_of_not_dvd_index_of_card_eq_504 (ggCard_lTwoEight d q hq2 hq3 hd e) hX h3

end CFSG.StandardType
