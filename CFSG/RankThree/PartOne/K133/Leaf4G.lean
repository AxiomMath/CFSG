module

public import CFSG.RankThree.PartOne.K133.G2Char
public import CFSG.RankThree.PartOne.K133.G2Odd
public import CFSG.RankThree.PartOne.K133.Leaf4Sp
public import CFSG.RankThree.PartOne.S11c.OddG2Plane
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

set_option linter.unusedSectionVars false

theorem goodRes_G2_prime_field (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hℓ2 : ℓ ≠ 2) (hcard : Nat.card K = ℓ) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hin : ∀ E : Subgroup (MulAut (adjointGroup .G2 K)), IsElementaryAbelian p E →
      E ≤ inner (adjointGroup .G2 K)) :
    GoodRes p (adjointGroup .G2 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hKodd : Odd (Nat.card K) := by rw [hcard]; exact hℓ.odd_of_ne_two hℓ2
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    refine goodRes_of_inner_noConfig_el hp center_adjointGroup_eq_bot hin ?_
    intro C hC hCc Kb hKs hKn hpKb hcomm
    refine g2_no_simple_normalizing_pSubgroup K h2 (U := C) (Kb := Kb) hKn ?_
      (IsElementaryAbelian.isPGroup p C) ?_
    · intro hbot
      rw [hbot] at hCc
      simp only [Subgroup.card_bot] at hCc
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    · intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h := hcomm x hx k hk
        have e : k * x * k⁻¹ = x := by rw [← h, mul_inv_cancel_right]
        rw [e]
        exact hx
      · intro hx
        have h : k * x * k⁻¹ * k = k * (k * x * k⁻¹) := hcomm _ hx k hk
        have h1 : k * x = k * (k * x * k⁻¹) := by rw [← h]; group
        have e : x = k * x * k⁻¹ := mul_left_cancel h1
        rw [e]
        exact hx
  · have hpK : ¬ p ∣ Nat.card K := by
      rw [hcard]
      intro h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h)
    exact (noRankThree_G2_odd K hKodd hp h5 hpK hin).dead.good.goodRes

theorem kf133ResMaxAt_leaf4_zero (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf4 0) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he1, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hmod : ChevalleyExceptionalModel X .G2 q.p q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e0
      (CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2)
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod.2
  have hKc : Nat.card K = q.p := by rw [hK, he1, pow_one]
  have : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK
  let e' : X ≃* adjointGroup .G2 K := e.trans (adjointQuotientEquiv .G2 K)
  have hmodA : ChevalleyExceptionalModel (adjointGroup .G2 K) .G2 q.p q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e'.symm hmod
  have hin : ∀ E : Subgroup (MulAut (adjointGroup .G2 K)), IsElementaryAbelian p E →
      E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K) := fun E hE => by
    have : Fact p.Prime := ⟨hp⟩
    exact le_inner_of_forall_orderOf_inner hp (fun β hβ =>
      CFSG.RankThree.PartOne.g2_prime_order_automorphism_inner q.prime_p hq2 hmodA
        ⟨fun _ => he1, fun _ => by omega⟩ hp (by omega) β hβ) E hE
  exact GoodRes.of_mulEquiv hp e' (goodRes_G2_prime_field K hq2 hKc hp h5 hin)

end CFSG.RankThree.PartOne.K133
