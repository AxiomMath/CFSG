module

public import CFSG.RankThree.PartOne.K133.OddChar4
public import CFSG.RankThree.PartOne.S11c.PlaneSp
public import CFSG.RankThree.PartOne.CTP.SeitzSpIndex
public import CFSG.RankThree.PartOne.K133.ResTransfer
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem le_inner_of_forall_orderOf_inner {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (h : ∀ β : MulAut X, orderOf β = p → β ∈ inner X) (E : Subgroup (MulAut X))
    (hE : IsElementaryAbelian p E) : E ≤ inner X := by
  intro β hβ
  have hβp : β ^ p = 1 := by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) ⟨β, hβ⟩
    simpa using congrArg Subtype.val this
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβp) with h1 | h1
  · rw [orderOf_eq_one_iff.1 h1]
    exact ⟨1, map_one _⟩
  · exact h β h1

theorem statedSp_scalar_sq {K : Type} [Field K] (z : StatedSp 2 K)
    (hz : (z : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K) : z ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  have hc : (z : GL (Fin 2 ⊕ Fin 2) K) ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  exact LIT.sq_eq_one_of_form (CFSG.Assembly.RankThreeEven.sympForm 2 K) (LIT.sympForm_det 2)
    (z : GL (Fin 2 ⊕ Fin 2) K) hc
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 z.2)

theorem goodRes_statedProj_sp_four {K : Type} [Field K] [Finite K] {r p : ℕ} [Fact r.Prime] [CharP K r]
    (hcard : Nat.card K = r) (hp : p.Prime) (h5 : 5 ≤ p)
    [IsSimpleGroup (StatedProj (StatedSp 2 K))]
    (hne : ∃ a b : StatedProj (StatedSp 2 K), a * b ≠ b * a)
    (hin : ∀ E : Subgroup (MulAut (StatedProj (StatedSp 2 K))), IsElementaryAbelian p E →
      E ≤ inner (StatedProj (StatedSp 2 K))) :
    GoodRes p (StatedProj (StatedSp 2 K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hr : r.Prime := Fact.out
  have hZ : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := center_eq_bot_of_simple_nonabelian hne
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  by_cases hpr : p = r
  · subst hpr
    exact goodRes_statedProj_four_char h5 (exists_natCast_of_card_eq_prime hcard) (by simp)
      (StatedSp 2 K) hne hin
  · have hpK : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K r p] at h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).1 h0).symm
    have hno : NoRankThree p (StatedProj (StatedSp 2 K)) := by
      refine noRankThree_of_inner_rank_el hp hZ hin ?_
      intro A hA hAc
      have hle := statedProj_card_le_of_bound (N := 2) (k := 2) hp hp2 (StatedSp 2 K)
        (fun z hz => statedSp_scalar_sq z hz)
        (fun E hEM hcomm hexp => by
          have := LIT.card_le_pow_half_of_form_gl hp hpK (CFSG.Assembly.RankThreeEven.sympForm 2 K)
            (LIT.sympForm_det 2) (LIT.sympForm_alt 2) E hcomm hexp
            (fun g hg => CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1
              (hEM hg))
          simpa using this) A hA
      rw [hAc] at hle
      have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    exact hno.dead.good.goodRes

theorem kf133ResMaxAt_leaf4_one (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf4 1) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he1, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF := CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
  have : Finite Fd :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
  have : Fact p.Prime := ⟨hp⟩
  have e1 : X ≃* StatedProj (StatedSp 2 Fd) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
  have : IsSimpleGroup (StatedProj (StatedSp 2 Fd)) := e1.symm.isSimpleGroup
  have hne' : ∃ a b : StatedProj (StatedSp 2 Fd), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcard1 : Nat.card Fd = q.p := by rw [hF, he1, pow_one]
  have : CharP Fd q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hF
  have hin : ∀ E : Subgroup (MulAut (StatedProj (StatedSp 2 Fd))), IsElementaryAbelian p E →
      E ≤ inner (StatedProj (StatedSp 2 Fd)) := fun E hE =>
    le_inner_of_forall_orderOf_inner hp
      (fun β hβ => sp_prime_order_inner q.prime_p q.exponent_pos hF hp (by omega) (by omega) β hβ) E hE
  exact GoodRes.of_mulEquiv hp e1 (goodRes_statedProj_sp_four hcard1 hp h5 hne' hin)

end CFSG.RankThree.PartOne.K133
