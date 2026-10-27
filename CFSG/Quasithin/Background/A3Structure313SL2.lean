module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
import CFSG.Adapters.StatedPSLTwo
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.A313

open Matrix CFSG.Assembly.LowTwoRank

theorem exists_finset_card_four {r : ℕ} [Fact r.Prime] (h5 : 5 ≤ r) :
    ∃ s : Finset (ZMod r), s.card = 4 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod r)))
    (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
  exact ⟨t, ht⟩

theorem isPerfect_sl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h5)

theorem isSimple_psl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)

theorem isQuasisimple_sl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  have hperf := isPerfect_sl2 hr h5
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin 2) (ZMod r) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) := isSimple_psl2 hr h5
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative (SpecialLinearGroup (Fin 2) (ZMod r) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) := ⟨⟨fun a b => hcon a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ hcomm

theorem card_sl2 {r : ℕ} (hr : r.Prime) :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod r)) = r * (r ^ 2 - 1) := by
  have := Fact.mk hr
  have hq : 1 < Fintype.card (ZMod r) := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    show Fintype.card (ZMod r) ^ 2 - Fintype.card (ZMod r) =
      Fintype.card (ZMod r) * (Fintype.card (ZMod r) - 1) by rw [Nat.mul_sub_one, sq],
    ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm, ZMod.card]

theorem card_rootsOfUnity_two {K : Type*} [Field K] (hchar : (2 : K) ≠ 0) :
    Nat.card (rootsOfUnity 2 K) = 2 := by
  classical
  let z : rootsOfUnity 2 K :=
    ⟨(-1 : Kˣ), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp [pow_two]⟩
  have hz : z ≠ (1 : rootsOfUnity 2 K) := by
    intro hz
    have hvU : (-1 : Kˣ) = 1 := by
      simpa [z] using congrArg (fun x : rootsOfUnity 2 K ↦ (x : Kˣ)) hz
    have hv' : (-1 : K) = 1 := congrArg Units.val hvU
    apply hchar
    calc (2 : K) = 1 - (-1) := by ring
      _ = 1 - 1 := by rw [hv']
      _ = 0 := by ring
  apply (Nat.card_eq_two_iff' (1 : rootsOfUnity 2 K)).2
  refine ⟨z, hz, ?_⟩
  intro y hy
  have hyPow : (y : Kˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 (y : Kˣ)).mp y.property
  let a : K := ((y : Kˣ) : K)
  have hyPow' : a ^ 2 = 1 := by simpa [a] using congrArg Units.val hyPow
  have hfactor : (a - 1) * (a + 1) = 0 := by
    calc (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = 0 := by rw [hyPow']; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exfalso
    apply hy
    apply Subtype.ext
    apply Units.ext
    change a = 1
    exact sub_eq_zero.mp hminus
  · apply Subtype.ext
    apply Units.ext
    change a = -1
    exact eq_neg_of_add_eq_zero_left hplus

theorem card_center_sl2 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) = 2 := by
  have := Fact.mk hr
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := ZMod r)
  rw [Nat.card_congr e.toEquiv]
  exact card_rootsOfUnity_two (CFSG.SectionRank.Ccomm.two_ne_zero_zmod hr2)

theorem isPSL_two_of_mulEquiv {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {Y : Type} [Group Y]
    (e : Y ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) : IsPSL 2 r 1 Y :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_two_of_mulEquiv_zmod hr h5 e

variable {X : Type} [Group X]

theorem IsSL2.isQuasisimple {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : IsSL2 r X) :
    CFSG.IsQuasisimple X :=
  h.elim fun e => CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 hr h5)

theorem IsSL2.card_eq {r : ℕ} (hr : r.Prime) (h : IsSL2 r X) :
    Nat.card X = r * (r ^ 2 - 1) :=
  h.elim fun e => by rw [Nat.card_congr e.toEquiv, card_sl2 hr]

theorem IsSL2.card_center {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : IsSL2 r X) :
    Nat.card (Subgroup.center X) = 2 :=
  h.elim fun e => by
    rw [← card_center_sl2 hr hr2, ← Subgroup.map_center_eq e,
      Subgroup.card_map_of_injective e.injective]

theorem mul_sq_sub_one_injective {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (h : p * (p ^ 2 - 1) = q * (q ^ 2 - 1)) : p = q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : p ^ 2 - 1 < q ^ 2 - 1 := by
      have : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
      omega
    have h2 : 0 < p ^ 2 - 1 → p * (p ^ 2 - 1) < q * (q ^ 2 - 1) := fun hpos =>
      Nat.mul_lt_mul'' hlt h1
    by_cases hpos : 0 < p ^ 2 - 1
    · exact absurd h (Nat.ne_of_lt (h2 hpos))
    · have hp1 : p = 1 := by
        by_contra hp1
        have : 2 ≤ p := by omega
        have : 4 ≤ p ^ 2 := by nlinarith
        omega
      subst hp1
      have : 0 < q * (q ^ 2 - 1) := by
        have : 2 ≤ q := by omega
        have : 4 ≤ q ^ 2 := by nlinarith
        exact Nat.mul_pos (by omega) (by omega)
      simp at h
      omega
  · have h1 : q ^ 2 - 1 < p ^ 2 - 1 := by
      have : q ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      omega
    by_cases hpos : 0 < q ^ 2 - 1
    · exact absurd h (Nat.ne_of_gt (Nat.mul_lt_mul'' hlt h1))
    · have hq1 : q = 1 := by
        by_contra hq1
        have : 2 ≤ q := by omega
        have : 4 ≤ q ^ 2 := by nlinarith
        omega
      subst hq1
      have : 0 < p * (p ^ 2 - 1) := by
        have : 2 ≤ p := by omega
        have : 4 ≤ p ^ 2 := by nlinarith
        exact Nat.mul_pos (by omega) (by omega)
      simp at h
      omega

theorem IsSL2.eq_of_isSL2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : IsSL2 p X)
    (h2 : IsSL2 q X) : p = q := by
  have := IsSL2.card_eq hp h1
  rw [IsSL2.card_eq hq h2] at this
  exact (mul_sq_sub_one_injective hq.one_lt.le hp.one_lt.le this).symm

theorem IsSL2.eq_bot_of_odd {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : IsSL2 r X) {K : Subgroup X}
    [K.Normal] (hK : Odd (Nat.card K)) : K = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (IsSL2.isQuasisimple hr h5 h)
    (N := K) inferInstance with htop | hle
  · exfalso
    have hcard : Nat.card K = Nat.card X := by rw [htop, Subgroup.card_top]
    rw [hcard, IsSL2.card_eq hr h] at hK
    have hr2 : ¬ 2 ∣ r := fun h2 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2
      omega
    have h3 : 2 ∣ r ^ 2 - 1 := by
      have hodd : Odd r := hr.odd_of_ne_two (by omega)
      have : Odd (r ^ 2) := hodd.pow
      have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [Nat.odd_iff] at this
      omega
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr (Dvd.dvd.mul_left h3 r))
  · have hdvd : Nat.card K ∣ Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le hle
    rw [IsSL2.card_center hr (by omega) h] at hdvd
    have : Nat.card K = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hK
        exact absurd hK (by decide)
    exact Subgroup.eq_bot_of_card_eq K this

theorem IsSL2.not_isSolvable {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : IsSL2 r X) :
    ¬ Group.IsSolvable X := by
  have hq := IsSL2.isQuasisimple hr h5 h
  have : Group.IsPerfect X := hq.1
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable X

end CFSG.Quasithin.A313
