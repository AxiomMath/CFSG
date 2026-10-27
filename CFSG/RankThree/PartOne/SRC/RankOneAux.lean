module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup

theorem exists_lift_coprime {W Q : Type*} [Group W] [Finite W] [Group Q] (ρ : W →* Q)
    (hρ : Function.Surjective ρ) {p : ℕ} (hp : p.Prime) {h : Q} (hh : Nat.Coprime (orderOf h) p) :
    ∃ g : W, ρ g = h ∧ Nat.Coprime (orderOf g) p := by
  obtain ⟨g₀, hg₀⟩ := hρ h
  have ho : orderOf g₀ ≠ 0 := (orderOf_pos g₀).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.ne_one
  have hcop : Nat.Coprime (p ^ a) b := Nat.Coprime.pow_left a ((hp.coprime_iff_not_dvd).mpr hb)
  obtain ⟨u, hu0, hu1⟩ := Nat.chineseRemainder hcop 0 1
  have hhb : orderOf h ∣ b := by
    have h1 : orderOf h ∣ p ^ a * b := by
      rw [← hab, ← hg₀]
      exact orderOf_map_dvd ρ g₀
    exact (Nat.Coprime.pow_right a hh).dvd_of_dvd_mul_left h1
  refine ⟨g₀ ^ u, ?_, ?_⟩
  · rw [map_pow, hg₀]
    have : h ^ u = h ^ 1 := by
      rw [pow_eq_pow_iff_modEq]
      exact (hu1.of_dvd hhb)
    simpa using this
  · have hgb : (g₀ ^ u) ^ b = 1 := by
      rw [← pow_mul]
      have hdvd : orderOf g₀ ∣ u * b := by
        rw [hab]
        exact Nat.mul_dvd_mul ((Nat.modEq_zero_iff_dvd.mp hu0)) dvd_rfl
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hgb)
      ((hp.coprime_iff_not_dvd).mpr hb).symm

theorem eq_top_of_perfect_pgroup_quotient {W : Type*} [Group W] [Finite W] [Group.IsPerfect W]
    {p : ℕ} [Fact p.Prime] (N : Subgroup W) [N.Normal] (hN : IsPGroup p (W ⧸ N)) : N = ⊤ := by
  have hperf : Group.IsPerfect (W ⧸ N) := by
    rw [Group.isPerfect_def]
    have h1 : commutator W = ⊤ := Group.IsPerfect.commutator_eq_top
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' N)) h1
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h2
    rw [commutator_def]
    exact h2
  have hsub : Subsingleton (W ⧸ N) := by
    by_contra hns
    have : Nontrivial (W ⧸ N) := not_subsingleton_iff_nontrivial.mp hns
    have : Group.IsNilpotent (W ⧸ N) := hN.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (W ⧸ N) inferInstance
  have h1 : N.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_of_subsingleton (1 : W ⧸ N)
  exact Subgroup.index_eq_one.mp h1

theorem padicValNat_pow_sub_pow {p : ℕ} (hp : p.Prime) {i k : ℕ} (hik : i < k) :
    padicValNat p (p ^ k - p ^ i) = i := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hik
  have h1 : p ^ (i + d + 1) - p ^ i = p ^ i * (p ^ (d + 1) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, add_assoc]
  have hpos : 1 < p ^ (d + 1) := Nat.one_lt_pow (Nat.succ_ne_zero d) hp.one_lt
  have h2 : p ^ (d + 1) - 1 ≠ 0 := by omega
  rw [h1, padicValNat.mul (pow_ne_zero _ hp.ne_zero) h2, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd, add_zero]
  intro hdvd
  have hpd : p ∣ p ^ (d + 1) := dvd_pow_self p (Nat.succ_ne_zero d)
  have h3 : p ∣ p ^ (d + 1) - (p ^ (d + 1) - 1) := Nat.dvd_sub hpd hdvd
  have h4 : p ^ (d + 1) - (p ^ (d + 1) - 1) = 1 := by omega
  rw [h4] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem pow_sub_pow_ne_zero {p : ℕ} (hp : p.Prime) {i k : ℕ} (hik : i < k) : p ^ k - p ^ i ≠ 0 := by
  have : p ^ i < p ^ k := Nat.pow_lt_pow_right hp.one_lt hik
  omega

theorem not_pow_four_dvd_card_GL {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k ≤ 3) :
    ¬ p ^ 4 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod p)) := by
  have hp : p.Prime := Fact.out
  rw [Matrix.card_GL_field (𝔽 := ZMod p) k, ZMod.card]
  intro hdvd
  have hne : (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact pow_sub_pow_ne_zero hp i.2
  have h4 := (padicValNat_dvd_iff_le (p := p) hne).mp hdvd
  interval_cases k
  · simp at h4
  · simp only [Fin.prod_univ_one, Fin.val_zero] at h4
    rw [padicValNat_pow_sub_pow hp (by norm_num)] at h4
    omega
  · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one] at h4
    rw [padicValNat.mul (pow_sub_pow_ne_zero hp (by norm_num)) (pow_sub_pow_ne_zero hp (by norm_num)),
      padicValNat_pow_sub_pow hp (by norm_num), padicValNat_pow_sub_pow hp (by norm_num)] at h4
    omega
  · simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two] at h4
    rw [padicValNat.mul (mul_ne_zero (pow_sub_pow_ne_zero hp (by norm_num))
        (pow_sub_pow_ne_zero hp (by norm_num))) (pow_sub_pow_ne_zero hp (by norm_num)),
      padicValNat.mul (pow_sub_pow_ne_zero hp (by norm_num)) (pow_sub_pow_ne_zero hp (by norm_num)),
      padicValNat_pow_sub_pow hp (by norm_num), padicValNat_pow_sub_pow hp (by norm_num),
      padicValNat_pow_sub_pow hp (by norm_num)] at h4
    omega

theorem isElementaryAbelian_range {A G : Type*} [CommGroup A] [Group G] {p : ℕ} (f : A →* G)
    (hpow : ∀ a : A, a ^ p = 1) : IsElementaryAbelian p f.range := by
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow, hpow, map_one]
    rfl

theorem isElementaryAbelian_map' {A G : Type*} [Group A] [Group G] {p : ℕ} (f : A →* G)
    {E : Subgroup A} (hE : IsElementaryAbelian p E) : IsElementaryAbelian p (E.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map hE _

end CFSG.RankThree.PartOne.SRC
