module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.GroupTheory.Perm.FiberSubgroup
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

theorem pow_dvd_pow_padicValNat {p k N : ℕ} [Fact p.Prime] (hN : N ≠ 0) (h : p ^ k ∣ N) :
    p ^ k ∣ p ^ padicValNat p N :=
  pow_dvd_pow p ((padicValNat_dvd_iff_le hN).mp h)

theorem padicValNat_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) {g : ι → ℕ}
    (hg : ∀ i ∈ s, g i ≠ 0) :
    padicValNat p (s.prod g) = s.sum fun i => padicValNat p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValNat.mul (hg a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem padicValNat_two_factorial_le {m : ℕ} (hm : m ≠ 0) :
    padicValNat 2 m.factorial ≤ m - 1 := by
  have h := padicValNat_factorial_lt_of_ne_zero 2 hm
  omega

theorem padicValNat_two_factorial_two_pow (a : ℕ) :
    padicValNat 2 (2 ^ a).factorial = 2 ^ a - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, Nat.mul_comm (2 ^ a) 2, padicValNat_factorial_mul (n := 2 ^ a), ih]
      have h : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      omega

theorem padicValNat_two_factorial_add_le (x y : ℕ) :
    padicValNat 2 x.factorial + padicValNat 2 y.factorial ≤ padicValNat 2 (x + y).factorial := by
  have hdvd : x.factorial * y.factorial ∣ (x + y).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add x y
  have hxy : (x + y).factorial ≠ 0 := Nat.factorial_ne_zero (x + y)
  have h2 : 2 ^ (padicValNat 2 x.factorial + padicValNat 2 y.factorial) ∣
      (x + y).factorial := by
    rw [pow_add]
    exact dvd_trans (mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd) hdvd
  exact (padicValNat_dvd_iff_le hxy).mp h2

theorem two_mul_padicValNat_two_factorial_lt {m : ℕ} (hm : m ≠ 0) :
    2 * padicValNat 2 m.factorial < padicValNat 2 (2 * m).factorial := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmf : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hchne : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hchoose : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m) (by omega)
    have h2m : 2 * m - m = m := by omega
    rwa [h2m] at h
  have hval : padicValNat 2 (2 * m).factorial =
      padicValNat 2 ((2 * m).choose m) + padicValNat 2 m.factorial +
        padicValNat 2 m.factorial := by
    rw [← hchoose]
    rw [padicValNat.mul (Nat.mul_ne_zero hchne hmf) hmf, padicValNat.mul hchne hmf]
  have hc : 1 ≤ padicValNat 2 ((2 * m).choose m) :=
    one_le_padicValNat_of_dvd hchne (Nat.two_dvd_centralBinom_of_one_le hmpos)
  rw [hval]
  omega

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem card_dvd_of_isPGroup {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) :
    Nat.card R ∣ 2 ^ padicValNat 2 (Nat.card Ω).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : Nat.card R ∣ Nat.card (Perm Ω) := Subgroup.card_subgroup_dvd_card R
  rw [Nat.card_perm] at hdvd
  rw [hk] at hdvd ⊢
  exact pow_dvd_pow_padicValNat (Nat.factorial_ne_zero _) hdvd

theorem card_eq_of_not_two_dvd_index {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.index) : Nat.card R = 2 ^ padicValNat 2 (Nat.card Ω).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hcard : Nat.card R * R.index = (Nat.card Ω).factorial := by
    rw [Subgroup.card_mul_index, Nat.card_perm]
  have hindex : R.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact Nat.factorial_ne_zero _ hcard.symm
  have hval : padicValNat 2 (Nat.card Ω).factorial = k := by
    rw [← hcard, hk, padicValNat.mul (pow_ne_zero k (by norm_num)) hindex,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hRi, add_zero]
  rw [hk, hval]

theorem not_two_dvd_index_of_dvd_card {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R)
    (hc : 2 ^ padicValNat 2 (Nat.card Ω).factorial ∣ Nat.card R) : ¬ 2 ∣ R.index := by
  intro h2dvd
  have hdvd := card_dvd_of_isPGroup hR
  have heq : Nat.card R = 2 ^ padicValNat 2 (Nat.card Ω).factorial := Nat.dvd_antisymm hdvd hc
  have hcard : Nat.card R * R.index = (Nat.card Ω).factorial := by
    rw [Subgroup.card_mul_index, Nat.card_perm]
  have hcontra : 2 ^ (padicValNat 2 (Nat.card Ω).factorial + 1) ∣ (Nat.card Ω).factorial := by
    have h1 : 2 ^ (padicValNat 2 (Nat.card Ω).factorial + 1) ∣ Nat.card R * R.index := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul (by rw [heq]) h2dvd
    rwa [hcard] at h1
  exact pow_succ_padicValNat_not_dvd (Nat.factorial_ne_zero _) hcontra

theorem two_mul_card_dvd_of_le_alternatingGroup (h2 : 2 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R) :
    2 * Nat.card R ∣ 2 ^ padicValNat 2 (Nat.card Ω).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  haveI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdvd : Nat.card R ∣ Nat.card ↥(alternatingGroup Ω) := Subgroup.card_dvd_of_le hRA
  have h2dvd : 2 * Nat.card R ∣ (Nat.card Ω).factorial := by
    rw [← Nat.card_perm, ← two_mul_nat_card_alternatingGroup]
    exact Nat.mul_dvd_mul_left 2 hdvd
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
  rw [hk, h2k] at h2dvd ⊢
  exact pow_dvd_pow_padicValNat (Nat.factorial_ne_zero _) h2dvd

theorem two_mul_card_eq_of_not_two_dvd_relIndex (h2 : 2 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) :
    2 * Nat.card R = 2 ^ padicValNat 2 (Nat.card Ω).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  haveI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hrelcard :
      Nat.card R * R.relIndex (alternatingGroup Ω) = Nat.card ↥(alternatingGroup Ω) := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := alternatingGroup Ω)
    rw [inf_eq_left.mpr hRA, mul_comm] at h
    exact h
  have h2card : 2 * Nat.card R * R.relIndex (alternatingGroup Ω) = (Nat.card Ω).factorial := by
    rw [mul_assoc, hrelcard, two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hrel : R.relIndex (alternatingGroup Ω) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2card
    exact Nat.factorial_ne_zero _ h2card.symm
  have hval : padicValNat 2 (Nat.card Ω).factorial = k + 1 := by
    rw [← h2card, hk,
      padicValNat.mul (Nat.mul_ne_zero (by norm_num) (pow_ne_zero k (by norm_num))) hrel,
      padicValNat.mul (by norm_num) (pow_ne_zero k (by norm_num)), padicValNat_self,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hRi]
    omega
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
  rw [hk, hval, h2k]

theorem not_two_dvd_relIndex_of_dvd_two_mul_card (h2 : 2 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hc : 2 ^ padicValNat 2 (Nat.card Ω).factorial ∣ 2 * Nat.card R) :
    ¬ 2 ∣ R.relIndex (alternatingGroup Ω) := by
  intro hrel2
  haveI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdvd := two_mul_card_dvd_of_le_alternatingGroup h2 hRA hR
  have heq : 2 * Nat.card R = 2 ^ padicValNat 2 (Nat.card Ω).factorial := Nat.dvd_antisymm hdvd hc
  have hrelcard :
      Nat.card R * R.relIndex (alternatingGroup Ω) = Nat.card ↥(alternatingGroup Ω) := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := alternatingGroup Ω)
    rw [inf_eq_left.mpr hRA, mul_comm] at h
    exact h
  have h2card : 2 * Nat.card R * R.relIndex (alternatingGroup Ω) = (Nat.card Ω).factorial := by
    rw [mul_assoc, hrelcard, two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hcontra : 2 ^ (padicValNat 2 (Nat.card Ω).factorial + 1) ∣ (Nat.card Ω).factorial := by
    have h1 : 2 ^ (padicValNat 2 (Nat.card Ω).factorial + 1) ∣
        2 * Nat.card R * R.relIndex (alternatingGroup Ω) := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul (by rw [heq]) hrel2
    rwa [h2card] at h1
  exact pow_succ_padicValNat_not_dvd (Nat.factorial_ne_zero _) hcontra

theorem card_fiberSubgroup {ι : Type*} [Fintype ι] (f : Ω → ι) :
    Nat.card ↥(TauCeti.fiberSubgroup f) = ∏ i, (Nat.card {x // f x = i}).factorial := by
  calc Nat.card ↥(TauCeti.fiberSubgroup f)
      = Nat.card ((i : ι) → Perm {a // f a = i}) :=
        Nat.card_congr (TauCeti.fiberSubgroupMulEquivPiPerm f).toEquiv
    _ = ∏ i, Nat.card (Perm {a // f a = i}) := Nat.card_pi
    _ = ∏ i, (Nat.card {a // f a = i}).factorial :=
        Finset.prod_congr rfl fun i _ => Nat.card_perm

theorem padicValNat_card_fiberSubgroup {ι : Type*} [Fintype ι] (f : Ω → ι) :
    padicValNat 2 (Nat.card ↥(TauCeti.fiberSubgroup f)) =
      ∑ i, padicValNat 2 (Nat.card {x // f x = i}).factorial := by
  rw [card_fiberSubgroup f]
  exact padicValNat_prod Finset.univ fun i _ => Nat.factorial_ne_zero _

theorem two_mul_card_inf_alternatingGroup {ι : Type*} [Fintype ι] (f : Ω → ι)
    (hi : ∃ i, 2 ≤ Nat.card {x // f x = i}) :
    2 * Nat.card ↥(TauCeti.fiberSubgroup f ⊓ alternatingGroup Ω) =
      Nat.card ↥(TauCeti.fiberSubgroup f) := by
  classical
  obtain ⟨i, hi⟩ := hi
  haveI : Nontrivial {x // f x = i} := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := Nontrivial.exists_pair_ne (α := {x // f x = i})
  have hne : (a : Ω) ≠ b := fun h => hab (Subtype.ext h)
  have hmem : Equiv.swap (a : Ω) b ∈ TauCeti.fiberSubgroup f := by
    rw [TauCeti.mem_fiberSubgroup]
    intro x
    by_cases hx : x = (a : Ω)
    · subst hx
      rw [Equiv.swap_apply_left, b.2, a.2]
    · by_cases hy : x = (b : Ω)
      · subst hy
        rw [Equiv.swap_apply_right, a.2, b.2]
      · rw [Equiv.swap_apply_of_ne_of_ne hx hy]
  have hsign : Equiv.Perm.sign (Equiv.swap (a : Ω) b) = -1 := Equiv.Perm.sign_swap hne
  set F := TauCeti.fiberSubgroup f
  set A := alternatingGroup Ω
  have hsub : (F ⊓ A).subgroupOf F = (Equiv.Perm.sign.comp F.subtype).ker := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker,
      MonoidHom.comp_apply, Equiv.Perm.mem_alternatingGroup]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨x.2, h⟩
  have hrange : (Equiv.Perm.sign.comp F.subtype).range = ⊤ := by
    rw [eq_top_iff']
    intro u
    rcases Int.units_eq_one_or u with h | h
    · rw [h]
      exact MonoidHom.mem_range.mpr ⟨1, map_one _⟩
    · rw [h]
      exact MonoidHom.mem_range.mpr ⟨⟨Equiv.swap (a : Ω) b, hmem⟩, hsign⟩
  have hidx : ((F ⊓ A).subgroupOf F).index = 2 := by
    rw [hsub, Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hcard := Subgroup.card_mul_index ((F ⊓ A).subgroupOf F)
  rw [hidx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := F ⊓ A) (K := F) inf_le_left).toEquiv]
    at hcard
  omega

theorem card_dvd_of_forall_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Ω → ι)
    {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (hf : ∀ g ∈ R, ∀ x, f (g x) = f x) :
    Nat.card R ∣ 2 ^ ∑ i, padicValNat 2 (Nat.card {x // f x = i}).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hle : R ≤ TauCeti.fiberSubgroup f := by
    intro g hg
    rw [TauCeti.mem_fiberSubgroup]
    exact hf g hg
  have hdvd : Nat.card R ∣ Nat.card ↥(TauCeti.fiberSubgroup f) := Subgroup.card_dvd_of_le hle
  have hne : Nat.card ↥(TauCeti.fiberSubgroup f) ≠ 0 := by
    rw [card_fiberSubgroup f]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  rw [hk] at hdvd ⊢
  rw [← padicValNat_card_fiberSubgroup f]
  exact pow_dvd_pow_padicValNat hne hdvd

theorem two_mul_card_dvd_of_forall_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Ω → ι)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hf : ∀ g ∈ R, ∀ x, f (g x) = f x) (hi : ∃ i, 2 ≤ Nat.card {x // f x = i}) :
    2 * Nat.card R ∣ 2 ^ ∑ i, padicValNat 2 (Nat.card {x // f x = i}).factorial := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hle : R ≤ TauCeti.fiberSubgroup f := by
    intro g hg
    rw [TauCeti.mem_fiberSubgroup]
    exact hf g hg
  have hdvd : Nat.card R ∣ Nat.card ↥(TauCeti.fiberSubgroup f ⊓ alternatingGroup Ω) :=
    Subgroup.card_dvd_of_le (le_inf hle hRA)
  have h2dvd : 2 * Nat.card R ∣ Nat.card ↥(TauCeti.fiberSubgroup f) := by
    rw [← two_mul_card_inf_alternatingGroup f hi]
    exact Nat.mul_dvd_mul_left 2 hdvd
  have hne : Nat.card ↥(TauCeti.fiberSubgroup f) ≠ 0 := by
    rw [card_fiberSubgroup f]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
  rw [hk, h2k] at h2dvd ⊢
  rw [← padicValNat_card_fiberSubgroup f]
  exact pow_dvd_pow_padicValNat hne h2dvd

end CFSG.Permutation.SylowTwoNormalizer
