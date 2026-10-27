module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Nat.Prime.Basic
import CFSG.LocalAnalysis.StandardType.KGLangH90
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType

theorem kgLangH90_pPart {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] (β : MulAut G)
    {N : Subgroup G} (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hβN : ∀ g, β g ∈ N ↔ g ∈ N)
    (hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 → ∃ s ∈ N, c = s⁻¹ * β s)
    {c : G} (hc : c ∈ N) (hcp : ∃ k : ℕ, c ^ p ^ k = 1)
    (hcn : ((List.range p).map fun i => (β ^ i) c).prod = 1) :
    ∃ s ∈ N, (∃ k : ℕ, s ^ p ^ k = 1) ∧ c = s⁻¹ * β s := by
  obtain ⟨s, hsN, hs⟩ := hH90 c hc hcn
  have hn : Nat.card N ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcopm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
  have hcop : Nat.Coprime m (p ^ a) := hcopm.symm.pow_right a
  have hcpa : c ^ p ^ a = 1 := by
    obtain ⟨k, hk⟩ := hcp
    have h1 : orderOf c ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp).mp h1
    have h2 : orderOf c ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hc
    rw [hnm, hr] at h2
    have h3 : p ^ r ∣ p ^ a := (hcopm.pow_left r).dvd_of_dvd_mul_right h2
    exact orderOf_dvd_iff_pow_eq_one.mp (by rwa [hr])
  have ht_exists : ∃ t, m * t ≡ 1 [MOD p ^ a] := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; exact ⟨0, by simp [Nat.ModEq]⟩
    · have hlt : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
      obtain ⟨t, _, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
      exact ⟨t, by rw [Nat.ModEq, ht, Nat.mod_eq_of_lt hlt]⟩
  obtain ⟨t, hmt⟩ := ht_exists
  have hsn : s ^ Nat.card N = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard N hsN)
  refine ⟨s ^ (m * t), N.pow_mem hsN _, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul]
    have harith : m * t * p ^ a = t * (p ^ a * m) := by
      rw [mul_comm m t, mul_assoc t m (p ^ a), mul_comm m (p ^ a)]
    rw [harith, ← hnm, mul_comm t (Nat.card N), pow_mul, hsn, one_pow]
  · have hfix : c ^ (m * t) = c := by
      rw [pow_eq_pow_of_modEq hmt hcpa, pow_one]
    rw [← hfix, hs]
    have hcomm : Commute s (β s) := hab s hsN (β s) ((hβN s).mpr hsN)
    rw [hcomm.inv_left.mul_pow, inv_pow, map_pow]

theorem kgLangDatum_of_pow {p j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) {K : Type} [Group K] [Finite K]
    {α₀ : MulAut K} (hα₀p : α₀ ^ p = 1) (A₀ : Set (MulAut K)) (M : Subgroup K)
    (hab : ∀ a ∈ M, ∀ c ∈ M, a * c = c * a) (hst : ∀ t, (α₀ ^ j) t ∈ M ↔ t ∈ M)
    (hfix : ∀ α ∈ A₀, ∀ t ∈ M, α t = t)
    (h90 : ∀ c ∈ M, ((List.range p).map fun i => ((α₀ ^ j) ^ i) c).prod = 1 →
      ∃ s ∈ M, c = s⁻¹ * (α₀ ^ j) s)
    (e : K) (he : e ∈ M) (he1 : e ≠ 1) (hep : e ^ p = 1) (heα : (α₀ ^ j) e = e) :
    (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧ (∀ α ∈ A₀, ∀ t ∈ M, α t = t) ∧
      (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
      e ∈ M ∧ e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e := by
  have hcop : Nat.Coprime j p := (hp.coprime_iff_not_dvd.mpr hj).symm
  obtain ⟨j', _, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hα₀eq : α₀ = (α₀ ^ j) ^ j' := by
    rw [← pow_mul]
    have hdecomp : j * j' = p * (j * j' / p) + 1 := by
      rw [← hj']
      exact (Nat.div_add_mod (j * j') p).symm
    rw [hdecomp, pow_add, pow_mul, hα₀p, one_pow, one_mul, pow_one]
  have hstα : ∀ t, α₀ t ∈ M ↔ t ∈ M := by
    intro t
    rw [hα₀eq]
    have hgen : ∀ n (x : K), ((α₀ ^ j) ^ n) x ∈ M ↔ x ∈ M := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih => intro x; rw [pow_succ, MulAut.mul_apply, ih, hst]
    exact hgen j' t
  letI : CommGroup M := CommGroup.mk fun a b => Subtype.ext (hab a a.2 b b.2)
  let βM : MulAut M :=
    { toFun t := ⟨α₀ (t : K), (hstα (t : K)).mpr t.2⟩
      invFun t := ⟨α₀⁻¹ (t : K), (hstα (α₀⁻¹ (t : K))).mp (by
        rw [MulAut.apply_inv_self]; exact t.2)⟩
      left_inv t := Subtype.ext (by simp)
      right_inv t := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (map_mul α₀ (a : K) (b : K)) }
  have hpow_coe : ∀ (n : ℕ) (x : M), ((βM ^ n) x : K) = (α₀ ^ n) (x : K) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
        rfl
  have hpow_coe' : ∀ (n i : ℕ) (x : M), (((βM ^ n) ^ i) x : K) = ((α₀ ^ n) ^ i) (x : K) := by
    intro n i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply, hpow_coe]
  have hβp : βM ^ p = 1 := by
    ext x
    simp only [hpow_coe, hα₀p, MulAut.one_apply]
  have hcoe_norm : ∀ (n : ℕ) (x : M),
      ((List.range p).map fun i => ((βM ^ n) ^ i) x).prod = 1 →
      ((List.range p).map fun i => ((α₀ ^ n) ^ i) (x : K)).prod = 1 := by
    intro n x hx
    have h := congrArg (fun y : M => (y : K)) hx
    rw [Subgroup.val_list_prod] at h
    have hmap : (List.map (fun y : M => (y : K))
        (List.map (fun i => ((βM ^ n) ^ i) x) (List.range p)))
        = List.map (fun i => ((α₀ ^ n) ^ i) (x : K)) (List.range p) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hpow_coe' n i x
    rw [hmap] at h
    simpa using h
  have h90M : ∀ c : M, ((List.range p).map fun i => ((βM ^ j) ^ i) c).prod = 1 →
      ∃ s : M, c = s⁻¹ * (βM ^ j) s := by
    intro c hc
    obtain ⟨s, hsM, hs⟩ := h90 (c : K) c.2 (hcoe_norm j c hc)
    refine ⟨⟨s, hsM⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hpow_coe]
    exact hs
  have hH90β : ∀ c : M, ((List.range p).map fun i => (βM ^ i) c).prod = 1 →
      ∃ s : M, c = s⁻¹ * βM s := (kgLangH90_pow_iff hp hj βM hβp).mpr h90M
  refine ⟨hstα, hfix, ?_, he, he1, hep, ?_⟩
  · intro c hcM hcn
    have hcnM : ((List.range p).map fun i => (βM ^ i) ⟨c, hcM⟩).prod = 1 := by
      apply Subtype.ext
      rw [Subgroup.val_list_prod]
      have hmap : (List.map (fun y : M => (y : K))
          (List.map (fun i => (βM ^ i) ⟨c, hcM⟩) (List.range p)))
          = List.map (fun i => (α₀ ^ i) c) (List.range p) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hpow_coe i ⟨c, hcM⟩
      rw [hmap]
      simpa using hcn
    obtain ⟨s, hs⟩ := hH90β ⟨c, hcM⟩ hcnM
    refine ⟨(s : K), s.2, ?_⟩
    have h := congrArg (fun y : M => (y : K)) hs
    have hbs : ((βM s : M) : K) = α₀ (s : K) := by
      simpa using hpow_coe 1 s
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hbs] at h
    simpa using h
  · rw [hα₀eq]
    have hgen : ∀ n, ((α₀ ^ j) ^ n) e = e := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, MulAut.mul_apply, heα, ih]
    exact hgen j'

end CFSG.StandardType
