module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.ModEq

public section

namespace CFSG.StandardType

namespace OrdPNsOm

open QuadraticMap

section Chi

variable (K : Type) [Field K] [CharP K 2]

@[expose] def wp : K →+ K where
  toFun t := t ^ 2 + t
  map_zero' := by ring
  map_add' a b := by
    change (a + b) ^ 2 + (a + b) = (a ^ 2 + a) + (b ^ 2 + b)
    rw [CharTwo.add_sq]
    ring

variable {K}

theorem wp_apply (t : K) : wp K t = t ^ 2 + t := rfl

theorem mem_ker_wp {t : K} : t ∈ (wp K).ker ↔ t = 0 ∨ t = 1 := by
  rw [AddMonoidHom.mem_ker, wp_apply]
  constructor
  · intro h
    have h1 : t * (t + 1) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have h2 := eq_neg_of_add_eq_zero_left h0
      rwa [CharTwo.neg_eq] at h2
  · rintro (rfl | rfl)
    · ring
    · rw [one_pow]
      exact CharTwo.add_self_eq_zero 1

theorem card_ker_wp : Nat.card (wp K).ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨0, (wp K).ker.zero_mem⟩, ⟨1, mem_ker_wp.mpr (Or.inr rfl)⟩,
    fun h => zero_ne_one (congrArg Subtype.val h), ?_⟩
  ext ⟨t, ht⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
  exact mem_ker_wp.mp ht

open Classical in
@[expose] noncomputable def chi (a : K) : ℤ := if a ∈ (wp K).range then 1 else -1

theorem chi_of_mem {a : K} (h : a ∈ (wp K).range) : chi a = 1 := by
  simp [chi, h]

theorem chi_of_not_mem {a : K} (h : a ∉ (wp K).range) : chi a = -1 := by
  simp [chi, h]

theorem chi_zero : chi (0 : K) = 1 := chi_of_mem (wp K).range.zero_mem

theorem chi_eq_one_or (a : K) : chi a = 1 ∨ chi a = -1 := by
  by_cases h : a ∈ (wp K).range
  · exact Or.inl (chi_of_mem h)
  · exact Or.inr (chi_of_not_mem h)

variable [Finite K]

theorem index_range_wp : (wp K).range.index = 2 := by
  rw [AddSubgroup.index_range, card_ker_wp]

theorem exists_not_mem_range_wp : ∃ c : K, c ∉ (wp K).range := by
  by_contra h
  push Not at h
  have h1 : (wp K).range = ⊤ := eq_top_iff.mpr fun c _ => h c
  have h2 := index_range_wp (K := K)
  rw [h1, AddSubgroup.index_top] at h2
  exact absurd h2 (by norm_num)

theorem chi_add (a b : K) : chi (a + b) = chi a * chi b := by
  have h := AddSubgroup.add_mem_iff_of_index_two (index_range_wp (K := K)) (a := a) (b := b)
  by_cases ha : a ∈ (wp K).range <;> by_cases hb : b ∈ (wp K).range
  · rw [chi_of_mem ha, chi_of_mem hb, chi_of_mem (h.mpr (iff_of_true ha hb)), one_mul]
  · rw [chi_of_mem ha, chi_of_not_mem hb, chi_of_not_mem fun h' => hb ((h.mp h').mp ha), one_mul]
  · rw [chi_of_not_mem ha, chi_of_mem hb, chi_of_not_mem fun h' => ha ((h.mp h').mpr hb),
      mul_one]
  · rw [chi_of_not_mem ha, chi_of_not_mem hb, chi_of_mem (h.mpr (iff_of_false ha hb))]
    norm_num

theorem sum_chi [Fintype K] : ∑ t : K, chi t = 0 := by
  obtain ⟨c, hc⟩ := exists_not_mem_range_wp (K := K)
  have h1 : ∑ t : K, chi (t + c) = ∑ t : K, chi t :=
    Fintype.sum_equiv (Equiv.addRight c) _ _ fun t => rfl
  have h2 : ∑ t : K, chi (t + c) = -∑ t : K, chi t := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [chi_add, chi_of_not_mem hc]
    ring
  linarith

theorem sum_chi_sq_mul [Fintype K] {r : K} (hr : r ≠ 0) : ∑ y : K, chi (y ^ 2 * r) = 0 := by
  have hinj : Function.Injective fun y : K => y ^ 2 * r := by
    intro y y' h
    have h1 : y ^ 2 = y' ^ 2 := mul_right_cancel₀ hr h
    exact frobenius_inj K 2 h1
  rw [Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj) _ chi fun y => rfl]
  exact sum_chi

theorem sum_compl_chi_sq_mul [Fintype K] [DecidableEq K] {r : K} (hr : r ≠ 0) :
    ∑ y ∈ ({0} : Finset K)ᶜ, chi (y ^ 2 * r) = -1 := by
  have h := sum_chi_sq_mul (K := K) hr
  rw [Fintype.sum_eq_add_sum_compl 0] at h
  rw [show (0 : K) ^ 2 * r = 0 by ring, chi_zero] at h
  linarith

end Chi

section Sum

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

variable (Q) in
@[expose] noncomputable def charSum (U : Submodule K V) : ℤ :=
  ∑ᶠ v : U, chi (Q v)

omit [Finite K] in
theorem charSum_eq (U : Submodule K V) [Fintype U] :
    charSum Q U = ∑ v : U, chi (Q (v : V)) :=
  finsum_eq_sum_of_fintype _

omit [CharP K 2] [Finite K] in
theorem quad_smul_add_smul (a b : V) (x y : K) :
    Q (x • a + y • b) = x ^ 2 * Q a + y ^ 2 * Q b + x * y * polar Q a b := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right]
  simp only [smul_eq_mul]
  ring

variable [Finite V]

theorem charSum_sup {U₁ U₂ : Submodule K V} (hd : U₁ ⊓ U₂ = ⊥)
    (ho : ∀ a ∈ U₁, ∀ b ∈ U₂, polar Q a b = 0) :
    charSum Q (U₁ ⊔ U₂) = charSum Q U₁ * charSum Q U₂ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set e : U₁ × U₂ → ↥(U₁ ⊔ U₂) := fun x => ⟨x.1 + x.2, Submodule.add_mem_sup x.1.2 x.2.2⟩
    with he
  have hbij : Function.Bijective e := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : V) + b = a' + b' := congrArg Subtype.val h
      have h2 : (a : V) - a' ∈ U₁ ⊓ U₂ := by
        refine ⟨U₁.sub_mem a.2 a'.2, ?_⟩
        have h3 : (a : V) - a' = b' - b := by
          rw [sub_eq_sub_iff_add_eq_add, h1]
          exact add_comm _ _
        rw [h3]
        exact U₂.sub_mem b'.2 b.2
      rw [hd, Submodule.mem_bot, sub_eq_zero] at h2
      have h4 : (b : V) = b' := by
        rw [h2] at h1
        exact add_left_cancel h1
      exact Prod.ext (Subtype.ext h2) (Subtype.ext h4)
    · rintro ⟨v, hv⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [charSum_eq, charSum_eq, charSum_eq,
    ← Fintype.sum_bijective e hbij (fun x => chi (Q ((x.1 : V) + x.2)))
      (fun v : ↥(U₁ ⊔ U₂) => chi (Q (v : V))) fun x => rfl,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [QuadraticMap.map_add Q, ho a a.2 b b.2, add_zero, chi_add]

omit [Finite K] in
theorem charSum_pair [Fintype K] {a b : V} (hab : LinearIndependent K ![a, b]) :
    charSum Q (Submodule.span K {a, b}) = ∑ x : K, ∑ y : K, chi (Q (x • a + y • b)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set e : K × K → ↥(Submodule.span K {a, b}) := fun x =>
    ⟨x.1 • a + x.2 • b, Submodule.mem_span_pair.mpr ⟨x.1, x.2, rfl⟩⟩ with he
  have hbij : Function.Bijective e := by
    constructor
    · rintro ⟨x, y⟩ ⟨x', y'⟩ h
      have h1 : x • a + y • b = x' • a + y' • b := congrArg Subtype.val h
      have h2 : (x - x') • a + (y - y') • b = 0 := by
        rw [sub_smul, sub_smul]
        rw [← sub_eq_zero] at h1
        rw [← h1]
        abel
      obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.mp hab _ _ h2
      exact Prod.ext (sub_eq_zero.mp h3) (sub_eq_zero.mp h4)
    · rintro ⟨v, hv⟩
      obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hv
      exact ⟨(x, y), rfl⟩
  rw [charSum_eq, ← Fintype.sum_bijective e hbij (fun x => chi (Q (x.1 • a + x.2 • b)))
    (fun v : ↥(Submodule.span K {a, b}) => chi (Q (v : V))) fun x => rfl,
    Fintype.sum_prod_type]

theorem charSum_hyp {e f : V} (hef : LinearIndependent K ![e, f]) (he : Q e = 0) (hf : Q f = 0)
    (hpol : polar Q e f = 1) : charSum Q (Submodule.span K {e, f}) = Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [charSum_pair hef]
  simp only [quad_smul_add_smul, he, hf, hpol, mul_zero, zero_add, mul_one]
  rw [Fintype.sum_eq_add_sum_compl 0]
  have h0 : ∀ x ∈ ({0} : Finset K)ᶜ, ∑ y : K, chi (x * y) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [Fintype.sum_bijective (x * ·) (mulLeft_bijective₀ x hx0) _ chi fun y => rfl]
    exact sum_chi
  rw [Finset.sum_eq_zero h0, add_zero, Nat.card_eq_fintype_card]
  simp [chi_zero]

theorem charSum_aniso {a b : V} (hab : LinearIndependent K ![a, b]) (ha : Q a = 1) {c₀ : K}
    (hb : Q b = c₀) (hc₀ : c₀ ∉ (wp K).range) (hpol : polar Q a b = 1) :
    charSum Q (Submodule.span K {a, b}) = -Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [charSum_pair hab, Finset.sum_comm]
  simp only [quad_smul_add_smul, ha, hb, hpol, mul_one]
  rw [Fintype.sum_eq_add_sum_compl 0]
  have hz : ∑ x : K, chi (x ^ 2 + (0 : K) ^ 2 * c₀ + x * 0) = 0 := by
    have h := sum_chi_sq_mul (K := K) one_ne_zero
    simpa using h
  have hy : ∀ y ∈ ({0} : Finset K)ᶜ, ∑ x : K, chi (x ^ 2 + y ^ 2 * c₀ + x * y) =
      ∑ t : K, chi (y ^ 2 * (t ^ 2 + t + c₀)) := by
    intro y hy
    have hy0 : y ≠ 0 := by simpa using hy
    rw [← Fintype.sum_bijective (· * y) (mulRight_bijective₀ y hy0)
      (fun t => chi ((t * y) ^ 2 + y ^ 2 * c₀ + t * y * y))
      (fun x => chi (x ^ 2 + y ^ 2 * c₀ + x * y)) fun t => rfl]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hr : ∀ t : K, t ^ 2 + t + c₀ ≠ 0 := by
    intro t h0
    apply hc₀
    refine ⟨t, ?_⟩
    rw [wp_apply]
    have h1 := eq_neg_of_add_eq_zero_right h0
    rw [CharTwo.neg_eq] at h1
    exact h1.symm
  rw [hz, zero_add, Finset.sum_congr rfl hy, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t _ => sum_compl_chi_sq_mul (hr t)]
  simp [Nat.card_eq_fintype_card]

omit [Finite K] in
theorem charSum_modEq {p : ℕ} [Fact p.Prime] {U : Submodule K V} {y : V →ₗ[K] V}
    (hyU : ∀ u ∈ U, y u ∈ U) (hyQ : ∀ v, Q (y v) = Q v) (hyp : y ^ p = 1)
    (hfix : ∀ u ∈ U, y u = u → u = 0) : charSum Q U ≡ 1 [ZMOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have key : ∀ s : ℤ, Fintype.card {u : U // chi (Q (u : V)) = s} ≡
      Fintype.card {u : {u : U // chi (Q (u : V)) = s} // (u.1 : V) = 0} [MOD p] := by
    intro s
    set f : Function.End {u : U // chi (Q (u : V)) = s} := fun u =>
      ⟨⟨y u.1, hyU _ u.1.2⟩, by rw [hyQ]; exact u.2⟩ with hf
    have hiter : ∀ (k : ℕ) (u : {u : U // chi (Q (u : V)) = s}),
        ((f^[k] u).1 : V) = (y ^ k) (u.1 : V) := by
      intro k
      induction k with
      | zero => intro u; rfl
      | succ k ih =>
        intro u
        rw [Function.iterate_succ_apply, ih, pow_succ, Module.End.mul_apply]
    have hfp : f ^ p ^ 1 = 1 := by
      funext u
      change f^[p ^ 1] u = u
      refine Subtype.ext (Subtype.ext ?_)
      rw [hiter, pow_one, hyp, Module.End.one_apply]
    have h1 := Equiv.Perm.card_fixedPoints_modEq hfp
    have h2 : Fintype.card (Function.fixedPoints f) =
        Fintype.card {u : {u : U // chi (Q (u : V)) = s} // (u.1 : V) = 0} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun u => ?_)
      constructor
      · intro hu
        have h3 : y (u.1 : V) = u.1 := congrArg (fun w => ((w.1 : U) : V)) hu
        exact hfix _ u.1.2 h3
      · intro hu
        refine Subtype.ext (Subtype.ext ?_)
        change y (u.1 : V) = u.1
        rw [hu, map_zero]
    rw [h2] at h1
    exact h1
  have hc1 : Fintype.card {u : {u : U // chi (Q (u : V)) = 1} // (u.1 : V) = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, by rw [ZeroMemClass.coe_zero, QuadraticMap.map_zero, chi_zero]⟩, rfl⟩, ?_⟩
    rintro ⟨⟨u, hu⟩, hu0⟩
    exact Subtype.ext (Subtype.ext (Subtype.ext hu0))
  have hc2 : Fintype.card {u : {u : U // chi (Q (u : V)) = -1} // (u.1 : V) = 0} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨⟨u, hu⟩, hu0⟩ => ?_⟩
    have h0 : (u : V) = 0 := hu0
    rw [h0, QuadraticMap.map_zero, chi_zero] at hu
    norm_num at hu
  have hsum : charSum Q U = (Fintype.card {u : U // chi (Q (u : V)) = 1} : ℤ) -
      Fintype.card {u : U // chi (Q (u : V)) = -1} := by
    rw [charSum_eq]
    have h1 : ∀ u : U, chi (Q (u : V)) = (if chi (Q (u : V)) = 1 then 1 else 0) -
        (if chi (Q (u : V)) = -1 then 1 else 0) := by
      intro u
      rcases chi_eq_one_or (Q (u : V)) with h | h <;> simp [h]
    rw [Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_boole, Fintype.card_subtype, Fintype.card_subtype]
  have k1 := key 1
  have k2 := key (-1)
  rw [hc1] at k1
  rw [hc2] at k2
  have k1' : (Fintype.card {u : U // chi (Q (u : V)) = 1} : ℤ) ≡ 1 [ZMOD p] := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr k1)
  have k2' : (Fintype.card {u : U // chi (Q (u : V)) = -1} : ℤ) ≡ 0 [ZMOD p] := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr k2)
  rw [hsum]
  simpa using k1'.sub k2'

end Sum

end OrdPNsOm

end CFSG.StandardType
