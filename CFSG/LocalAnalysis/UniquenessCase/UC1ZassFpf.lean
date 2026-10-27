module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
public import TauCeti.RepresentationTheory.BaseChange

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open TensorProduct

section General

variable {A : Type*} [CommSemiring A] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module A M]

@[expose] def Fpf (ρ : Representation A G M) : Prop :=
  ∀ g : G, g ≠ 1 → ∀ v : M, ρ g v = v → v = 0

variable {ρ : Representation A G M}

theorem Fpf.sum_pow_apply (hf : Fpf ρ) {g : G} (hg : g ≠ 1) (v : M) :
    ∑ i ∈ Finset.range (orderOf g), ρ (g ^ i) v = 0 := by
  refine hf g hg _ ?_
  have h1 : ρ g (∑ i ∈ Finset.range (orderOf g), ρ (g ^ i) v) =
      ∑ i ∈ Finset.range (orderOf g), ρ (g ^ (i + 1)) v := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', map_mul, Module.End.mul_apply]
  rw [h1]
  have h2 := Finset.sum_range_succ (fun i => ρ (g ^ i) v) (orderOf g)
  have h3 := Finset.sum_range_succ' (fun i => ρ (g ^ i) v) (orderOf g)
  have hn : ρ (g ^ orderOf g) v = ρ (g ^ 0) v := by simp [pow_orderOf_eq_one]
  have h4 := h3.symm.trans h2
  simp only [hn] at h4
  exact add_right_cancel h4

theorem Fpf.apply_eq_neg (hf : Fpf ρ) {g : G} (hg : orderOf g = 2) (v : M) : ρ g v = -v := by
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg
  have h := hf.sum_pow_apply hg1 v
  rw [hg] at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one, map_one, Module.End.one_apply] at h
  exact eq_neg_of_add_eq_zero_right h

theorem Fpf.neg_one (hf : Fpf ρ) {g : G} (hg : orderOf g = 2) : ρ g = -1 :=
  LinearMap.ext fun v => by simpa using hf.apply_eq_neg hg v

theorem Fpf.one_add_add_sq (hf : Fpf ρ) {g : G} (hg : orderOf g = 3) :
    1 + ρ g + ρ g ^ 2 = 0 := by
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg
  refine LinearMap.ext fun v => ?_
  have h := hf.sum_pow_apply hg1 v
  rw [hg] at h
  simpa [Finset.sum_range_succ, pow_two, add_assoc, map_mul] using h

theorem nontrivial_of_injective [Nontrivial G] (hρ : Function.Injective ρ) : Nontrivial M := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (hρ (Subsingleton.elim (ρ g) (ρ 1)))

end General

section BaseChange

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}

theorem Fpf.baseChange (hf : Fpf ρ) (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Fpf (ρ.baseChange K) := by
  intro g hg w hw
  by_contra hw0
  let σ : Representation (ZMod p) (Multiplicative ℕ) V :=
    powersHom (Module.End (ZMod p) V) (ρ g)
  have hfix : ∀ n : Multiplicative ℕ, (σ.baseChange K) n w = w := by
    intro n
    have hw' : (ρ g).baseChange K w = w := by simpa using hw
    rw [Representation.baseChange_apply]
    have hn : σ n = ρ g ^ Multiplicative.toAdd n := by simp [σ]
    rw [hn, LinearMap.baseChange_pow]
    induction Multiplicative.toAdd n with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hw', ih]
  obtain ⟨v, hv0, hv⟩ := Representation.exists_common_fixed_vector_of_baseChange σ hw0 hfix
  refine hv0 (hf g hg v ?_)
  simpa [σ] using hv (Multiplicative.ofAdd 1)

end BaseChange

section PrimeToP

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Finite V] {ρ : Representation (ZMod p) G V}

theorem Fpf.not_dvd_card [Nontrivial V] (hf : Fpf ρ) : ¬ p ∣ Nat.card G := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hA : IsPGroup p (Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hg, pow_one]
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (UC46.fixV_ne_bot_of_pGroup (ρ := ρ) hA)
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg
  exact hv0 (hf g hg1 v (hv g (Subgroup.mem_zpowers g)))

end PrimeToP

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
