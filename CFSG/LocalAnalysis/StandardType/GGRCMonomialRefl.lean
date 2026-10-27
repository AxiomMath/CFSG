module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

theorem ggRC_monomial_refl_shape {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (r : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r) (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p)
    (hc : ∀ i, c i ≠ 0) (hrb : ∀ i, r (b i) = c i • b (σ i)) :
    (∃ i, σ = 1 ∧ c i = -1 ∧ ∀ j, j ≠ i → c j = 1) ∨
      ∃ i j, i ≠ j ∧ σ = Equiv.swap i j ∧ c i * c j = 1 ∧ ∀ k, k ≠ i → k ≠ j → c k = 1 := by
  classical
  let T : V →ₗ[ZMod p] V := r.toLinearMap - LinearMap.id
  let u : Fin n → V := fun m => T (b m)
  have hr2 : ∀ v : V, r (r v) = v := by
    intro v
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hr.1
    simpa [LinearEquiv.mul_apply] using h
  have hu : ∀ m, u m = c m • b (σ m) - b m := by
    intro m
    change r (b m) - b m = c m • b (σ m) - b m
    rw [hrb m]
  have key : ∀ i, (c i * c (σ i)) • b (σ (σ i)) = b i := by
    intro i
    have h := hr2 (b i)
    rw [hrb i] at h
    rw [map_smul, hrb (σ i), smul_smul] at h
    exact h
  have hcoeff_key : ∀ i, (if σ (σ i) = i then c i * c (σ i) else 0) = 1 := by
    intro i
    have h := congrArg (fun v => b.repr v i) (key i)
    simpa [map_smul, Module.Basis.repr_self_apply, smul_eq_mul, Finsupp.single_apply] using h
  have hσ2 : ∀ i, σ (σ i) = i := by
    intro i
    by_cases hii : σ (σ i) = i
    · exact hii
    · have h := hcoeff_key i
      rw [if_neg hii] at h
      exact absurd h zero_ne_one
  have hcσ : ∀ i, c i * c (σ i) = 1 := by
    intro i
    have h := hcoeff_key i
    rw [if_pos (hσ2 i)] at h
    exact h
  have hfin : Module.finrank (ZMod p) T.range = 1 := hr.2
  have hspan : T.range = Submodule.span (ZMod p) (Set.range u) := by
    rw [LinearMap.range_eq_map, ← Module.Basis.span_eq b, Submodule.map_span]
    congr 1
    exact (Set.range_comp (T : V → V) b).symm
  have hfin_bot : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) V) = 0 :=
    finrank_bot (ZMod p) V
  have hex : ∃ m, u m ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hbot : T.range = ⊥ := by
      rw [hspan, Submodule.span_eq_bot]
      rintro _ ⟨m, rfl⟩
      exact h m
    rw [hbot, hfin_bot] at hfin
    exact zero_ne_one hfin
  obtain ⟨k, hk⟩ := hex
  have hu_mem : ∀ m, u m ∈ T.range := fun m => LinearMap.mem_range.mpr ⟨b m, rfl⟩
  have hsk : T.range = Submodule.span (ZMod p) ({u k} : Set V) := by
    refine eq_span_singleton_of_mem_of_finrank_eq_one (S := T.range) (w := u k) hfin ?_ hk
    exact hu_mem k
  have prop : ∀ m : Fin n, ∃ a : ZMod p, a • u k = u m := by
    intro m
    have hm : u m ∈ Submodule.span (ZMod p) ({u k} : Set V) := by
      rw [← hsk]
      exact hu_mem m
    exact Submodule.mem_span_singleton.mp hm
  have hcoeff_u : ∀ m t, b.repr (u m) t =
      (if σ m = t then c m else 0) - (if m = t then 1 else 0) := by
    intro m t
    have hrepr : b.repr (u m) =
        c m • Finsupp.single (σ m) (1 : ZMod p) - Finsupp.single m 1 := by
      simp only [hu m, map_sub, map_smul, Module.Basis.repr_self]
    rw [hrepr]
    simp [Finsupp.single_apply, smul_eq_mul]
  have hrel_of : ∀ (m t : Fin n) (a : ZMod p), a • u k = u m →
      b.repr (u m) t = a * b.repr (u k) t := by
    intro m t a ha
    have hrepr : b.repr (u m) = a • b.repr (u k) := by
      rw [← ha, map_smul]
    have := congrArg (fun f : Fin n →₀ ZMod p => f t) hrepr
    simpa [smul_eq_mul] using this
  rcases eq_or_ne (σ k) k with hfx | hne
  ·
    have hck_ne : c k ≠ 1 := by
      intro h1
      apply hk
      rw [hu k, hfx, h1]
      simp
    have hck : c k = -1 := by
      have h := hcσ k
      rw [hfx] at h
      have hsq : c k ^ 2 = 1 := by simpa [pow_two] using h
      rcases (sq_eq_one_iff.mp hsq) with h1 | h1
      · exact absurd h1 hck_ne
      · exact h1
    have hσ_apply : ∀ m, σ m = m := by
      intro m
      by_contra hm
      obtain ⟨a, ha⟩ := prop m
      have hrel := hrel_of m (σ m) a ha
      have hL : b.repr (u m) (σ m) = c m := by
        rw [hcoeff_u m (σ m)]
        simp [Ne.symm hm]
      have htk : σ m ≠ k := by
        intro h
        have hmk : m = k := σ.injective (by rw [h, hfx])
        rw [hmk] at hm
        exact hm hfx
      have hR : b.repr (u k) (σ m) = 0 := by
        rw [hcoeff_u k (σ m), hfx]
        simp [Ne.symm htk]
      rw [hL, hR, mul_zero] at hrel
      exact (hc m) hrel
    have hσ_eq_one : σ = 1 := Equiv.ext hσ_apply
    have hcj : ∀ j, j ≠ k → c j = 1 := by
      intro j hjk
      by_contra hcj1
      obtain ⟨a, ha⟩ := prop j
      have hrel := hrel_of j j a ha
      have hL : b.repr (u j) j = c j - 1 := by
        rw [hcoeff_u j j]
        simp [hσ_apply j]
      have hR : b.repr (u k) j = 0 := by
        rw [hcoeff_u k j, hfx]
        simp [Ne.symm hjk]
      rw [hL, hR, mul_zero] at hrel
      exact hcj1 (sub_eq_zero.mp hrel)
    exact Or.inl ⟨k, hσ_eq_one, hck, hcj⟩
  ·
    have hkj : σ (σ k) = k := hσ2 k
    have hfixed : ∀ m, σ m = m → c m = 1 := by
      intro m hfm
      by_contra hcm1
      obtain ⟨a, ha⟩ := prop m
      have hrel := hrel_of m m a ha
      have hmk : m ≠ k := by
        intro h
        rw [h] at hfm
        exact hne hfm
      have hmj : m ≠ σ k := by
        intro h
        have hk' : σ m = k := by rw [h, hkj]
        rw [hfm] at hk'
        exact hmk hk'
      have hL : b.repr (u m) m = c m - 1 := by
        rw [hcoeff_u m m]
        simp [hfm]
      have hR : b.repr (u k) m = 0 := by
        rw [hcoeff_u k m]
        simp [Ne.symm hmk, Ne.symm hmj]
      rw [hL, hR, mul_zero] at hrel
      exact hcm1 (sub_eq_zero.mp hrel)
    have hfix_out : ∀ m, m ≠ k → m ≠ σ k → σ m = m := by
      intro m hmk hmj
      by_contra hσm
      obtain ⟨a, ha⟩ := prop m
      have hrel := hrel_of m (σ m) a ha
      have hL : b.repr (u m) (σ m) = c m := by
        rw [hcoeff_u m (σ m)]
        simp [Ne.symm hσm]
      have ht_k : σ m ≠ k := by
        intro h
        have hmk' : m = σ k := by
          have h2 := congrArg σ h
          rwa [hσ2 m] at h2
        exact hmj hmk'
      have ht_j : σ m ≠ σ k := by
        intro h
        exact hmk (σ.injective h)
      have hR : b.repr (u k) (σ m) = 0 := by
        rw [hcoeff_u k (σ m)]
        simp [Ne.symm ht_j, Ne.symm ht_k]
      rw [hL, hR, mul_zero] at hrel
      exact (hc m) hrel
    have hσ_swap : σ = Equiv.swap k (σ k) := by
      apply Equiv.ext
      intro m
      by_cases hmk : m = k
      · subst hmk
        rw [Equiv.swap_apply_left]
      · by_cases hmj : m = σ k
        · subst hmj
          rw [hσ2 k, Equiv.swap_apply_right]
        · rw [hfix_out m hmk hmj]
          rcases eq_or_ne ((Equiv.swap k (σ k)) m) m with hm | hm
          · exact hm.symm
          · exfalso
            rcases Equiv.eq_or_eq_of_swap_apply_ne_self hm with hk | hj
            · exact hmk hk
            · exact hmj hj
    have hcm : ∀ m, m ≠ k → m ≠ σ k → c m = 1 := by
      intro m hmk hmj
      apply hfixed m
      have h1 : σ m = Equiv.swap k (σ k) m :=
        congrArg (fun e : Equiv.Perm (Fin n) => e m) hσ_swap
      rw [h1]
      by_contra h
      rcases Equiv.eq_or_eq_of_swap_apply_ne_self h with hm | hm
      · exact hmk hm
      · exact hmj hm
    exact Or.inr ⟨k, σ k, hne.symm, hσ_swap, hcσ k, hcm⟩

theorem ggRC_scalar_eq_one_or_neg_one_of_monomial_refl {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin n) (ZMod p) V) (r : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r)
    (d : ZMod p) (hd : d ≠ 0) (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hrb : ∀ i, r (b i) = (d * ε i) • b (σ i)) :
    d = 1 ∨ d = -1 := by
  have hcoeff : ∀ i, d * ε i ≠ 0 := by
    intro i
    rcases hε i with h | h <;> simp [h, hd]
  have hone (i : Fin n) (hi : d * ε i = 1) : d = 1 ∨ d = -1 := by
    rcases hε i with h | h
    · exact Or.inl (by simpa [h] using hi)
    · exact Or.inr (neg_eq_iff_eq_neg.mp (by simpa [h] using hi))
  rcases ggRC_monomial_refl_shape hp2 b r hr σ (fun i => d * ε i) hcoeff hrb with h | h
  · obtain ⟨i, -, -, hfix⟩ := h
    obtain ⟨j, hji, -⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
    exact hone j (hfix j hji)
  · obtain ⟨i, j, -, -, -, hfix⟩ := h
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    exact hone k (hfix k hki hkj)

end CFSG.StandardType

end
