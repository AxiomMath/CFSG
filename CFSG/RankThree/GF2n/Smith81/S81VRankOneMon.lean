module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOneExp

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (D : RankOneData K V)

structure Setup (v₀ : V) (k : ℕ) : Prop where
  fix1 : finrank K D.fix = 1
  mem : v₀ ∈ D.fix
  ne0 : v₀ ≠ 0
  sv : D.s v₀ ∉ D.fix
  char : ∀ c : Kˣ, D.a (D.d c) v₀ = (c : K) ^ k • v₀

structure Exp (f : ℕ) where
  hf : Fintype.card K = 2 ^ f
  E : Finset (Fin f) → (V →ₗ[K] V)
  hE : ∀ t : K, (D.X t : V →ₗ[K] V) = ∑ B : Finset (Fin f), t ^ bitSum B • E B
  hE0 : E ∅ = 1
  hprod : ∀ B C, E B * E C = if Disjoint B C then E (B ∪ C) else 0
  hspan : ∀ B, E B ∈ Submodule.span K (Set.range fun t : K => (D.X t : V →ₗ[K] V))

variable {D} {v₀ : V} {k : ℕ} {f : ℕ}

private theorem bitSum_empty_s {f : ℕ} : bitSum (∅ : Finset (Fin f)) = 0 := by
  simp [bitSum]

private theorem bitSum_map_s {f : ℕ} (B : Finset (Fin f)) :
    bitSum B = ∑ k ∈ B.map Fin.valEmbedding, (2 : ℕ) ^ k :=
  (Finset.sum_map B Fin.valEmbedding (fun k : ℕ => (2 : ℕ) ^ k)).symm

private theorem bitSum_inj_s {f : ℕ} : Function.Injective (bitSum (f := f)) := by
  intro B C h
  rw [bitSum_map_s, bitSum_map_s] at h
  exact Finset.map_injective Fin.valEmbedding (Finset.geomSum_injective le_rfl h)

private theorem bitSum_lt_s {f : ℕ} (B : Finset (Fin f)) : bitSum B < 2 ^ f := by
  rw [bitSum_map_s]
  refine Nat.geomSum_lt (by norm_num) ?_
  intro k hk
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.1 hk
  exact r.isLt

private theorem bitSum_pos_s {f : ℕ} {B : Finset (Fin f)} (hB : B.Nonempty) : 1 ≤ bitSum B := by
  obtain ⟨r, hr⟩ := hB
  have h1 : 2 ^ (r : ℕ) ≤ ∑ x ∈ B, 2 ^ (x : ℕ) :=
    Finset.single_le_sum (f := fun x : Fin f => (2 : ℕ) ^ (x : ℕ)) (fun i _ => Nat.zero_le _) hr
  have h2 : 1 ≤ 2 ^ (r : ℕ) := Nat.one_le_two_pow
  have h3 : bitSum B = ∑ x ∈ B, 2 ^ (x : ℕ) := rfl
  omega

private theorem eq_of_mod_eq_of_bounds {x y n : ℕ} (hx1 : 1 ≤ x) (hxn : x ≤ n) (hy1 : 1 ≤ y)
    (hyn : y ≤ n) (hxy : x % n = y % n) : x = y := by
  rcases Nat.lt_or_ge x n with h1 | h1 <;> rcases Nat.lt_or_ge y n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hxy
    exact hxy
  · have hy : y = n := by omega
    rw [Nat.mod_eq_of_lt h1, hy, Nat.mod_self] at hxy
    omega
  · have hx : x = n := by omega
    rw [Nat.mod_eq_of_lt h2, hx, Nat.mod_self] at hxy
    omega
  · omega

private theorem exists_max_above {f : ℕ} (E : Finset (Fin f) → V →ₗ[K] V) (v : V)
    (B : Finset (Fin f)) (hB : E B v ≠ 0) :
    ∃ C, B ⊆ C ∧ E C v ≠ 0 ∧ ∀ D', C ⊂ D' → E D' v = 0 := by
  classical
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Finset (Fin f) => B ⊆ C ∧ E C v ≠ 0) Finset.card
    ⟨B, by simp [hB]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
  refine ⟨C, hC.1, hC.2, fun D' hD' => ?_⟩
  by_contra hne
  have hmem : D' ∈ Finset.univ.filter fun C : Finset (Fin f) => B ⊆ C ∧ E C v ≠ 0 := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hC.1.trans hD'.1, hne⟩
  have h1 := hmax D' hmem
  have h2 := Finset.card_lt_card hD'
  omega

theorem Exp.down (X : D.Exp f) {B C : Finset (Fin f)} (hBC : B ⊆ C) (hC : X.E C (D.s v₀) ≠ 0) :
    X.E B (D.s v₀) ≠ 0 := by
  intro hB
  apply hC
  have hsplit : X.E C = X.E (C \ B) * X.E B := by
    rw [X.hprod (C \ B) B, if_pos Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hBC]
  rw [hsplit, Module.End.mul_apply, hB, map_zero]

theorem Exp.maximal_fix [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k)
    {B : Finset (Fin f)} (hB : X.E B (D.s v₀) ≠ 0)
    (hmax : ∀ C, B ⊂ C → X.E C (D.s v₀) = 0) : X.E B (D.s v₀) ∈ D.fix := by
  have hzS : X.E B (D.s v₀) ∈ D.S v₀ := D.E_apply_mem_S X.hspan B
  have hCz : ∀ C : Finset (Fin f), C ≠ ∅ → X.E C (X.E B (D.s v₀)) = 0 := by
    intro C hCne
    rw [← Module.End.mul_apply, X.hprod C B]
    by_cases hdisj : Disjoint C B
    · rw [if_pos hdisj]
      have hlt : B ⊂ C ∪ B := by
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hCne
        exact (Finset.ssubset_iff_of_subset Finset.subset_union_right).2
          ⟨x, Finset.mem_union_left B hx, Finset.disjoint_left.1 hdisj hx⟩
      exact hmax (C ∪ B) hlt
    · rw [if_neg hdisj, LinearMap.zero_apply]
  have hE0' : X.E ∅ (X.E B (D.s v₀)) = X.E B (D.s v₀) := by
    rw [X.hE0, Module.End.one_apply]
  have hX : ∀ t : K, D.X t (X.E B (D.s v₀)) = X.E B (D.s v₀) := by
    intro t
    have h1 : (D.X t : V →ₗ[K] V) (X.E B (D.s v₀)) =
        ∑ C : Finset (Fin f), t ^ bitSum C • X.E C (X.E B (D.s v₀)) := by
      rw [X.hE t, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    have h2 : ∑ C : Finset (Fin f), t ^ bitSum C • X.E C (X.E B (D.s v₀)) =
        t ^ bitSum (∅ : Finset (Fin f)) • X.E ∅ (X.E B (D.s v₀)) :=
      Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) fun C _ hC => by
        rw [hCz C hC, smul_zero]
    rw [h2, bitSum_empty_s, pow_zero, one_smul, hE0'] at h1
    exact h1
  exact D.mem_fix_of_X_fixed h.fix1 h.mem h.ne0 hzS hX

theorem Exp.maximal_mod [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k)
    {B : Finset (Fin f)} (hB : X.E B (D.s v₀) ≠ 0) (hz : X.E B (D.s v₀) ∈ D.fix) :
    bitSum B % (Fintype.card K - 1) = k % (Fintype.card K - 1) := by
  obtain ⟨c0, hc0⟩ : ∃ c0 : K, c0 • v₀ = X.E B (D.s v₀) := by
    have hv : (⟨v₀, h.mem⟩ : D.fix) ≠ 0 := fun h' => h.ne0 (congrArg Subtype.val h')
    obtain ⟨c0, hc0⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 h.fix1 ⟨_, hz⟩
    exact ⟨c0, congrArg Subtype.val hc0⟩
  have hkey : ∀ c : Kˣ, (c : K) ^ (2 * bitSum B) * ((c⁻¹ : Kˣ) : K) ^ k = (c : K) ^ k := by
    intro c
    have e1 := D.torus_eigen_E X.hf X.hE h.char c B
    have e2 : D.a (D.d c) (X.E B (D.s v₀)) = ((c : K) ^ k) • X.E B (D.s v₀) := by
      rw [← hc0, map_smul, h.char c, smul_smul, smul_smul, mul_comm]
    have h3 : (((c : K) ^ (2 * bitSum B)) * ((c⁻¹ : Kˣ) : K) ^ k - (c : K) ^ k) •
        X.E B (D.s v₀) = 0 := by
      rw [sub_smul, ← e1, e2, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hB
  have hpow : ∀ c : Kˣ, (c : K) ^ (2 * bitSum B) = (c : K) ^ (2 * k) := by
    intro c
    have hc : (c : K) ≠ 0 := c.ne_zero
    have hk := hkey c
    rw [Units.val_inv_eq_inv_val] at hk
    calc (c : K) ^ (2 * bitSum B)
        = (c : K) ^ (2 * bitSum B) * (((c : K)⁻¹) ^ k * (c : K) ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hc, one_pow, mul_one]
      _ = ((c : K) ^ (2 * bitSum B) * ((c : K)⁻¹) ^ k) * (c : K) ^ k := by ring
      _ = (c : K) ^ k * (c : K) ^ k := by rw [hk]
      _ = (c : K) ^ (2 * k) := by rw [← pow_add, two_mul]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Fintype.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card]
  have hgpow : g ^ (2 * bitSum B) = g ^ (2 * k) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact hpow g)
  have hmod2 : 2 * bitSum B ≡ 2 * k [MOD Fintype.card K - 1] := by
    rw [← hord]
    exact pow_eq_pow_iff_modEq.1 hgpow
  have hcard1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hodd : Odd (Fintype.card K - 1) := by
    have hf1 : f ≠ 0 := by
      rintro rfl
      have := X.hf
      simp at this
      omega
    obtain ⟨j, hj⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
    have h2 : Fintype.card K = 2 * 2 ^ j := by
      rw [X.hf, hj, pow_succ]
      ring
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    exact ⟨2 ^ j - 1, by omega⟩
  have hcop : Nat.gcd (Fintype.card K - 1) 2 = 1 :=
    Nat.Coprime.symm (Nat.coprime_two_left.2 hodd)
  exact Nat.ModEq.cancel_left_of_coprime hcop hmod2

theorem Exp.exists_nonempty [FiniteDimensional K V] (X : D.Exp f) (h : D.Setup v₀ k) :
    ∃ B : Finset (Fin f), B.Nonempty ∧ X.E B (D.s v₀) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hX : ∀ t : K, D.X t (D.s v₀) = D.s v₀ := by
    intro t
    have h1 : (D.X t : V →ₗ[K] V) (D.s v₀) =
        ∑ C : Finset (Fin f), t ^ bitSum C • X.E C (D.s v₀) := by
      rw [X.hE t, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    have h2 : ∑ C : Finset (Fin f), t ^ bitSum C • X.E C (D.s v₀) =
        t ^ bitSum (∅ : Finset (Fin f)) • X.E ∅ (D.s v₀) :=
      Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) fun C _ hC => by
        rw [hcon C (Finset.nonempty_iff_ne_empty.2 hC), smul_zero]
    rw [h2, bitSum_empty_s, pow_zero, one_smul, X.hE0, Module.End.one_apply] at h1
    exact h1
  have hzS : D.s v₀ ∈ D.S v₀ := by
    have h0 : X.E ∅ (D.s v₀) ∈ D.S v₀ := D.E_apply_mem_S X.hspan ∅
    rwa [X.hE0, Module.End.one_apply] at h0
  exact h.sv (D.mem_fix_of_X_fixed h.fix1 h.mem h.ne0 hzS hX)

theorem Exp.monomial_structure [FiniteDimensional K V] (hf2 : 2 ≤ f) (X : D.Exp f) (h : D.Setup v₀ k) :
    ∃ B' : Finset (Fin f), B'.Nonempty ∧ (∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') ∧
      X.E B' (D.s v₀) ∈ D.fix ∧ X.E B' (D.s v₀) ≠ 0 ∧
      bitSum B' % (Fintype.card K - 1) = k % (Fintype.card K - 1) := by
  clear hf2
  obtain ⟨B0, hB0ne, hB0⟩ := X.exists_nonempty h
  obtain ⟨B', hB0B', hB'ne, hB'max⟩ := exists_max_above X.E (D.s v₀) B0 hB0
  have hB'nonempty : B'.Nonempty := hB0ne.mono hB0B'
  have hB'fix : X.E B' (D.s v₀) ∈ D.fix := X.maximal_fix h hB'ne hB'max
  have hB'mod := X.maximal_mod h hB'ne hB'fix
  have huniq : ∀ C : Finset (Fin f), X.E C (D.s v₀) ≠ 0 →
      (∀ D', C ⊂ D' → X.E D' (D.s v₀) = 0) → C = B' := by
    intro C hCne hCmax
    have hCnon : C.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hC0
      subst hC0
      exact hB0 (hCmax B0 (Finset.empty_ssubset.2 hB0ne))
    have hCmod := X.maximal_mod h hCne (X.maximal_fix h hCne hCmax)
    have hbitC := bitSum_lt_s C
    have hbitB := bitSum_lt_s B'
    have hpC := bitSum_pos_s hCnon
    have hpB := bitSum_pos_s hB'nonempty
    have hcard : Fintype.card K = 2 ^ f := X.hf
    apply bitSum_inj_s
    exact eq_of_mod_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
      (hCmod.trans hB'mod.symm)
  refine ⟨B', hB'nonempty, fun B => ⟨fun hB => ?_, fun hBB' => X.down hBB' hB'ne⟩, hB'fix, hB'ne,
    hB'mod⟩
  obtain ⟨C, hBC, hCne, hCmax⟩ := exists_max_above X.E (D.s v₀) B hB
  rw [huniq C hCne hCmax] at hBC
  exact hBC

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
