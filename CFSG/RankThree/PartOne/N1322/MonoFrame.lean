module

public import CFSG.RankThree.PartOne.N1322.MonoRefl
public import CFSG.RankThree.PartOne.N1322.CoreData

public section

namespace CFSG.RankThree.PartOne.N1322

open Matrix Equiv

variable {K : Type*} [Field K]

theorem mono_mulVec_apply (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) (c : Fin 3 → K) (j : Fin 3) :
    (((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ c) (σ j) = a j * c j := by
  simp only [Matrix.mulVec, dotProduct, mono_val, monoMat_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro m _ hm
    have : σ j ≠ σ m := fun h => hm (σ.injective h).symm
    simp [this]
  · simp

theorem single_eq_smul (k : Fin 3) (x : K) :
    (Pi.single k x : Fin 3 → K) = x • Pi.single k 1 := by
  ext m
  by_cases h : m = k <;> simp [h]

structure MonoStd (X : Subgroup (GL (Fin 3) K)) : Prop where
  isMono : ∀ x ∈ X, ∃ σ a, x = mono σ a
  trans : ∀ i j : Fin 3, ∃ x ∈ X, ∃ σ a, x = mono σ a ∧ σ i = j

theorem MonoStd.conj {X : Subgroup (GL (Fin 3) K)} (h : MonoStd X) (τ : Perm (Fin 3))
    (b : Fin 3 → Kˣ) : MonoStd (X.map (cj (mono τ b : GL (Fin 3) K)).toMonoidHom) := by
  have hP : ∀ (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ), HasPerm ((mono τ b : GL (Fin 3) K) *
      mono σ a * (mono τ b)⁻¹) (τ * σ * τ⁻¹) := fun σ a =>
    ((hasPerm_mono τ b).mul (hasPerm_mono σ a)).mul (hasPerm_mono τ b).inv
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨σ, a, rfl⟩ := h.isMono x hx
    obtain ⟨c, hc⟩ := hP σ a
    exact ⟨_, c, hc⟩
  · intro i j
    obtain ⟨x, hx, σ, a, rfl, hσ⟩ := h.trans (τ⁻¹ i) (τ⁻¹ j)
    obtain ⟨c, hc⟩ := hP σ a
    refine ⟨_, Subgroup.mem_map_of_mem _ hx, τ * σ * τ⁻¹, c, hc, ?_⟩
    show τ (σ (τ⁻¹ i)) = j
    rw [hσ]
    simp

theorem exists_c_line {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X) :
    ∃ (k : Fin 3) (μ : K), μ ≠ 0 ∧ d.c = μ • Pi.single k 1 ∧
      ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ k = k ∧ a k = 1 := by
  classical
  have hLm : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a := fun l hl => hm.isMono l (h.Lle hl)
  have hrel : ∀ (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ), (mono σ a : GL (Fin 3) K) ∈ d.Lm →
      ∀ j, (a j : K) * d.c j = d.c (σ j) := by
    intro σ a hl j
    have := congrFun (h.c_fix _ hl) (σ j)
    rwa [mono_mulVec_apply] at this
  by_cases hall : ∀ j, d.c j ≠ 0
  · exfalso
    obtain ⟨e⟩ := h.Ldih
    have hcard : Nat.card d.Lm = 2 * d.n := by
      have : NeZero d.n := ⟨by rcases h.n_mem with h | h | h <;> omega⟩
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    choose! σf af hσaf using hLm
    have hinj : Function.Injective (fun l : d.Lm => σf l.1) := by
      intro l l' hll'
      apply Subtype.ext
      have hl := hσaf l.1 l.2
      have hl' := hσaf l'.1 l'.2
      simp only at hll'
      have hrl := hrel _ _ (hl ▸ l.2)
      have hrl' := hrel _ _ (hl' ▸ l'.2)
      have haa : af l.1 = af l'.1 := by
        funext j
        apply Units.ext
        have h1 := hrl j
        have h2' := hrl' j
        rw [hll'] at h1
        rw [← h2'] at h1
        exact mul_right_cancel₀ (hall j) h1
      calc (l : GL (Fin 3) K) = mono (σf l.1) (af l.1) := hl
        _ = mono (σf l'.1) (af l'.1) := by rw [hll', haa]
        _ = l' := hl'.symm
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcard] at hle
    have h6 : Nat.card (Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
    rw [h6] at hle
    rcases h.n_mem with h' | h' | h' <;> omega
  · push Not at hall
    obtain ⟨j0, hj0⟩ := hall
    have hex : ∃ j, d.c j ≠ 0 := by
      by_contra hno
      push Not at hno
      exact h.c_ne (funext hno)
    have hfix : ∃ k : Fin 3, ∀ σ : Perm (Fin 3), (∀ j, d.c (σ j) = 0 ↔ d.c j = 0) → σ k = k := by
      have key : ∀ z : Fin 3 → Bool, (∃ j, z j = true) → (∃ j, z j = false) →
          ∃ k, ∀ σ : Perm (Fin 3), (∀ j, z (σ j) = z j) → σ k = k := by decide
      obtain ⟨j1, hj1⟩ := hex
      obtain ⟨k, hk⟩ := key (fun j => decide (d.c j = 0)) ⟨j0, by simpa using hj0⟩
        ⟨j1, by simpa using hj1⟩
      refine ⟨k, fun σ hσ => hk σ (fun j => ?_)⟩
      show decide (d.c (σ j) = 0) = decide (d.c j = 0)
      simp only [decide_eq_decide]
      exact hσ j
    obtain ⟨k, hk⟩ := hfix
    have hσk : ∀ (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ), (mono σ a : GL (Fin 3) K) ∈ d.Lm →
        σ k = k := by
      intro σ a hl
      apply hk σ
      intro j
      rw [← hrel σ a hl j]
      constructor
      · intro h0
        exact (mul_eq_zero.mp h0).resolve_left (a j).ne_zero
      · intro h0
        rw [h0, mul_zero]
    obtain ⟨μ, hμ⟩ := h.lines (Pi.single k 1) (by simp) (by
      intro l hl
      obtain ⟨σ, a, hla⟩ := hLm l hl
      refine ⟨a k, ?_⟩
      have hl' : (mono σ a : GL (Fin 3) K) ∈ d.Lm := hla ▸ hl
      rw [hla, mono_mulVec_single, hσk σ a hl', single_eq_smul])
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hμ
      exact absurd (congrFun hμ k) (by simp)
    have hc : d.c = μ⁻¹ • Pi.single k 1 := by
      rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨k, μ⁻¹, inv_ne_zero hμ0, hc, ?_⟩
    intro l hl
    obtain ⟨σ, a, hla⟩ := hLm l hl
    have hl' : (mono σ a : GL (Fin 3) K) ∈ d.Lm := hla ▸ hl
    refine ⟨σ, a, hla, hσk σ a hl', ?_⟩
    have h1 := hrel σ a hl' k
    rw [hσk σ a hl'] at h1
    have hck : d.c k ≠ 0 := by
      rw [hc]; simp [hμ0]
    exact Units.ext (mul_right_cancel₀ hck (by rw [h1, Units.val_one, one_mul]))

theorem exists_relabel {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X) :
    ∃ P : GL (Fin 3) K, MonoHyp (d.conj P) ∧ MonoStd (d.conj P).X ∧
      (∃ μ : K, μ ≠ 0 ∧ (d.conj P).c = μ • Pi.single 2 1) ∧
      (∀ l ∈ (d.conj P).Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1) := by
  obtain ⟨k, μ, hμ, hc, hL⟩ := exists_c_line h hm
  set τ : Perm (Fin 3) := swap k 2 with hτ
  refine ⟨mono τ (fun _ => 1), h.conj _, hm.conj τ _, ⟨μ, hμ, ?_⟩, ?_⟩
  · show ((mono τ (fun _ => 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = _
    rw [hc, Matrix.mulVec_smul, mono_mulVec_single]
    simp [hτ]
  · intro l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    obtain ⟨σ, a, rfl, hσ, ha⟩ := hL l hl
    refine ⟨τ * σ * τ⁻¹, fun j => a (τ⁻¹ j), ?_, ?_, ?_⟩
    · show (mono τ (fun _ => 1) : GL (Fin 3) K) * mono σ a * (mono τ (fun _ => 1))⁻¹ = _
      exact mono_conj_perm τ σ a
    · simp [hτ, hσ]
    · simp [hτ, ha]

end CFSG.RankThree.PartOne.N1322
