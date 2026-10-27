module

public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.S15K

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f : ℕ} {𝕂 : Type} [Field 𝕂] (hU : UnitaryFieldData ℓ f 𝕂) {W : Type*} [AddCommGroup W]
  [Module 𝕂 W] [FiniteDimensional 𝕂 W]

theorem exists_coincident_of_isotropic_stable {p : ℕ} [NeZero p] {ζ : 𝕂} (hζ : IsPrimitiveRoot ζ p)
    (hpq : p ∣ ℓ ^ f + 1) {B : W →ₛₗ[hU.bar] W →ₗ[𝕂] 𝕂} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {ι : Type*} [Finite ι] (g : ι → End 𝕂 W) (hcomm : ∀ i j, Commute (g i) (g j))
    (hpow : ∀ i, g i ^ p = 1) (hiso : ∀ i v w, B (g i v) (g i w) = B v w) {R : Submodule 𝕂 W}
    (hRne : R ≠ ⊥) (hRst : ∀ i, ∀ r ∈ R, g i r ∈ R) (hRiso : ∀ r ∈ R, ∀ r' ∈ R, B r r' = 0) :
    ∃ (b : Basis (Fin (finrank 𝕂 W)) 𝕂 W) (μ : ι → Fin (finrank 𝕂 W) → 𝕂),
      (∀ i j, g i (b j) = μ i j • b j) ∧ (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      ∃ j₁ j₂, j₁ ≠ j₂ ∧ ∀ i, μ i j₁ = μ i j₂ := by
  classical
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis hU hζ hpq hB hBl g hcomm hpow hiso
  refine ⟨b, μ, hbμ, hbo, ?_⟩
  have hcoord : ∀ i (j : Fin (finrank 𝕂 W)) (v : W), b.coord j (g i v) = μ i j * b.coord j v := by
    intro i j v
    have : (b.coord j).comp (g i) = μ i j • b.coord j := by
      refine b.ext fun k => ?_
      simp only [LinearMap.comp_apply, hbμ, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      split_ifs with h1
      · subst h1
        ring
      · simp
    simpa using LinearMap.congr_fun this v
  let supp : W → Finset (Fin (finrank 𝕂 W)) := fun v => Finset.univ.filter fun j => b.coord j v ≠ 0
  have hex : ∃ n, ∃ v ∈ R, v ≠ 0 ∧ (supp v).card = n := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
    exact ⟨_, v, hv, hv0, rfl⟩
  obtain ⟨v, hvR, hv0, hvn⟩ := Nat.find_spec hex
  set n := Nat.find hex with hn
  have hmin : ∀ v' ∈ R, v' ≠ 0 → n ≤ (supp v').card := fun v' hv' hv'0 =>
    Nat.find_min' hex ⟨v', hv', hv'0, rfl⟩
  have hsuppne : (supp v).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hv0
    refine b.ext_elem fun j => ?_
    by_contra hj
    have hj' : b.coord j v ≠ 0 := by simpa [Basis.coord_apply] using hj
    have : j ∈ supp v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
    rw [hemp] at this
    exact Finset.notMem_empty _ this
  obtain ⟨j₀, hj₀⟩ := hsuppne
  have hj₀' : b.coord j₀ v ≠ 0 := (Finset.mem_filter.mp hj₀).2
  have hchar : ∀ i, ∀ j, b.coord j v ≠ 0 → μ i j = μ i j₀ := by
    intro i j hj
    set v' : W := g i v - μ i j₀ • v with hv'
    have hv'R : v' ∈ R := R.sub_mem (hRst i v hvR) (R.smul_mem _ hvR)
    have hcv' : ∀ k, b.coord k v' = (μ i k - μ i j₀) * b.coord k v := by
      intro k
      rw [hv', map_sub, map_smul, hcoord, smul_eq_mul]
      ring
    have hv'0 : v' = 0 := by
      by_contra hne
      have h1 := hmin v' hv'R hne
      have h2 : supp v' ⊂ supp v := by
        refine ⟨fun k hk => ?_, fun hsub => ?_⟩
        · have hk' : b.coord k v' ≠ 0 := (Finset.mem_filter.mp hk).2
          rw [hcv'] at hk'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hk'⟩
        · have := hsub hj₀
          have hk' := (Finset.mem_filter.mp this).2
          rw [hcv', sub_self, zero_mul] at hk'
          exact hk' rfl
      have := Finset.card_lt_card h2
      omega
    have h3 : b.coord j v' = 0 := by rw [hv'0]; simp
    rw [hcv'] at h3
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hj
  have hBvv : B v v = ∑ j, hU.bar (b.coord j v) * b.coord j v := by
    have hvsum : v = ∑ j, b.coord j v • b j := by
      conv_lhs => rw [← b.sum_repr v]
      rfl
    have h2 : ∀ j, B (b j) v = b.coord j v := by
      intro j
      calc B (b j) v = B (b j) (∑ k, b.coord k v • b k) := by rw [← hvsum]
        _ = ∑ k, b.coord k v * B (b j) (b k) := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
        _ = b.coord j v := by simp [hbo]
    calc B v v = B (∑ j, b.coord j v • b j) v := by rw [← hvsum]
      _ = ∑ j, B (b.coord j v • b j) v := by rw [map_sum, LinearMap.sum_apply]
      _ = ∑ j, hU.bar (b.coord j v) * b.coord j v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smulₛₗ, LinearMap.smul_apply, h2, smul_eq_mul]
  have hBvv0 : B v v = 0 := hRiso v hvR v hvR
  have hcard : 2 ≤ (supp v).card := by
    by_contra hlt
    have h1 : (supp v).card = 1 := by
      have := Finset.card_pos.mpr ⟨j₀, hj₀⟩
      omega
    obtain ⟨j', hj'⟩ := Finset.card_eq_one.mp h1
    have hj₀eq : j₀ = j' := by
      have : j₀ ∈ ({j'} : Finset _) := hj' ▸ hj₀
      exact Finset.mem_singleton.mp this
    have hz : ∀ j, j ≠ j₀ → b.coord j v = 0 := by
      intro j hjne
      by_contra hjn
      have : j ∈ supp v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjn⟩
      rw [hj', Finset.mem_singleton] at this
      exact hjne (this.trans hj₀eq.symm)
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hz j hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
      at hBvv
    rw [hBvv0] at hBvv
    have hbar : hU.bar (b.coord j₀ v) ≠ 0 := by
      intro h0
      exact hj₀' ((map_eq_zero_iff _ hU.bar.injective).mp h0)
    exact (mul_ne_zero hbar hj₀') hBvv.symm
  obtain ⟨j₁, hj₁, hj₁ne⟩ : ∃ j₁ ∈ supp v, j₁ ≠ j₀ := by
    by_contra hcon
    push Not at hcon
    have : supp v ⊆ {j₀} := fun j hj => Finset.mem_singleton.mpr (hcon j hj)
    have := Finset.card_le_card this
    simp at this
    omega
  exact ⟨j₁, j₀, hj₁ne, fun i => hchar i j₁ (Finset.mem_filter.mp hj₁).2⟩

end CFSG.RankThree.PartOne.S15K
