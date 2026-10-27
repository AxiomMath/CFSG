module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F1

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section PCore

variable {E : Type} [Group E]

theorem burnsideF4m_mem_normalizer_inf {Gp M : Subgroup E} [Gp.Normal] {g : E} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxG, hxM⟩
    exact ⟨Subgroup.Normal.conj_mem inferInstance x hxG g,
      M.mul_mem (M.mul_mem hg hxM) (M.inv_mem hg)⟩
  · rintro ⟨hxG, hxM⟩
    have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    refine ⟨?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hxG g⁻¹
      rw [inv_inv] at this
      rw [h1]
      exact this
    · rw [h1]
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) hxM) hg

theorem burnsideF4m_pCoreOf_inf_le [Finite E] (Gp : Subgroup E) [Gp.Normal] (M : Subgroup E) :
    pCoreOf 2 (Gp ⊓ M) ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro g hg
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (burnsideF4m_mem_normalizer_inf hg)

theorem burnsideF4m_pCoreOf_inf_le' [Finite E] (Gp : Subgroup E) [Gp.Normal] (M : Subgroup E) :
    pCoreOf 2 M ⊓ Gp ≤ pCoreOf 2 (Gp ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf inf_le_right (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) x
  have h2 : x ∈ Gp ↔ g * x * g⁻¹ ∈ Gp := by
    constructor
    · intro hx
      exact Subgroup.Normal.conj_mem inferInstance x hx g
    · intro hx
      have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hx g⁻¹
      simpa [mul_assoc] using this
  exact and_congr h1 h2

theorem burnsideF4m_pCoreOf_eq_inf_of_le [Finite E] (Gp : Subgroup E) [Gp.Normal]
    (M : Subgroup E) (h : pCoreOf 2 M ≤ Gp) : pCoreOf 2 M = pCoreOf 2 (Gp ⊓ M) :=
  le_antisymm (le_inf le_rfl h |>.trans (burnsideF4m_pCoreOf_inf_le' Gp M))
    (burnsideF4m_pCoreOf_inf_le Gp M)

theorem burnsideF4m_exists_sq_mem [Finite E] {Gp X : Subgroup E} (hX : IsPGroup 2 X)
    (hXG : ¬ X ≤ Gp) : ∃ r ∈ X, r ∉ Gp ∧ r * r ∈ Gp := by
  classical
  obtain ⟨x, hxX, hxG⟩ := Set.not_subset.mp hXG
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hex : ∃ j, x ^ 2 ^ j ∈ Gp := ⟨k, by rw [hk']; exact Gp.one_mem⟩
  set j := Nat.find hex with hj
  have hj0 : j ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj, h0, pow_zero, pow_one] at this
    exact hxG this
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨x ^ 2 ^ i, X.pow_mem hxX _, ?_, ?_⟩
  · have := Nat.find_min hex (show i < j by omega)
    exact this
  · rw [← pow_add, ← two_mul, ← pow_succ', ← hi]
    exact Nat.find_spec hex

theorem burnsideF4m_index_sup_zpowers {Gp : Subgroup E} [Gp.Normal] {r : E} (hr : r ∉ Gp)
    (hr2 : r * r ∈ Gp) : (Gp.subgroupOf (Gp ⊔ Subgroup.zpowers r)).index = 2 := by
  have hrY : r ∈ Gp ⊔ Subgroup.zpowers r := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  have hpow : ∀ n : ℤ, r ^ n ∈ Gp ∨ r ^ n * r⁻¹ ∈ Gp := by
    intro n
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · left
      rw [hk, zpow_mul, zpow_two]
      have : r ^ (2 : ℤ) = r * r := by rw [zpow_two]
      exact Gp.zpow_mem (by rw [← this, zpow_two]; exact hr2) k
    · right
      rw [hk, zpow_add, zpow_mul, zpow_one, mul_inv_cancel_right]
      exact Gp.zpow_mem (by rw [zpow_two]; exact hr2) k
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨r, hrY⟩, fun b => ?_⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp b.2
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases hpow n with hn | hn
  · have hb : (b : E) ∈ Gp := by rw [← hyz]; exact Gp.mul_mem hy hn
    refine Or.inr ⟨hb, fun hbr => hr ?_⟩
    have := Gp.mul_mem (Gp.inv_mem hb) hbr
    simpa using this
  · have hbr : (b : E) * r⁻¹ ∈ Gp := by rw [← hyz, mul_assoc]; exact Gp.mul_mem hy hn
    have hbr' : (b : E) * r ∈ Gp := by
      have := Gp.mul_mem hbr hr2
      simpa [mul_assoc] using this
    refine Or.inl ⟨hbr', fun hb => hr ?_⟩
    have := Gp.mul_mem (Gp.inv_mem hb) hbr'
    simpa using this

theorem burnsideF4m_normalizer_inf_le {Gp M₁ M₂ : Subgroup E} [Gp.Normal] {C : Type} [Group C]
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₁ ⊓ M₂, e = n * k) (φ : C →* E)
    (hφ : Function.Injective φ) (hrange : φ.range = Gp) {P : Subgroup C}
    (hP : Gp ⊓ M₂ = P.map φ)
    (hself : ∀ g : C, g ∈ Subgroup.normalizer (P : Set C) → g ∈ P) :
    Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) ≤ M₂ := by
  intro e he
  obtain ⟨n, hn, k, hk, rfl⟩ := hsplit e
  have hkN := burnsideF4m_mem_normalizer_inf (Gp := Gp) hk.2
  have hnN : n ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) := by
    have := (Subgroup.normalizer _).mul_mem he ((Subgroup.normalizer _).inv_mem hkN)
    simpa using this
  rw [← hrange] at hn
  obtain ⟨g, rfl⟩ := hn
  have hg : g ∈ Subgroup.normalizer (P : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp hnN) (φ x)
    rw [hP, Subgroup.mem_map_iff_mem hφ, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at h1
    exact h1
  have hgP := hself g hg
  have hφg : φ g ∈ M₂ := by
    have : φ g ∈ Gp ⊓ M₂ := by rw [hP]; exact Subgroup.mem_map_of_mem φ hgP
    exact this.2
  exact M₂.mul_mem hφg hk.2

end PCore

end CFSG.ASVolI
