module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def CharTwoMod (X Q₀ : Subgroup G) : Prop :=
  ∀ g ∈ X, (∀ p ∈ pCoreOf 2 X, ⁅g, p⁆ ∈ Q₀) → g ∈ pCoreOf 2 X

@[expose] def cent2Mod (X Q₀ : Subgroup G) (hX : X ≤ Subgroup.normalizer (Q₀ : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ p ∈ pCoreOf 2 X, ⁅g, p⁆ ∈ Q₀}
  one_mem' := ⟨X.one_mem, fun p _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
    refine ⟨X.mul_mem hgX hhX, fun p hp => ?_⟩
    have e : ⁅g * h, p⁆ = g * ⁅h, p⁆ * g⁻¹ * ⁅g, p⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Q₀.mul_mem ?_ (hg p hp)
    exact (Subgroup.mem_normalizer_iff.mp (hX hgX) _).mp (hh p hp)
  inv_mem' := by
    rintro g ⟨hgX, hg⟩
    refine ⟨X.inv_mem hgX, fun p hp => ?_⟩
    have e : ⁅g⁻¹, p⁆ = g⁻¹ * (⁅g, p⁆)⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem hgX)) _).mp (Q₀.inv_mem (hg p hp))

theorem cent2Mod_le {X Q₀ : Subgroup G} (hX : X ≤ Subgroup.normalizer (Q₀ : Set G)) :
    cent2Mod X Q₀ hX ≤ X := fun _ hg => hg.1

theorem le_normalizer_cent2Mod {X Q₀ : Subgroup G} (hX : X ≤ Subgroup.normalizer (Q₀ : Set G)) :
    X ≤ Subgroup.normalizer (cent2Mod X Q₀ hX : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  have key : ∀ x ∈ X, ∀ g ∈ cent2Mod X Q₀ hX, x * g * x⁻¹ ∈ cent2Mod X Q₀ hX := by
    intro x hx g hg
    refine ⟨X.mul_mem (X.mul_mem hx hg.1) (X.inv_mem hx), fun p hp => ?_⟩
    have hp' : x⁻¹ * p * x ∈ pCoreOf 2 X := by
      have := (Subgroup.mem_normalizer_iff.mp (hPn (X.inv_mem hx)) p).mp hp
      simpa using this
    have e : ⁅x * g * x⁻¹, p⁆ = x * ⁅g, x⁻¹ * p * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hX hx) _).mp (hg.2 _ hp')
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key x hx g, fun h => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem charTwoMod_of_odd [Finite G] {X Q₀ : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (Q₀ : Set G))
    (h : ∀ c ∈ X, Odd (orderOf c) → (∀ p ∈ pCoreOf 2 X, ⁅c, p⁆ ∈ Q₀) → c = 1) :
    CharTwoMod X Q₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := cent2Mod X Q₀ hX with hC
  have hC2 : IsPGroup 2 C := by
    intro g
    obtain ⟨a, m', hm', hord⟩ := Nat.exists_eq_two_pow_mul_odd
      (orderOf_pos (g : G)).ne'
    have hg' : (g : G) ^ 2 ^ a ∈ C := Subgroup.pow_mem C g.2 _
    have hodd' : Odd (orderOf ((g : G) ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (by positivity) (hord ▸ dvd_mul_right _ _), hord,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm'
    have h1 : (g : G) ^ 2 ^ a = 1 := h _ hg'.1 hodd' hg'.2
    exact ⟨a, Subtype.ext (by simpa using h1)⟩
  have hle : C ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (cent2Mod_le hX) (le_normalizer_cent2Mod hX) hC2
  exact fun g hgX hg => hle ⟨hgX, hg⟩

end CFSG.Quasithin.N204
