module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsLin
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec8_dimCount_of_K_symm {K E : Type} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (halt : ∀ e, B e e = 0) (u v : E) : B u v = B v u := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : B (u + v) (u + v) = 0 := halt _
  simp only [map_add, LinearMap.add_apply, halt u, halt v, add_zero, zero_add] at h1
  linear_combination h1 - (B v u) * h2

theorem sec8_dimCount_of_K_trace_sep {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] (a : K)
    (ha : a ≠ 0) : ∃ c : K, Algebra.trace (ZMod 2) K (a * c) ≠ 0 := by
  haveI : Module.Finite (ZMod 2) K := Module.finite_iff_finite.mpr inferInstance
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply ha
  apply (traceForm_nondegenerate (ZMod 2) K).1 a
  intro c
  rw [Algebra.traceForm_apply]
  exact hcon c

theorem sec8_dimCount_of_K_natCard {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem sec8_dimCount_of_K_beta {K E : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup E]
    [Module K E] [Algebra (ZMod 2) K] [Module (ZMod 2) E] [IsScalarTower (ZMod 2) K E]
    (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate) (halt : ∀ e, B e e = 0) :
    ∃ β : LinearMap.BilinForm (ZMod 2) E,
      (∀ x y, β x y = Algebra.trace (ZMod 2) K (B x y)) ∧ β.Nondegenerate ∧ β.IsRefl := by
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm (ZMod 2) E,
      ∀ x y, β x y = Algebra.trace (ZMod 2) K (B x y) :=
    ⟨LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) K (B x y))
      (fun m₁ m₂ n => by simp only [map_add, LinearMap.add_apply])
      (fun c m n => by
        have hcm : c • m = algebraMap (ZMod 2) K c • m :=
          (IsScalarTower.algebraMap_smul (A := K) c m).symm
        have hc : B (c • m) n = c • B m n := by
          rw [hcm, map_smul, LinearMap.smul_apply, smul_eq_mul, Algebra.smul_def]
        simp only [hc, map_smul])
      (fun m n₁ n₂ => by simp only [map_add])
      (fun c m n => by
        have hcn : c • n = algebraMap (ZMod 2) K c • n :=
          (IsScalarTower.algebraMap_smul (A := K) c n).symm
        have hc : B m (c • n) = c • B m n := by
          rw [hcn, map_smul, smul_eq_mul, Algebra.smul_def]
        simp only [hc, map_smul]),
     fun x y => rfl⟩
  have hβsymm : ∀ x y : E, β x y = β y x := by
    intro x y
    rw [hβ, hβ, sec8_dimCount_of_K_symm B halt x y]
  have hleft : ∀ x : E, (∀ y : E, β x y = 0) → x = 0 := by
    intro x hx
    apply hnd.1 x
    intro y
    by_contra hne
    obtain ⟨c, hc⟩ := sec8_dimCount_of_K_trace_sep (B x y) hne
    apply hc
    have h := hx (c • y)
    rw [hβ, map_smul, smul_eq_mul, mul_comm] at h
    exact h
  have hright : ∀ y : E, (∀ x : E, β x y = 0) → y = 0 :=
    fun y hy => hleft y (fun z => by rw [hβsymm]; exact hy z)
  exact ⟨β, hβ, And.intro hleft hright, fun x y h => by rw [hβsymm]; exact h⟩

theorem sec8_dimCount_of_K {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [AddCommGroup E]
    [Module K E] [Module.Finite K E] (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (halt : ∀ e, B e e = 0) (X X' L : E →ₗ[K] E)
    (hXiso : ∀ u v, B (X u) (X v) = B u v) (hX'iso : ∀ u v, B (X' u) (X' v) = B u v)
    (hXs : Function.Surjective X) (hX's : Function.Surjective X')
    (haa : ∀ e ∈ LinearMap.range (X - 1), (X' - 1) e = 0)
    (hE'' : ∀ e, e ∈ LinearMap.range (X' - 1) ↔ ∃ e' ∈ LinearMap.range (X - 1), e = L e')
    (hdisj : ∀ e, e ∈ LinearMap.range (X - 1) → e ∈ LinearMap.range (X' - 1) → e = 0)
    (hL : Function.Injective L)
    (hdim : Nat.card ↥(LinearMap.range (X - 1)) = Nat.card K ^ 4)
    (S Bpt : AddSubgroup E) (hS : ∀ s ∈ S, ∀ s' ∈ S, B s s' = 0)
    (hSdim : Nat.card ↥S * Nat.card ↥S = Nat.card E) (hB : Nat.card ↥Bpt ≤ Nat.card K)
    (hSe : ∀ s ∈ S, X' (X s) - s ∈ Bpt) (hSL : ∀ s ∈ S, L s - s ∈ Bpt) : False := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  letI : Module (ZMod 2) E := Module.compHom E (algebraMap (ZMod 2) K)
  haveI : IsScalarTower (ZMod 2) K E := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  haveI : Finite E := Module.finite_of_finite K
  haveI : Module.Finite (ZMod 2) E := Module.finite_iff_finite.mpr inferInstance
  haveI : Module.Finite (ZMod 2) K := Module.finite_iff_finite.mpr inferInstance
  obtain ⟨β, hβ, hnd₀, hrefl₀⟩ := sec8_dimCount_of_K_beta B hnd halt
  obtain ⟨Xz, hXz⟩ : ∃ T : E →ₗ[ZMod 2] E, ∀ x, T x = X x :=
    ⟨X.restrictScalars (ZMod 2), fun _ => rfl⟩
  obtain ⟨Xz', hXz'⟩ : ∃ T : E →ₗ[ZMod 2] E, ∀ x, T x = X' x :=
    ⟨X'.restrictScalars (ZMod 2), fun _ => rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ T : E →ₗ[ZMod 2] E, ∀ x, T x = L x :=
    ⟨L.restrictScalars (ZMod 2), fun _ => rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ T : Submodule (ZMod 2) E, ∀ x, x ∈ T ↔ x ∈ S :=
    ⟨AddSubgroup.toZModSubmodule 2 S, fun x => AddSubgroup.mem_toZModSubmodule 2⟩
  obtain ⟨Bp₀, hBp₀⟩ : ∃ T : Submodule (ZMod 2) E, ∀ x, x ∈ T ↔ x ∈ Bpt :=
    ⟨AddSubgroup.toZModSubmodule 2 Bpt, fun x => AddSubgroup.mem_toZModSubmodule 2⟩
  have hsubz : ∀ y, (Xz - 1) y = (X - 1) y := fun y => by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hXz]
  have hsubz' : ∀ y, (Xz' - 1) y = (X' - 1) y := fun y => by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hXz']
  have hrange1 : ∀ e : E, e ∈ LinearMap.range (Xz - 1) ↔ e ∈ LinearMap.range (X - 1) := by
    intro e
    simp only [LinearMap.mem_range, hsubz]
  have hrange2 : ∀ e : E, e ∈ LinearMap.range (Xz' - 1) ↔ e ∈ LinearMap.range (X' - 1) := by
    intro e
    simp only [LinearMap.mem_range, hsubz']
  have hcardz : Nat.card ↥(LinearMap.range (Xz - 1)) = Nat.card ↥(LinearMap.range (X - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange1)
  have hNatK : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := sec8_dimCount_of_K_natCard
  have hNatE : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := sec8_dimCount_of_K_natCard
  have hpowz : Nat.card ↥(LinearMap.range (Xz - 1)) =
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (Xz - 1)) := sec8_dimCount_of_K_natCard
  have hpowS : Nat.card ↥S₀ = 2 ^ Module.finrank (ZMod 2) ↥S₀ := sec8_dimCount_of_K_natCard
  have hpowBp : Nat.card ↥Bp₀ = 2 ^ Module.finrank (ZMod 2) ↥Bp₀ := sec8_dimCount_of_K_natCard
  have hcardS₀ : Nat.card ↥S₀ = Nat.card ↥S := Nat.card_congr (Equiv.subtypeEquivRight hS₀)
  have hcardBp₀ : Nat.card ↥Bp₀ = Nat.card ↥Bpt :=
    Nat.card_congr (Equiv.subtypeEquivRight hBp₀)
  have hdimz : Module.finrank (ZMod 2) ↥(LinearMap.range (Xz - 1)) =
      4 * Module.finrank (ZMod 2) K := by
    have key : 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (Xz - 1)) =
        2 ^ (4 * Module.finrank (ZMod 2) K) := by
      rw [← hpowz, hcardz, hdim, hNatK]
      ring
    exact Nat.pow_right_injective (le_refl 2) key
  have hf : 0 < Module.finrank (ZMod 2) K := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) K) with h0 | h0
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hNatK, h0, pow_zero]
      have h3 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hSdim₀ : 2 * Module.finrank (ZMod 2) ↥S₀ = Module.finrank (ZMod 2) E := by
    have key : 2 ^ (2 * Module.finrank (ZMod 2) ↥S₀) = 2 ^ Module.finrank (ZMod 2) E := by
      rw [← hNatE, ← hSdim, ← hcardS₀, hpowS, two_mul, pow_add]
    exact Nat.pow_right_injective (le_refl 2) key
  have hBp₀le : Module.finrank (ZMod 2) ↥Bp₀ ≤ Module.finrank (ZMod 2) K := by
    have h : 2 ^ Module.finrank (ZMod 2) ↥Bp₀ ≤ 2 ^ Module.finrank (ZMod 2) K := by
      rw [← hpowBp, hcardBp₀, ← hNatK]
      exact hB
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hSle : S₀ ≤ β.orthogonal S₀ := by
    intro s hs
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hβ, hS n ((hS₀ n).mp hn) s ((hS₀ s).mp hs), map_zero]
  have hXiso₀ : ∀ u v, β (Xz u) (Xz v) = β u v := by
    intro u v
    simp only [hβ, hXz, hXiso]
  have hX'iso₀ : ∀ u v, β (Xz' u) (Xz' v) = β u v := by
    intro u v
    simp only [hβ, hXz', hX'iso]
  have hXs₀ : Function.Surjective Xz := by
    intro y
    obtain ⟨x, hx⟩ := hXs y
    exact ⟨x, by rw [hXz, hx]⟩
  have hX's₀ : Function.Surjective Xz' := by
    intro y
    obtain ⟨x, hx⟩ := hX's y
    exact ⟨x, by rw [hXz', hx]⟩
  have haa₀ : (Xz' - 1) ∘ₗ (Xz - 1) = 0 := by
    apply LinearMap.ext
    intro e
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hsubz, hsubz']
    exact haa _ (LinearMap.mem_range_self (X - 1) e)
  have hEz : LinearMap.range (Xz' - 1) = (LinearMap.range (Xz - 1)).map Lz := by
    ext e
    rw [hrange2 e, hE'' e, Submodule.mem_map]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨e', (hrange1 e').mpr he', hLz e'⟩
    · rintro ⟨y, hy, hyl⟩
      exact ⟨y, (hrange1 y).mp hy, by rw [← hyl, hLz]⟩
  have hdisj₀ : LinearMap.range (Xz - 1) ⊓ LinearMap.range (Xz' - 1) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.mp he
    rw [Submodule.mem_bot]
    exact hdisj e ((hrange1 e).mp h1) ((hrange2 e).mp h2')
  have hLzinj : Function.Injective Lz := by
    intro a b hab
    apply hL
    rw [← hLz a, ← hLz b]
    exact hab
  have hSe₀ : ∀ s ∈ S₀, (Xz' * Xz - 1) s ∈ Bp₀ := by
    intro s hs
    rw [hBp₀]
    have h1 : (Xz' * Xz - 1) s = X' (X s) - s := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, hXz, hXz']
    rw [h1]
    exact hSe s ((hS₀ s).mp hs)
  have hSL₀ : ∀ s ∈ S₀, (Lz - 1) s ∈ Bp₀ := by
    intro s hs
    rw [hBp₀]
    have h1 : (Lz - 1) s = L s - s := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hLz]
    rw [h1]
    exact hSL s ((hS₀ s).mp hs)
  exact thm111_core β hnd₀ hrefl₀ Xz Xz' Lz hXiso₀ hX'iso₀ hXs₀ hX's₀ haa₀ hEz hdisj₀
    hLzinj (Module.finrank (ZMod 2) K) hf hdimz S₀ Bp₀ hSle hSdim₀ hBp₀le hSe₀ hSL₀

end CFSG.RankThree.GF2n.Stroth80
