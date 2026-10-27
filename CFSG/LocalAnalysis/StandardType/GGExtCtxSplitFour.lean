module

public import CFSG.LocalAnalysis.StandardType.GGExtCtx
public import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFourModel

public section

namespace CFSG.StandardType.GGExtCtx

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_top_of_classRefl_minus_four [Fact (Nat.Prime 5)] {V : Type} [AddCommGroup V]
    [Module (ZMod 5) V] [Module.Finite (ZMod 5) V] {A : Subgroup (V ≃ₗ[ZMod 5] V)}
    {T : Submodule (ZMod 5) V} {AT : Subgroup (↥T ≃ₗ[ZMod 5] ↥T)} (X : GGExtCtx A T AT)
    (hT : Module.finrank (ZMod 5) ↥T = 4) {Q : QuadraticForm (ZMod 5) ↥T}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {c : ZMod 5} (hc : c ≠ 0)
    (hAT : AT = Subgroup.closure (ZS.ClassRefl 5 Q c)) : T = ⊤ := by
  obtain ⟨u₁, u₂, d, hu₁, hu₂, hd, hd12, hdc1, hdc2, hcoc, hidx⟩ :=
    OFourMinusFive.exists_splitData hT hQ hminus hc
  have hu₁' : u₁ ∈ AT := by rw [hAT]; exact hu₁
  have hu₂' : u₂ ∈ AT := by rw [hAT]; exact hu₂
  have hd' : d ∈ AT := by rw [hAT]; exact hd
  let S : Set (↥T ≃ₗ[ZMod 5] ↥T) := {u₁, u₂, d}
  have hS : S ⊆ AT := by
    intro s hs
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hu₁'
    · exact hu₂'
    · exact hd'
  have hidx' : ¬ 5 ∣ (closure S).relIndex AT := by
    simpa only [S, hAT] using hidx
  let s₁ : ↥AT := ⟨u₁, hu₁'⟩
  let s₂ : ↥AT := ⟨u₂, hu₂'⟩
  let s₃ : ↥AT := ⟨d, hd'⟩
  let û₁ : V ≃ₗ[ZMod 5] V := (X.restrictEquiv.symm s₁ : ↥A)
  let û₂ : V ≃ₗ[ZMod 5] V := (X.restrictEquiv.symm s₂ : ↥A)
  let dh : V ≃ₗ[ZMod 5] V := (X.restrictEquiv.symm s₃ : ↥A)
  have hs3 : s₃ ^ 12 = 1 := by
    apply Subtype.ext
    simp [s₃, hd12]
  have hdh12 : dh ^ 12 = 1 := by
    have h : (X.restrictEquiv.symm s₃ : ↥A) ^ 12 = 1 := by
      rw [← map_pow, hs3, map_one]
    simpa [dh] using congrArg (fun x : ↥A => (x : V ≃ₗ[ZMod 5] V)) h
  have hs12 : s₃ * s₁ * s₃⁻¹ = s₁ ^ 4 * s₂ ^ 4 := by
    apply Subtype.ext
    simp [s₁, s₂, s₃, hdc1]
  have hs22 : s₃ * s₂ * s₃⁻¹ = s₁ ^ 3 * s₂ ^ 4 := by
    apply Subtype.ext
    simp [s₁, s₂, s₃, hdc2]
  have hdc1' : dh * û₁ * dh⁻¹ = û₁ ^ 4 * û₂ ^ 4 := by
    have h : (X.restrictEquiv.symm s₃ : ↥A) * (X.restrictEquiv.symm s₁ : ↥A)
        * (X.restrictEquiv.symm s₃ : ↥A)⁻¹
        = (X.restrictEquiv.symm s₁ : ↥A) ^ 4
          * (X.restrictEquiv.symm s₂ : ↥A) ^ 4 := by
      simp only [← map_mul, ← map_inv, ← map_pow]
      rw [hs12]
    simpa [û₁, û₂, dh] using congrArg (fun x : ↥A => (x : V ≃ₗ[ZMod 5] V)) h
  have hdc2' : dh * û₂ * dh⁻¹ = û₁ ^ 3 * û₂ ^ 4 := by
    have h : (X.restrictEquiv.symm s₃ : ↥A) * (X.restrictEquiv.symm s₂ : ↥A)
        * (X.restrictEquiv.symm s₃ : ↥A)⁻¹
        = (X.restrictEquiv.symm s₁ : ↥A) ^ 3
          * (X.restrictEquiv.symm s₂ : ↥A) ^ 4 := by
      simp only [← map_mul, ← map_inv, ← map_pow]
      rw [hs22]
    simpa [û₁, û₂, dh] using congrArg (fun x : ↥A => (x : V ≃ₗ[ZMod 5] V)) h
  have hres1 : ∀ (k : ℕ) (z : ↥T),
      (û₁ ^ k) (z : V) = (((u₁ ^ k) z : ↥T) : V) := by
    intro k z
    have h := X.restrictEquiv_symm_apply (s₁ ^ k) z
    rw [map_pow X.restrictEquiv.symm s₁ k] at h
    rw [Subgroup.coe_pow] at h
    simpa [û₁, s₁] using h
  have hres2 : ∀ (k : ℕ) (z : ↥T),
      (û₂ ^ k) (z : V) = (((u₂ ^ k) z : ↥T) : V) := by
    intro k z
    have h := X.restrictEquiv_symm_apply (s₂ ^ k) z
    rw [map_pow X.restrictEquiv.symm s₂ k] at h
    rw [Subgroup.coe_pow] at h
    simpa [û₂, s₂] using h
  have hresd : ∀ z : ↥T, dh (z : V) = ((d z : ↥T) : V) := by
    intro z
    simpa [dh, s₃] using X.restrictEquiv_symm_apply s₃ z
  rw [Submodule.eq_top_iff']
  intro v
  have h120 : (12 : ZMod 5) ≠ 0 := by
    have hu : ((ZMod.unitOfCoprime 12 (by decide : Nat.Coprime 12 5) : (ZMod 5)ˣ) :
        ZMod 5) ≠ 0 := Units.ne_zero _
    simpa using hu
  obtain ⟨w₀, hw₀, hw₀v⟩ :=
    X.exists_fixed_sub_mem (a := dh) (X.restrictEquiv.symm s₃).2 (n := 12) hdh12 h120 v
  have hxT : û₁ w₀ - w₀ ∈ T := X.disp û₁ (X.restrictEquiv.symm s₁).2 w₀
  have hyT : û₂ w₀ - w₀ ∈ T := X.disp û₂ (X.restrictEquiv.symm s₂).2 w₀
  have h1 : ∑ k ∈ Finset.range 4, (u₁ ^ k) ⟨û₁ w₀ - w₀, hxT⟩ +
        (u₁ ^ 4) (∑ k ∈ Finset.range 4, (u₂ ^ k) ⟨û₂ w₀ - w₀, hyT⟩) =
      d ⟨û₁ w₀ - w₀, hxT⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, ← hres1, ← hres2, ← hresd]
    exact sum_cocycle_eq (b := û₁) (c := û₂) (d := dh) (g := û₁) (w := w₀) hw₀ hdc1'
  have h2 : ∑ k ∈ Finset.range 3, (u₁ ^ k) ⟨û₁ w₀ - w₀, hxT⟩ +
        (u₁ ^ 3) (∑ k ∈ Finset.range 4, (u₂ ^ k) ⟨û₂ w₀ - w₀, hyT⟩) =
      d ⟨û₂ w₀ - w₀, hyT⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, ← hres1, ← hres2, ← hresd]
    exact sum_cocycle_eq (b := û₁) (c := û₂) (d := dh) (g := û₂) (w := w₀) hw₀ hdc2'
  obtain ⟨hx0, hy0⟩ := hcoc ⟨û₁ w₀ - w₀, hxT⟩ ⟨û₂ w₀ - w₀, hyT⟩ h1 h2
  have hxw : û₁ w₀ = w₀ := by
    have h : û₁ w₀ - w₀ = 0 := by simpa using congrArg Subtype.val hx0
    exact sub_eq_zero.mp h
  have hyw : û₂ w₀ = w₀ := by
    have h : û₂ w₀ - w₀ = 0 := by simpa using congrArg Subtype.val hy0
    exact sub_eq_zero.mp h
  have hfix : ∀ s (hs : s ∈ S),
      ((X.restrictEquiv.symm ⟨s, hS hs⟩ : ↥A) : V ≃ₗ[ZMod 5] V) w₀ = w₀ := by
    intro s hs
    have hs' : s = u₁ ∨ s = u₂ ∨ s = d := by
      simpa only [S, Set.mem_insert_iff, Set.mem_singleton_iff] using hs
    rcases hs' with h | h | h
    · subst s
      have hs1 : (⟨u₁, hS hs⟩ : ↥AT) = s₁ := Subtype.ext rfl
      rw [hs1]
      simpa [û₁] using hxw
    · subst s
      have hs2 : (⟨u₂, hS hs⟩ : ↥AT) = s₂ := Subtype.ext rfl
      rw [hs2]
      simpa [û₂] using hyw
    · subst s
      have hs3' : (⟨d, hS hs⟩ : ↥AT) = s₃ := Subtype.ext rfl
      rw [hs3']
      simpa [dh] using hw₀
  have hwT : w₀ ∈ T := X.mem_of_forall_fixed_lift (S := S) (v := w₀) hS hidx' hfix
  have hv : v = w₀ - (w₀ - v) := (sub_sub_self w₀ v).symm
  rw [hv]
  exact T.sub_mem hwT hw₀v

end CFSG.StandardType.GGExtCtx

end
