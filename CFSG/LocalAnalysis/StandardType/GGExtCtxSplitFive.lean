module

public import CFSG.LocalAnalysis.StandardType.GGExtCtx
public import CFSG.LocalAnalysis.StandardType.GGExtCtxSplitFiveModel

public section

namespace CFSG.StandardType

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lift_pow_apply {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
    {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)} (X : GGExtCtx A T AT)
    {g : ↥T ≃ₗ[ZMod p] ↥T} (hg : g ∈ AT) (k : ℕ) (z : ↥T) :
    ((((X.restrictEquiv.symm ⟨g, hg⟩ : ↥A) : V ≃ₗ[ZMod p] V) ^ k) (z : V)) =
      ((((g ^ k) z : ↥T) : V)) := by
  have h := X.restrictEquiv_symm_apply (⟨g, hg⟩ ^ k) z
  rw [map_pow X.restrictEquiv.symm ⟨g, hg⟩ k, Subgroup.coe_pow] at h
  exact h

private theorem lift_sub_fixed {V : Type} [AddCommGroup V] [Module (ZMod 7) V]
    {T : Submodule (ZMod 7) V} (g : ↥T ≃ₗ[ZMod 7] ↥T) (ghat : V ≃ₗ[ZMod 7] V)
    (w : V) (t : ↥T) (hgt : ghat (t : V) = ((g t : ↥T) : V))
    {hzT : ghat w - w ∈ T} (ht : g t - t = ⟨ghat w - w, hzT⟩) :
    ghat (w - (t : V)) = w - (t : V) := by
  rw [map_sub, hgt, ← sub_add_cancel (ghat w) w,
    ← show ((g t : ↥T) : V) - (t : V) = ghat w - w by
      simpa only [Submodule.coe_sub, Submodule.coe_mk] using
        congrArg (fun z : ↥T => (z : V)) ht]
  abel

theorem GGExtCtx.eq_top_of_classRefl_five_seven {V : Type} [AddCommGroup V] [Module (ZMod 7) V]
    [Module.Finite (ZMod 7) V] {A : Subgroup (V ≃ₗ[ZMod 7] V)} {T : Submodule (ZMod 7) V}
    {AT : Subgroup (↥T ≃ₗ[ZMod 7] ↥T)} (X : GGExtCtx A T AT)
    (hT : Module.finrank (ZMod 7) ↥T = 5) {Q : QuadraticForm (ZMod 7) ↥T}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod 7} (hc : c ≠ 0)
    (hAT : AT = Subgroup.closure (ZS.ClassRefl 7 Q c)) : T = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ℓ, s, d, hℓ, hs, hd, hd3, hdc1, hdc2, hcoc, hidx⟩ :=
    OFiveSeven.exists_splitData hT hQ hc
  have hℓ' : ℓ ∈ AT := by rw [hAT]; exact hℓ
  have hs' : s ∈ AT := by rw [hAT]; exact hs
  have hd' : d ∈ AT := by rw [hAT]; exact hd
  let s₁ : ↥AT := ⟨ℓ, hℓ'⟩
  let s₂ : ↥AT := ⟨s, hs'⟩
  let s₃ : ↥AT := ⟨d, hd'⟩
  let S : Set (↥T ≃ₗ[ZMod 7] ↥T) := {ℓ, s}
  have hS : S ⊆ AT := by rintro a (rfl | rfl) <;> assumption
  have hidx' : ¬ 7 ∣ (closure S).relIndex AT := by simpa only [S, hAT] using hidx
  let lhat : V ≃ₗ[ZMod 7] V := (X.restrictEquiv.symm s₁ : ↥A)
  let shat : V ≃ₗ[ZMod 7] V := (X.restrictEquiv.symm s₂ : ↥A)
  let dhat : V ≃ₗ[ZMod 7] V := (X.restrictEquiv.symm s₃ : ↥A)
  let χ : ↥AT →* (V ≃ₗ[ZMod 7] V) := A.subtype.comp X.restrictEquiv.symm
  have hresd : ∀ z : ↥T, dhat (z : V) = ((d z : ↥T) : V) :=
    fun z => by simpa using lift_pow_apply X hd' 1 z
  have hdhat3 : dhat ^ 3 = 1 := by
    have h : s₃ ^ 3 = 1 := by apply Subtype.ext; simp [s₃, hd3]
    rw [show dhat = χ s₃ from rfl, ← map_pow, h, map_one]
  have hdc1' : dhat * lhat * dhat⁻¹ = lhat ^ 4 := by
    have h : s₃ * s₁ * s₃⁻¹ = s₁ ^ 4 := by apply Subtype.ext; simp [s₁, s₃, hdc1]
    rw [show dhat = χ s₃ from rfl, show lhat = χ s₁ from rfl, ← map_mul, ← map_inv,
      ← map_mul, h, map_pow]
  have hdc2' : dhat * shat * dhat⁻¹ = shat ^ 2 := by
    have h : s₃ * s₂ * s₃⁻¹ = s₂ ^ 2 := by apply Subtype.ext; simp [s₂, s₃, hdc2]
    rw [show dhat = χ s₃ from rfl, show shat = χ s₂ from rfl, ← map_mul, ← map_inv,
      ← map_mul, h, map_pow]
  rw [Submodule.eq_top_iff']
  intro v
  have h30 : (3 : ZMod 7) ≠ 0 := by
    show ((3 : ℕ) : ZMod 7) ≠ 0
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    norm_num at h
  obtain ⟨w₀, hw₀, hw₀v⟩ :=
    X.exists_fixed_sub_mem (a := dhat) (X.restrictEquiv.symm s₃).2 (n := 3) hdhat3 h30 v
  have hxT : lhat w₀ - w₀ ∈ T := X.disp lhat (X.restrictEquiv.symm s₁).2 w₀
  have hyT : shat w₀ - w₀ ∈ T := X.disp shat (X.restrictEquiv.symm s₂).2 w₀
  have h1 : ∑ k ∈ Finset.range 4, (ℓ ^ k) ⟨lhat w₀ - w₀, hxT⟩ =
      d ⟨lhat w₀ - w₀, hxT⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_mk, ← lift_pow_apply X hℓ', ← hresd]
    simpa only [Finset.sum_range_zero, map_zero, add_zero] using
      sum_cocycle_eq (c := lhat) (i := 4) (j := 0) hw₀ (by simpa using hdc1')
  have h2 : ∑ k ∈ Finset.range 2, (s ^ k) ⟨shat w₀ - w₀, hyT⟩ =
      d ⟨shat w₀ - w₀, hyT⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_mk, ← lift_pow_apply X hs', ← hresd]
    simpa only [Finset.sum_range_zero, map_zero, add_zero] using
      sum_cocycle_eq (c := shat) (i := 2) (j := 0) hw₀ (by simpa using hdc2')
  obtain ⟨t, htℓ, hts⟩ := hcoc ⟨lhat w₀ - w₀, hxT⟩ ⟨shat w₀ - w₀, hyT⟩ h1 h2
  have hlw : lhat (w₀ - (t : V)) = w₀ - (t : V) :=
    lift_sub_fixed ℓ lhat w₀ t (by simpa using lift_pow_apply X hℓ' 1 t) htℓ
  have hsw : shat (w₀ - (t : V)) = w₀ - (t : V) :=
    lift_sub_fixed s shat w₀ t (by simpa using lift_pow_apply X hs' 1 t) hts
  have hwT : w₀ - (t : V) ∈ T := by
    refine X.mem_of_forall_fixed_lift (S := S) (v := w₀ - (t : V)) hS hidx' ?_
    intro a ha
    rcases (show a = ℓ ∨ a = s by
      simpa only [S, Set.mem_insert_iff, Set.mem_singleton_iff] using ha) with h | h
    · subst a
      simpa [lhat, show (⟨ℓ, hS ha⟩ : ↥AT) = s₁ from Subtype.ext rfl] using hlw
    · subst a
      simpa [shat, show (⟨s, hS ha⟩ : ↥AT) = s₂ from Subtype.ext rfl] using hsw
  have hw₁v : w₀ - (t : V) - v ∈ T := by
    rw [show w₀ - (t : V) - v = (w₀ - v) - (t : V) by abel]
    exact T.sub_mem hw₀v t.2
  exact (sub_sub_self (w₀ - (t : V)) v).symm ▸ T.sub_mem hwT hw₁v

end CFSG.StandardType

end
