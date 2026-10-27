module

public import CFSG.RankThree.PartOne.S12.ReflField
public import Mathlib.LinearAlgebra.PID

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

open Module LinearMap

section Nop

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def Nop (T : V ≃ₗ[K] V) : V →ₗ[K] V := LinearMap.id - (T : V →ₗ[K] V)

theorem Nop_apply (T : V ≃ₗ[K] V) (x : V) : Nop T x = x - T x := rfl

theorem ReflData.nop_eq {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) :
    Nop T = φ.smulRight r := by
  ext x
  rw [Nop_apply, h.apply x]
  simp

theorem ReflData.nop_apply {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) (x : V) :
    Nop T x = φ x • r := by
  rw [h.nop_eq]
  rfl

theorem ReflData.nop_comp_nop {T T' : V ≃ₗ[K] V} {r r' : V} {φ φ' : V →ₗ[K] K}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') :
    Nop T ∘ₗ Nop T' = (φ r') • φ'.smulRight r := by
  ext x
  simp only [LinearMap.comp_apply, h'.nop_apply, map_smul, h.nop_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_eq_mul, smul_smul]
  rw [mul_comm]

theorem ReflData.trace_nop [FiniteDimensional K V] {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K}
    (h : ReflData T r φ) : LinearMap.trace K V (Nop T) = 2 := by
  rw [h.nop_eq, LinearMap.trace_smulRight, h.pair]

theorem ReflData.trace_nop_comp_nop [FiniteDimensional K V] {T T' : V ≃ₗ[K] V} {r r' : V}
    {φ φ' : V →ₗ[K] K} (h : ReflData T r φ) (h' : ReflData T' r' φ') :
    LinearMap.trace K V (Nop T ∘ₗ Nop T') = φ r' * φ' r := by
  rw [h.nop_comp_nop h', map_smul, LinearMap.trace_smulRight, smul_eq_mul]

theorem nop_conj (g T : V ≃ₗ[K] V) :
    Nop (g * T * g⁻¹) = (g : V →ₗ[K] V) ∘ₗ Nop T ∘ₗ ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  ext x
  simp only [Nop_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_sub]
  have : g ((g⁻¹ : V ≃ₗ[K] V) x) = x := by
    show g (g.symm x) = x
    exact g.apply_symm_apply x
  rw [this]

end Nop

section RSet

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure IsRSet (𝒟 : Finset (V ≃ₗ[K] V)) : Prop where
  refl : ∀ T ∈ 𝒟, ∃ (r : V) (φ : V →ₗ[K] K), ReflData T r φ
  conj : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T * S * T⁻¹ ∈ 𝒟
  ord : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → (T * S) ^ 1 = 1 ∨ (T * S) ^ 2 = 1 ∨ (T * S) ^ 3 = 1

theorem IsRSet.dich [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ 𝒟) (hS : S ∈ 𝒟)
    (hne : T ≠ S) :
    (Nop T ∘ₗ Nop S = 0 ∧ Nop S ∘ₗ Nop T = 0 ∧ T * S = S * T) ∨
    (LinearMap.trace K V (Nop T ∘ₗ Nop S) = 1 ∧ Nop T ∘ₗ Nop S ≠ 0 ∧
      Nop S ∘ₗ Nop T ≠ 0 ∧ T * S ≠ S * T) := by
  obtain ⟨r, φ, hd⟩ := h.refl T hT
  obtain ⟨r', φ', hd'⟩ := h.refl S hS
  rcases dichotomy h2 h3 hd hd' hne (h.ord T hT S hS hne) with ⟨h1, h1'⟩ | hb
  · left
    refine ⟨?_, ?_, commute_of_orth hd hd' h1 h1'⟩
    · rw [hd.nop_comp_nop hd', h1, zero_smul]
    · rw [hd'.nop_comp_nop hd, h1', zero_smul]
  · right
    have ht : LinearMap.trace K V (Nop T ∘ₗ Nop S) = 1 := by
      rw [hd.trace_nop_comp_nop hd']
      exact hb
    have ht' : LinearMap.trace K V (Nop S ∘ₗ Nop T) = 1 := by
      rw [hd'.trace_nop_comp_nop hd, mul_comm]
      exact hb
    refine ⟨ht, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at ht
      exact zero_ne_one ht
    · intro h0
      rw [h0, map_zero] at ht'
      exact zero_ne_one ht'
    · intro hc
      obtain ⟨e1, e2⟩ := commute_orth h2 h3 hd hd' hne hc
      rw [e1, zero_mul] at hb
      exact zero_ne_one hb

@[expose] def Conn (𝒟 : Finset (V ≃ₗ[K] V)) : Prop :=
  ∀ P : Finset (V ≃ₗ[K] V), P ⊆ 𝒟 → P.Nonempty →
    (∀ T ∈ P, ∀ S ∈ 𝒟, T * S ≠ S * T → S ∈ P) → P = 𝒟

@[expose] def Ssum (𝒟 : Finset (V ≃ₗ[K] V)) : V →ₗ[K] V := ∑ T ∈ 𝒟, Nop T

@[expose] def Uspan (𝒟 : Finset (V ≃ₗ[K] V)) : Submodule K V :=
  Submodule.span K {x | ∃ T ∈ 𝒟, x ∈ LinearMap.range (Nop T)}

theorem Ssum_apply (𝒟 : Finset (V ≃ₗ[K] V)) (x : V) : Ssum 𝒟 x = ∑ T ∈ 𝒟, Nop T x := by
  unfold Ssum
  rw [LinearMap.sum_apply]

theorem Ssum_conj {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T₀ : V ≃ₗ[K] V} (hT : T₀ ∈ 𝒟)
    (x : V) : Ssum 𝒟 (T₀ x) = T₀ (Ssum 𝒟 x) := by
  have hinj : Function.Injective (fun T : V ≃ₗ[K] V => T₀ * T * T₀⁻¹) := fun a b hab =>
    mul_left_cancel (mul_right_cancel hab)
  have himg : 𝒟.image (fun T : V ≃ₗ[K] V => T₀ * T * T₀⁻¹) = 𝒟 := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hy
      exact h.conj T₀ hT S hS
    · rw [Finset.card_image_of_injective _ hinj]
  have hsum : ∑ T ∈ 𝒟, Nop (T₀ * T * T₀⁻¹) (T₀ x) = ∑ T ∈ 𝒟, Nop T (T₀ x) := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  have hterm : ∀ T : V ≃ₗ[K] V, Nop (T₀ * T * T₀⁻¹) (T₀ x) = T₀ (Nop T x) := by
    intro T
    rw [nop_conj]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (T₀⁻¹ : V ≃ₗ[K] V) (T₀ x) = x := by
      show T₀.symm (T₀ x) = x
      exact T₀.symm_apply_apply x
    rw [this]
  rw [Ssum_apply, Ssum_apply, map_sum]
  simp only [← hterm]
  exact hsum.symm

theorem ReflData.exists_kappa (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K}
    (h : ReflData T r φ) (C : V →ₗ[K] V) (hC : ∀ x, C (T x) = T (C x)) :
    ∃ κ : K, C ∘ₗ Nop T = κ • Nop T := by
  have hN : ∀ x, C (Nop T x) = Nop T (C x) := by
    intro x
    simp only [Nop_apply, map_sub, hC]
  set x₀ : V := (2 : K)⁻¹ • r with hx₀
  have hφ : φ x₀ = 1 := by
    rw [hx₀, map_smul, h.pair, smul_eq_mul, inv_mul_cancel₀ h2]
  have hCr : C r = φ (C x₀) • r := by
    have := hN x₀
    rw [h.nop_apply, h.nop_apply, hφ, one_smul] at this
    exact this
  refine ⟨φ (C x₀), ?_⟩
  ext x
  simp only [LinearMap.comp_apply, h.nop_apply, map_smul, hCr, LinearMap.smul_apply, smul_smul]
  rw [mul_comm]

theorem kappa_unique {N : V →ₗ[K] V} (hN : N ≠ 0) {κ κ' : K} (h : κ • N = κ' • N) : κ = κ' := by
  by_contra hne
  have h0 : (κ - κ') • N = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact hne (sub_eq_zero.1 h1)
  · exact hN h1

theorem kappa_eq_of_noncomm {T S : V ≃ₗ[K] V} (C : V →ₗ[K] V) (hCT : ∀ x, C (T x) = T (C x))
    {κ κ' : K} (hκ : C ∘ₗ Nop T = κ • Nop T) (hκ' : C ∘ₗ Nop S = κ' • Nop S)
    (hne : Nop T ∘ₗ Nop S ≠ 0) : κ = κ' := by
  have hCN : C ∘ₗ Nop T = Nop T ∘ₗ C := by
    ext x
    simp only [LinearMap.comp_apply, Nop_apply, map_sub, hCT]
  have e1 : C ∘ₗ (Nop T ∘ₗ Nop S) = κ • (Nop T ∘ₗ Nop S) := by
    rw [← LinearMap.comp_assoc, hκ]
    rfl
  have e2 : C ∘ₗ (Nop T ∘ₗ Nop S) = κ' • (Nop T ∘ₗ Nop S) := by
    rw [← LinearMap.comp_assoc, hCN, LinearMap.comp_assoc, hκ', LinearMap.comp_smul]
  exact kappa_unique hne (e1.symm.trans e2)

theorem exists_const_kappa [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hconn : Conn 𝒟) (hne : 𝒟.Nonempty)
    (C : V →ₗ[K] V) (hC : ∀ T ∈ 𝒟, ∀ x, C (T x) = T (C x)) :
    ∃ κ : K, ∀ T ∈ 𝒟, C ∘ₗ Nop T = κ • Nop T := by
  obtain ⟨T₀, hT₀⟩ := hne
  obtain ⟨r, φ, hd⟩ := h.refl T₀ hT₀
  obtain ⟨κ₀, hκ₀⟩ := hd.exists_kappa h2 C (hC T₀ hT₀)
  have hP : 𝒟.filter (fun T => C ∘ₗ Nop T = κ₀ • Nop T) = 𝒟 := by
    refine hconn _ (Finset.filter_subset _ _) ⟨T₀, Finset.mem_filter.2 ⟨hT₀, hκ₀⟩⟩ ?_
    intro T hT S hS hTS
    have hTm := (Finset.mem_filter.1 hT)
    obtain ⟨r', φ', hd'⟩ := h.refl S hS
    obtain ⟨κ₁, hκ₁⟩ := hd'.exists_kappa h2 C (hC S hS)
    have hTSne : T ≠ S := fun e => hTS (by rw [e])
    have hnc : Nop T ∘ₗ Nop S ≠ 0 := by
      rcases h.dich h2 h3 hTm.1 hS hTSne with ⟨-, -, hc⟩ | ⟨-, hn, -, -⟩
      · exact absurd hc hTS
      · exact hn
    have hk : κ₀ = κ₁ := by
      have := kappa_eq_of_noncomm C (hC T hTm.1) hTm.2 hκ₁ hnc
      exact this
    exact Finset.mem_filter.2 ⟨hS, by rw [hκ₁, hk]⟩
  refine ⟨κ₀, fun T hT => ?_⟩
  have hTP : T ∈ 𝒟.filter (fun T => C ∘ₗ Nop T = κ₀ • Nop T) := by rw [hP]; exact hT
  exact (Finset.mem_filter.1 hTP).2

theorem trace_identity [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hconn : Conn 𝒟) (hne : 𝒟.Nonempty) :
    ∃ lam : K, (∀ T ∈ 𝒟, Ssum 𝒟 ∘ₗ Nop T = lam • Nop T) ∧
      (∀ T ∈ 𝒟, 2 * lam = 4 + ((𝒟.filter fun S => T * S ≠ S * T).card : K)) ∧
      ((finrank K (Uspan 𝒟) : K) * lam = 2 * 𝒟.card) ∧
      (∀ y ∈ Uspan 𝒟, Ssum 𝒟 y = lam • y) := by
  obtain ⟨lam, hlam⟩ := exists_const_kappa h2 h3 h hconn hne (Ssum 𝒟)
    (fun T hT x => Ssum_conj h hT x)
  have hscalar : ∀ y ∈ Uspan 𝒟, Ssum 𝒟 y = lam • y := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro x ⟨T, hT, z, rfl⟩
      have := LinearMap.congr_fun (hlam T hT) z
      simpa using this
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, smul_add]
    · intro a x _ hx
      rw [map_smul, hx, smul_comm]
  refine ⟨lam, hlam, ?_, ?_, hscalar⟩
  · intro T hT
    obtain ⟨r, φ, hd⟩ := h.refl T hT
    have htr := congrArg (LinearMap.trace K V) (hlam T hT)
    rw [map_smul, hd.trace_nop, smul_eq_mul] at htr
    have hcomp : Ssum 𝒟 ∘ₗ Nop T = ∑ S ∈ 𝒟, Nop S ∘ₗ Nop T := by
      ext x
      simp only [LinearMap.comp_apply, Ssum_apply, LinearMap.sum_apply]
    have hterm : ∀ S ∈ 𝒟, LinearMap.trace K V (Nop S ∘ₗ Nop T) =
        (if S = T then (4 : K) else 0) + (if T * S ≠ S * T then 1 else 0) := by
      intro S hS
      by_cases hST : S = T
      · subst hST
        obtain ⟨r', φ', hd'⟩ := h.refl S hS
        rw [hd'.trace_nop_comp_nop hd', hd'.pair]
        simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
        norm_num
      · rcases h.dich h2 h3 hS hT hST with ⟨h0, -, hc⟩ | ⟨ht, -, -, hnc⟩
        · have h0' : T * S = S * T := hc.symm
          have : (T * S ≠ S * T) = False := by simp [h0']
          rw [h0, map_zero]
          simp [hST, h0']
        · have h0' : T * S ≠ S * T := fun e => hnc e.symm
          rw [ht]
          simp [hST, h0']
    rw [hcomp, map_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_ite_eq' 𝒟 T (fun _ => (4 : K)), Finset.sum_boole] at htr
    simp only [hT, ite_true] at htr
    linear_combination -htr
  · set U := Uspan 𝒟 with hU
    have hmem : ∀ x, Ssum 𝒟 x ∈ U := by
      intro x
      rw [Ssum_apply]
      refine Submodule.sum_mem _ fun T hT => ?_
      exact Submodule.subset_span ⟨T, hT, LinearMap.mem_range_self _ x⟩
    have hres : (Ssum 𝒟).restrict (fun x _ => hmem x) = lam • LinearMap.id := by
      ext ⟨y, hy⟩
      exact hscalar y hy
    have htr := LinearMap.trace_restrict_eq_of_forall_mem U (Ssum 𝒟) hmem
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
    have hsum : LinearMap.trace K V (Ssum 𝒟) = 2 * 𝒟.card := by
      unfold Ssum
      rw [map_sum]
      have : ∀ T ∈ 𝒟, LinearMap.trace K V (Nop T) = 2 := by
        intro T hT
        obtain ⟨r, φ, hd⟩ := h.refl T hT
        exact hd.trace_nop
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [← hsum, ← htr, mul_comm]

end RSet

end ReflF

end CFSG.RankThree.PartOne
