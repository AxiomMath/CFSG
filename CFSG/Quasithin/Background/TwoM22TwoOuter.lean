module

public import CFSG.Quasithin.Background.TwoM22TwoDefs
public import CFSG.Quasithin.Background.SmithB45HM22Cover
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvOut

public section

namespace CFSG.GroupTheory

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem exists_inner_mul_of_not_mem_inner_of_card_outer_center_le_two
    {P : Type*} [Group P] [Finite P] (hP : Group.IsPerfect P)
    (hOut : Nat.card (Outer (P ⧸ Subgroup.center P)) ≤ 2)
    {α β : MulAut P}
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P)
    (hβ : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P) :
    ∃ g : P, α * β⁻¹ = MulAut.conj g := by
  haveI : Group.IsPerfect P := hP
  have hcenter_iff : ∀ γ : MulAut P,
      centerQuotientHom P γ ∈ inner (P ⧸ Subgroup.center P) ↔ γ ∈ inner P := by
    intro γ
    constructor
    · rintro ⟨xbar, hx⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) xbar
      have hγ : centerQuotientHom P γ = centerQuotientHom P (MulAut.conj x) := by
        rw [centerQuotient_conj]
        exact hx.symm
      exact ⟨x, (centerQuotientHom_injective P hγ).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk' (Subgroup.center P) x, (centerQuotient_conj x).symm⟩
  have hmap : ∀ γ : MulAut P,
      centerQuotientOuterHom P (QuotientGroup.mk' (inner P) γ) =
        QuotientGroup.mk' (inner (P ⧸ Subgroup.center P)) (centerQuotientHom P γ) := by
    intro γ
    rw [centerQuotientOuterHom, QuotientGroup.map_mk']
    rfl
  have hqα : centerQuotientOuterHom P (QuotientGroup.mk' (inner P) α) ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk' (inner (P ⧸ Subgroup.center P)) (centerQuotientHom P α) = 1 := by
      rw [← hmap α]
      exact h
    exact hα ((hcenter_iff α).1 ((QuotientGroup.eq_one_iff _).mp h1))
  have hqβ : centerQuotientOuterHom P (QuotientGroup.mk' (inner P) β) ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk' (inner (P ⧸ Subgroup.center P)) (centerQuotientHom P β) = 1 := by
      rw [← hmap β]
      exact h
    exact hβ ((hcenter_iff β).1 ((QuotientGroup.eq_one_iff _).mp h1))
  have hqeq : centerQuotientOuterHom P (QuotientGroup.mk' (inner P) α) =
      centerQuotientOuterHom P (QuotientGroup.mk' (inner P) β) := by
    have hcard : Nat.card (Outer (P ⧸ Subgroup.center P)) = 2 := by
      have hne1 : Nat.card (Outer (P ⧸ Subgroup.center P)) ≠ 1 := by
        intro h1
        haveI : Subsingleton (Outer (P ⧸ Subgroup.center P)) :=
          (Nat.card_eq_one_iff_unique.mp h1).1
        exact hqα (Subsingleton.elim _ 1)
      have hpos : 0 < Nat.card (Outer (P ⧸ Subgroup.center P)) := Nat.card_pos
      omega
    obtain ⟨y, hy, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : Outer (P ⧸ Subgroup.center P))).mp hcard
    exact (huniq _ hqα).trans (huniq _ hqβ).symm
  have hclass : QuotientGroup.mk' (inner P) α = QuotientGroup.mk' (inner P) β :=
    centerQuotient_outer_injective P (by rw [hmap α, hmap β]; exact hqeq)
  have hmem : α * β⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P := by
    have h1 : QuotientGroup.mk' (inner P) (α * β⁻¹) = 1 := by
      rw [map_mul, map_inv, hclass, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

end CFSG.GroupTheory

namespace CFSG.Quasithin.TwoM22

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem card_eq_two_mul_card_M22_of_central_extension
    {E : Type} [Group E] [Finite E] (q : E →* ↥NativeSporadic.M22)
    (hq : Function.Surjective q) (hker : q.ker = Subgroup.center E)
    (hZ : Nat.card (Subgroup.center E) = 2) : Nat.card E = 2 * 443520 := by
  have hquot : Nat.card (E ⧸ Subgroup.center E) = 443520 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  calc Nat.card E = Nat.card (E ⧸ Subgroup.center E) * Nat.card (Subgroup.center E) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = 443520 * 2 := by rw [hquot, hZ]
    _ = 2 * 443520 := by norm_num

theorem mul_self_eq_one_of_isTwoM22TwoModel
    {W : Type} [Group W] [Finite W] {M : Subgroup W} {T : W} (hmod : IsTwoM22TwoModel M T)
    {N : Type} [Group N] [Finite N] (D : Subgroup N) [D.Normal] (hidx : D.index = 2)
    (hperf : Group.IsPerfect ↥D) (q : ↥D →* ↥CFSG.Blueprint.NativeSporadic.M22)
    (hq : Function.Surjective q) (hker : q.ker = Subgroup.center ↥D)
    (hZ : Nat.card (Subgroup.center ↥D) = 2)
    (hC : ∀ g : N, (∀ d ∈ D, g * d = d * g) → g ∈ D)
    {s : N} (hsD : s ∉ D) (hs : s * s = 1) {n : N} (hnD : n ∉ D)
    (hn : ∀ d ∈ D, n * n * d = d * (n * n)) : n * n = 1 := by
  haveI : Group.IsPerfect ↥D := hperf
  haveI : Group.IsPerfect ↥M := hmod.perfect
  obtain ⟨qM, hqM, hkerM⟩ := hmod.exists_quot
  have hcardD : Nat.card ↥D = 2 * 443520 :=
    card_eq_two_mul_card_M22_of_central_extension q hq hker hZ
  have hcardM : Nat.card ↥M = 2 * 443520 :=
    card_eq_two_mul_card_M22_of_central_extension qM hqM hkerM hmod.card_center
  obtain ⟨θ⟩ := CFSG.Quasithin.HM22.nonempty_mulEquiv_of_card_eq q hq hker.le
    qM hqM hkerM.le (hcardD.trans hcardM.symm) (by rw [hcardD]; norm_num)
  have houtM22 : Nat.card (Outer ↥NativeSporadic.M22) ≤ 2 :=
    CFSG.GH74.GLS.IVK.GHInv.card_outer_le_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
  have eM : ↥M ⧸ Subgroup.center ↥M ≃* ↥NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hkerM).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective qM hqM)
  have houtMZ : Nat.card (Outer (↥M ⧸ Subgroup.center ↥M)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eM).toEquiv]
    exact houtM22
  let γ : N →* MulAut ↥M :=
    (MulAut.congr θ).toMonoidHom.comp (MulAut.conjNormal (H := D))
  have hγ_eval (d : ↥D) :
      γ s (θ d) = θ ((MulAut.conjNormal (H := D) s) d) := by
    change (MulAut.congr θ) (MulAut.conjNormal s) (θ d) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply]
  let τHom : ↥M →* ↥M :=
    { toFun := fun m => ⟨T * (m : W) * T⁻¹, hmod.conj_T_mem m m.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have τHom_inj : Function.Injective τHom := by
    intro x y hxy
    have h : T * (x : W) * T⁻¹ = T * (y : W) * T⁻¹ :=
      congrArg (fun z : ↥M => (z : W)) hxy
    apply Subtype.ext
    calc (x : W) = T⁻¹ * (T * (x : W) * T⁻¹) * T := by group
      _ = T⁻¹ * (T * (y : W) * T⁻¹) * T := by rw [h]
      _ = (y : W) := by group
  let τ : MulAut ↥M := MulEquiv.ofBijective τHom (Finite.injective_iff_bijective.mp τHom_inj)
  have hτ_apply (m : ↥M) : ((τ m : ↥M) : W) = T * (m : W) * T⁻¹ := rfl
  have hγ_outer : γ s ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M := by
    rintro ⟨m₀, hm₀⟩
    let d₀ : ↥D := θ.symm m₀
    have hconj : ∀ d : ↥D,
        MulAut.conjNormal (H := D) s d = MulAut.conjNormal (H := D) d₀ d := by
      intro d
      apply θ.injective
      calc θ (MulAut.conjNormal (H := D) s d) = γ s (θ d) := (hγ_eval d).symm
        _ = (MulAut.conj m₀) (θ d) := by rw [hm₀]
        _ = m₀ * θ d * m₀⁻¹ := rfl
        _ = θ d₀ * θ d * (θ d₀)⁻¹ := by
          rw [show m₀ = θ d₀ from (MulEquiv.apply_symm_apply θ m₀).symm]
        _ = θ d₀ * θ d * θ d₀⁻¹ := by rw [map_inv]
        _ = θ (d₀ * d) * θ d₀⁻¹ := by rw [map_mul]
        _ = θ (d₀ * d * d₀⁻¹) := by
          rw [← map_mul]
        _ = θ ((MulAut.conjNormal (H := D) d₀) d) := by
          congr 1
    have hcentral : ∀ d ∈ D, (d₀⁻¹ * s) * d = d * (d₀⁻¹ * s) := by
      intro d hd
      have h := congrArg (fun x : ↥D => (x : N)) (hconj ⟨d, hd⟩)
      simp only [MulAut.conjNormal_apply, Subgroup.coe_inv] at h
      calc ((d₀⁻¹ * s) * d : N) = (↑d₀)⁻¹ * (s * ↑d * s⁻¹) * s := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = (↑d₀)⁻¹ * (↑d₀ * ↑d * (↑d₀)⁻¹) * s := by rw [h]
        _ = (d * (d₀⁻¹ * s) : N) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
    have hs_mem : d₀⁻¹ * s ∈ D := hC (d₀⁻¹ * s) hcentral
    apply hsD
    have h1 : (d₀ : N) * (d₀⁻¹ * s) ∈ D := D.mul_mem d₀.2 hs_mem
    simpa using h1
  have hτ_outer : τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M := by
    rintro ⟨m₀, hm₀⟩
    have hcent : ∀ x ∈ M, (m₀⁻¹ * T) * x = x * (m₀⁻¹ * T) := by
      intro x hx
      have h := congrArg (fun f : MulAut ↥M => ((f ⟨x, hx⟩ : ↥M) : W)) hm₀
      simp only [hτ_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc ((m₀⁻¹ * T) * x : W) = (↑m₀)⁻¹ * (T * x * T⁻¹) * T := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = (↑m₀)⁻¹ * ((↑m₀) * x * (↑m₀)⁻¹) * T := by rw [← h]
        _ = (x * (m₀⁻¹ * T) : W) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
    have hmem : m₀⁻¹ * T ∈ M := hmod.mem_of_commute (m₀⁻¹ * T) hcent
    apply hmod.T_not_mem
    have h1 : (m₀ : W) * (m₀⁻¹ * T) ∈ M := M.mul_mem m₀.2 hmem
    simpa using h1
  obtain ⟨m₀, hm₀⟩ :=
    CFSG.GroupTheory.exists_inner_mul_of_not_mem_inner_of_card_outer_center_le_two
      hmod.perfect houtMZ hγ_outer hτ_outer
  have hγ_eq : γ s = MulAut.conj m₀ * τ := by
    calc γ s = (γ s * τ⁻¹) * τ := by group
      _ = MulAut.conj m₀ * τ := by rw [hm₀]
  let u : W := (m₀ : W) * T
  have hγ_conj (x : ↥M) : ((γ s x : ↥M) : W) = u * (x : W) * u⁻¹ := by
    rw [hγ_eq, MulAut.mul_apply, MulAut.conj_apply]
    change (m₀ : W) * ((τ x : ↥M) : W) * (m₀ : W)⁻¹ = u * (x : W) * u⁻¹
    rw [hτ_apply]
    simp only [u]
    group
  have hα_sq : γ s * γ s = 1 := by
    calc γ s * γ s = γ (s * s) := by rw [map_mul]
      _ = γ 1 := by rw [hs]
      _ = 1 := map_one γ
  have hu2_central : ∀ x : ↥M, u * u * (x : W) = (x : W) * (u * u) := by
    intro x
    have h1 : ((γ s (γ s x) : ↥M) : W) = (x : W) := by
      have h := congrArg (fun f : MulAut ↥M => f x) hα_sq
      simpa using congrArg (fun z : ↥M => (z : W)) h
    have h2 : u * (u * (x : W) * u⁻¹) * u⁻¹ = (x : W) := by
      rw [hγ_conj (γ s x), hγ_conj x] at h1
      exact h1
    have h3 : u * u * (x : W) * u⁻¹ * u⁻¹ = (x : W) := by
      calc u * u * (x : W) * u⁻¹ * u⁻¹ = u * (u * (x : W) * u⁻¹) * u⁻¹ := by group
        _ = (x : W) := h2
    calc u * u * (x : W) = (u * u * (x : W) * u⁻¹ * u⁻¹) * (u * u) := by group
      _ = (x : W) * (u * u) := by rw [h3]
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hmod.mul_self_T
  have hu2_eq : u * u = (m₀ : W) * (T * (m₀ : W) * T⁻¹) := by
    change (m₀ : W) * T * ((m₀ : W) * T) = _
    rw [hTinv]
    group
  have hu2eq1 : u * u = 1 := by
    have h : (m₀ : W) * T * ((m₀ : W) * T) = 1 := by
      apply hmod.mul_self_eq_one m₀ m₀.2
      intro x hx
      simpa only [u] using hu2_central ⟨x, hx⟩
    simpa only [u] using h
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2eq1
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hnsD : n * s ∈ D := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hnD hsD
  let d₁ : ↥D := ⟨n * s, hnsD⟩
  have hsd_mem : s * (d₁ : N) * s ∈ D := by
    have h := (inferInstance : D.Normal).conj_mem (d₁ : N) d₁.2 s
    rwa [hsinv] at h
  have hnnD : n * n ∈ D :=
    (Subgroup.mul_mem_iff_of_index_two hidx (a := n) (b := n)).mpr Iff.rfl
  have hn_eq : n = (d₁ : N) * s := by
    change n = (n * s) * s
    rw [mul_assoc, hs, mul_one]
  have hnn_eq : n * n = (d₁ : N) * (s * (d₁ : N) * s) := by
    rw [hn_eq]
    group
  have hsd_eq : s * (d₁ : N) * s =
      (((MulAut.conjNormal (H := D) s) d₁ : ↥D) : N) := by
    rw [MulAut.conjNormal_apply]
    simp [hsinv]
  let x₀ : ↥M := θ d₁
  have hθ_nn : θ ⟨n * n, hnnD⟩ = x₀ * γ s x₀ := by
    have h1 : (⟨n * n, hnnD⟩ : ↥D) = d₁ * ⟨s * (d₁ : N) * s, hsd_mem⟩ := by
      apply Subtype.ext
      exact hnn_eq
    rw [h1, map_mul]
    congr 1
    rw [hγ_eval]
    congr 1
    apply Subtype.ext
    exact hsd_eq
  have hθ_central : ∀ y : ↥M, θ ⟨n * n, hnnD⟩ * y = y * θ ⟨n * n, hnnD⟩ := by
    intro y
    obtain ⟨d, rfl⟩ := θ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hn d d.2)
  let m₁ : ↥M := x₀ * m₀
  have hsq_eq : ((θ ⟨n * n, hnnD⟩ : ↥M) : W) =
      ((m₁ : W) * T) * ((m₁ : W) * T) := by
    rw [hθ_nn]
    change (x₀ : W) * ((γ s x₀ : ↥M) : W) = ((m₁ : W) * T) * ((m₁ : W) * T)
    rw [hγ_conj x₀, hu_inv]
    simp only [m₁, u, Subgroup.coe_mul]
    group
  have hsq_one : ((m₁ : W) * T) * ((m₁ : W) * T) = 1 := by
    apply hmod.mul_self_eq_one m₁ m₁.2
    intro x hx
    rw [← hsq_eq]
    exact congrArg (fun z : ↥M => (z : W)) (hθ_central ⟨x, hx⟩)
  have hθ_one : θ ⟨n * n, hnnD⟩ = 1 := by
    apply Subtype.ext
    rw [hsq_eq, hsq_one]
    rfl
  have hnn_one : (⟨n * n, hnnD⟩ : ↥D) = 1 :=
    θ.injective (hθ_one.trans (map_one θ).symm)
  exact congrArg Subtype.val hnn_one

end CFSG.Quasithin.TwoM22
