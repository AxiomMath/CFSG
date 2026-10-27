module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Quasithin.Background.G10SixteenB

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G118

@[expose] def EndTrivial (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∀ f ∈ endOn H I, f = 0 ∨ f = 1

theorem mem_endOn_iff {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    {f : Module.End (ZMod 2) I} :
    f ∈ endOn H I ↔ ∀ (h : GLV V) (hh : conjSub h I = I), h ∈ H →
      ((restrictEquiv h I hh : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I) * f =
        f * ((restrictEquiv h I hh : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I) := by
  unfold endOn
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hf h hh hH
    exact hf _ ⟨h, hh, hH, rfl⟩
  · rintro hf _ ⟨h, hh, hH, rfl⟩
    exact hf h hh hH

section Schur

variable {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem injective_of_mem_endOn (hI : IsIrr H I) {f : Module.End (ZMod 2) I}
    (hf : f ∈ endOn H I) (hf0 : f ≠ 0) : Function.Injective f := by
  rw [mem_endOn_iff] at hf
  set J : Submodule (ZMod 2) V := (LinearMap.ker f).map I.subtype with hJ
  have hJinv : Invariant H J := by
    rintro h hH _ ⟨k, hk, rfl⟩
    have hh : conjSub h I = I := hI.1.conjSub_eq hH
    refine ⟨restrictEquiv h I hh k, ?_, rfl⟩
    have := congrArg (fun g : Module.End (ZMod 2) I => g k) (hf h hh hH)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
    have hk' : f k = 0 := hk
    show f (restrictEquiv h I hh k) = 0
    rw [← this, hk', map_zero]
  have hJle : J ≤ I := Submodule.map_subtype_le I _
  rcases hI.eq_bot_or_eq hJinv hJle with h0 | h1
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have : (x : V) ∈ J := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact Submodule.coe_eq_zero.1 this
  · exfalso
    apply hf0
    refine LinearMap.ext fun x => ?_
    have : (x : V) ∈ J := by rw [h1]; exact x.2
    obtain ⟨k, hk, hkx⟩ := this
    have : k = x := Subtype.ext hkx
    rw [← this]
    exact (LinearMap.mem_ker.1 hk)

theorem conj_mem_endOn {a : GLV V} (haI : conjSub a I = I) (ha' : ∀ h ∈ H, a⁻¹ * h * a ∈ H)
    {f : Module.End (ZMod 2) I} (hf : f ∈ endOn H I) :
    ((restrictEquiv a I haI : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I) * f *
      (((restrictEquiv a I haI).symm : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I) ∈ endOn H I := by
  rw [mem_endOn_iff] at hf ⊢
  intro h hh hH
  have hH' : a⁻¹ * h * a ∈ H := ha' h hH
  have hh' : conjSub (a⁻¹ * h * a) I = I := by
    have hinv : conjSub a⁻¹ I = I := by
      have := conjSub_inv_conjSub a I
      rwa [haI] at this
    rw [conjSub_mul, conjSub_mul, haI, hh, hinv]
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (restrictEquiv a I haI).surjective x
  have key := congrArg (fun g : Module.End (ZMod 2) I => g y) (hf _ hh' hH')
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at key
  have hA : ∀ z : ↥I, restrictEquiv a I haI (restrictEquiv (a⁻¹ * h * a) I hh' z) =
      restrictEquiv h I hh (restrictEquiv a I haI z) := by
    intro z
    apply Subtype.ext
    show a ((a⁻¹ * h * a : GLV V) (z : V)) = h (a (z : V))
    simp
  have h2 : (restrictEquiv a I haI).symm (restrictEquiv h I hh (restrictEquiv a I haI y)) =
      restrictEquiv (a⁻¹ * h * a) I hh' y := by
    apply (restrictEquiv a I haI).injective
    rw [LinearEquiv.apply_symm_apply, hA y]
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [h2, ← key, hA]

theorem endTrivial_of_finrank_raU_eq_one [Finite V] (hI : IsIrr H I)
    (h2 : 2 < Module.finrank (ZMod 2) I) {a : GLV V} (haI : conjSub a I = I)
    (ha' : ∀ h ∈ H, a⁻¹ * h * a ∈ H) (h1 : Module.finrank (ZMod 2) ↥(raU a I) = 1) :
    EndTrivial H I := by
  intro f₀ hf₀
  by_contra hnt
  push Not at hnt
  obtain ⟨hf00, hf01⟩ := hnt
  set ā : I ≃ₗ[ZMod 2] I := restrictEquiv a I haI with hā
  set T : Module.End (ZMod 2) I := commMap a I haI with hT
  have hTrk : Module.finrank (ZMod 2) ↥(LinearMap.range T) = 1 := (finrank_raU_eq haI).symm.trans h1
  by_cases hcomm : ∀ f ∈ endOn H I, (ā : I →ₗ[ZMod 2] I) * f = f * (ā : I →ₗ[ZMod 2] I)
  ·
    have hTf : ∀ y : I, f₀ (T y) = T (f₀ y) := by
      intro y
      have := congrArg (fun g : Module.End (ZMod 2) I => g y) (hcomm f₀ hf₀)
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
      show f₀ (ā y - y) = ā (f₀ y) - f₀ y
      rw [map_sub, this]
    obtain ⟨c, hc0, hc⟩ := finrank_eq_one_iff'.1 hTrk
    obtain ⟨y, hy⟩ := c.2
    have hmem : f₀ (c : I) ∈ LinearMap.range T := ⟨f₀ y, by rw [← hTf, hy]⟩
    obtain ⟨r, hr⟩ := hc ⟨f₀ (c : I), hmem⟩
    have hr' : r • (c : I) = f₀ (c : I) := congrArg Subtype.val hr
    have hinj := injective_of_mem_endOn hI hf₀ hf00
    have hc0' : (c : I) ≠ 0 := fun h => hc0 (Subtype.ext h)
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · apply hc0'
      apply hinj
      rw [← hr', zero_smul, map_zero]
    · have hsub : f₀ - 1 ∈ endOn H I := Subalgebra.sub_mem _ hf₀ (Subalgebra.one_mem _)
      have hne : f₀ - 1 ≠ 0 := sub_ne_zero.2 hf01
      have hinj' := injective_of_mem_endOn hI hsub hne
      apply hc0'
      apply hinj'
      rw [map_zero]
      show f₀ (c : I) - (c : I) = 0
      rw [← hr', one_smul, sub_self]
  ·
    push Not at hcomm
    obtain ⟨f₁, hf₁, hne₁⟩ := hcomm
    set c : Module.End (ZMod 2) I :=
      (ā : I →ₗ[ZMod 2] I) * f₁ * (ā.symm : I →ₗ[ZMod 2] I) - f₁ with hc
    have hcmem : c ∈ endOn H I :=
      Subalgebra.sub_mem _ (conj_mem_endOn haI ha' hf₁) hf₁
    have hc0 : c ≠ 0 := by
      intro h0
      apply hne₁
      refine LinearMap.ext fun x => ?_
      have h0' : (ā : I →ₗ[ZMod 2] I) * f₁ * (ā.symm : I →ₗ[ZMod 2] I) - f₁ = 0 := h0
      have := congrArg (fun g : Module.End (ZMod 2) I => g (ā x)) h0'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at this
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
      exact sub_eq_zero.1 this
    have hcinj := injective_of_mem_endOn hI hcmem hc0
    set P : Submodule (ZMod 2) I := LinearMap.ker T with hP
    have hmap : P.map c ≤ LinearMap.range T := by
      rintro _ ⟨p, hp, rfl⟩
      have hp' : T p = 0 := hp
      have hap : ā p = p := by
        have : ā p - p = 0 := hp'
        exact sub_eq_zero.1 this
      refine ⟨f₁ p, ?_⟩
      have hsymm : ā.symm p = p := by
        rw [LinearEquiv.symm_apply_eq]
        exact hap.symm
      show ā (f₁ p) - f₁ p = ā (f₁ (ā.symm p)) - f₁ p
      rw [hsymm]
    have hle : Module.finrank (ZMod 2) ↥(P.map c) ≤ 1 := by
      have := Submodule.finrank_mono hmap
      omega
    have heq : Module.finrank (ZMod 2) ↥(P.map c) = Module.finrank (ZMod 2) ↥P :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective c hcinj P)).symm
    have hrn : Module.finrank (ZMod 2) ↥(LinearMap.range T) + Module.finrank (ZMod 2) ↥P =
        Module.finrank (ZMod 2) I := LinearMap.finrank_range_add_finrank_ker T
    omega

theorem endTrivial_of_hIso {J : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hiso : HIso H J I) (hJt : EndTrivial H J) : EndTrivial H I := by
  obtain ⟨φ, hφ⟩ := hiso
  intro f hf
  rw [mem_endOn_iff] at hf
  have hφ1 : ∀ (h : GLV V) (hhJ : conjSub h J = J) (hhI : conjSub h I = I), h ∈ H → ∀ i : J,
      φ (restrictEquiv h J hhJ i) = restrictEquiv h I hhI (φ i) := by
    intro h hhJ hhI hH i
    apply Subtype.ext
    exact (hφ h hH i (restrictEquiv h J hhJ i) rfl).symm
  have hφ2 : ∀ (h : GLV V) (hhJ : conjSub h J = J) (hhI : conjSub h I = I), h ∈ H → ∀ w : I,
      φ.symm (restrictEquiv h I hhI w) = restrictEquiv h J hhJ (φ.symm w) := by
    intro h hhJ hhI hH w
    apply φ.injective
    rw [LinearEquiv.apply_symm_apply, hφ1 h hhJ hhI hH, LinearEquiv.apply_symm_apply]
  set f' : Module.End (ZMod 2) J := (φ.symm : I →ₗ[ZMod 2] J) ∘ₗ f ∘ₗ (φ : J →ₗ[ZMod 2] I) with hf'
  have hf'mem : f' ∈ endOn H J := by
    rw [mem_endOn_iff]
    intro h hhJ hH
    have hhI : conjSub h I = I := hI.conjSub_eq hH
    refine LinearMap.ext fun i => ?_
    have key := congrArg (fun g : Module.End (ZMod 2) I => g (φ i)) (hf h hhI hH)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at key
    simp only [hf', Module.End.mul_apply, LinearEquiv.coe_coe, LinearMap.coe_comp,
      Function.comp_apply]
    rw [hφ1 h hhJ hhI hH, ← key, hφ2 h hhJ hhI hH]
  have hfeq : ∀ x : I, f x = φ (f' (φ.symm x)) := by
    intro x
    simp [hf']
  rcases hJt f' hf'mem with h0 | h1
  · left
    refine LinearMap.ext fun x => ?_
    rw [hfeq, h0]
    simp
  · right
    refine LinearMap.ext fun x => ?_
    rw [hfeq, h1]
    simp

end Schur

end G118

end G11

end CFSG.Quasithin
