module

public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Quasithin.Background.RonanG1016McL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Conv

variable {K : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

theorem isTransvOn_conj [Finite V] (hKinv : Invariant K J) {γ : GLV V} (hγ : γ ∈ K) {s : GLV V}
    (hs : IsTransvOn J s) : IsTransvOn J (γ * s * γ⁻¹) := by
  obtain ⟨hs1, hfr⟩ := hs
  have hγJ : conjSub γ J = J := hKinv.conjSub_eq hγ
  have hγiJ : conjSub γ⁻¹ J = J := hKinv.conjSub_eq (K.inv_mem hγ)
  have h : conjSub (γ * s * γ⁻¹) J = J := by
    rw [conjSub_mul, conjSub_mul, hγiJ, hs1, hγJ]
  refine ⟨h, ?_⟩
  have hrange : LinearMap.range (commMap (γ * s * γ⁻¹) J h) =
      (LinearMap.range (commMap s J hs1)).map (restrictEquiv γ J hγJ : ↥J →ₗ[ZMod 2] ↥J) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨commMap s J hs1 (restrictEquiv γ⁻¹ J hγiJ i), ⟨_, rfl⟩, ?_⟩
      apply Subtype.ext
      simp only [coe_commMap, LinearEquiv.coe_coe, coe_restrictEquiv]
      simp [mul_assoc, map_sub]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨restrictEquiv γ J hγJ x, ?_⟩
      apply Subtype.ext
      simp only [coe_commMap, LinearEquiv.coe_coe, coe_restrictEquiv]
      simp [mul_assoc, map_sub]
  rw [hrange, LinearEquiv.finrank_map_eq (restrictEquiv γ J hγJ)]
  exact hfr

theorem hgen_of_le_normalClosure [Finite V] (hKinv : Invariant K J) {a : GLV V}
    (haT : IsTransvOn J a) (haK : a ∈ K)
    (hT : K ≤ normalClosure K (Subgroup.zpowers a)) :
    K ≤ Subgroup.closure {s | s ∈ K ∧ IsTransvOn J s} := by
  refine hT.trans ?_
  unfold normalClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
  have h1 : γ * a ^ n * γ⁻¹ = (γ * a * γ⁻¹) ^ n := by
    have := map_zpow (MulAut.conj γ) a n
    simpa using this
  rw [h1]
  have hgen : γ * a * γ⁻¹ ∈ Subgroup.closure {s | s ∈ K ∧ IsTransvOn J s} :=
    Subgroup.subset_closure
      ⟨K.mul_mem (K.mul_mem hγ haK) (K.inv_mem hγ), isTransvOn_conj hKinv hγ haT⟩
  exact Subgroup.zpow_mem _ hgen n

theorem sp_body (hJ : IsIrr K J) (f : LinearMap.BilinForm (ZMod 2) ↥J) (hnd : f.Nondegenerate)
    (halt : f.IsAlt)
    (h : ∀ g : ↥J ≃ₗ[ZMod 2] ↥J, g ∈ restrictRange K J hJ.1 ↔ ∀ x y, f (g x) (g y) = f x y) :
    ∃ f : LinearMap.BilinForm (ZMod 2) ↥J, (∀ x, f x x = 0) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      ((∀ k ∈ K, ∀ x y x' y' : ↥J, k (x : V) = (x' : V) → k (y : V) = (y' : V) →
          f x' y' = f x y) ∧
        ∀ g : ↥J ≃ₗ[ZMod 2] ↥J, (∀ x y, f (g x) (g y) = f x y) →
          ∃ k ∈ K, ∀ i : ↥J, k (i : V) = ((g i : ↥J) : V)) := by
  refine ⟨f, fun x => halt x, fun x hx => hnd.1 x hx, ?_, ?_⟩
  · intro k hk x y x' y' hx hy
    have hmem := restrictEquiv_mem_restrictRange hJ.1 hk
    have h1 := (h _).1 hmem x y
    have e1 : restrictEquiv k J (hJ.1.conjSub_eq hk) x = x' := Subtype.ext hx
    have e2 : restrictEquiv k J (hJ.1.conjSub_eq hk) y = y' := Subtype.ext hy
    rwa [e1, e2] at h1
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := (mem_restrictRange_iff hJ.1).1 ((h g).2 hg)
    exact ⟨k, hk, fun i => (hkg i).symm⟩

theorem orth_body (hJ : IsIrr K J) (Q : QuadraticForm (ZMod 2) ↥J)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h : ∀ g : ↥J ≃ₗ[ZMod 2] ↥J, g ∈ restrictRange K J hJ.1 ↔ ∀ x, Q (g x) = Q x) :
    ∃ q : ↥J → ZMod 2, (∀ (c : ZMod 2) x, q (c • x) = c * c * q x) ∧
      (∃ B' : LinearMap.BilinForm (ZMod 2) ↥J, (∀ x y, q (x + y) = q x + q y + B' x y) ∧
        (∀ x, (∀ y, B' x y = 0) → x = 0)) ∧
      (∀ k ∈ K, ∀ x x' : ↥J, k (x : V) = (x' : V) → q x' = q x) ∧
      ∀ g : ↥J ≃ₗ[ZMod 2] ↥J, (∀ x, q (g x) = q x) →
        ∃ k ∈ K, ∀ i : ↥J, k (i : V) = ((g i : ↥J) : V) := by
  refine ⟨⇑Q, fun c x => by rw [QuadraticMap.map_smul, smul_eq_mul],
    ⟨QuadraticMap.polarBilin Q, fun x y => ?_, fun x hx => hnd.1 x hx⟩, ?_, ?_⟩
  · rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.map_add Q]
  · intro k hk x x' hx
    have hmem := restrictEquiv_mem_restrictRange hJ.1 hk
    have h1 := (h _).1 hmem x
    have e1 : restrictEquiv k J (hJ.1.conjSub_eq hk) x = x' := Subtype.ext hx
    rwa [e1] at h1
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := (mem_restrictRange_iff hJ.1).1 ((h g).2 hg)
    exact ⟨k, hk, fun i => (hkg i).symm⟩

theorem autAll_of_top [Finite V] {H : Subgroup (GLV V)} (hJ : IsIrr K J) (hHnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hHJ : Invariant H J) (hfaith : FaithfulOn H J) (hHne : H ≠ ⊥)
    (h3 : 3 ≤ Module.finrank (ZMod 2) ↥J) (htop : restrictRange K J hJ.1 = ⊤) : AutAll H J := by
  have hsimple : IsSimpleGroup (↥J ≃ₗ[ZMod 2] ↥J) :=
    CFSG.Quasithin.MulAutTwo.isSimpleGroup_linearEquiv h3
  have hnorm : (restrictRange H J hHJ).Normal := ⟨fun g hg k => by
    obtain ⟨h₀, hh₀, hgh⟩ := (mem_restrictRange_iff hHJ).1 hg
    have hk : k ∈ restrictRange K J hJ.1 := htop ▸ Subgroup.mem_top k
    obtain ⟨k₀, hk₀, hkk⟩ := (mem_restrictRange_iff hJ.1).1 hk
    refine (mem_restrictRange_iff hHJ).2 ⟨k₀ * h₀ * k₀⁻¹, hHnorm k₀ hk₀ h₀ hh₀, fun i => ?_⟩
    have h1 : ((k.symm i : ↥J) : V) = k₀⁻¹ (i : V) := by
      have := hkk (k.symm i)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [this]
      simp
    show ((k (g (k.symm i)) : ↥J) : V) = (k₀ * h₀ * k₀⁻¹) (i : V)
    rw [hkk, hgh, h1]
    rfl⟩
  have hne : restrictRange H J hHJ ≠ ⊥ := by
    obtain ⟨⟨h₁, hh₁⟩, hh₁1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hHne
    have hh₁1 : h₁ ≠ 1 := fun h => hh₁1' (Subtype.ext h)
    have hu : ∃ u ∈ J, (h₁ : GLV V) u ≠ u := by
      by_contra hcon
      push Not at hcon
      have hc : (h₁ : GLV V) ∈ centralizerOn H J := ⟨hh₁, hcon⟩
      rw [hfaith] at hc
      exact hh₁1 (Subgroup.mem_bot.1 hc)
    obtain ⟨u, hu, hne⟩ := hu
    intro hbot
    have hmem := restrictEquiv_mem_restrictRange hHJ hh₁
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hne
    have := congrArg (fun e : ↥J ≃ₗ[ZMod 2] ↥J => ((e ⟨u, hu⟩ : ↥J) : V)) hmem
    exact this
  rcases hsimple.eq_bot_or_eq_top_of_normal (restrictRange H J hHJ) with h | h
  · exact absurd h hne
  · intro g
    have hg : g ∈ restrictRange H J hHJ := h ▸ Subgroup.mem_top g
    obtain ⟨k, hk, hkg⟩ := (mem_restrictRange_iff hHJ).1 hg
    exact ⟨k, hk, fun i => (hkg i).symm⟩

end Conv

end G11

end CFSG.Quasithin
