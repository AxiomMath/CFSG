module

public import CFSG.RankThree.PartTwo.Toolkit.H1
public import Certificates.Certificate8173

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

variable {Y : Type*} [Group Y] {D : Type*} [AddCommGroup D] [Module (ZMod 3) D]

theorem exists_complement_of_sub (ρ : Representation (ZMod 3) Y D) (W : Submodule (ZMod 3) D)
    {σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)} (hσ : AllCoboundary σ)
    (hW : SubmoduleIso ρ W σ) (hQ : Module.finrank (ZMod 3) (D ⧸ W) = 1)
    (htriv : ∀ (y : Y) (d : D), ρ y d - d ∈ W) :
    ∃ W' : Submodule (ZMod 3) D, IsYSubmodule ρ W' ∧ IsCompl W W' := by
  obtain ⟨f, hf, hrange, hfσ⟩ := hW
  obtain ⟨x, hx0, hxspan⟩ := finrank_eq_one_iff'.1 hQ
  obtain ⟨d₀, rfl⟩ := W.mkQ_surjective x
  have hd₀ : d₀ ∉ W := fun h => hx0 ((Submodule.Quotient.mk_eq_zero W).2 h)
  have hmem : ∀ y : Y, ∃ v, f v = ρ y d₀ - d₀ := fun y => by
    have := htriv y d₀
    rw [← hrange] at this
    exact this
  choose c hc using hmem
  have hcoc : IsCocycle σ c := by
    intro y z
    apply hf
    rw [map_add, hfσ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel
  obtain ⟨m, hm⟩ := hσ c hcoc
  set d₁ := d₀ - f m with hd₁
  have hfix : ∀ y : Y, ρ y d₁ = d₁ := fun y => by
    have h1 : f (c y) = f (σ y m) - f m := by rw [hm, map_sub]
    rw [hc, hfσ] at h1
    rw [hd₁, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 h1
  have hd₁W : d₁ ∉ W := fun h => hd₀ (by
    have : d₀ = d₁ + f m := by rw [hd₁]; abel
    rw [this]
    exact W.add_mem h (hrange ▸ LinearMap.mem_range_self f m))
  refine ⟨Submodule.span (ZMod 3) {d₁}, fun y w hw => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d₁)
  · rw [isCompl_iff, Submodule.disjoint_def, codisjoint_iff]
    refine ⟨fun w hwW hw => ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      by_cases ha : a = 0
      · rw [ha, zero_smul]
      · exact absurd (by simpa [ha] using W.smul_mem a⁻¹ hwW) hd₁W
    · rw [eq_top_iff]
      intro d _
      obtain ⟨a, ha⟩ := hxspan (W.mkQ d)
      have hfm : W.mkQ (f m) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (hrange ▸ LinearMap.mem_range_self f m)
      have hmk : W.mkQ d₁ = W.mkQ d₀ := by
        rw [hd₁, map_sub, hfm, sub_zero]
      have hdiff : d - a • d₁ ∈ W := by
        refine (Submodule.Quotient.mk_eq_zero W).1 ?_
        change W.mkQ (d - a • d₁) = 0
        rw [map_sub, map_smul, hmk, ha, sub_self]
      rw [Submodule.mem_sup]
      exact ⟨d - a • d₁, hdiff, a • d₁, Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self d₁), by abel⟩

theorem eq_dotProduct (L : (Fin 3 → ZMod 3) →ₗ[ZMod 3] ZMod 3) (v : Fin 3 → ZMod 3) :
    L v = (fun i => L (Pi.single i 1)) ⬝ᵥ v := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 3) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, dotProduct, smul_eq_mul, mul_comm]

theorem transpose_mulVec_dotProduct (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (x v : Fin 3 → ZMod 3) : (Mᵀ *ᵥ x) ⬝ᵥ v = x ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem eq_of_dotProduct_eq {x x' : Fin 3 → ZMod 3} (h : ∀ v, x ⬝ᵥ v = x' ⬝ᵥ v) : x = x' := by
  ext j
  have := h (Pi.single j 1)
  rwa [dotProduct_single, dotProduct_single, mul_one, mul_one] at this

theorem exists_complement_of_quot (ρ : Representation (ZMod 3) Y D) (W : Submodule (ZMod 3) D)
    {σ τ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)} (Mat : Y → Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hσM : ∀ (y : Y) (v : Fin 3 → ZMod 3), σ y v = Mat y *ᵥ v)
    (hτM : ∀ (y : Y) (v : Fin 3 → ZMod 3), τ y v = (Mat y⁻¹)ᵀ *ᵥ v) (hτ : AllCoboundary τ)
    (hW1 : Module.finrank (ZMod 3) W = 1) (hWtriv : ∀ y : Y, ∀ w ∈ W, ρ y w = w)
    (hQ : QuotientIso ρ W σ) :
    ∃ W' : Submodule (ZMod 3) D, IsYSubmodule ρ W' ∧ IsCompl W W' := by
  obtain ⟨q, hqs, hker, hqρ⟩ := hQ
  obtain ⟨w, hw0, hwspan⟩ := finrank_eq_one_iff'.1 hW1
  have hw₀ : (w : D) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one (ZMod 3) hw₀
  have hWeq : ∀ x ∈ W, x = lam x • (w : D) := fun x hx => by
    obtain ⟨a, ha⟩ := hwspan ⟨x, hx⟩
    have hx' : x = a • (w : D) := (congrArg Subtype.val ha).symm
    rw [hx', map_smul, hlam, smul_eq_mul, mul_one]
  obtain ⟨s₀, hs₀⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hqs₀ : ∀ v, q (s₀ v) = v := fun v => LinearMap.congr_fun hs₀ v
  have hqw : q (w : D) = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact w.2
  have he : ∀ (y : Y) (v : Fin 3 → ZMod 3), s₀ v - ρ y (s₀ (σ y⁻¹ v)) ∈ W := fun y v => by
    rw [← hker, LinearMap.mem_ker, map_sub, hqρ, hqs₀, hqs₀, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply, sub_self]
  have hemul : ∀ (y z : Y) (v : Fin 3 → ZMod 3),
      s₀ v - ρ (y * z) (s₀ (σ (y * z)⁻¹ v)) =
        (s₀ v - ρ y (s₀ (σ y⁻¹ v))) + (s₀ (σ y⁻¹ v) - ρ z (s₀ (σ z⁻¹ (σ y⁻¹ v)))) := by
    intro y z v
    have hW := hWtriv y _ (he z (σ y⁻¹ v))
    rw [map_sub] at hW
    rw [_root_.mul_inv_rev, map_mul σ, Module.End.mul_apply, map_mul, Module.End.mul_apply]
    rw [← sub_eq_zero] at hW ⊢
    rw [← hW]
    abel
  let L : Y → (Fin 3 → ZMod 3) →ₗ[ZMod 3] ZMod 3 := fun y =>
    lam ∘ₗ (s₀ - ρ y ∘ₗ s₀ ∘ₗ σ y⁻¹)
  have hL : ∀ y v, L y v = lam (s₀ v - ρ y (s₀ (σ y⁻¹ v))) := fun _ _ => rfl
  let γ : Y → Fin 3 → ZMod 3 := fun y i => L y (Pi.single i 1)
  have hγ : ∀ y v, γ y ⬝ᵥ v = lam (s₀ v - ρ y (s₀ (σ y⁻¹ v))) := fun y v => by
    rw [← hL, eq_dotProduct (L y) v]
  have hγc : IsCocycle τ γ := by
    intro y z
    apply eq_of_dotProduct_eq
    intro v
    rw [add_dotProduct, hτM, transpose_mulVec_dotProduct, ← hσM, hγ, hγ, hγ, hemul, map_add,
      add_comm]
  obtain ⟨u, hu⟩ := hτ γ hγc
  let ℓ : (Fin 3 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun v => u ⬝ᵥ v
      map_add' := dotProduct_add u
      map_smul' := fun a v => by rw [dotProduct_smul, RingHom.id_apply] }
  let s : (Fin 3 → ZMod 3) →ₗ[ZMod 3] D := s₀ + ℓ.smulRight (w : D)
  have hs : ∀ v, s v = s₀ v + (u ⬝ᵥ v) • (w : D) := fun _ => rfl
  have hqs : ∀ v, q (s v) = v := fun v => by
    rw [hs, map_add, map_smul, hqw, smul_zero, add_zero, hqs₀]
  have hsσ : ∀ (y : Y) (v : Fin 3 → ZMod 3), s v = ρ y (s (σ y⁻¹ v)) := by
    intro y v
    have h1 := hWeq _ (he y v)
    rw [← hγ, hu, sub_dotProduct, hτM, transpose_mulVec_dotProduct, ← hσM, sub_smul] at h1
    rw [hs, hs, map_add, map_smul, hWtriv y _ w.2]
    rw [← sub_eq_zero, ← sub_eq_zero.2 h1]
    abel
  have hequiv : ∀ (y : Y) (v : Fin 3 → ZMod 3), s (σ y v) = ρ y (s v) := fun y v => by
    rw [hsσ y (σ y v), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  refine ⟨LinearMap.range s, fun y x hx => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hx
    rw [← hequiv]
    exact LinearMap.mem_range_self s _
  · rw [isCompl_iff, Submodule.disjoint_def, codisjoint_iff, eq_top_iff]
    refine ⟨fun x hxW hx => ?_, fun d _ => ?_⟩
    · obtain ⟨v, rfl⟩ := hx
      have : q (s v) = 0 := by rw [← LinearMap.mem_ker, hker]; exact hxW
      rw [hqs] at this
      rw [this, map_zero]
    · rw [Submodule.mem_sup]
      refine ⟨d - s (q d), ?_, s (q d), LinearMap.mem_range_self s _, by abel⟩
      rw [← hker, LinearMap.mem_ker, map_sub, hqs, sub_self]

theorem sl33Splitting : SL33Splitting.{u, v} := by
  intro Y _ φ D _ _ ρ W _ h
  rcases h with ⟨hiso | hiso, hQ, htriv⟩ | ⟨hW1, hWtriv, hq | hq⟩
  · exact exists_complement_of_sub ρ W (coboundary_nat φ) hiso hQ htriv
  · exact exists_complement_of_sub ρ W (coboundary_dual φ) hiso hQ htriv
  · exact exists_complement_of_quot ρ W (σ := natRepVia φ.toMonoidHom)
      (τ := dualRepVia φ.toMonoidHom) (fun y => (φ y : Matrix (Fin 3) (Fin 3) (ZMod 3)))
      (fun y v => natRepVia_apply _ y v) (fun y v => dualRepVia_apply _ y v)
      (coboundary_dual φ) hW1 hWtriv hq
  · refine exists_complement_of_quot ρ W (σ := dualRepVia φ.toMonoidHom)
      (τ := natRepVia φ.toMonoidHom)
      (fun y => (φ y⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ)
      (fun y v => dualRepVia_apply _ y v) (fun y v => ?_) (coboundary_nat φ) hW1 hWtriv hq
    rw [natRepVia_apply, inv_inv, Matrix.transpose_transpose]
    rfl

end CFSG.RankThree.PartTwo.Toolkit
