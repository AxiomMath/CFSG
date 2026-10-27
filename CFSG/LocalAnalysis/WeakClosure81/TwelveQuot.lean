module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Quot

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem kerIn_map_top_eq (M C : Subgroup G) [C.Normal] (hC : C ≤ M) :
    CFSG.Quasithin.kerIn (M.map (QuotientGroup.mk' C)) ⊤ =
      (CFSG.Quasithin.kerIn M ⊤).map (QuotientGroup.mk' C) := by
  have hpre : (M.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C) = M :=
    Subgroup.comap_map_eq_self (f := QuotientGroup.mk' C) (H := M) (by
      rw [QuotientGroup.ker_mk']
      exact hC)
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [CFSG.Quasithin.mem_kerIn] at hx
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [CFSG.Quasithin.mem_kerIn]
    intro g _
    have h := hx (QuotientGroup.mk' C g) (Subgroup.mem_top _)
    have h' : QuotientGroup.mk' C (g * y * g⁻¹) ∈ M.map (QuotientGroup.mk' C) := by
      simpa [map_mul] using h
    rw [← hpre, Subgroup.mem_comap]
    exact h'
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.Quasithin.mem_kerIn]
    intro b _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C b
    have hy' := (CFSG.Quasithin.mem_kerIn.mp hy) g (Subgroup.mem_top g)
    refine Subgroup.mem_map.mpr ⟨g * y * g⁻¹, hy', ?_⟩
    simp [map_mul]

theorem Setting12Two.quotient (h : Setting12Two A M n) (C : Subgroup G) [C.Normal]
    (hC : C ≤ CFSG.Quasithin.kerIn M ⊤) :
    Setting12Two (A.map (QuotientGroup.mk' C)) (M.map (QuotientGroup.mk' C)) n := by
  have hCM : C ≤ M := hC.trans CFSG.Quasithin.kerIn_le
  have hpre : (M.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C) = M :=
    Subgroup.comap_map_eq_self (f := QuotientGroup.mk' C) (H := M) (by
      rw [QuotientGroup.ker_mk']
      exact hCM)
  refine ⟨?_, ?_, ?_, ?_, ?_, h.one_lt_n⟩
  · exact h.A_two.map (QuotientGroup.mk' C)
  · exact Subgroup.map_mono h.A_le_M
  · intro htop
    apply h.M_ne
    have hcomap : (M.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C) = ⊤ := by
      rw [htop, Subgroup.comap_top]
    rwa [hpre] at hcomap
  · intro N hAN hNtop
    have hNne : N.comap (QuotientGroup.mk' C) ≠ ⊤ := by
      intro hcomap
      apply hNtop
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) N,
        hcomap, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    have hAle : A ≤ N.comap (QuotientGroup.mk' C) := fun a ha =>
      hAN (Subgroup.mem_map_of_mem (QuotientGroup.mk' C) ha)
    have hle : N.comap (QuotientGroup.mk' C) ≤ M := h.unique_max _ hAle hNne
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) N]
    exact Subgroup.map_mono hle
  · have hK : CFSG.Quasithin.kerIn (M.map (QuotientGroup.mk' C)) ⊤ =
        (CFSG.Quasithin.kerIn M ⊤).map (QuotientGroup.mk' C) :=
      kerIn_map_top_eq M C hCM
    let e : (G ⧸ C) ⧸ CFSG.Quasithin.kerIn (M.map (QuotientGroup.mk' C)) ⊤ ≃*
        G ⧸ CFSG.Quasithin.kerIn M ⊤ :=
      (QuotientGroup.quotientMulEquivOfEq hK).trans
        (QuotientGroup.quotientQuotientEquivQuotient C (CFSG.Quasithin.kerIn M ⊤) hC)
    rcases h.type with ht | ht
    · exact Or.inl (CFSG.Quasithin.IsPSL.of_mulEquiv e.symm ht)
    · exact Or.inr (CFSG.Quasithin.IsSz.of_mulEquiv e.symm ht)

theorem Setting12Two.ker_le_of_irreducible (h : Setting12Two A M n) {X : Type} [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X] (σ : G →* LGL 2 X) (hirr : IsChiefFactor σ ⊤ ⊥)
    (hnt : IsNoncentral σ ⊤ ⊥) : σ.ker ≤ CFSG.Quasithin.kerIn M ⊤ := by
  unfold IsChiefFactor at hirr
  unfold IsNoncentral at hnt
  by_contra hnot
  have hnotM : ¬ σ.ker ≤ M := fun hM => hnot (by
    intro x hx
    rw [CFSG.Quasithin.mem_kerIn]
    intro b _
    exact hM ((inferInstance : σ.ker.Normal).conj_mem x hx b))
  have hsup : A ⊔ σ.ker = ⊤ := by
    by_contra hne
    exact hnotM (le_trans le_sup_right (h.unique_max (A ⊔ σ.ker) le_sup_left hne))
  obtain ⟨x₀, -, hx₀0, hx₀fix⟩ :=
    exists_fixed_of_isPGroup (p := 2) (P := A.map σ) (h.A_two.map σ)
      (U := (⊤ : Submodule (ZMod 2) X)) (ne_of_gt hirr.1)
      (by intro g _ u _; exact Submodule.mem_top)
  have hσfix : ∀ g : G, σ g x₀ = x₀ := by
    intro g
    have hg : g ∈ A ⊔ σ.ker := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨a, ha, k, hk, hak⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hσk : σ k = 1 := hk
    calc σ g x₀ = σ (a * k) x₀ := by rw [← hak]
      _ = (σ a * σ k) x₀ := by rw [map_mul]
      _ = σ a x₀ := by rw [hσk, mul_one]
      _ = x₀ := hx₀fix (σ a) (Subgroup.mem_map_of_mem σ ha)
  let U : Submodule (ZMod 2) X := Submodule.span (ZMod 2) {x₀}
  have hx₀U : x₀ ∈ U := Submodule.mem_span_singleton_self x₀
  have hUbot : U ≠ ⊥ := by
    intro h
    rw [h] at hx₀U
    exact hx₀0 (by simpa using hx₀U)
  have hfixU : ∀ g : G, ∀ u ∈ U, σ g u = u := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hσfix g]
  have hinvU : ∀ g : G, ∀ u ∈ U, σ g u ∈ U := by
    intro g u hu
    rw [hfixU g u hu]
    exact hu
  rcases hirr.2.2.2 U bot_le le_top hinvU with hU | hU
  · exact hUbot hU
  · obtain ⟨g, w, hw, hgw⟩ := hnt
    have hw' : σ g w = w := hfixU g w (by rw [hU]; exact hw)
    exact hgw (by rw [hw', sub_self]; exact Submodule.zero_mem _)

end Quot

section KerLift

variable {G : Type} [Group G]

private theorem b12_TwelveQuot_forall_map_iff (ρ : G →* LGL 2 V) (W : Submodule (ZMod 2) V) :
    (∀ g : G ⧸ ρ.ker, ∀ w ∈ W, QuotientGroup.kerLift ρ g w ∈ W) ↔
      (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) := by
  constructor
  · intro h g w hw
    simpa using h (QuotientGroup.mk' ρ.ker g) w hw
  · intro h g w hw
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective ρ.ker g
    simpa using h g' w hw

theorem repQuad_kerLift (ρ : G →* LGL 2 V) (A : Subgroup G) :
    RepQuad (QuotientGroup.kerLift ρ) (A.map (QuotientGroup.mk' ρ.ker)) ↔ RepQuad ρ A := by
  have hcomp : (QuotientGroup.kerLift ρ).comp (QuotientGroup.mk' ρ.ker) = ρ :=
    MonoidHom.ext fun g => QuotientGroup.kerLift_mk (φ := ρ) g
  have hmap : (A.map (QuotientGroup.mk' ρ.ker)).map (QuotientGroup.kerLift ρ) = A.map ρ := by
    rw [Subgroup.map_map, hcomp]
  unfold RepQuad
  rw [hmap]

theorem isChiefFactor_kerLift (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V) :
    IsChiefFactor (QuotientGroup.kerLift ρ) W₁ W₂ ↔ IsChiefFactor ρ W₁ W₂ := by
  unfold IsChiefFactor
  refine and_congr Iff.rfl (and_congr (b12_TwelveQuot_forall_map_iff ρ W₁)
    (and_congr (b12_TwelveQuot_forall_map_iff ρ W₂) ?_))
  refine forall_congr' fun U => ?_
  exact imp_congr Iff.rfl (imp_congr Iff.rfl
    (imp_congr (b12_TwelveQuot_forall_map_iff ρ U) Iff.rfl))

theorem isNoncentral_kerLift (ρ : G →* LGL 2 V) (W₁ W₂ : Submodule (ZMod 2) V) :
    IsNoncentral (QuotientGroup.kerLift ρ) W₁ W₂ ↔ IsNoncentral ρ W₁ W₂ := by
  unfold IsNoncentral
  constructor
  · rintro ⟨g, w, hw, hg⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective ρ.ker g
    exact ⟨g', w, hw, by simpa using hg⟩
  · rintro ⟨g, w, hw, hg⟩
    exact ⟨QuotientGroup.mk' ρ.ker g, w, hw, by simpa using hg⟩

end KerLift

end CFSG.LocalAnalysis.WeakClosure81
