module

public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourNonregular

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace SteinbergBN
open CFSG.RankThree.Classical

theorem map_conjSL_ringHom {L L' : Type} [Field L] [Field L'] (f : L →+* L')
    (P : GL (Fin 2) L) (B : SL2 L) :
    Matrix.SpecialLinearGroup.map f (conjSL P B) =
      conjSL (Matrix.GeneralLinearGroup.map f P) (Matrix.SpecialLinearGroup.map f B) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_conjSL, coe_conjSL,
    Matrix.SpecialLinearGroup.map_apply_coe, ← map_inv, map_mul, map_mul]
  rfl

theorem specialLinearGroup_map_algebraMap_tower {K K₂ K₆ : Type} [Field K] [Field K₂] [Field K₆]
    [Algebra K K₂] [Algebra K₂ K₆] [Algebra K K₆] [IsScalarTower K K₂ K₆] (A : SL2 K) :
    Matrix.SpecialLinearGroup.map (algebraMap K₂ K₆)
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A) =
      Matrix.SpecialLinearGroup.map (algebraMap K K₆) A := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (IsScalarTower.algebraMap_apply K K₂ K₆ _).symm

theorem cyclotomic_transport_derived (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]
    (M : IntermediateField K Ω) (g : ModGL .F4 Ω)
    (hgM : g ∈ (adjointGroup .F4 M).map (baseChangeGL (algebraMap M Ω)))
    (Γ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹) (x : ModGL .F4 Ω)
    (hxΓ : x ∈ Γ) (h y : ModGL .F4 Ω)
    (hhM : h ∈ (adjointGroup .F4 M).map (baseChangeGL (algebraMap M Ω)))
    (hy : y = h * x * h⁻¹) (Γ₁ D : Subgroup (ModGL .F4 Ω))
    (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom) (hD : D = Γ₁ ⊓ Subgroup.centralizer {y})
    (a : ModGL .F4 M) (ha : a ∈ adjointGroup .F4 M) (S : Subgroup (ModGL .F4 M))
    (hSD : ∀ s ∈ S, baseChangeGL (algebraMap M Ω) (a * s * a⁻¹) ∈ ⁅D, D⁆) :
    ∃ x₀ : adjointGroup .F4 K,
      baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
      (Subgroup.centralizer {x₀}).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      ∃ R₀ : Subgroup (adjointGroup .F4 K),
        R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ ∧
        ∃ k ∈ adjointGroup .F4 M,
          (R₀.map ((baseChangeGL (algebraMap K M)).comp (adjointGroup .F4 K).subtype)).map
              (MulAut.conj k).toMonoidHom = S := by
  classical
  set ιK : K →+* Ω := algebraMap K Ω with hιK
  set ι : M →+* Ω := algebraMap M Ω with hι
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hcomp : ∀ r : ModGL .F4 K, baseChangeGL ι (baseChangeGL (algebraMap K M) r) =
      baseChangeGL ιK r := fun r => by
    rw [baseChangeGL_baseChangeGL, hι, hιK, ← IsScalarTower.algebraMap_eq]
  rw [hΓ] at hxΓ
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxΓ
  set x₀ : adjointGroup .F4 K := ⟨x₁, hx₁⟩ with hx₀
  have hx₀x : baseChangeGL ιK (x₀ : ModGL .F4 K) = g * x * g⁻¹ := by
    change baseChangeGL ιK x₁ = g * x * g⁻¹
    rw [← hx₁x]
    change baseChangeGL ιK x₁ = g * (g⁻¹ * baseChangeGL ιK x₁ * g⁻¹⁻¹) * g⁻¹
    group
  have hCx := map_centralizer_eq_map_conj K Ω g Γ hΓ x h y hy Γ₁ D hΓ₁ hD x₀ hx₀x
  have hCx' : (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
      Subgroup (adjointGroup .F4 K)).map
        ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
      (⁅D, D⁆ : Subgroup (ModGL .F4 Ω)).map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
    rw [Subgroup.map_commutator, hCx, ← Subgroup.map_commutator]
  refine ⟨x₀, hx₀x, hCx, ?_⟩
  obtain ⟨g₀, hg₀, rfl⟩ := hgM
  obtain ⟨h₀, hh₀, rfl⟩ := hhM
  set b₀ := g₀ * h₀⁻¹ * a with hb₀
  have hb₀C : b₀ ∈ adjointGroup .F4 M := mul_mem (mul_mem hg₀ (inv_mem hh₀)) ha
  have hclaim : ∀ s ∈ S, ∃ r ∈ (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
      Subgroup (adjointGroup .F4 K)),
      baseChangeGL ιK (r : ModGL .F4 K) = baseChangeGL ι (b₀ * s * b₀⁻¹) := by
    intro s hs
    have hmem : baseChangeGL ι (b₀ * s * b₀⁻¹) ∈
        (⁅D, D⁆ : Subgroup (ModGL .F4 Ω)).map
          (MulAut.conj (baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹)).toMonoidHom := by
      refine ⟨_, hSD s hs, ?_⟩
      change baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹ * baseChangeGL ι (a * s * a⁻¹) *
        (baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹)⁻¹ = _
      rw [hb₀]
      simp only [map_mul, map_inv]
      group
    rw [← hCx'] at hmem
    obtain ⟨r, hr, hre⟩ := hmem
    exact ⟨r, hr, hre⟩
  refine ⟨(S.comap ((MulAut.conj b₀⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K M)).comp
    (adjointGroup .F4 K).subtype))) ⊓ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆,
    inf_le_right, b₀⁻¹, inv_mem hb₀C, ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact (Subgroup.mem_inf.1 hr).1
  · intro s hs
    obtain ⟨r, hr, hre⟩ := hclaim s hs
    have hr' : baseChangeGL (algebraMap K M) (r : ModGL .F4 K) = b₀ * s * b₀⁻¹ :=
      hinj (by rw [hcomp, hre])
    have hks : b₀⁻¹ * baseChangeGL (algebraMap K M) (r : ModGL .F4 K) * b₀⁻¹⁻¹ = s := by
      rw [hr']
      group
    refine ⟨_, ⟨r, Subgroup.mem_inf.2 ⟨?_, hr⟩, rfl⟩, ?_⟩
    · change b₀⁻¹ * baseChangeGL (algebraMap K M) (r : ModGL .F4 K) * b₀⁻¹⁻¹ ∈ S
      rw [hks]
      exact hs
    · exact hks

end CFSG.RankThree.Chevalley
