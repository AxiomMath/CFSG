module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_dualHom dualHom_dualHom
  dualHom_transvection_mulVec)
open scoped Matrix

variable {G : Type} [Group G]

section Fix

variable {F : Type} [Field F]

theorem burnsideC135_transvection_mem_ut {i j : Fin 3} (hij : i < j) (b : F) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) b ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F := by
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne
      (ne_of_gt hlk), Matrix.single_apply]
    rw [if_neg]
    · rw [zero_add]
    · rintro ⟨rfl, rfl⟩
      exact absurd (hij.trans hlk) (lt_irrefl _)
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ hij

theorem burnsideC135_sylow_fix [Finite F] [CharP F 2]
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F)) :
    ∃ y₀ y₁ : Fin 3 → F,
      (∀ x : Fin 3 → F, (∀ t ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)), (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
        ∃ c : F, x = c • y₀) ∧
      (∀ x : Fin 3 → F, (∀ t ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)),
        ((dualHom t : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) →
          ∃ c : F, x = c • y₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) F) P₀ T
  have hmemT : ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F,
      g * u * g⁻¹ ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨u, by rw [hP₀]; exact hu, rfl⟩
  have h01 : (0 : Fin 3) < 1 := by decide
  have h12 : (1 : Fin 3) < 2 := by decide
  have hgm : ∀ (a b : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      ((a * b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        (a : Matrix (Fin 3) (Fin 3) F) *ᵥ ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    intro a b v
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  have hinv : ∀ (a : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((a : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
    intro a v
    rw [← hgm, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1,
    ((dualHom g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single 2 1, fun x hx => ?_, fun x hx => ?_⟩
  ·
    set y := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x
      with hy
    have hfix : ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F,
        (u : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
      intro u hu
      have h1 := hx _ (hmemT u hu)
      rw [hgm, hgm, hy] at *
      have h2 := congrArg (fun v => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ v) h1
      simp only [hinv] at h2
      exact h2
    have hy1 : y 1 = 0 := by
      have h1 := hfix _ (burnsideC135_transvection_mem_ut h01 1)
      rw [CFSG.Quasithin.H13.Ch4.transvection_mulVec] at h1
      have h2 := congrFun h1 0
      simpa using h2
    have hy2 : y 2 = 0 := by
      have h1 := hfix _ (burnsideC135_transvection_mem_ut h12 1)
      rw [CFSG.Quasithin.H13.Ch4.transvection_mulVec] at h1
      have h2 := congrFun h1 1
      simpa using h2
    refine ⟨y 0, ?_⟩
    have hyv : y = y 0 • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp [hy1, hy2]
    have hx' : x = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
      rw [hy, ← hgm, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [hx']
    conv_lhs => rw [hyv]
    rw [Matrix.mulVec_smul]
  ·
    set y := ((dualHom g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ x with hy
    have hfix : ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 F,
        ((dualHom u : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
      intro u hu
      have h1 := hx _ (hmemT u hu)
      rw [map_mul, map_mul, hgm, hgm] at h1
      have h2 := congrArg (fun v => ((dualHom g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ v) h1
      simp only [map_inv] at h2 ⊢
      rw [hinv] at h2
      rw [hy, map_inv]
      exact h2
    have hy0 : y 0 = 0 := by
      have h1 := hfix _ (burnsideC135_transvection_mem_ut h01 1)
      rw [dualHom_transvection_mulVec] at h1
      have h2 := congrFun h1 1
      simpa using h2
    have hy1 : y 1 = 0 := by
      have h1 := hfix _ (burnsideC135_transvection_mem_ut h12 1)
      rw [dualHom_transvection_mulVec] at h1
      have h2 := congrFun h1 2
      simpa using h2
    refine ⟨y 2, ?_⟩
    have hyv : y = y 2 • Pi.single 2 1 := by
      funext i
      fin_cases i <;> simp [hy0, hy1]
    have hx' : x = ((dualHom g : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
      rw [hy, map_inv, ← hgm, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mulVec]
    rw [hx']
    conv_lhs => rw [hyv]
    rw [Matrix.mulVec_smul]

end Fix

section Image

variable [Finite G] {X S L : Subgroup G} {F : Type} [Field F] [Finite F]

theorem burnsideC135_image_sylow (hS : IsSylowTwoOf S X) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G))
    {ρ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F} (hρ : Function.Surjective ρ) :
    IsPGroup 2 (((S ⊓ L).subgroupOf L).map ρ) ∧ ¬ 2 ∣ (((S ⊓ L).subgroupOf L).map ρ).index := by
  have hSL : IsSylowTwoOf (S ⊓ L) L := CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS hLX hXL
  refine ⟨IsPGroup.map ?_ ρ, fun h2 => hSL.2.2 ?_⟩
  · exact hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm
  · exact h2.trans (Subgroup.index_map_dvd _ hρ)

end Image

end CFSG.ASVolI

end
