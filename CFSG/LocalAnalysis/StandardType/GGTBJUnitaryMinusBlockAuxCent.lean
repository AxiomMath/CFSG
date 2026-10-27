module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F] {f m ε p : ℕ}

theorem map_centralizer_eq_inf_centralizer
    {h : UnitaryFieldData 2 f F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε}
    {φ : hypSU h m ε →* G} (hker : φ.ker ≤ Subgroup.center (hypSU h m ε))
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {C : Set G}
    (χ : G → Multiplicative (Fin m → ZMod p))
    (hχ : ∀ c ∈ C, ∀ g ∈ φ.range,
      c * g * c⁻¹ = (φ (τ (χ c))) * g * (φ (τ (χ c)))⁻¹) :
    (Subgroup.centralizer (τ '' (χ '' C))).map φ =
      φ.range ⊓ Subgroup.centralizer C := by
  classical
  apply le_antisymm
  ·
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    change φ s ∈ Subgroup.centralizer C
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hmem : φ s ∈ φ.range := ⟨s, rfl⟩
    have hact := hχ c hc (φ s) hmem
    have hsu : τ (χ c) ∈ τ '' (χ '' C) := ⟨χ c, ⟨c, hc, rfl⟩, rfl⟩
    have hcomm : τ (χ c) * (s : hypSU h m ε) = (s : hypSU h m ε) * τ (χ c) :=
      (Subgroup.mem_centralizer_iff.mp hs) _ hsu
    have h1 : c * (φ s) * c⁻¹ = φ s := by
      rw [hact]
      have hmul : (φ (τ (χ c))) * (φ s) = (φ s) * (φ (τ (χ c))) := by
        rw [← map_mul, ← map_mul, hcomm]
      rw [hmul]
      group
    exact mul_inv_eq_iff_eq_mul.mp h1
  ·
    rintro x ⟨hxr, hxC⟩
    obtain ⟨s, rfl⟩ := hxr
    refine Subgroup.mem_map_of_mem φ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨c, hc, rfl⟩ := hw
    have hact := hχ c hc (φ s) ⟨s, rfl⟩
    have hcommc : c * (φ s) = (φ s) * c :=
      (Subgroup.mem_centralizer_iff.mp hxC) c hc
    have hcommφ : (φ s) * φ (τ (χ c)) = φ (τ (χ c)) * φ s := by
      have h1 : c * (φ s) * c⁻¹ = φ s := by
        rw [hcommc]
        group
      rw [hact] at h1
      have h2 : φ (τ (χ c)) * φ s = φ s * φ (τ (χ c)) := by
        have h3 := congrArg (fun y => y * φ (τ (χ c))) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    have hq : φ ⁅s, τ (χ c)⁆ = 1 := by
      rw [map_commutatorElement]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcommφ
    have hz : ⁅s, τ (χ c)⁆ ∈ φ.ker := MonoidHom.mem_ker.mpr hq
    have hzpow : ⁅s, τ (χ c)⁆ ^ p = 1 := by
      have hmem : ⁅s, τ (χ c)⁆ ∈ Subgroup.center (hypSU h m ε) := hker hz
      have hupow : (τ (χ c)) ^ p = 1 := by
        have hu : (χ c) ^ p = 1 := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_pow, toAdd_one]
          ext i
          simp only [Pi.smul_apply, Pi.zero_apply]
          rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rw [← map_pow, hu, map_one]
      have hcomm : Commute (τ (χ c)) ⁅s, τ (χ c)⁆ := Subgroup.mem_center_iff.mp hmem _
      rw [hcomm.commutatorElement_pow_right p, hupow]
      simp
    have hone : ⁅s, τ (χ c)⁆ = 1 := hkp _ hz hzpow
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

end CFSG.StandardType.SuSplitRootGen
