module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_threeElt_of_pm {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx : M.xV ≠ 0) (hNT : GGNoTransvection 3 Bs)
    (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)))
    (hfix : ggLin (p := 3) M.model φ M.xV = M.xV) (h3 : φ ^ 3 = 1)
    (hpm : ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV}) :
    φ ∈ ggAutomizer L Bs := by
  obtain ⟨w, hw, ε, hε, hv⟩ := hpm
  let ρ : MulAut ↥Bs := φ * w
  let S : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model ρ
  have hwfix : ggLin (p := 3) M.model w M.xV = M.xV := by
    have hmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self M.xV
    exact mem_ggFixedSubmodule_iff.mp hmem w hw
  have hSx : S M.xV = M.xV := by
    change ggLin (p := 3) M.model (φ * w) M.xV = M.xV
    rw [map_mul, LinearEquiv.mul_apply, hwfix, hfix]
  let F : M.V →ₗ[ZMod 3] Submodule.span (ZMod 3) {M.xV} :=
    LinearMap.codRestrict (Submodule.span (ZMod 3) {M.xV})
      (S.toLinearMap - ε • LinearMap.id) (fun v => by
        change ggLin (p := 3) M.model (φ * w) v - ε • v ∈
          Submodule.span (ZMod 3) {M.xV}
        exact hv v)
  let ψ : M.V →ₗ[ZMod 3] ZMod 3 :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) M.V M.xV hx).symm.toLinearMap ∘ₗ F
  have hSf : ∀ v : M.V, S v = ε • v + ψ v • M.xV := by
    intro v
    have h2 := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul (ZMod 3) M.V M.xV hx (F v)
    have h3 : ψ v • M.xV = (F v : M.V) := by
      rw [show ψ v = (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) M.V M.xV hx).symm (F v)
        from rfl]
      exact h2
    have h4 : (F v : M.V) = S v - ε • v := rfl
    rw [h3, h4]
    abel
  have hψx : ψ M.xV = 1 - ε := by
    have h := hSf M.xV
    rw [hSx] at h
    have h3 : M.xV - ε • M.xV = ψ M.xV • M.xV := (sub_eq_iff_eq_add').mpr h
    have h4 : (1 - ε) • M.xV = ψ M.xV • M.xV := by
      rw [sub_smul, one_smul]
      exact h3
    have h5 : (1 - ε - ψ M.xV) • M.xV = 0 := by
      rw [sub_smul, h4, sub_self]
    have h6 : 1 - ε - ψ M.xV = 0 := by
      rcases smul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd h6 hx
    exact (sub_eq_zero.mp h6).symm
  have hS1 : S * S = 1 := by
    rcases hε with rfl | rfl
    · by_cases hψ0 : ψ = 0
      · have hSeq : S = 1 := by
          refine LinearEquiv.ext fun v => ?_
          rw [hSf v, hψ0]
          simp
        rw [hSeq, one_mul]
      · exfalso
        have htrans : GGIsTransvection 3 ρ :=
          ggIsTransvection_of_apply M.model hx hψ0 (by simpa using hψx) (fun v => by
            change S v = v + ψ v • M.xV
            rw [hSf v, one_smul])
        have hρtop : ρ ∈ ggAutomizer ⊤ Bs := by
          have hmono : ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top
          change φ * w ∈ ggAutomizer ⊤ Bs
          exact Subgroup.mul_mem _ hφ (hmono hw)
        rw [ggAutomizer_eq] at hρtop
        exact hNT ρ hρtop htrans
    · refine LinearEquiv.ext fun v => ?_
      have hψSv : ψ (S v) = ψ v := by
        rw [hSf v, map_add, map_smul, map_smul, hψx]
        rw [smul_eq_mul, smul_eq_mul]
        ring
      calc S (S v) = -(S v) + ψ (S v) • M.xV := by rw [hSf (S v), neg_one_smul]
        _ = -(-v + ψ v • M.xV) + ψ v • M.xV := by rw [hψSv, hSf v, neg_one_smul]
        _ = v := by abel
  have hρρ : ρ * ρ = 1 := by
    apply ggLin_injective (p := 3) M.model
    show ggLin (p := 3) M.model (ρ * ρ) = ggLin (p := 3) M.model 1
    rw [map_mul, map_one]
    exact hS1
  have hφeq : φ = ρ * w⁻¹ := by
    change φ = (φ * w) * w⁻¹
    group
  have hρN : ρ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
    change φ * w ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))
    exact Subgroup.mul_mem _ hN (Subgroup.le_normalizer hw)
  have hconj : ρ * w⁻¹ * ρ⁻¹ ∈ ggAutomizer L Bs :=
    (Subgroup.mem_normalizer_iff.mp hρN (w⁻¹)).mp (Subgroup.inv_mem _ hw)
  have hφφ : φ * φ ∈ ggAutomizer L Bs := by
    have heq : φ * φ = (ρ * w⁻¹ * ρ⁻¹) * w⁻¹ := by
      rw [hφeq, inv_eq_of_mul_eq_one_right hρρ]
      group
    rw [heq]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hw)
  have hφ4 : φ = (φ * φ) * (φ * φ) := by
    have h2 : φ ^ 4 = φ := by
      have h4 : (4 : ℕ) = 3 + 1 := rfl
      rw [h4, pow_add, h3, one_mul, pow_one]
    have h1 : φ ^ 4 = (φ * φ) * (φ * φ) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    exact h2.symm.trans h1
  rw [hφ4]
  exact Subgroup.mul_mem _ hφφ hφφ

end CFSG.StandardType

end
