module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCert
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open Certificates.A8Nbr476 Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem ggA8Nbr_exists_lin_of_rank_one {N : M4} (hN : N ≠ 0) (hsq : N * N = 0)
    (hmin : ∀ i j k l : Fin 4, N i k * N j l = N i l * N j k) :
    ∃ u w : Fin 4 → ZMod 7, u ≠ 0 ∧ w ≠ 0 ∧ w ⬝ᵥ u = 0 ∧
      ∀ v : Fin 4 → ZMod 7, v ᵥ* N = (v ⬝ᵥ u) • w := by
  obtain ⟨i0, k0, h0⟩ : ∃ i k, N i k ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (Matrix.ext fun i k => h i k)
  have hNuw : ∀ i k, N i k = N i k0 * ((N i0 k0)⁻¹ * N i0 k) := by
    intro i k
    have h := hmin i i0 k0 k
    field_simp
    linear_combination -h
  have hss : ∑ k, N i0 k * N k k0 = 0 := by
    have h := congrFun (congrFun hsq i0) k0
    simpa [Matrix.mul_apply] using h
  refine ⟨fun i => N i k0, fun k => (N i0 k0)⁻¹ * N i0 k, ?_, ?_, ?_, fun v => ?_⟩
  · exact fun h => h0 (congrFun h i0)
  · intro h
    have h1 := congrFun h k0
    simp only [Pi.zero_apply, inv_mul_cancel₀ h0] at h1
    exact one_ne_zero h1
  · show ∑ k, ((N i0 k0)⁻¹ * N i0 k) * N k k0 = 0
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hss, mul_zero]
  · funext k
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, ← hNuw i k]

theorem ggIsTransv_exists_lin {X : M4} (hX : IsTransv X) :
    ∃ u w : Fin 4 → ZMod 7, u ≠ 0 ∧ w ≠ 0 ∧ w ⬝ᵥ u = 0 ∧
      ∀ v : Fin 4 → ZMod 7, v ᵥ* X = v + (v ⬝ᵥ u) • w := by
  obtain ⟨hne, hsq, hmin⟩ := hX
  obtain ⟨u, w, hu, hw, hwu, hv⟩ :=
    ggA8Nbr_exists_lin_of_rank_one (N := X - 1) (sub_ne_zero.mpr hne) hsq hmin
  refine ⟨u, w, hu, hw, hwu, fun v => ?_⟩
  rw [← hv v, show X = (X - 1) + 1 by abel, vecMul_add, vecMul_one]
  simp [add_comm]

@[expose] def ggA8Nbr_dotForm (u : Fin 4 → ZMod 7) : Module.Dual (ZMod 7) (Fin 4 → ZMod 7) where
  toFun v := v ⬝ᵥ u
  map_add' a b := add_dotProduct a b u
  map_smul' c v := by rw [smul_dotProduct]; rfl

theorem ggA8Nbr_dotForm_apply (u v : Fin 4 → ZMod 7) : ggA8Nbr_dotForm u v = v ⬝ᵥ u := rfl

theorem ggA8Nbr_dotForm_ne_zero {u : Fin 4 → ZMod 7} (hu : u ≠ 0) : ggA8Nbr_dotForm u ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have h1 := LinearMap.congr_fun h (Pi.single i 1)
  apply hi
  simpa [ggA8Nbr_dotForm_apply, dotProduct_single] using h1

section Coord

variable {G : Type} [Group G] {Bs : Subgroup G}

theorem ggA8Nbr_false_of_coord (L K : Subgroup G)
    (hNT : GGNoTransvection 7 Bs) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) {c : Case}
    (hc : c ∈ allCases) (hx : c ∉ excCases)
    (hgen : ∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
      ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) : False := by
  let S : Submonoid M4 :=
    { carrier := {g | ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
        ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) g}
      mul_mem' := by
        rintro g₁ g₂ ⟨φ₁, hφ₁, h₁⟩ ⟨φ₂, hφ₂, h₂⟩
        refine ⟨φ₂ * φ₁, Subgroup.mul_mem _ hφ₂ hφ₁, fun b => ?_⟩
        rw [MulAut.mul_apply, h₂, h₁, Matrix.vecMul_vecMul]
      one_mem' := ⟨1, Subgroup.one_mem _, fun b => by simp⟩ }
  obtain ⟨g, ⟨φ, hφA, hφ⟩, hT⟩ := ggA8Nbr_exists_transv_of_case hc hx S hgen
  obtain ⟨u, w, hu, hw, hwu, hvec⟩ := ggIsTransv_exists_lin hT
  have hlin : ∀ v, ggLin (p := 7) ι φ v = v + (ggA8Nbr_dotForm u v) • w := by
    intro v
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ggLin_apply_ofMul, hφ, hvec]
    rfl
  have htr := ggIsTransvection_of_apply (p := 7) ι hw (ggA8Nbr_dotForm_ne_zero hu)
    (by rw [ggA8Nbr_dotForm_apply]; exact hwu) hlin
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  exact hNT φ (mem_ggAutomizer_iff.mp (hle hφA)) htr

end Coord

end CFSG.StandardType

end
