module

public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem cycThree_mul_diagTau_aux {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    (cycThree : GL (Fin 3) K) * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ * cycThree := by
  have h1 : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ := by
    apply Units.ext
    rw [cycThree_conj_diagTau hτ, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul,
      Matrix.one_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [← h1]
  group

theorem sLTwoData_exists_transvection {X : Type} [Group X] (D : SLTwoData X π p f K) {z : X}
    (hz : z ∈ D.L₀) (hz3 : z ^ 3 = 1) (hzC : z ∉ Subgroup.centralizer (D.L₀ : Set X)) {c₀ : X}
    (hc₀ : c₀ ∈ D.L₀ ⊓ Subgroup.centralizer (D.L₀ : Set X)) (hc₀1 : c₀ ≠ 1) :
    ∃ v : X, v ∈ D.L₀ ∧ v ^ 3 = 1 ∧ v * z * v⁻¹ * z⁻¹ = c₀ ^ 2 := by
  have hK := D.piField
  have hq := D.modThree
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  set cL : D.L₀ := ⟨c₀, hc₀.1⟩ with hcL
  have hcS : ((D.e cL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ₀ hτ₀1 fun s hs => ?_
    obtain ⟨w, hw⟩ : ∃ w : D.L₀, D.e w = ⟨s, hs⟩ := ⟨D.e.symm ⟨s, hs⟩, by simp⟩
    have hwc : cL * w = w * cL :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc₀.2 w w.2).symm
    have h1 := congrArg (fun v => ((D.e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hwc
    simp only [map_mul, Subgroup.coe_mul, hw] at h1
    exact h1
  obtain ⟨ζ, hζ⟩ := hcS
  have hζ3 : ζ ^ 3 = 1 := pow_three_eq_one_of_scalar_mem_slPi hπ (hζ ▸ (D.e cL).2)
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hc₀1
    have h1 : D.e cL = 1 := by
      apply Subtype.ext
      rw [← hζ, h, map_one, Subgroup.coe_one]
    have h2 : cL = 1 := D.e.injective (by rw [h1, map_one])
    simpa [hcL] using congrArg Subtype.val h2
  have hτ : (ζ : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hζ3
    simpa using this
  have hτ1 : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hτ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  set zL : D.L₀ := ⟨z, hz⟩ with hzL
  have hεL : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := (D.e zL).2
  have hzL3 : zL ^ 3 = 1 := Subtype.ext (by simp [hzL, hz3])
  have hε3 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hzL3, map_one, Subgroup.coe_one]
  have hεZ : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hεZ
    apply hzC
    have hS := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hεZ
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : D.e ⟨w, hw⟩ * D.e zL = D.e zL * D.e ⟨w, hw⟩ :=
      Subtype.ext (commute_of_mem_statedScalars hS _)
    have h2 : (⟨w, hw⟩ : D.L₀) * zL = zL * ⟨w, hw⟩ :=
      D.e.injective (by rw [map_mul, map_mul, h1])
    exact congrArg Subtype.val h2
  have hε1 : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ≠ 1 :=
    fun h => hεZ (h ▸ one_mem _)
  obtain ⟨g, hgH, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 hεL hεZ (orderOf_eq_prime hε3 hε1)
  have hε : ((D.e zL : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = g * diagTau hτ * g⁻¹ :=
    eq_conj_of_inv_conj hgD
  have hvhL : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ hgH (cycThree_mem_slPi hπ)
  have hvh3 : (g * cycThree * g⁻¹ : GL (Fin 3) K) ^ 3 = 1 := by
    rw [conj_pow, cycThree_pow_three, mul_one, mul_inv_cancel]
  set vL : D.L₀ := D.e.symm ⟨g * cycThree * g⁻¹, hvhL⟩ with hvLdef
  have hvL : D.e vL = ⟨g * cycThree * g⁻¹, hvhL⟩ := by
    rw [hvLdef]
    exact D.e.apply_symm_apply _
  refine ⟨(vL : X), vL.2, ?_, ?_⟩
  · have h3 : vL ^ 3 = 1 := by
      apply D.e.injective
      apply Subtype.ext
      rw [map_pow, hvL, map_one]
      simpa using hvh3
    simpa using congrArg Subtype.val h3
  · have hcomm : D.e (vL * zL * vL⁻¹ * zL⁻¹) = D.e (cL ^ 2) := by
      apply Subtype.ext
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hvL]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hε, ← hζ]
      have e1 : g * cycThree * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * cycThree * g⁻¹)⁻¹ *
          (g * diagTau hτ * g⁻¹)⁻¹ =
          g * (cycThree * diagTau hτ * cycThree⁻¹ * (diagTau hτ)⁻¹) * g⁻¹ := by group
      have e2 : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ * (diagTau hτ)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (ζ : K) hτ0 ^ 2) := by
        rw [cycThree_mul_diagTau_aux hτ hτ0]
        group
      rw [e1, e2, Units.mk0_val, map_pow]
      have hsc : (GeneralLinearGroup.scalar (Fin 3) ζ) ^ 2 * g =
          g * (GeneralLinearGroup.scalar (Fin 3) ζ) ^ 2 :=
        (Commute.pow_right (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g) 2).eq.symm
      calc g * GeneralLinearGroup.scalar (Fin 3) ζ ^ 2 * g⁻¹
          = GeneralLinearGroup.scalar (Fin 3) ζ ^ 2 * g * g⁻¹ := by rw [hsc]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ ^ 2 := by group
    have h2 : vL * zL * vL⁻¹ * zL⁻¹ = cL ^ 2 := D.e.injective hcomm
    have h3 := congrArg Subtype.val h2
    simpa [hzL, hcL] using h3

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
