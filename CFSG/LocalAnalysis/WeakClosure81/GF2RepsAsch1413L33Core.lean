module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Aut
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Dec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33X
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Open

private theorem a1413L33Core_kap_mem_centralizer (N : GL (Fin 2) (ZMod 3)) :
    l33Kap N ∈ inner L33P ⊓
      centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P)) := by
  have hcent : l33Kap N ∈
      centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [l33Kap_neg_one.symm, ← map_mul, ← map_mul]
    congr 1
    rw [neg_one_mul, mul_neg_one]
  exact ⟨l33Kap_mem_inner N, hcent⟩

private theorem a1413L33Core_delta_cancel (δ c u : MulAut L33P) (hδ : δ * δ = 1) :
    c * (u * δ) * (δ * c⁻¹ * δ) * (δ * u⁻¹) = c * u * c⁻¹ * u⁻¹ := by
  have h1 : c * (u * δ) * (δ * c⁻¹ * δ) * (δ * u⁻¹) =
      c * u * (δ * δ) * c⁻¹ * (δ * δ) * u⁻¹ := by group
  rw [h1, hδ]
  group

private theorem a1413L33Core_mem_iSup (A : Subgroup (MulAut L33P)) (u : MulAut L33P)
    (W : GL (Fin 2) (ZMod 3)) (N : GL (Fin 2) (ZMod 3)) (hu : u ∈ A)
    (hN : l33Kap N ∈ inner L33P ⊓
      centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P)))
    (hWu : l33Kap W = (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹) :
    l33Kap W ∈ (⨆ c ∈ (inner L33P ⊓
      centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P))),
        A.map (MulAut.conj c).toMonoidHom) := by
  have hmapN : l33Kap N * u * (l33Kap N)⁻¹ ∈
      A.map (MulAut.conj (l33Kap N)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hmap1 : u⁻¹ ∈ A.map (MulAut.conj (1 : MulAut L33P)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨u⁻¹, A.inv_mem hu, by simp⟩
  have h1mem : (1 : MulAut L33P) ∈ inner L33P ⊓
      centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P)) :=
    ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hmem : (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹ ∈
      (⨆ c ∈ (inner L33P ⊓
        centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P))),
          A.map (MulAut.conj c).toMonoidHom) :=
    mul_mem
      (Subgroup.mem_iSup_of_mem (l33Kap N) (Subgroup.mem_iSup_of_mem hN hmapN))
      (Subgroup.mem_iSup_of_mem (1 : MulAut L33P)
        (Subgroup.mem_iSup_of_mem h1mem hmap1))
  rw [hWu]
  exact hmem

theorem l33_core (A : Subgroup (MulAut L33P)) (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hz : (MulAut.conj (tInv : L33P)) ∈ A) :
    ∃ i : MulAut L33P, i * i = MulAut.conj (tInv : L33P) ∧
      i ∈ (⨆ c ∈ (inner L33P ⊓ centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P))),
        A.map (MulAut.conj c).toMonoidHom) ∧
      ∀ x ∈ l33X, i * x * i⁻¹ ∈ l33X := by
  let ζ : MulAut L33P := MulAut.conj (tInv : L33P)
  have hz' : ζ ∈ A := hz
  have hζkap : ζ = l33Kap (-1) := l33Kap_neg_one.symm
  have hneg1 : (-1 : GL (Fin 2) (ZMod 3)) ≠ 1 := by decide
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hneg1
    apply l33Kap_injective
    rw [map_one, ← hζkap]
    exact h
  have hζ2 : ζ * ζ = 1 := by
    rw [hζkap, ← map_mul, neg_mul_neg, one_mul, map_one]
  have hzp : zpowers ζ ≤ A := Subgroup.zpowers_le.mpr hz'
  have hnotle : ¬ A ≤ zpowers ζ := by
    intro hle
    have heq : A = zpowers ζ := le_antisymm hle hzp
    have hcard : Nat.card (zpowers ζ) = 4 := by rw [← heq]; exact hA
    rw [Nat.card_zpowers] at hcard
    have horder : orderOf ζ = 2 := orderOf_eq_prime (by rwa [pow_two]) hζ1
    omega
  obtain ⟨u, hu, hu_notin⟩ := Set.not_subset.mp hnotle
  have hu_ne_one : u ≠ 1 := by
    intro h; rw [h] at hu_notin; exact hu_notin (Subgroup.one_mem _)
  have hu_ne_zeta : u ≠ ζ := by
    intro h; rw [h] at hu_notin; exact hu_notin (Subgroup.mem_zpowers ζ)
  have hu2 : u * u = 1 := by
    have h := hAe.2 u hu
    rwa [pow_two] at h
  have hu_comm : u * ζ = ζ * u := by
    have h := (hAe.1.is_comm).comm (⟨u, hu⟩ : ↥A) (⟨ζ, hz'⟩ : ↥A)
    exact congrArg Subtype.val h
  obtain ⟨M, ε, hε, hu_eq⟩ := l33_mem_centralizer_zeta u hu_comm
  interval_cases ε
  ·
    have hu_eq0 : u = l33Kap M := by simpa using hu_eq
    have hMM : M * M = 1 := by
      apply l33Kap_injective
      rw [map_mul, map_one, ← hu_eq0]
      exact hu2
    have hM1 : M ≠ 1 := by
      intro h; apply hu_ne_one; rw [hu_eq0, h, map_one]
    have hMm1 : M ≠ -1 := by
      intro h; apply hu_ne_zeta; rw [hu_eq0, h, l33Kap_neg_one]
    obtain ⟨N, hN⟩ := l33_dec_inner M hMM hM1 hMm1
    let W : GL (Fin 2) (ZMod 3) := N * M * N⁻¹ * M⁻¹
    have hW2 : W * W = -1 := by
      have h : W ^ 2 = -1 := hN
      rwa [pow_two] at h
    have hWu : l33Kap W = (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹ := by
      calc l33Kap W = l33Kap N * l33Kap M * (l33Kap N)⁻¹ * (l33Kap M)⁻¹ := by
            simp only [W, map_mul, map_inv]
        _ = (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹ := by rw [hu_eq0]
    refine ⟨l33Kap W, ?_, ?_, l33X_normalized W⟩
    · rw [← map_mul, hW2, l33Kap_neg_one]
    · exact a1413L33Core_mem_iSup A u W N hu (a1413L33Core_kap_mem_centralizer N) hWu
  ·
    have hu_eq1 : u = l33Kap M * dualAut 3 (ZMod 3) := by simpa using hu_eq
    have hδ2 : dualAut 3 (ZMod 3) * dualAut 3 (ZMod 3) = 1 :=
      (standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.1
    have hM_it : M * GeneralLinearGroup.inverseTranspose M = 1 := by
      apply l33Kap_injective
      rw [map_mul, map_one]
      calc l33Kap M * l33Kap (GeneralLinearGroup.inverseTranspose M)
          = l33Kap M * (dualAut 3 (ZMod 3) * l33Kap M * dualAut 3 (ZMod 3)) := by
            rw [← l33Kap_dual]
        _ = (l33Kap M * dualAut 3 (ZMod 3)) * (l33Kap M * dualAut 3 (ZMod 3)) := by
            group
        _ = u * u := by rw [hu_eq1]
        _ = 1 := hu2
    have hsym : ((M : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose =
        (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      have hmat : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          (((M : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹).transpose = 1 := by
        have h := congrArg (fun u : GL (Fin 2) (ZMod 3) =>
          (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) hM_it
        rw [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.coe_inverseTranspose,
          Matrix.GeneralLinearGroup.coe_inv] at h
        exact h
      have h2 : ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ *
          (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose = 1 := by
        have h := congrArg Matrix.transpose hmat
        rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
      have hMMinv : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ = 1 := by
        have h := congrArg (fun u : GL (Fin 2) (ZMod 3) =>
          (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) (mul_inv_cancel M)
        simpa [Units.val_mul, Units.val_one, ← Units.val_inv_eq_inv_val] using h
      calc (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose
          = 1 * (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose := (one_mul _).symm
        _ = ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
              (M : Matrix (Fin 2) (Fin 2) (ZMod 3))⁻¹) *
              (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose := by rw [hMMinv]
        _ = (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
              ((M : Matrix (Fin 2) (Fin 2) (ZMod 3))⁻¹ *
              (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose) := by rw [mul_assoc]
        _ = (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) * 1 := by rw [h2]
        _ = (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) := mul_one _
    obtain ⟨N, hN⟩ := l33_dec_outer M hsym
    let W : GL (Fin 2) (ZMod 3) := N * M * GeneralLinearGroup.inverseTranspose N⁻¹ * M⁻¹
    have hWmat : (W : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          (N : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose *
            ((M⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      simp only [W, Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]
    have hW2 : W * W = -1 := by
      apply Units.ext
      rw [Units.val_mul, Units.coe_neg_one, hWmat, ← pow_two]
      exact hN
    have hM_eq : l33Kap M = u * dualAut 3 (ZMod 3) := by
      rw [hu_eq1, mul_assoc, hδ2, mul_one]
    have hN_inv : l33Kap (GeneralLinearGroup.inverseTranspose N⁻¹) =
        dualAut 3 (ZMod 3) * (l33Kap N)⁻¹ * dualAut 3 (ZMod 3) := by
      rw [← l33Kap_dual (N⁻¹), map_inv]
    have hMinv : l33Kap (M⁻¹) = (l33Kap M)⁻¹ := map_inv l33Kap M
    have hWu : l33Kap W = (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹ := by
      calc l33Kap W
          = l33Kap N * l33Kap M * l33Kap (GeneralLinearGroup.inverseTranspose N⁻¹) *
              l33Kap (M⁻¹) := by
            simp only [W, map_mul]
        _ = l33Kap N * l33Kap M *
              (dualAut 3 (ZMod 3) * (l33Kap N)⁻¹ * dualAut 3 (ZMod 3)) *
              (l33Kap M)⁻¹ := by
            rw [hN_inv, hMinv]
        _ = (l33Kap N * u * (l33Kap N)⁻¹) * u⁻¹ := by
            rw [hM_eq, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left hδ2]
            exact a1413L33Core_delta_cancel (dualAut 3 (ZMod 3)) (l33Kap N) u hδ2
    refine ⟨l33Kap W, ?_, ?_, l33X_normalized W⟩
    · rw [← map_mul, hW2, l33Kap_neg_one]
    · exact a1413L33Core_mem_iSup A u W N hu (a1413L33Core_kap_mem_centralizer N) hWu

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
