module

public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRankOne

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

section Split

variable {K : Type*} [Field K] {p : ℕ} {r : ℕ}

theorem torusElt_apply_single (d : Fin r → Kˣ) (c : Fin r ⊕ Fin r) :
    torusElt r K d (Pi.single c 1) = ((Sum.elim d d⁻¹ c : Kˣ) : K) • Pi.single c 1 := by
  funext c'
  rw [torusElt_apply, Pi.smul_apply, Pi.single_apply]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

theorem span_range_single_eq_top :
    Submodule.span K (Set.range fun c : Fin r ⊕ Fin r => (Pi.single c (1 : K) :
      Fin r ⊕ Fin r → K)) = ⊤ := by
  have h := (Pi.basisFun K (Fin r ⊕ Fin r)).span_eq
  have e : (⇑(Pi.basisFun K (Fin r ⊕ Fin r))) =
      fun c : Fin r ⊕ Fin r => (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) :=
    funext fun c => Pi.basisFun_apply K _ c
  rwa [e] at h

end Split

section Roots

variable {K : Type*} [Field K] {p r : ℕ}

theorem apply_single_of_chars [NeZero p]
    {A : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))} {ζ : K} (hζ : ζ ^ p = 1)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inl i) 1) =
          ζ ^ (χ i g).toAdd.val • Pi.single (Sum.inl i) 1 ∧
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inr i) 1) =
          (ζ ^ (χ i g).toAdd.val)⁻¹ • Pi.single (Sum.inr i) 1)
    (g : A) (c : Fin r ⊕ Fin r) :
    (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single c 1) =
      zetaPow ζ (coordChar χ c g).toAdd • Pi.single c 1 := by
  rcases c with i | i
  · exact (hχ g i).1
  · rw [(hχ g i).2]
    simp only [coordChar, Sum.elim_inr, MonoidHom.inv_apply, toAdd_inv, zetaPow_neg hζ]
    rfl

theorem split_root_le_derivedCentralizer (hp : p.Prime) (hp3 : 3 < p) {ζ : K}
    (hζ : orderOf ζ = p) (A : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))
    (hAG : A ≤ orthElementaryGroup (quadPlus r K)) (hAcard : Nat.card A = p ^ 2)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inl i) 1) =
          ζ ^ (χ i g).toAdd.val • Pi.single (Sum.inl i) 1 ∧
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inr i) 1) =
          (ζ ^ (χ i g).toAdd.val)⁻¹ • Pi.single (Sum.inr i) 1)
    {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a ∈ A, a ≠ 1 ∧
      rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ2 : ζ * ζ ≠ 1 := fun h => by
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have h2 := Nat.le_of_dvd (by norm_num) (hζ ▸ h1)
    omega
  obtain ⟨a, b, hab, hwt, h1, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
  obtain ⟨g, hg1, hgψ⟩ := exists_ne_one_mem_ker hp hAcard (coordChar χ a * (coordChar χ b)⁻¹)
  have hgab : coordChar χ a g = coordChar χ b g := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at hgψ
    exact hgψ
  refine ⟨(g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)), g.2, fun h => hg1 (Subtype.ext h),
    ?_⟩
  have hgc := apply_single_of_chars hζp χ hχ g
  have hκ : zetaPow ζ (coordChar χ a g).toAdd * zetaPow ζ (coordChar χ b.swap g).toAdd = 1 := by
    rw [← zetaPow_add hζp, coordChar_swap, MonoidHom.inv_apply, toAdd_inv, hgab, add_neg_cancel,
      zetaPow_zero]
  set ζ' : Kˣ := Units.mk0 ζ hζ0 with hζ'
  set δ := torusElt r K fun i => ζ' ^ α i with hδ
  have hδG : δ ∈ orthElementaryGroup (quadPlus r K) := by
    have h := rootH_mem (r := r) (K := K) α ζ
    rwa [show rootH r K α ζ = δ from rootH_eq_torusElt hα ζ'] at h
  have hδc : ∀ c : Fin r ⊕ Fin r,
      δ (Pi.single c 1) = ((ζ' ^ (coordWt c ⬝ᵥ α) : Kˣ) : K) • Pi.single c 1 := fun c => by
    rw [hδ, torusElt_apply_single, sumElim_zpow_eq]
  have hα' : α = coordWt a - coordWt b := hwt.symm
  have hμ : coordWt a ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct, ite_eq_left rfl,
      ite_eq_right (ne_of_coordIdx_ne hab), ite_eq_right (ne_swap_of_coordIdx_ne hab)]
    norm_num
  have hν : coordWt b.swap ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct,
      ite_eq_right (fun h => ne_swap_of_coordIdx_ne hab h.symm),
      ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, ite_eq_right (swap_ne_self b),
      ite_eq_left rfl]
    norm_num
  have hδa : δ * (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * δ :=
    mul_comm_of_eigen span_range_single_eq_top (by
      rintro _ ⟨c, rfl⟩
      exact ⟨_, _, hδc c, hgc c⟩)
  have hG₀ : orthElementaryGroup (quadPlus r K) ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus r K) := orthElementaryGroup_le _
  have hpolar : ∀ t : K, polar (quadPlus r K) (Pi.single a 1) (t • -(Pi.single b.swap 1)) = 0 :=
    fun t => by
      rw [smul_neg, polar_neg_right,
        polar_single_smul_single (swap_ne_swap_of_coordIdx_ne hab).symm t, neg_zero]
  rintro _ ⟨t, rfl⟩
  have hrp : rootElt r K α t = eichler (quadPlus r K) (Pi.single a 1)
      (t • -(Pi.single b.swap 1)) := by
    rw [h1]
    show eichler (quadPlus r K) (Pi.single a 1) ((-t) • Pi.single b.swap 1) = _
    rw [smul_neg, neg_smul]
  rw [hrp]
  refine eichler_mem_derivedCentralizer (Q := quadPlus r K) hG₀ (hpolar t)
    (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa
    (κ := zetaPow ζ (coordChar χ a g).toAdd) (κ' := zetaPow ζ (coordChar χ b.swap g).toAdd)
    (μ := ζ) (ν := ζ) (hgc a) ?_ hκ ?_ ?_ hζ2
  · rw [smul_neg, map_neg, map_smul, hgc b.swap, smul_neg, smul_comm]
  · rw [hδc a, hμ]
    simp [hζ']
  · rw [smul_neg, map_neg, map_smul, hδc b.swap, hν, smul_neg, smul_comm]
    simp [hζ']

end Roots

end CFSG.RankThree.PartOne.KCOrthogonal
