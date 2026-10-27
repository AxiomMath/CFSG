module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.OrthOrderBound

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Matrices

variable {m : ℕ}

theorem dDiag_apply (d : Fin m → (ZMod 3)ˣ) (v : DVec m) (k : Fin m) :
    ZS.diagMap 3 (dBasis m) d v k = (d k : ZMod 3) * v k := by
  simp [ZS.diagMap, dBasis, Pi.basisFun_equivFun, LinearEquiv.smulOfUnit, Units.smul_def]

theorem dSign_apply_vec (a b : Fin m) (v : DVec m) (k : Fin m) :
    dSign m a b v k = if k = a ∨ k = b then -v k else v k := by
  rw [dSign, dDiag_apply]
  by_cases h : k = a ∨ k = b <;> simp [h]

theorem dNeg_apply_coord (i : Fin m) (v : DVec m) (k : Fin m) :
    dNeg m i v k = if k = i then -v k else v k := by
  rw [dNeg, dDiag_apply]
  by_cases h : k = i <;> simp [h]

theorem dSign_mem_dEven {a b : Fin m} (hab : a ≠ b) : dSign m a b ∈ dEven m := by
  have h : dSign m a b = (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b := by
    rw [dTau, if_pos rfl, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]
  exact (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m _)) (dTau_mem_dEven m true hab)

theorem dEven_fix_zero (hm : 2 ≤ m) (v : DVec m) (hv : ∀ g ∈ dEven m, g v = v) : v = 0 := by
  funext k
  obtain ⟨b, hb⟩ : ∃ b : Fin m, b ≠ k := by
    by_cases h0 : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
  have h1 := congrFun (hv (dSign m k b) (dSign_mem_dEven (Ne.symm hb))) k
  rw [dSign_apply_vec, if_pos (Or.inl rfl)] at h1
  have h2 : ∀ x : ZMod 3, -x = x → x = 0 := by decide
  exact h2 _ h1

theorem dEven_comm_top (hm : 2 ≤ m) :
    ggLinCom ((dEven m : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)) :
      Set (DVec m ≃ₗ[ZMod 3] DVec m)) = ⊤ := by
  rw [eq_top_iff, ← (dBasis m).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin m, b ≠ k := by
    by_cases h0 : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
  have hmem : dSign m k b ∈ ((dEven m : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)) :
      Set (DVec m ≃ₗ[ZMod 3] DVec m)) := dSign_mem_dEven (Ne.symm hb)
  have hk : dBasis m k ∈ ggLinMove (dSign m k b) := by
    refine ⟨dBasis m k, ?_⟩
    have h1 : dSign m k b (dBasis m k) = -dBasis m k := by
      funext j
      rw [dSign_apply_vec]
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj, dBasis, Pi.basisFun_apply]
    have h2 : ∀ x : DVec m, -x - x = x := by
      intro x
      funext j
      have h3 : ∀ y : ZMod 3, -y - y = y := by decide
      exact h3 (x j)
    change dSign m k b (dBasis m k) - dBasis m k = dBasis m k
    rw [h1, h2]
  exact (le_iSup₂ (f := fun a (_ : a ∈ ((dEven m : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)) :
    Set (DVec m ≃ₗ[ZMod 3] DVec m))) => ggLinMove a) (dSign m k b) hmem) hk


theorem dDot_apply (v w : DVec m) : dDot m v w = v ⬝ᵥ w := rfl

theorem dDot_basis (i j : Fin m) :
    dDot m (dBasis m i) (dBasis m j) = if i = j then 1 else 0 := by
  rw [dDot_apply]
  simp only [dBasis, Pi.basisFun_apply, single_dotProduct, Pi.single_apply]
  by_cases h : i = j <;> simp [h]

theorem dEven_dDot {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ dEven m) (v w : DVec m) :
    dDot m (g v) (g w) = dDot m v w := by
  obtain ⟨σ, c, hc, -, hact⟩ := hg
  have hsq : ∀ i, c i * c i = 1 := fun i => by
    rcases hc i with h | h <;> rw [h] <;> decide
  have key : (dDot m).compl₁₂ (g : DVec m →ₗ[ZMod 3] DVec m) (g : DVec m →ₗ[ZMod 3] DVec m) =
      dDot m := by
    refine LinearMap.ext_basis (dBasis m) (dBasis m) fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hact, map_smul, LinearMap.smul_apply,
      dDot_basis, smul_eq_mul]
    by_cases h : i = j
    · subst h; simp [hsq]
    · simp [h, σ.injective.eq_iff]
  exact congrArg (fun B => B v w) key

end Matrices

end CFSG.StandardType.QTwo

end
