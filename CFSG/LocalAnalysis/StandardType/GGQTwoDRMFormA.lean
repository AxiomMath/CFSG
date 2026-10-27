module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coordinates

variable {m : ℕ}

theorem ggDSimple_chain {k : Fin m} (hk : k.val + 1 < m) :
    ggDSimple 3 m k = dBasis m k - dBasis m ⟨k.val + 1, hk⟩ := by
  funext j
  simp only [ggDSimple, if_pos hk, Pi.sub_apply, dBasis, Pi.basisFun_apply, Pi.single_apply,
    Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem ggDSimple_fork {k : Fin m} (hk : ¬ k.val + 1 < m) (hm : 2 ≤ m) :
    ggDSimple 3 m k = dBasis m ⟨m - 2, by omega⟩ + dBasis m ⟨m - 1, by omega⟩ := by
  funext j
  simp only [ggDSimple, if_neg hk, Pi.add_apply, dBasis, Pi.basisFun_apply, Pi.single_apply,
    Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem dDot_ggDSimple (hm : 4 ≤ m) (i j : Fin m) :
    dDot m (ggDSimple 3 m i) (ggDSimple 3 m j) = (CartanMatrix.D m i j : ZMod 3) :=
  ggQ2_DW_simple_dot 3 m hm i j

theorem ggDSimple_linearIndependent (hm : 4 ≤ m) : LinearIndependent (ZMod 3) (ggDSimple 3 m) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hG : ∀ j : Fin m, ∑ i, g i * (CartanMatrix.D m i j : ZMod 3) = 0 := by
    intro j
    have h := congrArg (fun v => dDot m v (ggDSimple 3 m j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [dDot_ggDSimple hm]
  have hdet : (Matrix.of fun i j : Fin m => (CartanMatrix.D m i j : ZMod 3)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j : Fin m => (CartanMatrix.D m i j : ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.D m) := by
      ext i j
      rfl
    rw [hmap, ← RingHom.map_det, CartanMatrix.D_det (by omega)]
    decide
  have hv : Matrix.vecMul g (Matrix.of fun i j : Fin m => (CartanMatrix.D m i j : ZMod 3)) = 0 := by
    funext j
    simpa [Matrix.vecMul, dotProduct] using hG j
  exact fun j => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) j

theorem cartanD_zero_row (hm : 4 ≤ m) (y : Fin m) (hy : y.val ≠ 0) :
    CartanMatrix.D m ⟨0, by omega⟩ y ≠ 0 ↔ y.val = 1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

end Coordinates

@[expose, reducible] noncomputable def dRMLin (m : ℕ) (hm : 4 ≤ m) : GGQ2Lin 3 where
  ι := Fin m
  coxeter := ggCoxeterMatrixD m
  cartan := CartanMatrix.D m
  V := DVec m
  coroot := ggDSimple 3 m
  root := fun k => dDot m (ggDSimple 3 m k)
  a := ⟨0, by omega⟩
  b := ⟨1, by omega⟩
  a_ne_b := by simp [Fin.ext_iff]
  a_leaf := by
    refine ⟨⟨1, by omega⟩, ⟨by simp [Fin.ext_iff], ?_⟩, ?_⟩
    · exact (cartanD_zero_row hm ⟨1, by omega⟩ (by simp)).mpr rfl
    · rintro y ⟨hy, hy'⟩
      exact Fin.ext ((cartanD_zero_row hm y fun h => hy (Fin.ext h)).mp hy')
  isWeyl := Or.inl ⟨m, Equiv.refl _, by omega, Or.inr (Or.inr ⟨hm, by
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl⟩)⟩
  isCartan := ggIntCartan_D m
  pairing := fun i j => dDot_ggDSimple hm i j

section Weyl

variable {m : ℕ}

theorem dDot_comm (v w : DVec m) : dDot m v w = dDot m w v := dotProduct_comm v w

theorem dDot_dBasis_right (v : DVec m) (i : Fin m) : dDot m v (dBasis m i) = v i := by
  rw [dDot_apply]
  simp [dBasis, Pi.basisFun_apply]

theorem eq_dTau_of_dDot_reflection (ε : Bool) {a b : Fin m} (hab : a ≠ b) {c : DVec m}
    (hc : c = dBasis m a - (if ε then (-1 : ZMod 3) else 1) • dBasis m b)
    {T : DVec m ≃ₗ[ZMod 3] DVec m} (hT : ∀ v, T v = v - dDot m c v • c) :
    T = dTau m ε a b := by
  have hs : (if ε then (-1 : ZMod 3) else 1) * (if ε then (-1 : ZMod 3) else 1) = 1 := by
    cases ε <;> decide
  generalize hsdef : (if ε then (-1 : ZMod 3) else 1) = s at hc hs
  have hca : c a = 1 := by
    rw [hc]
    simp [dBasis, hab]
  have hcb : c b = -s := by
    rw [hc]
    simp [dBasis, Ne.symm hab]
  refine (dBasis m).ext' fun i => ?_
  rw [hT, dDot_dBasis_right]
  by_cases hia : i = a
  · subst hia
    rw [dTau_apply_left m ε hab, hsdef, hca, hc]
    module
  · by_cases hib : i = b
    · subst hib
      rw [dTau_apply_right m ε hab, hsdef, hcb, hc]
      have : dBasis m i - (-s) • (dBasis m a - s • dBasis m i) =
          s • dBasis m a + (1 - s * s) • dBasis m i := by module
      rw [this, hs, sub_self, zero_smul, add_zero]
    · have hci : c i = 0 := by
        rw [hc]
        simp [dBasis, hia, hib]
      rw [dTau_apply_of_ne m ε hia hib, hci, zero_smul, sub_zero]

theorem dRMLin_simpleRefl_mem (hm : 4 ≤ m) (k : Fin m) :
    (dRMLin m hm).simpleRefl k ∈ dEven m := by
  have hrefl : ∀ v : DVec m, (dRMLin m hm).simpleRefl k v =
      v - dDot m (ggDSimple 3 m k) v • ggDSimple 3 m k := fun v =>
    Module.reflection_apply v ((dRMLin m hm).root_coroot_self k)
  by_cases hk : k.val + 1 < m
  · have hne : k ≠ ⟨k.val + 1, hk⟩ := by simp [Fin.ext_iff]
    rw [eq_dTau_of_dDot_reflection false hne (by simpa using ggDSimple_chain hk) hrefl]
    exact dTau_mem_dEven m false hne
  · have hne : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
    rw [eq_dTau_of_dDot_reflection true hne (by simp [ggDSimple_fork hk (by omega)]) hrefl]
    exact dTau_mem_dEven m true hne

theorem dRMLin_basis (hm : 4 ≤ m) : (dRMLin m hm).Basis :=
  ⟨ggDSimple_linearIndependent hm, by simp [Module.finrank_fintype_fun_eq_card]⟩

theorem dRMLin_weyl_le (hm : 4 ≤ m) : (dRMLin m hm).weyl ≤ dEven m := by
  unfold GGQ2Lin.weyl GGQ2Lin.parab
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact dRMLin_simpleRefl_mem hm k

theorem dRMLin_hβh (hm : 4 ≤ m) (γ : ↥(dRMLin m hm).rootPairs) (v : DVec m) :
    dDot m γ.1.2 v = (1 : ZMod 3) * γ.1.1 v := by
  obtain ⟨k, w, hw, h2, h1⟩ := γ.2
  have hwE : w ∈ dEven m := dRMLin_weyl_le hm hw
  have h3 : γ.1.1 v = dDot m (ggDSimple 3 m k) (w.symm v) := by
    rw [h1]
    rfl
  rw [one_mul, h3, h2]
  have h4 := dEven_dDot hwE (ggDSimple 3 m k) (w.symm v)
  rw [LinearEquiv.apply_symm_apply] at h4
  exact h4

end Weyl

end CFSG.StandardType.QTwo

end
