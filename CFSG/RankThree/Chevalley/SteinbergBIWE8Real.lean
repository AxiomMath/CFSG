module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

abbrev V8 := Fin Tag.E8.rank → ℝ

@[expose] def castV (v : L8) : V8 := fun k => (v k : ℝ)

theorem castV_injective : Function.Injective castV := fun u v h =>
  funext fun k => by
    have e := congrFun h k
    simp only [castV] at e
    exact_mod_cast e

theorem castV_sub (u v : L8) : castV (u - v) = castV u - castV v := by
  funext k; simp [castV]

theorem castV_neg (u : L8) : castV (-u) = -castV u := by
  funext k; simp [castV]

theorem castV_zsmul (c : ℤ) (u : L8) : castV (c • u) = (c : ℝ) • castV u := by
  funext k; simp [castV]

theorem castV_single (j : Fin Tag.E8.rank) : castV (eb j) = Pi.single j 1 := by
  funext k
  simp only [castV, eb, Pi.single_apply]
  split_ifs <;> simp

@[expose] def intMat (w : W8) : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  fun i j => (w • eb j) i

theorem intMat_mulVec (w : W8) (v : L8) : intMat w *ᵥ v = w • v := by
  funext i
  rw [smul_eq_sum_smul_single w v, Finset.sum_apply, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intMat, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem intMat_mul (w w' : W8) : intMat (w * w') = intMat w * intMat w' := by
  ext i j
  rw [intMat, mul_smul, ← intMat_mulVec w, mul_apply, mulVec, dotProduct]
  rfl

theorem intMat_one : intMat 1 = 1 := by
  ext i j
  simp only [intMat, one_smul, eb, one_apply, Pi.single_apply]

@[expose] def realAct (w : W8) : V8 →ₗ[ℝ] V8 := ((intMat w).map (Int.castRingHom ℝ)).mulVecLin

theorem realAct_castV (w : W8) (v : L8) : realAct w (castV v) = castV (w • v) := by
  funext i
  rw [realAct, mulVecLin_apply, ← intMat_mulVec, castV]
  simp only [mulVec, dotProduct, map_apply, castV, Int.cast_sum, Int.cast_mul, eq_intCast]

theorem realAct_mul (w w' : W8) : realAct (w * w') = realAct w ∘ₗ realAct w' := by
  rw [realAct, realAct, realAct, intMat_mul, Matrix.map_mul, mulVecLin_mul]

theorem realAct_one : realAct 1 = LinearMap.id := by
  rw [realAct, intMat_one, Matrix.map_one _ (map_zero _) (map_one _), mulVecLin_one]

theorem realAct_mul_apply (w w' : W8) (v : V8) : realAct (w * w') v = realAct w (realAct w' v) := by
  rw [realAct_mul]
  rfl

theorem linearMap_ext_castV {f g : V8 →ₗ[ℝ] V8} (h : ∀ v : L8, f (castV v) = g (castV v)) :
    f = g := by
  refine LinearMap.pi_ext fun j x => ?_
  have e : (Pi.single j x : V8) = x • castV (eb j) := by
    rw [castV_single]
    funext k
    simp [Pi.single_apply]
  rw [e, map_smul, map_smul, h]

theorem realAct_injective : Function.Injective realAct := by
  intro w w' h
  refine ext_single fun i => castV_injective ?_
  rw [← realAct_castV, ← realAct_castV, h]

@[expose] def e8Form : LinearMap.BilinForm ℝ V8 :=
  Matrix.toBilin' ((Tag.cartan .E8).map (Int.castRingHom ℝ))

theorem e8Form_apply (u v : V8) :
    e8Form u v = ∑ i, ∑ j, u i * (Tag.cartan .E8 i j : ℝ) * v j := by
  rw [e8Form, Matrix.toBilin'_apply]
  simp only [map_apply, eq_intCast]

theorem e8Form_castV (u v : L8) : e8Form (castV u) (castV v) = iform u v := by
  rw [e8Form_apply, iform]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_E8]
  rfl

theorem e8Form_self_root {β : L8} (hβ : IsRoot .E8 β) : e8Form (castV β) (castV β) = 2 := by
  rw [e8Form_castV, iform_self_of_isRoot hβ]
  norm_num

theorem realAct_rootReflection {β : L8} (hβ : IsRoot .E8 β) (v : V8) :
    realAct (rootReflection β) v = v - e8Form (castV β) v • castV β := by
  have h : realAct (rootReflection β) =
      LinearMap.id - (e8Form (castV β)).smulRight (castV β) := by
    refine linearMap_ext_castV fun u => ?_
    have hc := corootPair_mul hβ u
    rw [iform_self_of_isRoot hβ] at hc
    have hc' : corootPair β u = iform β u := by linarith
    rw [realAct_castV, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      e8Form_castV, rootReflection_smul hβ, castV_sub, castV_zsmul, hc']
  rw [h, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]

variable {k : ℕ}

@[expose] def prodRefl (β : Fin k → L8) : W8 := (List.ofFn fun i => rootReflection (β i)).prod

@[expose] def IsOrthFrame (β : Fin k → L8) : Prop :=
  (∀ i, IsRoot .E8 (β i)) ∧ Pairwise fun i j => iform (β i) (β j) = 0

theorem IsOrthFrame.tail {β : Fin (k + 1) → L8} (h : IsOrthFrame β) :
    IsOrthFrame (fun i : Fin k => β i.succ) :=
  ⟨fun _ => h.1 _, fun _ _ hij => h.2 (Fin.succ_injective _ |>.ne hij)⟩

theorem IsOrthFrame.form {β : Fin k → L8} (h : IsOrthFrame β) (i j : Fin k) :
    e8Form (castV (β i)) (castV (β j)) = if i = j then 2 else 0 := by
  split_ifs with hij
  · subst hij
    exact e8Form_self_root (h.1 i)
  · rw [e8Form_castV, h.2 hij]
    norm_num

theorem realAct_prodRefl {β : Fin k → L8} (h : IsOrthFrame β) (v : V8) :
    realAct (prodRefl β) v = v - ∑ i, e8Form (castV (β i)) v • castV (β i) := by
  induction k generalizing v with
  | zero =>
    rw [prodRefl, List.ofFn_zero, List.prod_nil, realAct_one, LinearMap.id_apply,
      Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  | succ k ih =>
    have ht := ih h.tail
    have e : prodRefl β = rootReflection (β 0) * prodRefl fun i : Fin k => β i.succ := by
      rw [prodRefl, prodRefl, List.ofFn_succ, List.prod_cons]
    rw [e, realAct_mul_apply, ht, realAct_rootReflection (h.1 0), Fin.sum_univ_succ]
    have h0 : ∀ i : Fin k, e8Form (castV (β 0)) (castV (β i.succ)) = 0 := fun i => by
      rw [h.form, ite_eq_right (Fin.succ_ne_zero i).symm]
    have hB : e8Form (castV (β 0)) (v - ∑ i : Fin k, e8Form (castV (β i.succ)) v •
        castV (β i.succ)) = e8Form (castV (β 0)) v := by
      rw [map_sub, map_sum]
      simp only [map_smul, h0, smul_zero, Finset.sum_const_zero, sub_zero]
    rw [hB]
    abel

@[expose] def negSpace (w : W8) : Submodule ℝ V8 := LinearMap.ker (realAct w + LinearMap.id)

theorem mem_negSpace {w : W8} {v : V8} : v ∈ negSpace w ↔ realAct w v = -v := by
  rw [negSpace, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]

end CFSG.RankThree.Chevalley.WeylE8
