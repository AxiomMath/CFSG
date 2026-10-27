module

public import CFSG.Quasithin.H13.L32NMatNGen
public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H.Mathieu.H12Pf

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.H13.MatNCert

@[expose] def cf (x : FieldFour) (b : Bool) : ZMod 2 := if b then imZ x else reZ x

@[expose] def beta (b : Bool) : FieldFour := if b then ω else 1

theorem cf_add (x y : FieldFour) (b : Bool) : cf (x + y) b = cf x b + cf y b := by
  revert x y b
  decide

theorem cf_zero (b : Bool) : cf 0 b = 0 := by
  revert b
  decide

@[expose] def cfHom (b : Bool) : FieldFour →+ ZMod 2 where
  toFun x := cf x b
  map_zero' := cf_zero b
  map_add' x y := cf_add x y b

theorem cf_mul (x y : FieldFour) (a : Bool) :
    cf (x * y) a = cf (x * beta true) a * cf y true + cf (x * beta false) a * cf y false := by
  revert x y a
  decide

@[expose] def idxEquiv : Fin 6 × Bool ≃ Fin 12 where
  toFun p := ⟨2 * p.1 + (if p.2 then 1 else 0), by have := p.1.isLt; split <;> omega⟩
  invFun k := (⟨k / 2, by omega⟩, k % 2 == 1)
  left_inv := by decide
  right_inv := by decide

@[expose] def realV (v : Fin 6 → FieldFour) (k : Fin 12) : ZMod 2 :=
  cf (v (idxEquiv.symm k).1) (idxEquiv.symm k).2

@[expose] def bv (k : Fin 12) : Fin 6 → FieldFour :=
  Pi.single (idxEquiv.symm k).1 (beta (idxEquiv.symm k).2)

@[expose] def realM (M : Matrix (Fin 6) (Fin 6) FieldFour) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun k l => realV (M.mulVec (bv l)) k

theorem realV_add (v w : Fin 6 → FieldFour) : realV (v + w) = realV v + realV w := by
  funext k
  exact cf_add _ _ _

theorem mulVec_single_apply (M : Matrix (Fin 6) (Fin 6) FieldFour) (j : Fin 6) (x : FieldFour)
    (i : Fin 6) : M.mulVec (Pi.single j x) i = M i j * x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem realV_mulVec (M : Matrix (Fin 6) (Fin 6) FieldFour) (v : Fin 6 → FieldFour) :
    realV (M.mulVec v) = (realM M).mulVec (realV v) := by
  funext k
  set i := (idxEquiv.symm k).1
  set a := (idxEquiv.symm k).2
  have hl : realV (M.mulVec v) k = ∑ j, cf (M i j * v j) a := by
    change cfHom a (M.mulVec v i) = ∑ j, cfHom a (M i j * v j)
    rw [Matrix.mulVec, dotProduct, map_sum]
  have hr : (realM M).mulVec (realV v) k =
      ∑ j, (cf (M i j * beta true) a * cf (v j) true +
        cf (M i j * beta false) a * cf (v j) false) := by
    simp only [Matrix.mulVec, dotProduct, realM, Matrix.of_apply]
    rw [← Equiv.sum_comp idxEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    simp only [realV, bv, Equiv.symm_apply_apply, mulVec_single_apply, i, a]
  rw [hl, hr]
  exact Finset.sum_congr rfl fun j _ => cf_mul _ _ _

@[expose] def unrealV (w : Fin 12 → ZMod 2) (j : Fin 6) : FieldFour :=
  ⟨decide (w (idxEquiv (j, false)) = 1), decide (w (idxEquiv (j, true)) = 1)⟩

theorem realV_unrealV (w : Fin 12 → ZMod 2) : realV (unrealV w) = w := by
  funext k
  obtain ⟨⟨j, b⟩, rfl⟩ := idxEquiv.surjective k
  have key : ∀ c₀ c₁ : ZMod 2, ∀ b : Bool,
      cf ⟨decide (c₀ = 1), decide (c₁ = 1)⟩ b = if b then c₁ else c₀ := by decide
  simp only [realV, unrealV, Equiv.symm_apply_apply, key]
  cases b <;> rfl

theorem unrealV_realV (v : Fin 6 → FieldFour) : unrealV (realV v) = v := by
  funext j
  simp only [unrealV, realV, Equiv.symm_apply_apply]
  generalize v j = x
  revert x
  decide

theorem realV_injective : Function.Injective realV := fun v w h => by
  rw [← unrealV_realV v, h, unrealV_realV]

theorem realV_surjective : Function.Surjective realV := fun w => ⟨unrealV w, realV_unrealV w⟩

theorem matrix_ext_of_mulVec {A B : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (h : ∀ v, A.mulVec (realV v) = B.mulVec (realV v)) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := realV_surjective w
  simpa using h v

theorem realM_mul (M N : Matrix (Fin 6) (Fin 6) FieldFour) :
    realM (M * N) = realM M * realM N :=
  matrix_ext_of_mulVec fun v => by
    rw [← realV_mulVec, ← Matrix.mulVec_mulVec, realV_mulVec, realV_mulVec,
      Matrix.mulVec_mulVec]

theorem realM_one : realM 1 = 1 :=
  matrix_ext_of_mulVec fun v => by rw [← realV_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

@[expose] def realHom : Matrix (Fin 6) (Fin 6) FieldFour →* Matrix (Fin 12) (Fin 12) (ZMod 2) where
  toFun := realM
  map_one' := realM_one
  map_mul' := realM_mul

@[expose] def realGL : GL (Fin 6) FieldFour →* GL (Fin 12) (ZMod 2) := Units.map realHom

theorem realGL_val (g : GL (Fin 6) FieldFour) :
    ((realGL g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      realM (g : Matrix (Fin 6) (Fin 6) FieldFour) := rfl

theorem realV_mulVec_GL (g : GL (Fin 6) FieldFour) (v : Fin 6 → FieldFour) :
    realV ((g : Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
      ((realGL g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (realV v) := by
  rw [realGL_val, realV_mulVec]

theorem realGL_injective : Function.Injective realGL := by
  intro g h hgh
  have hM : realM (g : Matrix (Fin 6) (Fin 6) FieldFour) =
      realM (h : Matrix (Fin 6) (Fin 6) FieldFour) := congrArg Units.val hgh
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply realV_injective
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, realV_mulVec, realV_mulVec, hM]

theorem realM_gens : colsN (realM hatM22N1) = H12Cert.gG.getD 0 [] ∧
    colsN (realM hatM22N2) = H12Cert.gG.getD 1 [] := by
  decide +kernel

theorem map_realGL_hatM22Γ₀ : hatM22Γ₀.map realGL = genSubN 12 H12Cert.gG := by
  rw [hatM22Γ₀, MonoidHom.map_closure, genSubN]
  congr 1
  ext g
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq]
  have h1 : colsN ((realGL hatM22G1 : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)) = H12Cert.gG.getD 0 [] := realM_gens.1
  have h2 : colsN ((realGL hatM22G2 : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)) = H12Cert.gG.getD 1 [] := realM_gens.2
  have hgG : H12Cert.gG = [H12Cert.gG.getD 0 [], H12Cert.gG.getD 1 []] := by decide +kernel
  constructor
  · rintro (rfl | rfl)
    · rw [h1, hgG]; simp
    · rw [h2, hgG]; simp
  · intro hg
    rw [hgG] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg
    · exact Or.inl (H13.MatNCert.eq_of_colsN_eq (hg.trans h1.symm))
    · exact Or.inr (H13.MatNCert.eq_of_colsN_eq (hg.trans h2.symm))

end CFSG.Quasithin.H.Mathieu.H12Pf
