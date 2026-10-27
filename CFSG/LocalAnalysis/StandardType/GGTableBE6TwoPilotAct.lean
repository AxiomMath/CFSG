module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotRel
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  TableBExc.E6Three E6TwoMat

namespace E6TwoPilot

@[expose] def msFun (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  v 0 • msCol 0 + v 1 • msCol 1 + v 2 • msCol 2 + v 3 • msCol 3

@[expose] def mtFun (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![v 2, v 0, v 1, v 3]

theorem msFun_add (v w : Fin 4 → ZMod 3) : msFun (v + w) = msFun v + msFun w := by
  simp only [msFun, Pi.add_apply, add_smul]
  abel

theorem mtFun_add (v w : Fin 4 → ZMod 3) : mtFun (v + w) = mtFun v + mtFun w := by
  funext k
  fin_cases k <;> rfl

theorem msFun_cube : ∀ v : Fin 4 → ZMod 3, msFun (msFun (msFun v)) = v := by
  decide +kernel

theorem mtFun_cube : ∀ v : Fin 4 → ZMod 3, mtFun (mtFun (mtFun v)) = v := by
  decide +kernel

theorem msFun_mtFun : ∀ v : Fin 4 → ZMod 3, msFun (mtFun v) = mtFun (msFun v) := by
  decide +kernel

theorem msFun_single (i : Fin 4) (a : ZMod 3) : msFun (Pi.single i a) = a • msCol i := by
  fin_cases i <;> simp [msFun]

theorem mtFun_single (i : Fin 4) (a : ZMod 3) :
    mtFun (Pi.single i a) = Pi.single (tPerm i) a := by
  fin_cases i <;> funext k <;> fin_cases k <;> rfl

@[expose] def msEquiv : (Fin 4 → ZMod 3) ≃+ (Fin 4 → ZMod 3) where
  toFun := msFun
  invFun v := msFun (msFun v)
  left_inv v := msFun_cube v
  right_inv v := msFun_cube v
  map_add' := msFun_add

@[expose] def mtEquiv : (Fin 4 → ZMod 3) ≃+ (Fin 4 → ZMod 3) where
  toFun := mtFun
  invFun v := mtFun (mtFun v)
  left_inv v := mtFun_cube v
  right_inv v := mtFun_cube v
  map_add' := mtFun_add

@[expose] def msAut : MulAut (Multiplicative (Fin 4 → ZMod 3)) :=
  AddEquiv.toMultiplicative msEquiv

@[expose] def mtAut : MulAut (Multiplicative (Fin 4 → ZMod 3)) :=
  AddEquiv.toMultiplicative mtEquiv

theorem msAut_ofAdd (v : Fin 4 → ZMod 3) : msAut (.ofAdd v) = .ofAdd (msFun v) :=
  rfl

theorem mtAut_ofAdd (v : Fin 4 → ZMod 3) : mtAut (.ofAdd v) = .ofAdd (mtFun v) :=
  rfl

theorem msAut_pow_three : msAut ^ 3 = 1 := by
  refine MulEquiv.ext fun n => ?_
  change msAut (msAut (msAut n)) = n
  exact msFun_cube n

theorem mtAut_pow_three : mtAut ^ 3 = 1 := by
  refine MulEquiv.ext fun n => ?_
  change mtAut (mtAut (mtAut n)) = n
  exact mtFun_cube n

theorem commute_msAut_mtAut : Commute msAut mtAut := by
  refine MulEquiv.ext fun n => ?_
  change msAut (mtAut n) = mtAut (msAut n)
  exact msFun_mtFun n

abbrev G9 : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

@[expose] noncomputable def phiAct : G9 →* MulAut (Multiplicative (Fin 4 → ZMod 3)) :=
  MonoidHom.noncommCoprod (RankThree.CentralCover.zmodPowHom msAut msAut_pow_three)
    (RankThree.CentralCover.zmodPowHom mtAut mtAut_pow_three)
    fun _ _ => Commute.pow_pow commute_msAut_mtAut _ _

theorem phiAct_apply (g : G9) :
    phiAct g = msAut ^ (Multiplicative.toAdd g.1).val * mtAut ^ (Multiplicative.toAdd g.2).val :=
  rfl

theorem iterate_ofAdd (f : MulAut (Multiplicative (Fin 4 → ZMod 3)))
    (F : (Fin 4 → ZMod 3) → Fin 4 → ZMod 3) (hf : ∀ v, f (.ofAdd v) = .ofAdd (F v)) (k : ℕ)
    (v : Fin 4 → ZMod 3) : (f ^ k) (.ofAdd v) = .ofAdd (F^[k] v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, hf, ih, Function.iterate_succ_apply]

theorem phiAct_ofAdd (g : G9) (v : Fin 4 → ZMod 3) :
    phiAct g (.ofAdd v) = .ofAdd (msFun^[(Multiplicative.toAdd g.1).val]
      (mtFun^[(Multiplicative.toAdd g.2).val] v)) := by
  rw [phiAct_apply, MulAut.mul_apply, iterate_ofAdd mtAut mtFun mtAut_ofAdd,
    iterate_ofAdd msAut msFun msAut_ofAdd]

theorem eq_zero_of_iterate_eq : ∀ a b : ZMod 3,
    (∀ v : Fin 4 → ZMod 3, msFun^[a.val] (mtFun^[b.val] v) = v) → a = 0 ∧ b = 0 := by
  decide +kernel

theorem phiAct_injective : Function.Injective phiAct := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : ∀ v : Fin 4 → ZMod 3, msFun^[(Multiplicative.toAdd g.1).val]
      (mtFun^[(Multiplicative.toAdd g.2).val] v) = v := fun v => by
    have := congrArg (fun f => f (Multiplicative.ofAdd v)) hg
    simp only [MulAut.one_apply, phiAct_ofAdd] at this
    exact Multiplicative.ofAdd.injective this
  obtain ⟨h1, h2⟩ := eq_zero_of_iterate_eq _ _ h
  exact Prod.ext (Multiplicative.toAdd.injective h1) (Multiplicative.toAdd.injective h2)

theorem card_semidirect : Nat.card (Multiplicative (Fin 4 → ZMod 3) ⋊[phiAct] G9) = 3 ^ 6 := by
  rw [SemidirectProduct.card, RankThree.CentralCover.card_multiplicative_fin_zmod, Nat.card_prod]
  change 3 ^ 4 * (Nat.card (ZMod 3) * Nat.card (ZMod 3)) = 3 ^ 6
  rw [Nat.card_zmod]
  norm_num

section Hom

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem torusE6Two_single_eq_pow (h2 : (2 : K) = 0) (i : Fin 4) (a : ZMod 3) :
    torusE6Two (K := K) h2 (.ofAdd (Pi.single i a)) = uE6Two i ^ a.val := by
  rw [torusE6Two_single, RankThree.CentralCover.zmodPowHom_apply]

omit [CharP K 2] in
theorem torusE6Two_nsmul (h2 : (2 : K) = 0) (k : ℕ) (v : Fin 4 → ZMod 3) :
    torusE6Two (K := K) h2 (.ofAdd (k • v)) = torusE6Two h2 (.ofAdd v) ^ k := by
  rw [ofAdd_nsmul, map_pow]

theorem torusE6Two_msAut (h2 : (2 : K) = 0) (n : Multiplicative (Fin 4 → ZMod 3)) :
    sE6Two K * torusE6Two h2 n * (sE6Two K)⁻¹ = torusE6Two h2 (msAut n) := by
  have key : (MulAut.conj (sE6Two K)).toMonoidHom.comp (torusE6Two h2) =
      (torusE6Two h2).comp msAut.toMonoidHom := by
    refine TableBExc.Three.hom_ext_of_single fun i a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : torusE6Two h2 (.ofAdd (msCol i)) = sE6Two K * uE6Two i * (sE6Two K)⁻¹ := by
      rw [sE6Two_mul_uE6Two h2 i, mul_inv_cancel_right]
    have hv : a • msCol i = a.val • msCol i := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    rw [torusE6Two_single_eq_pow, ← conj_pow, msAut_ofAdd, msFun_single, hv, torusE6Two_nsmul,
      hc]
  exact DFunLike.congr_fun key n

theorem torusE6Two_mtAut (h2 : (2 : K) = 0) (n : Multiplicative (Fin 4 → ZMod 3)) :
    tE6Two K * torusE6Two h2 n * (tE6Two K)⁻¹ = torusE6Two h2 (mtAut n) := by
  have key : (MulAut.conj (tE6Two K)).toMonoidHom.comp (torusE6Two h2) =
      (torusE6Two h2).comp mtAut.toMonoidHom := by
    refine TableBExc.Three.hom_ext_of_single fun i a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [torusE6Two_single_eq_pow, ← conj_pow, mtAut_ofAdd, mtFun_single, torusE6Two_single_eq_pow,
      tE6Two_conj_uE6Two]
  exact DFunLike.congr_fun key n

variable (K) in
@[expose] noncomputable def stHom : G9 →* adjointGroup .E6 K :=
  MonoidHom.noncommCoprod (RankThree.CentralCover.zmodPowHom (sE6Two K) sE6Two_pow_three)
    (RankThree.CentralCover.zmodPowHom (tE6Two K) tE6Two_pow_three)
    fun _ _ => Commute.pow_pow (tE6Two_mul_sE6Two (K := K)).symm _ _

theorem stHom_apply (g : G9) :
    stHom K g = sE6Two K ^ (Multiplicative.toAdd g.1).val *
      tE6Two K ^ (Multiplicative.toAdd g.2).val :=
  rfl

omit [CharP K 2] in
theorem conj_pow_torusE6Two (h2 : (2 : K) = 0) {x : adjointGroup .E6 K}
    {f : MulAut (Multiplicative (Fin 4 → ZMod 3))}
    (hx : ∀ n, x * torusE6Two h2 n * x⁻¹ = torusE6Two h2 (f n)) (k : ℕ)
    (n : Multiplicative (Fin 4 → ZMod 3)) :
    x ^ k * torusE6Two h2 n * (x ^ k)⁻¹ = torusE6Two h2 ((f ^ k) n) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ f k, MulAut.mul_apply, ← ih (f n), ← hx n, pow_succ x k]
    group

theorem stHom_conj_torusE6Two (h2 : (2 : K) = 0) (g : G9) (n : Multiplicative (Fin 4 → ZMod 3)) :
    stHom K g * torusE6Two h2 n * (stHom K g)⁻¹ = torusE6Two h2 (phiAct g n) := by
  rw [stHom_apply, phiAct_apply, MulAut.mul_apply,
    ← conj_pow_torusE6Two h2 (torusE6Two_msAut h2), ← conj_pow_torusE6Two h2 (torusE6Two_mtAut h2)]
  group

variable (K) in
@[expose] noncomputable def psiHom (h2 : (2 : K) = 0) :
    Multiplicative (Fin 4 → ZMod 3) ⋊[phiAct] G9 →* adjointGroup .E6 K :=
  SemidirectProduct.lift (torusE6Two h2) (stHom K) fun g =>
    MonoidHom.ext fun n => (stHom_conj_torusE6Two h2 g n).symm

theorem psiHom_apply (h2 : (2 : K) = 0) (x : Multiplicative (Fin 4 → ZMod 3) ⋊[phiAct] G9) :
    psiHom K h2 x = torusE6Two h2 x.left * stHom K x.right :=
  rfl

theorem psiHom_inl (h2 : (2 : K) = 0) (n : Multiplicative (Fin 4 → ZMod 3)) :
    psiHom K h2 (SemidirectProduct.inl n) = torusE6Two h2 n :=
  SemidirectProduct.lift_inl _ _ _ n

theorem psiHom_injective (h2 : (2 : K) = 0) : Function.Injective (psiHom K h2) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [psiHom_apply] at hx
  have hst : stHom K x.right = (torusE6Two h2 x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx
  have hg : x.right = 1 := by
    refine phiAct_injective ?_
    rw [map_one]
    refine MulEquiv.ext fun n => torusE6Two_injective h2 ?_
    rw [MulAut.one_apply, ← stHom_conj_torusE6Two h2, hst, inv_inv, ← map_inv, ← map_mul,
      ← map_mul]
    congr 1
    rw [mul_comm _ x.left, mul_inv_cancel_left]
  have hn : x.left = 1 := by
    rw [hg, map_one, mul_one] at hx
    exact torusE6Two_injective h2 (hx.trans (map_one _).symm)
  exact SemidirectProduct.ext hn hg

theorem card_range_psiHom (h2 : (2 : K) = 0) : Nat.card (psiHom K h2).range = 3 ^ 6 := by
  rw [← card_semidirect, ← Nat.card_congr (MonoidHom.ofInjective (psiHom_injective h2)).toEquiv]

end Hom

end E6TwoPilot

end CFSG.StandardType
