module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped BigOperators

private instance instBracketLocal {G : Type*} [Group G] : Bracket G G := commutatorElement

noncomputable section

private theorem ggF8_pow_two_val_injective : Function.Injective (fun e : ZMod 3 => 2 ^ e.val) := by
  intro e f h
  apply ZMod.val_injective
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h

private noncomputable def ggF8LinHom (μ : ZMod 3 → GaloisField 2 3) :
    GaloisField 2 3 →+ GaloisField 2 3 :=
  AddMonoidHom.mk' (fun x => ∑ e : ZMod 3, μ e * x ^ 2 ^ e.val) (by
    intro x y
    rw [show (∑ e : ZMod 3, μ e * (x + y) ^ 2 ^ e.val)
        = ∑ e : ZMod 3, (μ e * x ^ 2 ^ e.val + μ e * y ^ 2 ^ e.val) from by
      apply Finset.sum_congr rfl
      intro e _
      rw [add_pow_char_pow, mul_add]]
    rw [Finset.sum_add_distrib])

private theorem ggF8LinHom_eq_zero {δ : ZMod 3 → GaloisField 2 3}
    (hδ : ∀ x, ∑ e : ZMod 3, δ e * x ^ 2 ^ e.val = 0) : δ = 0 := by
  letI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  let p : Polynomial (GaloisField 2 3) :=
    ∑ e : ZMod 3, Polynomial.C (δ e) * Polynomial.X ^ (2 ^ e.val)
  have hp_eval : ∀ x, p.eval x = 0 := by
    intro x
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact hδ x
  have hpow_le : ∀ e : ZMod 3, 2 ^ e.val ≤ 4 := by
    intro e
    have h : e.val ≤ 2 := by have := ZMod.val_lt e; omega
    calc 2 ^ e.val ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
      _ = 4 := by norm_num
  have hp_nat : p.natDegree ≤ 4 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    show p.coeff m = 0
    simp only [p]
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro e _
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [if_neg]
    intro h
    have := hpow_le e
    omega
  have hcard8 : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hp : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Finset.univ
      (fun x _ => hp_eval x) (by rw [Finset.card_univ, hcard8]; omega)
  funext e
  have hc := congrArg (fun q : Polynomial (GaloisField 2 3) => q.coeff (2 ^ e.val)) hp
  rw [Polynomial.coeff_zero] at hc
  change δ e = 0
  rw [← hc]
  simp only [p]
  rw [Polynomial.finset_sum_coeff]
  have hsingle : (∑ b : ZMod 3,
      (Polynomial.C (δ b) * Polynomial.X ^ (2 ^ b.val)).coeff (2 ^ e.val))
      = (Polynomial.C (δ e) * Polynomial.X ^ (2 ^ e.val)).coeff (2 ^ e.val) :=
    Finset.sum_eq_single e
      (fun b _ hb => by
        rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        exact fun h => hb (ggF8_pow_two_val_injective h).symm)
      (fun he => (he (Finset.mem_univ e)).elim)
  rw [hsingle, Polynomial.coeff_C_mul_X_pow, if_pos rfl]

theorem ggF8_addMonoidHom_eq_linearized (f : GaloisField 2 3 →+ GaloisField 2 3) :
    ∃ μ : ZMod 3 → GaloisField 2 3, ∀ x, f x = ∑ e : ZMod 3, μ e * x ^ 2 ^ e.val := by
  letI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hinj : Function.Injective ggF8LinHom := by
    intro μ ν h
    have hsub : ∀ x, ∑ e : ZMod 3, (μ - ν) e * x ^ 2 ^ e.val = 0 := by
      intro x
      have hx : (∑ e : ZMod 3, μ e * x ^ 2 ^ e.val)
          = ∑ e : ZMod 3, ν e * x ^ 2 ^ e.val := congrFun (congrArg DFunLike.coe h) x
      calc ∑ e : ZMod 3, (μ - ν) e * x ^ 2 ^ e.val
          = (∑ e : ZMod 3, μ e * x ^ 2 ^ e.val)
            - (∑ e : ZMod 3, ν e * x ^ 2 ^ e.val) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro e _
            rw [Pi.sub_apply, sub_mul]
        _ = 0 := by rw [hx, sub_self]
    have hδ0 : (μ - ν) = 0 := ggF8LinHom_eq_zero hsub
    funext e
    have h' : μ e - ν e = 0 := by simpa using congrFun hδ0 e
    exact sub_eq_zero.mp h'
  have hcard : Nat.card (ZMod 3 → GaloisField 2 3)
      = Nat.card (GaloisField 2 3 →+ GaloisField 2 3) := by
    have hD : Nat.card (ZMod 3 → GaloisField 2 3) = 512 := by
      rw [Nat.card_fun, GaloisField.card 2 3 (by norm_num),
        Nat.card_eq_fintype_card, ZMod.card]
      norm_num
    have hC : Nat.card (GaloisField 2 3 →+ GaloisField 2 3) = 512 := by
      rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv,
        Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3),
        Module.finrank_linearMap (ZMod 2) (ZMod 2) (GaloisField 2 3) (GaloisField 2 3),
        GaloisField.finrank 2 (by norm_num), Nat.card_eq_fintype_card, ZMod.card]
      norm_num
    rw [hD, hC]
  haveI : Finite (GaloisField 2 3 →+ GaloisField 2 3) :=
    Finite.of_injective (fun g : GaloisField 2 3 →+ GaloisField 2 3 =>
      (g : GaloisField 2 3 → GaloisField 2 3)) (fun g h gh => DFunLike.ext _ _ (congrFun gh))
  haveI : Finite (ZMod 3 → GaloisField 2 3) := Pi.finite
  obtain ⟨μ, hμ⟩ := (Function.Injective.surjective_of_finite
    ((Finite.card_eq.mp hcard).some) hinj) f
  refine ⟨μ, fun x => ?_⟩
  exact (DFunLike.congr_fun hμ x).symm

private abbrev Idx : Type := Σ _ : Fin 3, Fin 3

private noncomputable def bF8 : Module.Basis (Fin 3) (ZMod 2) (GaloisField 2 3) :=
  Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 3)
    (GaloisField.finrank 2 (by norm_num))

private noncomputable def bV : Module.Basis Idx (ZMod 2) GGSL9V :=
  Pi.basis (fun _ : Fin 3 => bF8)

private theorem bV_apply (i : Idx) : bV i = Pi.single i.1 (bF8 i.2) := by
  rw [bV, Pi.basis_apply]

private noncomputable def phiGL : Matrix.GeneralLinearGroup Idx (ZMod 2) ≃*
    (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  (Matrix.GeneralLinearGroup.toLin' bV).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) GGSL9V)

private noncomputable def psiSL : Matrix.SpecialLinearGroup Idx (ZMod 2) →*
    (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  phiGL.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

private theorem toGL_transvection (i j : Idx) (hij : i ≠ j) (c : ZMod 2) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.GeneralLinearGroup.transvection i j hij c := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.GeneralLinearGroup.val_transvection]
  rfl

private noncomputable def elemT (i j : Idx) (hij : i ≠ j) (c : ZMod 2) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  psiSL (Matrix.SpecialLinearGroup.transvection hij c)

private theorem elemT_comm {a b c : Idx} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (c1 c2 : ZMod 2) :
    ⁅elemT a b hab c1, elemT b c hbc c2⁆ = elemT a c hac (c1 * c2) := by
  unfold elemT
  rw [← map_commutatorElement psiSL]
  rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac c1 c2]

private noncomputable def blockFun (a b : Fin 3) (f : GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3)
    (v : GGSL9V) : GGSL9V :=
  v + Pi.single b (f (v a))

private noncomputable def blockMap (a b : Fin 3) (hab : a ≠ b)
    (f : GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V where
  toFun := blockFun a b f
  map_add' v w := by
    simp only [blockFun, Pi.add_apply, map_add, Pi.single_add]
    abel
  map_smul' c v := by
    simp only [blockFun, Pi.smul_apply, map_smul, Pi.single_smul, smul_add, RingHom.id_apply]
  invFun := blockFun a b f
  left_inv v := by
    simp only [blockFun, Pi.add_apply, Pi.single_eq_of_ne hab, add_zero]
    rw [add_assoc, ← Pi.single_add, CharTwo.add_self_eq_zero, Pi.single_zero, add_zero]
  right_inv v := by
    simp only [blockFun, Pi.add_apply, Pi.single_eq_of_ne hab, add_zero]
    rw [add_assoc, ← Pi.single_add, CharTwo.add_self_eq_zero, Pi.single_zero, add_zero]

private theorem blockMap_add (a b : Fin 3) (hab : a ≠ b)
    (f g : GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3) :
    blockMap a b hab (f + g) = blockMap a b hab f * blockMap a b hab g := by
  apply LinearEquiv.ext
  intro v
  change v + (Pi.single b ((f + g) (v a)) : GGSL9V)
      = (v + (Pi.single b (g (v a)) : GGSL9V))
        + (Pi.single b (f ((v + (Pi.single b (g (v a)) : GGSL9V)) a)) : GGSL9V)
  rw [show (v + (Pi.single b (g (v a)) : GGSL9V)) a = v a by
    rw [Pi.add_apply, Pi.single_eq_of_ne hab, add_zero]]
  change v + (Pi.single b (f (v a) + g (v a)) : GGSL9V)
      = (v + (Pi.single b (g (v a)) : GGSL9V)) + (Pi.single b (f (v a)) : GGSL9V)
  rw [Pi.single_add]
  abel

private noncomputable def linLM (e : ZMod 3) (μ : GaloisField 2 3) :
    GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3 :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun x => μ * x ^ 2 ^ e.val) (by
      intro x y
      rw [add_pow_char_pow, mul_add]))

private theorem blockMap_eq_root (a b : Fin 3) (hab : a ≠ b) (e : ZMod 3) (μ : GaloisField 2 3) :
    blockMap a b hab (linLM e μ) = ggSL9Root a b hab e.val μ := by
  apply LinearEquiv.ext
  intro v
  change blockFun a b (linLM e μ) v = ggSL9Root a b hab e.val μ v
  rfl

private theorem ggSL9Root_mem_J {a b : Fin 3} (hab : a ≠ b) (e : ZMod 3)
    (μ : GaloisField 2 3) : ggSL9Root a b hab e.val μ ∈ ggSL9J a b e := by
  apply Subgroup.subset_closure
  exact Set.mem_union_left _ (Set.mem_setOf.mpr ⟨hab, μ, rfl⟩)

private theorem blockMap_mem_of_J {H : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    {a b : Fin 3} (hab : a ≠ b) (hJ : ∀ e : ZMod 3, ggSL9J a b e ≤ H)
    (f : GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3) : blockMap a b hab f ∈ H := by
  obtain ⟨μ, hμ⟩ := ggF8_addMonoidHom_eq_linearized f.toAddMonoidHom
  have hf : f = ∑ e : ZMod 3, linLM e (μ e) := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sum_apply]
    change f x = ∑ e : ZMod 3, μ e * x ^ 2 ^ e.val
    rw [← hμ x]
    rfl
  have hf3 : f = linLM 0 (μ 0) + linLM 1 (μ 1) + linLM 2 (μ 2) := by
    rw [hf]
    exact Fin.sum_univ_three (fun e => linLM e (μ e))
  rw [hf3, blockMap_add, blockMap_add]
  refine H.mul_mem (H.mul_mem ?_ ?_) ?_
  · rw [blockMap_eq_root]
    exact hJ 0 (ggSL9Root_mem_J hab 0 (μ 0))
  · rw [blockMap_eq_root]
    exact hJ 1 (ggSL9Root_mem_J hab 1 (μ 1))
  · rw [blockMap_eq_root]
    exact hJ 2 (ggSL9Root_mem_J hab 2 (μ 2))

private theorem phiGL_transvection_apply' (i j : Idx) (hij : i ≠ j) (c : ZMod 2) (v : GGSL9V) :
    (phiGL (Matrix.GeneralLinearGroup.transvection i j hij c)) v
      = v + (c * bV.coord j v) • bV i := by
  change (((Matrix.GeneralLinearGroup.toLin' bV)
      (Matrix.GeneralLinearGroup.transvection i j hij c)).toLinearEquiv) v
      = v + (c * bV.coord j v) • bV i
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  rw [Matrix.GeneralLinearGroup.val_transvection]
  rw [show Matrix.transvection i j c = 1 + Matrix.single i j c from rfl]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rw [map_add]
  have hx : (Fintype.linearCombination (ZMod 2) (⇑bV)) (⇑(bV.repr v)) = v := by
    simpa [Fintype.linearCombination_apply] using Module.Basis.sum_repr bV v
  rw [hx]
  rw [Fintype.linearCombination_apply]
  have hsingle : (∑ l, Function.update (0 : Idx → ZMod 2) i
        (c * (⇑(bV.repr v)) j) l • bV l)
      = Function.update (0 : Idx → ZMod 2) i (c * (⇑(bV.repr v)) j) i • bV i := by
    apply Finset.sum_eq_single i
    · intro l _ hli
      rw [Function.update_of_ne hli, Pi.zero_apply, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsingle]
  simp only [Function.update, dif_pos rfl]
  rw [Module.Basis.coord_apply]
  rfl

private noncomputable def crossF (a b : Idx) (c : ZMod 2) :
    GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3 :=
  (LinearMap.toSpanSingleton (ZMod 2) (GaloisField 2 3) (bF8 a.2)) ∘ₗ
    (c • bF8.coord b.2)

private theorem elemT_eq_blockMap (a b : Idx) (hab : a ≠ b) (hba : b.1 ≠ a.1) (c : ZMod 2) :
    elemT a b hab c = blockMap b.1 a.1 hba (crossF a b c) := by
  have hE : elemT a b hab c = phiGL (Matrix.GeneralLinearGroup.transvection a b hab c) := by
    unfold elemT psiSL
    rw [MonoidHom.comp_apply, toGL_transvection]
    rfl
  apply LinearEquiv.ext
  intro v
  change (elemT a b hab c) v = blockFun b.1 a.1 (crossF a b c) v
  rw [hE, phiGL_transvection_apply' a b hab c v]
  change v + (c * bV.coord b v) • bV a = v + Pi.single a.1 (crossF a b c (v b.1))
  have hcoord : bV.coord b v = bF8.coord b.2 (v b.1) := by
    rw [Module.Basis.coord_apply, bV, Pi.basis_repr, Module.Basis.coord_apply]
  rw [hcoord]
  rw [show (c * bF8.coord b.2 (v b.1)) • bV a
      = Pi.single a.1 ((c * bF8.coord b.2 (v b.1)) • bF8 a.2) by
    rw [bV_apply, Pi.single_smul]]
  rw [show crossF a b c (v b.1) = (c * bF8.coord b.2 (v b.1)) • bF8 a.2 by
    rw [crossF, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.toSpanSingleton_apply,
      smul_eq_mul]]

private theorem fin3_trichotomy {i j k x : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    x = i ∨ x = j ∨ x = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases x <;> simp_all

private theorem ggSL9J_comm (i j : Fin 3) (e : ZMod 3) :
    ggSL9J i j e = ggSL9J j i (-e) := by
  unfold ggSL9J
  rw [show (-(-e) : ZMod 3) = e from neg_neg e, Set.union_comm]

private theorem blockMap_mem_involving_k {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {H : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    (hJ_ik : ∀ e : ZMod 3, ggSL9J i k e ≤ H) (hJ_jk : ∀ e : ZMod 3, ggSL9J j k e ≤ H)
    (a b : Fin 3) (hab : a ≠ b) (hk : a = k ∨ b = k)
    (f : GaloisField 2 3 →ₗ[ZMod 2] GaloisField 2 3) : blockMap a b hab f ∈ H := by
  have hJ_ki : ∀ e : ZMod 3, ggSL9J k i e ≤ H := fun e => by
    rw [ggSL9J_comm]; exact hJ_ik (-e)
  have hJ_kj : ∀ e : ZMod 3, ggSL9J k j e ≤ H := fun e => by
    rw [ggSL9J_comm]; exact hJ_jk (-e)
  rcases hk with rfl | rfl
  · rcases fin3_trichotomy hij hik hjk (x := b) with h | h | h
    · subst h; exact blockMap_mem_of_J hik.symm hJ_ki f
    · subst h; exact blockMap_mem_of_J hjk.symm hJ_kj f
    · exact (hab h.symm).elim
  · rcases fin3_trichotomy hij hik hjk (x := a) with h | h | h
    · subst h; exact blockMap_mem_of_J hik hJ_ik f
    · subst h; exact blockMap_mem_of_J hjk hJ_jk f
    · exact (hab h).elim

private theorem commutator_mem {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

private theorem elemT_mem_cross_k {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {H : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    (hJ_ik : ∀ e : ZMod 3, ggSL9J i k e ≤ H) (hJ_jk : ∀ e : ZMod 3, ggSL9J j k e ≤ H)
    {a b : Idx} (hab : a ≠ b) (hblock : a.1 ≠ b.1) (hk : a.1 = k ∨ b.1 = k) (c : ZMod 2) :
    elemT a b hab c ∈ H := by
  have hba : b.1 ≠ a.1 := fun h => hblock h.symm
  rw [elemT_eq_blockMap a b hab hba c]
  exact blockMap_mem_involving_k hij hik hjk hJ_ik hJ_jk b.1 a.1 hba (Or.symm hk) (crossF a b c)

private theorem elemT_mem {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {H : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    (hJ_ik : ∀ e : ZMod 3, ggSL9J i k e ≤ H) (hJ_jk : ∀ e : ZMod 3, ggSL9J j k e ≤ H)
    (a b : Idx) (hab : a ≠ b) (c : ZMod 2) : elemT a b hab c ∈ H := by
  by_cases hblock : a.1 = b.1
  · let m : Idx := if a.1 = k then ⟨i, 0⟩ else ⟨k, 0⟩
    have hm : m.1 ≠ a.1 := by
      dsimp [m]
      split_ifs with h
      · intro hh; exact hik (hh.trans h)
      · intro hh; exact h hh.symm
    have ham : a ≠ m := fun hh => hm (congrArg Sigma.fst hh).symm
    have hmb : m ≠ b := fun hh => hm ((congrArg Sigma.fst hh).trans hblock.symm)
    have hma : a.1 ≠ m.1 := fun hh => hm hh.symm
    have hmb' : m.1 ≠ b.1 := fun hh => hm (hh.trans hblock.symm)
    have hk1 : a.1 = k ∨ m.1 = k := by
      dsimp [m]
      split_ifs with h
      · exact Or.inl h
      · exact Or.inr rfl
    have hk2 : m.1 = k ∨ b.1 = k := by
      rcases hk1 with h | h
      · exact Or.inr (hblock.symm.trans h)
      · exact Or.inl h
    have hcomm := elemT_comm ham hmb hab c 1
    rw [mul_one] at hcomm
    rw [← hcomm]
    exact commutator_mem
      (elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk ham hma hk1 c)
      (elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk hmb hmb' hk2 1)
  · by_cases hk : a.1 = k
    · exact elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk hab hblock (Or.inl hk) c
    · by_cases hk2 : b.1 = k
      · exact elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk hab hblock (Or.inr hk2) c
      · let m : Idx := ⟨k, 0⟩
        have ham : a ≠ m := fun hh => hk (congrArg Sigma.fst hh)
        have hmb : m ≠ b := fun hh => hk2 (congrArg Sigma.fst hh.symm)
        have hma : a.1 ≠ m.1 := fun hh => hk hh
        have hmb' : m.1 ≠ b.1 := fun hh => hk2 hh.symm
        have hk1 : a.1 = k ∨ m.1 = k := Or.inr rfl
        have hk2' : m.1 = k ∨ b.1 = k := Or.inl rfl
        have hcomm := elemT_comm ham hmb hab c 1
        rw [mul_one] at hcomm
        rw [← hcomm]
        exact commutator_mem
          (elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk ham hma hk1 c)
          (elemT_mem_cross_k hij hik hjk hJ_ik hJ_jk hmb hmb' hk2' 1)

private theorem psiSL_surjective : Function.Surjective psiSL := by
  intro g
  let M : Matrix.GeneralLinearGroup Idx (ZMod 2) := phiGL.symm g
  have hdet : (M : Matrix Idx Idx (ZMod 2)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det M = 1 := Subsingleton.elim _ _
    have h2 := Matrix.GeneralLinearGroup.val_det_apply M
    rw [h1] at h2
    exact h2.symm
  let A : Matrix.SpecialLinearGroup Idx (ZMod 2) := ⟨(M : Matrix Idx Idx (ZMod 2)), hdet⟩
  refine ⟨A, ?_⟩
  show phiGL (Matrix.SpecialLinearGroup.toGL A) = g
  have htoGL : Matrix.SpecialLinearGroup.toGL A = M := by
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mk]
  rw [htoGL]
  exact phiGL.apply_symm_apply g

private theorem closure_elemT_eq_top :
    Subgroup.closure (Set.range (fun t : Matrix.TransvectionStruct Idx (ZMod 2) =>
      elemT t.i t.j t.hij t.c)) = ⊤ := by
  have hsurj : Function.Surjective psiSL := psiSL_surjective
  have hmap := MonoidHom.map_closure psiSL
    (Set.range (fun t : Matrix.TransvectionStruct Idx (ZMod 2) => t.toSpecialLinearGroup))
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hmap
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj] at hmap
  have hset : Set.range (fun t : Matrix.TransvectionStruct Idx (ZMod 2) =>
        elemT t.i t.j t.hij t.c)
      = psiSL '' Set.range (fun t : Matrix.TransvectionStruct Idx (ZMod 2) =>
        t.toSpecialLinearGroup) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.toSpecialLinearGroup, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  rw [hset]
  exact hmap.symm

theorem ggSL9_closure_pair {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Subgroup.closure (⋃ e : ZMod 3, ((ggSL9J i k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) ∪
      (ggSL9J j k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))) = ⊤ := by
  let H := Subgroup.closure (⋃ e : ZMod 3, ((ggSL9J i k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) ∪
    (ggSL9J j k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))))
  have hJ_ik : ∀ e : ZMod 3, ggSL9J i k e ≤ H := fun e x hx =>
    Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨e, Set.mem_union_left _ hx⟩)
  have hJ_jk : ∀ e : ZMod 3, ggSL9J j k e ≤ H := fun e x hx =>
    Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨e, Set.mem_union_right _ hx⟩)
  have htop : H = ⊤ := by
    apply eq_top_iff.mpr
    rw [← closure_elemT_eq_top]
    apply (Subgroup.closure_le H).mpr
    rintro x ⟨t, rfl⟩
    exact elemT_mem hij hik hjk hJ_ik hJ_jk t.i t.j t.hij t.c
  exact htop

private theorem ggSL9J_mem_avoid_of_pair {ρ : Fin 3 × Fin 3 × ZMod 3}
    {a b : Fin 3} (hab : a ≠ b) (e : ZMod 3)
    (hpair : ¬ (a = ρ.1 ∧ b = ρ.2.1) ∧ ¬ (a = ρ.2.1 ∧ b = ρ.1)) :
    (ggSL9J a b e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) ⊆ (⋃ t ∈ GGSL9Refl \ {ρ},
      (ggSL9J t.1 t.2.1 t.2.2 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hrefl : (a, b, e) ∈ GGSL9Refl := hlt
    have hne : (a, b, e) ≠ ρ := by
      intro hh
      exact hpair.1 ⟨congrArg Prod.fst hh,
        congrArg (fun p : Fin 3 × Fin 3 × ZMod 3 => p.2.1) hh⟩
    intro x hx
    exact Set.mem_iUnion.mpr ⟨(a, b, e),
      Set.mem_iUnion.mpr ⟨⟨hrefl, hne⟩, hx⟩⟩
  · have hrefl : (b, a, -e) ∈ GGSL9Refl := hgt
    have hne : (b, a, -e) ≠ ρ := by
      intro hh
      exact hpair.2 ⟨congrArg (fun p : Fin 3 × Fin 3 × ZMod 3 => p.2.1) hh,
        congrArg Prod.fst hh⟩
    rw [ggSL9J_comm]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨(b, a, -e),
      Set.mem_iUnion.mpr ⟨⟨hrefl, hne⟩, hx⟩⟩

theorem ggSL9_avoidOne (ρ : Fin 3 × Fin 3 × ZMod 3) :
    Subgroup.closure (⋃ t ∈ GGSL9Refl \ {ρ},
      (ggSL9J t.1 t.2.1 t.2.2 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) = ⊤ := by
  rcases ρ with ⟨a, b, e0⟩
  change Subgroup.closure (⋃ t ∈ GGSL9Refl \ {(a, b, e0)},
    (ggSL9J t.1 t.2.1 t.2.2 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) = ⊤
  have hex : ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (¬ (i = a ∧ k = b) ∧ ¬ (i = b ∧ k = a)) ∧
      (¬ (j = a ∧ k = b) ∧ ¬ (j = b ∧ k = a)) := by
    fin_cases a <;> fin_cases b
    · exact ⟨1, 2, 0, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨0, 1, 2, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨0, 2, 1, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨1, 0, 2, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨0, 2, 1, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨1, 2, 0, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨2, 0, 1, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨2, 1, 0, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
    · exact ⟨0, 1, 2, by decide, by decide, by decide, ⟨by decide, by decide⟩,
        ⟨by decide, by decide⟩⟩
  obtain ⟨i, j, k, hij, hik, hjk, hpi, hpj⟩ := hex
  have hsub : (⋃ e : ZMod 3, ((ggSL9J i k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) ∪
      (ggSL9J j k e : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V)))) ⊆
      (⋃ t ∈ GGSL9Refl \ {(a, b, e0)},
        (ggSL9J t.1 t.2.1 t.2.2 : Set (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) := by
    rintro x hx
    rcases Set.mem_iUnion.mp hx with ⟨e, hx | hx⟩
    · exact ggSL9J_mem_avoid_of_pair (ρ := (a, b, e0)) hik e hpi hx
    · exact ggSL9J_mem_avoid_of_pair (ρ := (a, b, e0)) hjk e hpj hx
  have hpair := ggSL9_closure_pair hij hik hjk
  apply eq_top_iff.mpr
  rw [← hpair]
  exact Subgroup.closure_mono hsub

end

end CFSG.StandardType

end
