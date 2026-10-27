module

public import CFSG.RankThree.CentralLift.LinearRootRelations
public import CFSG.LieType.Universal.SpecialLinearRoots

public section

namespace CFSG.RankThree.CentralLift

namespace LinearRoots

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat pairMat_apply_pair
  pairMat_cases sl2Diag coe_sl2Diag sl2ConjDiag coe_sl2ConjDiag IsLinePerm monomialGL linePerm
  isLinePerm_linePerm linePerm_eq isLinePerm_signedPerm mem_monomialGL isLinePerm_one)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.LieType.RootSystem (coxeterMatrix weylAction weylAction_simple weylAction_injective)

variable {k : Type} [Field k] {n : ℕ}

section SL2

@[expose] def wSL (a : kˣ) : SpecialLinearGroup (Fin 2) k :=
  uSL (a : k) * vSL (-((a⁻¹ : kˣ) : k)) * uSL (a : k)

theorem coe_wSL (a : kˣ) :
    ((wSL a : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, (a : k); -((a⁻¹ : kˣ) : k), 0] := by
  rw [wSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL,
    coe_vSL]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two]

theorem wSL_mul_wSL_neg_one (a : kˣ) : wSL a * wSL (-1) = sl2Diag a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_wSL, coe_wSL, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two]

theorem wSL_one_mul_self : wSL (1 : kˣ) * wSL 1 = sl2Diag (-1) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_wSL, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two]

theorem wSL_mul_wSL (a b : kˣ) : wSL a * wSL b = sl2Diag (-(a * b⁻¹)) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_wSL, coe_wSL, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]

theorem wSL_one_inv : (wSL (1 : kˣ))⁻¹ = wSL (-1) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [wSL_mul_wSL_neg_one, map_one]

theorem swapSL_sl2Diag (a : kˣ) : swapSL (sl2Diag a) = sl2Diag (k := k) a⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_swapSL, coe_sl2Diag, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp

theorem sl2ConjDiag_sl2Diag (u a : kˣ) : sl2ConjDiag u (sl2Diag a) = sl2Diag (k := k) a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_sl2ConjDiag, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp

theorem sl2ConjDiag_inv_wSL_one (a : kˣ) : sl2ConjDiag a⁻¹ (wSL (1 : kˣ)) = wSL (k := k) a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_sl2ConjDiag, coe_wSL, coe_wSL]
  fin_cases x <;> fin_cases y <;> simp

theorem sl2ConjDiag_one (g : SpecialLinearGroup (Fin 2) k) : sl2ConjDiag 1 g = g := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_sl2ConjDiag]
  fin_cases x <;> fin_cases y <;> simp

end SL2

section Images

@[expose] def corootUnit (i j : Fin n) (a : kˣ) (x : Fin n) : kˣ :=
  if x = i then a else if x = j then a⁻¹ else 1

@[expose] def wSign (i : Fin n) (x : Fin n) : kˣ := if x = i then -1 else 1

theorem coe_rhoSL_sl2Diag {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    ((rhoSL k i j (sl2Diag a) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm 1 fun x => ((corootUnit i j a x : kˣ) : k) := by
  rw [coe_rhoSL hij, coe_sl2Diag, signedPerm_one]
  ext x y
  refine pairMat_cases (P := fun x y d => d = diagonal (fun x => ((corootUnit i j a x : kˣ) : k))
    x y) hij ?_ ?_ ?_ ?_ (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_)
    (fun x y hxa hxb hya hyb => ?_) x y
  · simp [corootUnit]
  · simp [diagonal_apply_ne _ hij]
  · simp [diagonal_apply_ne _ hij.symm]
  · simp [corootUnit, hij.symm]
  · rcases hx with rfl | rfl
    · exact (diagonal_apply_ne _ (Ne.symm hya)).symm
    · exact (diagonal_apply_ne _ (Ne.symm hyb)).symm
  · rcases hy with rfl | rfl
    · exact (diagonal_apply_ne _ hxa).symm
    · exact (diagonal_apply_ne _ hxb).symm
  · by_cases hxy : x = y
    · subst hxy
      simp [corootUnit, hxa, hxb]
    · rw [one_apply_ne hxy, diagonal_apply_ne _ hxy]

theorem coe_rhoSL_wSL_one {i j : Fin n} (hij : i ≠ j) :
    ((rhoSL k i j (wSL 1) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm (Equiv.swap i j) fun x => ((wSign i x : kˣ) : k) := by
  rw [coe_rhoSL hij, coe_wSL]
  ext x y
  refine pairMat_cases (P := fun x y d => d = signedPerm (Equiv.swap i j)
    (fun x => ((wSign i x : kˣ) : k)) x y) hij ?_
    ?_ ?_ ?_ (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_)
    (fun x y hxa hxb hya hyb => ?_) x y
  · simp [signedPerm_apply, Equiv.swap_apply_left, hij]
  · simp [signedPerm_apply, Equiv.swap_apply_right, wSign, hij.symm]
  · simp [signedPerm_apply, Equiv.swap_apply_left, wSign]
  · simp [signedPerm_apply, Equiv.swap_apply_right, hij.symm]
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb]
    rcases hx with rfl | rfl
    · rw [ite_eq_right_iff.2 fun h => absurd h.symm hya]
    · rw [ite_eq_right_iff.2 fun h => absurd h.symm hyb]
  · rw [signedPerm_apply]
    rcases hy with rfl | rfl
    · rw [Equiv.swap_apply_left, ite_eq_right_iff.2 fun h => absurd h hxb]
    · rw [Equiv.swap_apply_right, ite_eq_right_iff.2 fun h => absurd h hxa]
  · rw [signedPerm_apply, Equiv.swap_apply_of_ne_of_ne hya hyb]
    by_cases hxy : x = y
    · subst hxy
      simp [wSign, hxa]
    · rw [one_apply_ne hxy, ite_eq_right_iff.2 fun h => absurd h hxy]

end Images

section Defs

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

@[expose] noncomputable def wLift (i j : Fin n) (a : kˣ) : E :=
  xLift π i j a * xLift π j i (-((a⁻¹ : kˣ) : k)) * xLift π i j a

@[expose] noncomputable def hLin (i j : Fin n) (a : kˣ) : E := wLift π i j a * wLift π i j (-1)

@[expose] noncomputable def torusLin : Subgroup E :=
  Subgroup.closure {x | ∃ (i j : Fin n) (a : kˣ), i ≠ j ∧ hLin π i j a = x}

@[expose] noncomputable def wAdj (i : Fin n) : E :=
  if h : i.val + 1 < n then wLift π i ⟨i.val + 1, h⟩ 1 else 1

@[expose] noncomputable def monoLin : Subgroup E :=
  Subgroup.closure ((torusLin π : Set E) ∪ Set.range (wAdj π))

end Defs

variable (k n) in
@[expose] def diagonalSL : Subgroup (SpecialLinearGroup (Fin n) k) where
  carrier := {A | ∀ i j : Fin n, i ≠ j → (A : Matrix (Fin n) (Fin n) k) i j = 0}
  one_mem' := fun i j hij => by
    show (1 : Matrix (Fin n) (Fin n) k) i j = 0
    rw [one_apply_ne hij]
  mul_mem' := fun {A B} hA hB i j hij => by
    show ((A : Matrix (Fin n) (Fin n) k) * (B : Matrix (Fin n) (Fin n) k)) i j = 0
    rw [mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hil : i = l
    · subst hil
      rw [hB i j hij, mul_zero]
    · rw [hA i l hil, zero_mul]
  inv_mem' := fun {A} hA i j hij => by
    show (adjugate (A : Matrix (Fin n) (Fin n) k)) i j = 0
    rw [adjugate_apply]
    refine det_eq_zero_of_column_eq_zero j fun l => ?_
    by_cases hlj : l = j
    · subst hlj
      rw [updateRow_self, Pi.single_eq_of_ne (Ne.symm hij)]
    · rw [updateRow_ne hlj, hA l j hlj]

theorem mem_diagonalSL {A : SpecialLinearGroup (Fin n) k} :
    A ∈ diagonalSL k n ↔ ∀ i j : Fin n, i ≠ j → (A : Matrix (Fin n) (Fin n) k) i j = 0 :=
  Iff.rfl

variable (k n) in
@[expose] noncomputable def monomialSL : Subgroup (SpecialLinearGroup (Fin n) k) :=
  (monomialGL (Fin n) k).comap SpecialLinearGroup.toGL

section Lifts

variable [Finite k] {E : Type*} [Group E] [Finite E] {π : E →* SpecialLinearGroup (Fin n) k}
  (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem wLift_eq {i j : Fin n} (hij : i ≠ j) (a : kˣ) : wLift π i j a = rhoLift π i j (wSL a) := by
  rw [wLift, xLift_swap hk hπ hij]
  simp only [xLift, wSL, map_mul]

theorem hLin_eq {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    hLin π i j a = rhoLift π i j (sl2Diag a) := by
  rw [hLin, wLift_eq hk hπ hij, wLift_eq hk hπ hij, ← map_mul, wSL_mul_wSL_neg_one]

theorem hLin_mul {i j : Fin n} (hij : i ≠ j) (a b : kˣ) :
    hLin π i j (a * b) = hLin π i j a * hLin π i j b := by
  rw [hLin_eq hk hπ hij, hLin_eq hk hπ hij, hLin_eq hk hπ hij, map_mul, map_mul]

theorem hLin_one {i j : Fin n} (hij : i ≠ j) : hLin π i j 1 = 1 := by
  rw [hLin_eq hk hπ hij, map_one, map_one]

theorem hLin_inv {i j : Fin n} (hij : i ≠ j) (a : kˣ) : hLin π i j a⁻¹ = (hLin π i j a)⁻¹ := by
  rw [hLin_eq hk hπ hij, hLin_eq hk hπ hij, map_inv, map_inv]

theorem hLin_swap {i j : Fin n} (hij : i ≠ j) (a : kˣ) : hLin π j i a = hLin π i j a⁻¹ := by
  rw [hLin_eq hk hπ hij.symm, rhoLift_swap hk hπ hij, MonoidHom.comp_apply, swapSL_sl2Diag,
    ← hLin_eq hk hπ hij]

theorem pi_hLin {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    ((π (hLin π i j a) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm 1 fun x => ((corootUnit i j a x : kˣ) : k) := by
  rw [hLin_eq hk hπ hij, pi_rhoLift hk hπ, coe_rhoSL_sl2Diag hij]

theorem pi_wLift_one {i j : Fin n} (hij : i ≠ j) :
    ((π (wLift π i j 1) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm (Equiv.swap i j) fun x => ((wSign i x : kˣ) : k) := by
  rw [wLift_eq hk hπ hij, pi_rhoLift hk hπ, coe_rhoSL_wSL_one hij]

theorem conj_hLin_of_signedPerm {i j : Fin n} (hij : i ≠ j) {g : E} {σ : Equiv.Perm (Fin n)}
    {c : Fin n → kˣ} (hg : ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm σ fun x => (c x : k)) (a : kˣ) :
    g * hLin π i j a * g⁻¹ = hLin π (σ i) (σ j) a := by
  rw [hLin_eq hk hπ hij, conj_rhoLift_of_signedPerm hk hπ hij hg, sl2ConjDiag_sl2Diag,
    ← hLin_eq hk hπ (fun h => hij (σ.injective h))]

theorem commute_hLin {i j k' l : Fin n} (hij : i ≠ j) (hkl : k' ≠ l) (a b : kˣ) :
    Commute (hLin π i j a) (hLin π k' l b) := by
  have h := conj_hLin_of_signedPerm hk hπ hij (pi_hLin hk hπ hkl b) a
  simp only [Equiv.Perm.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem torusLin_commute {x y : E} (hx : x ∈ torusLin π) (hy : y ∈ torusLin π) :
    Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure
    (k := {x | ∃ (i j : Fin n) (a : kˣ), i ≠ j ∧ hLin π i j a = x}) (by
      rintro _ ⟨i, j, a, hij, rfl⟩ _ ⟨k', l, b, hkl, rfl⟩ _
      exact commute_hLin hk hπ hij hkl a b)
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : torusLin π) ⟨y, hy⟩)

theorem hLin_trans {i j k' : Fin n} (hij : i ≠ j) (hjk : j ≠ k') (hik : i ≠ k') (a : kˣ) :
    hLin π i k' a = hLin π i j a * hLin π j k' a := by
  have h1 : wLift π i j 1 * hLin π j k' a * (wLift π i j 1)⁻¹ = hLin π i k' a := by
    rw [conj_hLin_of_signedPerm hk hπ hjk (pi_wLift_one hk hπ hij) a, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have h2 : (hLin π j k' a)⁻¹ * wLift π i j 1 * hLin π j k' a = wLift π i j a := by
    have hd : ((π (hLin π j k' a)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        signedPerm 1 fun x => ((corootUnit j k' a⁻¹ x : kˣ) : k) := by
      rw [← hLin_inv hk hπ hjk, pi_hLin hk hπ hjk]
    have h := conj_rhoLift_of_signedPerm hk hπ hij hd (wSL 1)
    simp only [Equiv.Perm.one_apply, inv_inv] at h
    rw [wLift_eq hk hπ hij, h, wLift_eq hk hπ hij]
    congr 2
    have hci : corootUnit (k := k) j k' a⁻¹ i = 1 := by simp [corootUnit, hij, hik]
    have hcj : corootUnit (k := k) j k' a⁻¹ j = a⁻¹ := by simp [corootUnit]
    rw [hci, hcj, inv_one, mul_one, sl2ConjDiag_inv_wSL_one]
  have hv : (wLift π i j 1)⁻¹ = wLift π i j (-1) := by
    rw [wLift_eq hk hπ hij, wLift_eq hk hπ hij, ← map_inv, wSL_one_inv]
  have h3 : wLift π i j 1 * hLin π j k' a * (wLift π i j 1)⁻¹ =
      hLin π j k' a * hLin π i j a := by
    calc wLift π i j 1 * hLin π j k' a * (wLift π i j 1)⁻¹
        = hLin π j k' a * ((hLin π j k' a)⁻¹ * wLift π i j 1 * hLin π j k' a) *
            (wLift π i j 1)⁻¹ := by group
      _ = hLin π j k' a * hLin π i j a := by
          rw [h2, hv, mul_assoc]
          rfl
  rw [← h1, h3]
  exact ((commute_hLin hk hπ hjk hij a a).eq)

theorem wLift_one_mul_self {i j : Fin n} (hij : i ≠ j) :
    wLift π i j 1 * wLift π i j 1 = hLin π i j (-1) := by
  rw [wLift_eq hk hπ hij, ← map_mul, wSL_one_mul_self, hLin_eq hk hπ hij]

end Lifts

section Theta

variable (k) in
@[expose] def thetaEntry (z : Fin n) (t : Fin n → kˣ) (x : Fin n) : kˣ :=
  if x = z then ∏ m ∈ Finset.univ.erase z, (t m)⁻¹ else t x

theorem prod_thetaEntry (z : Fin n) (t : Fin n → kˣ) : ∏ x, thetaEntry k z t x = 1 := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ z), thetaEntry, ite_eq_left rfl,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun m hm => ?_
  rw [thetaEntry, ite_eq_right (Finset.ne_of_mem_erase hm), inv_mul_cancel]

theorem thetaEntry_mul (z : Fin n) (t s : Fin n → kˣ) (x : Fin n) :
    thetaEntry k z (t * s) x = thetaEntry k z t x * thetaEntry k z s x := by
  unfold thetaEntry
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [Pi.mul_apply, _root_.mul_inv_rev, mul_comm]
  · rfl

variable (k) in
@[expose] noncomputable def thetaDiag (z : Fin n) : (Fin n → kˣ) →* SpecialLinearGroup (Fin n) k
    where
  toFun t := ⟨diagonal fun x => ((thetaEntry k z t x : kˣ) : k), by
    rw [det_diagonal, ← Units.coe_prod, prod_thetaEntry, Units.val_one]⟩
  map_one' := by
    refine Subtype.ext ?_
    change diagonal (fun x => ((thetaEntry k z 1 x : kˣ) : k)) = 1
    rw [← diagonal_one]
    congr 1
    funext x
    simp [thetaEntry]
  map_mul' t s := by
    refine Subtype.ext ?_
    change diagonal (fun x => ((thetaEntry k z (t * s) x : kˣ) : k)) =
      diagonal (fun x => ((thetaEntry k z t x : kˣ) : k)) *
        diagonal (fun x => ((thetaEntry k z s x : kˣ) : k))
    rw [diagonal_mul_diagonal]
    congr 1
    funext x
    rw [thetaEntry_mul, Units.val_mul]

theorem coe_thetaDiag (z : Fin n) (t : Fin n → kˣ) :
    ((thetaDiag k z t : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      diagonal fun x => ((thetaEntry k z t x : kˣ) : k) := rfl

theorem thetaDiag_mulSingle {m z : Fin n} (hmz : m ≠ z) (a : kˣ) :
    thetaDiag k z (Pi.mulSingle m a) = rhoSL k m z (sl2Diag a) := by
  refine Subtype.ext ?_
  change diagonal (fun x => ((thetaEntry k z (Pi.mulSingle m a) x : kˣ) : k)) =
    ((rhoSL k m z (sl2Diag a) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [coe_rhoSL_sl2Diag hmz, signedPerm_one]
  congr 1
  funext x
  have hprod : ∏ l ∈ Finset.univ.erase z, (Pi.mulSingle m a l)⁻¹ = a⁻¹ := by
    rw [Finset.prod_eq_single m]
    · rw [Pi.mulSingle_eq_same]
    · intro l _ hlm
      rw [Pi.mulSingle_eq_of_ne hlm, inv_one]
    · intro h
      exact absurd (Finset.mem_erase.2 ⟨hmz, Finset.mem_univ m⟩) h
  by_cases hxz : x = z
  · subst hxz
    simp [thetaEntry, corootUnit, hprod, Ne.symm hmz]
  · by_cases hxm : x = m
    · subst hxm
      simp [thetaEntry, corootUnit, hxz]
    · simp [thetaEntry, corootUnit, hxz, hxm]

theorem thetaDiag_mulSingle_self (z : Fin n) (a : kˣ) : thetaDiag k z (Pi.mulSingle z a) = 1 := by
  refine Subtype.ext ?_
  change diagonal (fun x => ((thetaEntry k z (Pi.mulSingle z a) x : kˣ) : k)) = 1
  rw [← diagonal_one]
  congr 1
  funext x
  by_cases hxz : x = z
  · subst hxz
    simp only [thetaEntry]
    rw [Finset.prod_eq_one fun l hl => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hl), inv_one]]
    rfl
  · simp [thetaEntry, hxz]

theorem diagonalSL_le_range_thetaDiag (z : Fin n) : diagonalSL k n ≤ (thetaDiag k z).range := by
  intro D hD
  rw [mem_diagonalSL] at hD
  have hdiag : (D : Matrix (Fin n) (Fin n) k) = diagonal fun x => (D : Matrix (Fin n) (Fin n) k) x x
      := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hxy, hD x y hxy]
  have hdet : ∏ x, (D : Matrix (Fin n) (Fin n) k) x x = 1 := by
    rw [← det_diagonal, ← hdiag]
    exact D.2
  have hne : ∀ x, (D : Matrix (Fin n) (Fin n) k) x x ≠ 0 := fun x h => by
    have h0 : ∏ y, (D : Matrix (Fin n) (Fin n) k) y y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) h
    rw [hdet] at h0
    exact one_ne_zero h0
  refine ⟨fun x => Units.mk0 _ (hne x), Subtype.ext ?_⟩
  rw [coe_thetaDiag]
  refine Eq.trans ?_ hdiag.symm
  congr 1
  funext x
  by_cases hxz : x = z
  · subst hxz
    rw [thetaEntry, ite_eq_left rfl, Units.coe_prod]
    have h := Finset.mul_prod_erase Finset.univ (fun x => (D : Matrix (Fin n) (Fin n) k) x x)
      (Finset.mem_univ x)
    rw [hdet] at h
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Finset.prod_inv_distrib]
    exact (eq_inv_of_mul_eq_one_left h).symm
  · rw [thetaEntry, ite_eq_right hxz, Units.val_mk0]

theorem range_thetaDiag_le (z : Fin n) : (thetaDiag k z).range ≤ diagonalSL k n := by
  rintro _ ⟨t, rfl⟩
  rw [mem_diagonalSL]
  intro x y hxy
  rw [coe_thetaDiag, diagonal_apply_ne _ hxy]

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

@[expose] noncomputable def hZ (z m : Fin n) : kˣ →* E :=
  if m = z then 1 else (rhoLift π m z).comp sl2Diag

theorem hZ_of_eq {z m : Fin n} (h : m = z) : hZ π z m = 1 := ite_eq_left h

theorem hZ_of_ne {z m : Fin n} (h : m ≠ z) : hZ π z m = (rhoLift π m z).comp sl2Diag :=
  ite_eq_right h

theorem hLin_mem_torusLin {i j : Fin n} (hij : i ≠ j) (a : kˣ) : hLin π i j a ∈ torusLin π :=
  Subgroup.subset_closure ⟨i, j, a, hij, rfl⟩

variable [Finite k] [Finite E] {π} (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem hZ_apply {z m : Fin n} (hmz : m ≠ z) (a : kˣ) : hZ π z m a = hLin π m z a := by
  rw [hZ_of_ne π hmz, hLin_eq hk hπ hmz]
  rfl

theorem pairwise_commute_hZ (z : Fin n) :
    Pairwise fun i j : Fin n => ∀ x y : kˣ, Commute (hZ π z i x) (hZ π z j y) := by
  intro i j _ x y
  by_cases hiz : i = z
  · rw [hZ_of_eq π hiz]
    exact Commute.one_left _
  by_cases hjz : j = z
  · rw [hZ_of_eq π hjz]
    exact Commute.one_right _
  rw [hZ_apply hk hπ hiz, hZ_apply hk hπ hjz]
  exact commute_hLin hk hπ hiz hjz x y

@[expose] noncomputable def thetaLin (z : Fin n) : (Fin n → kˣ) →* E :=
  MonoidHom.noncommPiCoprod (hZ π z) (pairwise_commute_hZ hk hπ z)

theorem thetaLin_mulSingle {z m : Fin n} (hmz : m ≠ z) (a : kˣ) :
    thetaLin hk hπ z (Pi.mulSingle m a) = hLin π m z a := by
  rw [thetaLin, MonoidHom.noncommPiCoprod_mulSingle, hZ_apply hk hπ hmz]

theorem thetaLin_mulSingle_self (z : Fin n) (a : kˣ) : thetaLin hk hπ z (Pi.mulSingle z a) = 1 := by
  rw [thetaLin, MonoidHom.noncommPiCoprod_mulSingle, hZ_of_eq π rfl, MonoidHom.one_apply]

theorem comp_thetaLin (z : Fin n) : π.comp (thetaLin hk hπ z) = thetaDiag k z := by
  refine MonoidHom.pi_ext fun m a => ?_
  rw [MonoidHom.comp_apply]
  by_cases hmz : m = z
  · subst hmz
    rw [thetaLin_mulSingle_self, map_one, thetaDiag_mulSingle_self]
  · rw [thetaLin_mulSingle hk hπ hmz, thetaDiag_mulSingle hmz, hLin_eq hk hπ hmz, pi_rhoLift hk hπ]

theorem range_thetaLin (z : Fin n) : (thetaLin hk hπ z).range = torusLin π := by
  apply le_antisymm
  · rw [thetaLin, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun m => ?_
    rintro _ ⟨a, rfl⟩
    by_cases hmz : m = z
    · rw [hZ_of_eq π hmz, MonoidHom.one_apply]
      exact one_mem _
    · rw [hZ_apply hk hπ hmz]
      exact hLin_mem_torusLin π hmz a
  · rw [torusLin, Subgroup.closure_le]
    rintro _ ⟨i, j, a, hij, rfl⟩
    by_cases hjz : j = z
    · subst hjz
      exact ⟨Pi.mulSingle i a, thetaLin_mulSingle hk hπ hij a⟩
    by_cases hiz : i = z
    · subst hiz
      refine ⟨Pi.mulSingle j a⁻¹, ?_⟩
      rw [thetaLin_mulSingle hk hπ hjz, hLin_swap hk hπ (Ne.symm hij)]
    · refine ⟨Pi.mulSingle i a * Pi.mulSingle j a⁻¹, ?_⟩
      rw [map_mul, thetaLin_mulSingle hk hπ hiz, thetaLin_mulSingle hk hπ hjz,
        hLin_trans hk hπ hiz (Ne.symm hjz) hij, hLin_swap hk hπ hjz a]

theorem map_torusLin (z : Fin n) : (torusLin π).map π = diagonalSL k n := by
  rw [← range_thetaLin hk hπ z, ← MonoidHom.range_comp, comp_thetaLin hk hπ z]
  exact le_antisymm (range_thetaDiag_le z) (diagonalSL_le_range_thetaDiag z)

theorem injective_torusLin (z : Fin n) : Function.Injective (π.comp (torusLin π).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩ hx1
  rw [← range_thetaLin hk hπ z] at hx
  obtain ⟨t, rfl⟩ := hx
  have h1 : thetaDiag k z t = 1 := by
    rw [← comp_thetaLin hk hπ z]
    exact hx1
  have ht : ∀ m, m ≠ z → t m = 1 := by
    intro m hmz
    have h : ((thetaDiag k z t : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) m m =
        1 := by
      rw [h1, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    rw [coe_thetaDiag, diagonal_apply_eq, thetaEntry, ite_eq_right hmz] at h
    exact Units.ext (h.trans Units.val_one.symm)
  have hteq : t = Pi.mulSingle z (t z) := by
    funext m
    by_cases hmz : m = z
    · subst hmz
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hmz, ht m hmz]
  apply Subtype.ext
  change thetaLin hk hπ z t = 1
  rw [hteq, thetaLin_mulSingle_self]

end Theta

section Monomial

theorem ne_fin_succ (i : Fin n) (h : i.val + 1 < n) : i ≠ ⟨i.val + 1, h⟩ := fun e => by
  simpa using congrArg Fin.val e

theorem eq_diagonal_of_mem_diagonalSL {A : SpecialLinearGroup (Fin n) k}
    (hA : A ∈ diagonalSL k n) :
    (A : Matrix (Fin n) (Fin n) k) = diagonal fun x => (A : Matrix (Fin n) (Fin n) k) x x := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hxy, mem_diagonalSL.1 hA x y hxy]

theorem apply_self_ne_zero_of_mem_diagonalSL {A : SpecialLinearGroup (Fin n) k}
    (hA : A ∈ diagonalSL k n) (x : Fin n) : (A : Matrix (Fin n) (Fin n) k) x x ≠ 0 := by
  intro h
  have hdet : ∏ y, (A : Matrix (Fin n) (Fin n) k) y y = 1 := by
    rw [← det_diagonal, ← eq_diagonal_of_mem_diagonalSL hA]
    exact A.2
  have h0 : ∏ y, (A : Matrix (Fin n) (Fin n) k) y y = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ x) h
  rw [hdet] at h0
  exact one_ne_zero h0

theorem isLinePerm_one_of_mem_diagonalSL {A : SpecialLinearGroup (Fin n) k}
    (hA : A ∈ diagonalSL k n) : IsLinePerm 1 (A : Matrix (Fin n) (Fin n) k) := by
  intro x y
  rw [Equiv.Perm.one_apply]
  by_cases hyx : y = x
  · subst hyx
    exact iff_of_true (apply_self_ne_zero_of_mem_diagonalSL hA y) rfl
  · exact iff_of_false (fun h => h (mem_diagonalSL.1 hA y x hyx)) hyx

theorem mem_diagonalSL_of_isLinePerm_one {A : SpecialLinearGroup (Fin n) k}
    (h : IsLinePerm 1 (A : Matrix (Fin n) (Fin n) k)) : A ∈ diagonalSL k n :=
  mem_diagonalSL.2 fun _ _ hij => h.apply_eq_zero (by rwa [Equiv.Perm.one_apply])

theorem mem_monomialSL {A : SpecialLinearGroup (Fin n) k} :
    A ∈ monomialSL k n ↔ ∃ σ : Equiv.Perm (Fin n), IsLinePerm σ (A : Matrix (Fin n) (Fin n) k) :=
  ⟨fun hA => ⟨_, isLinePerm_linePerm ⟨SpecialLinearGroup.toGL A, hA⟩⟩,
    fun ⟨_, hσ⟩ => mem_monomialGL hσ⟩

theorem signedPerm_mem_monomialSL {A : SpecialLinearGroup (Fin n) k} {σ : Equiv.Perm (Fin n)}
    {c : Fin n → kˣ} (hA : (A : Matrix (Fin n) (Fin n) k) = signedPerm σ fun x => (c x : k)) :
    A ∈ monomialSL k n := by
  refine mem_monomialSL.2 ⟨σ, ?_⟩
  rw [hA]
  exact isLinePerm_signedPerm σ fun x => (c x).ne_zero

theorem diagonalSL_le_monomialSL : diagonalSL k n ≤ monomialSL k n :=
  fun _ hA => mem_monomialSL.2 ⟨1, isLinePerm_one_of_mem_diagonalSL hA⟩

theorem exists_signedPerm_of_mem_monomialSL {A : SpecialLinearGroup (Fin n) k}
    (hA : A ∈ monomialSL k n) : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → kˣ),
      (A : Matrix (Fin n) (Fin n) k) = signedPerm σ fun x => (c x : k) := by
  obtain ⟨σ, hσ⟩ := mem_monomialSL.1 hA
  refine ⟨σ, fun x => Units.mk0 _ (hσ.apply_ne_zero x), ?_⟩
  ext r s
  rw [signedPerm_apply]
  by_cases hr : r = σ s
  · rw [ite_eq_left hr, Units.val_mk0, hr]
  · rw [ite_eq_right hr, hσ.apply_eq_zero hr]

variable (k n) in
@[expose] noncomputable def coordPerm : monomialSL k n →* Equiv.Perm (Fin n) :=
  linePerm.comp (SpecialLinearGroup.toGL.subgroupComap (monomialGL (Fin n) k))

theorem isLinePerm_coordPerm (A : monomialSL k n) :
    IsLinePerm (coordPerm k n A) ((A : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
  isLinePerm_linePerm _

theorem coordPerm_eq {A : monomialSL k n} {σ : Equiv.Perm (Fin n)}
    (h : IsLinePerm σ ((A : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    coordPerm k n A = σ :=
  (isLinePerm_coordPerm A).unique h

end Monomial

section Basic

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

theorem torusLin_le_monoLin : torusLin π ≤ monoLin π := fun _ hx =>
  Subgroup.subset_closure (Or.inl hx)

theorem wAdj_mem_monoLin (i : Fin n) : wAdj π i ∈ monoLin π :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

end Basic

section Weyl

variable [Finite k] {E : Type*} [Group E] [Finite E] {π : E →* SpecialLinearGroup (Fin n) k}
  (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem wLift_one_inv {i j : Fin n} (hij : i ≠ j) : (wLift π i j 1)⁻¹ = wLift π i j (-1) := by
  rw [wLift_eq hk hπ hij, wLift_eq hk hπ hij, ← map_inv, wSL_one_inv]

theorem wLift_eq_hLin_mul {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    wLift π i j a = hLin π i j a * wLift π i j 1 := by
  rw [hLin, ← wLift_one_inv hk hπ hij, inv_mul_cancel_right]

theorem wLift_mul_wLift {i j : Fin n} (hij : i ≠ j) (a b : kˣ) :
    wLift π i j a * wLift π i j b = hLin π i j (-(a * b⁻¹)) := by
  rw [wLift_eq hk hπ hij, wLift_eq hk hπ hij, ← map_mul, wSL_mul_wSL, hLin_eq hk hπ hij]

theorem pi_wLift_mem {i j : Fin n} (hij : i ≠ j) (a : kˣ) :
    π (wLift π i j a) ∈ monomialSL k n := by
  rw [wLift_eq_hLin_mul hk hπ hij, map_mul]
  exact mul_mem (signedPerm_mem_monomialSL (pi_hLin hk hπ hij a))
    (signedPerm_mem_monomialSL (pi_wLift_one hk hπ hij))

theorem torusLin_le_comap_diagonalSL : torusLin π ≤ (diagonalSL k n).comap π := by
  rw [torusLin, Subgroup.closure_le]
  rintro _ ⟨i, j, a, hij, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, mem_diagonalSL]
  intro x y hxy
  rw [pi_hLin hk hπ hij, signedPerm_one, diagonal_apply_ne _ hxy]

theorem torusLin_le_comap : torusLin π ≤ (monomialSL k n).comap π :=
  (torusLin_le_comap_diagonalSL hk hπ).trans (Subgroup.comap_mono diagonalSL_le_monomialSL)

theorem monoLin_le_comap : monoLin π ≤ (monomialSL k n).comap π := by
  rw [monoLin, Subgroup.closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact torusLin_le_comap hk hπ hx
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    unfold wAdj
    split_ifs with h
    · exact pi_wLift_mem hk hπ (ne_fin_succ i h) 1
    · rw [map_one]
      exact one_mem _

theorem conj_mem_torusLin {g : E} (hg : π g ∈ monomialSL k n) {x : E} (hx : x ∈ torusLin π) :
    g * x * g⁻¹ ∈ torusLin π := by
  obtain ⟨σ, c, hc⟩ := exists_signedPerm_of_mem_monomialSL hg
  have hle : (torusLin π).map (MulAut.conj g).toMonoidHom ≤ torusLin π := by
    rw [torusLin, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, a, hij, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨σ i, σ j, a, σ.injective.ne hij,
      (conj_hLin_of_signedPerm hk hπ hij hc a).symm⟩
  exact hle ⟨x, hx, rfl⟩

theorem comap_monomialSL_le_normalizer :
    (monomialSL k n).comap π ≤ Subgroup.normalizer (torusLin π : Set E) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_torusLin hk hπ hg hx, fun hx => ?_⟩
  have hg' : π g⁻¹ ∈ monomialSL k n := by
    rw [map_inv]
    exact inv_mem hg
  have h := conj_mem_torusLin hk hπ hg' hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

theorem monoLin_le_normalizer : monoLin π ≤ Subgroup.normalizer (torusLin π : Set E) :=
  (monoLin_le_comap hk hπ).trans (comap_monomialSL_le_normalizer hk hπ)

theorem normal_torusLin_subgroupOf : ((torusLin π).subgroupOf (monoLin π)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (monoLin_le_normalizer hk hπ)

@[expose] noncomputable def weylPerm : monoLin π →* Equiv.Perm (Fin n) :=
  (coordPerm k n).comp ((π.subgroupComap (monomialSL k n)).comp
    (Subgroup.inclusion (monoLin_le_comap hk hπ)))

theorem isLinePerm_weylPerm (g : monoLin π) :
    IsLinePerm (weylPerm hk hπ g)
      ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
  isLinePerm_coordPerm _

theorem weylPerm_eq {g : monoLin π} {σ : Equiv.Perm (Fin n)}
    (h : IsLinePerm σ ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    weylPerm hk hπ g = σ :=
  (isLinePerm_weylPerm hk hπ g).unique h

theorem weylPerm_of_mem_torusLin {g : monoLin π} (hg : (g : E) ∈ torusLin π) :
    weylPerm hk hπ g = 1 :=
  weylPerm_eq hk hπ (isLinePerm_one_of_mem_diagonalSL (torusLin_le_comap_diagonalSL hk hπ hg))

theorem conj_wLift_one_of_signedPerm {a b : Fin n} (hab : a ≠ b) {g : E}
    {σ : Equiv.Perm (Fin n)} {c : Fin n → kˣ}
    (hg : ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm σ fun x => (c x : k)) :
    g * wLift π a b 1 * g⁻¹ = wLift π (σ a) (σ b) (c b * (c a)⁻¹)⁻¹ := by
  rw [wLift_eq hk hπ hab, conj_rhoLift_of_signedPerm hk hπ hab hg,
    wLift_eq hk hπ (σ.injective.ne hab), ← sl2ConjDiag_inv_wSL_one ((c b * (c a)⁻¹)⁻¹),
    inv_inv]

theorem commute_wLift_one {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Commute (wLift π a b 1) (wLift π c d 1) := by
  have h := conj_wLift_one_of_signedPerm hk hπ hab (pi_wLift_one hk hπ hcd)
  have ha : wSign (k := k) c a = 1 := by simp [wSign, hac]
  have hb : wSign (k := k) c b = 1 := by simp [wSign, hbc]
  rw [Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_of_ne_of_ne hbc hbd, ha, hb,
    inv_one, mul_one, inv_one] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem mul_mem_torusLin_of_conj {x y t t' : E} (hx : π x ∈ monomialSL k n)
    (ht : t ∈ torusLin π) (ht' : t' ∈ torusLin π) (hxy : x * y ∈ torusLin π) :
    x * t * y * t' ∈ torusLin π := by
  rw [show x * t * y * t' = x * t * x⁻¹ * (x * y) * t' by group]
  exact mul_mem (mul_mem (conj_mem_torusLin hk hπ hx ht) hxy) ht'

theorem wLift_braid_mem {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (wLift π a b 1 * wLift π b c 1) ^ 3 ∈ torusLin π ∧
      (wLift π b c 1 * wLift π a b 1) ^ 3 ∈ torusLin π := by
  have h1 := conj_wLift_one_of_signedPerm hk hπ hbc (pi_wLift_one hk hπ hab)
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)] at h1
  have h2 := conj_wLift_one_of_signedPerm hk hπ hab (pi_wLift_one hk hπ hbc)
  rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left] at h2
  have hgg : wLift π a b 1 * wLift π a b 1 ∈ torusLin π := by
    rw [wLift_one_mul_self hk hπ hab]
    exact hLin_mem_torusLin π hab _
  have hgg' : wLift π b c 1 * wLift π b c 1 ∈ torusLin π := by
    rw [wLift_one_mul_self hk hπ hbc]
    exact hLin_mem_torusLin π hbc _
  constructor
  · rw [show (wLift π a b 1 * wLift π b c 1) ^ 3 =
        wLift π a b 1 * wLift π b c 1 * (wLift π a b 1)⁻¹ * (wLift π a b 1 * wLift π a b 1) *
          (wLift π b c 1 * wLift π a b 1 * (wLift π b c 1)⁻¹) *
          (wLift π b c 1 * wLift π b c 1) by rw [pow_three]; group, h1, h2]
    exact mul_mem_torusLin_of_conj hk hπ (pi_wLift_mem hk hπ hac _) hgg hgg'
      (by rw [wLift_mul_wLift hk hπ hac]; exact hLin_mem_torusLin π hac _)
  · rw [show (wLift π b c 1 * wLift π a b 1) ^ 3 =
        wLift π b c 1 * wLift π a b 1 * (wLift π b c 1)⁻¹ * (wLift π b c 1 * wLift π b c 1) *
          (wLift π a b 1 * wLift π b c 1 * (wLift π a b 1)⁻¹) *
          (wLift π a b 1 * wLift π a b 1) by rw [pow_three]; group, h1, h2]
    exact mul_mem_torusLin_of_conj hk hπ (pi_wLift_mem hk hπ hac _) hgg' hgg
      (by rw [wLift_mul_wLift hk hπ hac]; exact hLin_mem_torusLin π hac _)

end Weyl

section Coxeter

variable {m : ℕ} {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) k}

theorem wAdj_castSucc (i : Fin m) : wAdj π i.castSucc = wLift π i.castSucc i.succ 1 := by
  have h : (i.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp
  rw [wAdj, dite_eq_left h]
  rfl

theorem wAdj_last : wAdj π (Fin.last m) = 1 := by
  rw [wAdj, dite_eq_right (by simp)]

theorem coxeter_A_adj {i j : Fin m} (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    coxeterMatrix (isFiniteType_A m) i j = 3 := by
  have hij : i ≠ j := fun e => by subst e; omega
  simp [CartanMatrix.A, hij, Ne.symm hij, h, h.symm]

theorem coxeter_A_far {i j : Fin m} (hij : i ≠ j)
    (h : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    coxeterMatrix (isFiniteType_A m) i j = 2 := by
  have h' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := fun h'' => h h''.symm
  simp [CartanMatrix.A, hij, Ne.symm hij, h, h']

variable [Finite k] [Finite E] (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem wAdj_coxeter_mem (i j : Fin m) :
    (wAdj π i.castSucc * wAdj π j.castSucc) ^ coxeterMatrix (isFiniteType_A m) i j ∈
      torusLin π := by
  rw [wAdj_castSucc, wAdj_castSucc]
  rcases eq_or_ne i j with rfl | hij
  · rw [CoxeterMatrix.diagonal, pow_one, wLift_one_mul_self hk hπ Fin.castSucc_lt_succ.ne]
    exact hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [coxeter_A_adj h]
    rcases h with h | h
    · rw [show i.succ = j.castSucc from
        Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
      exact (wLift_braid_mem hk hπ ((Fin.castSucc_injective m).ne hij) Fin.castSucc_lt_succ.ne
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))).1
    · rw [show j.succ = i.castSucc from
        Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
      exact (wLift_braid_mem hk hπ ((Fin.castSucc_injective m).ne hij.symm)
        Fin.castSucc_lt_succ.ne
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))).2
  · rw [coxeter_A_far hij h]
    rw [not_or] at h
    have hc := commute_wLift_one hk hπ (a := i.castSucc) (b := i.succ) (c := j.castSucc)
      (d := j.succ) Fin.castSucc_lt_succ.ne Fin.castSucc_lt_succ.ne
      ((Fin.castSucc_injective m).ne hij)
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
      ((Fin.succ_injective m).ne hij)
    rw [show (wLift π i.castSucc i.succ 1 * wLift π j.castSucc j.succ 1) ^ 2 =
        wLift π i.castSucc i.succ 1 * wLift π i.castSucc i.succ 1 *
          (wLift π j.castSucc j.succ 1 * wLift π j.castSucc j.succ 1) by
      rw [pow_two, mul_assoc, ← mul_assoc (wLift π j.castSucc j.succ 1), ← hc.eq]
      group]
    rw [wLift_one_mul_self hk hπ Fin.castSucc_lt_succ.ne,
      wLift_one_mul_self hk hπ Fin.castSucc_lt_succ.ne]
    exact mul_mem (hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _)
      (hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _)

theorem weylPerm_wAdj (i : Fin m) :
    weylPerm hk hπ ⟨wAdj π i.castSucc, wAdj_mem_monoLin π _⟩ = Equiv.swap i.castSucc i.succ := by
  refine weylPerm_eq hk hπ ?_
  change IsLinePerm _ ((π (wAdj π i.castSucc) : SpecialLinearGroup (Fin (m + 1)) k) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) k)
  rw [wAdj_castSucc, pi_wLift_one hk hπ Fin.castSucc_lt_succ.ne]
  exact isLinePerm_signedPerm _ fun x => (wSign (k := k) i.castSucc x).ne_zero

theorem weylPerm_surjective : Function.Surjective (weylPerm hk hπ) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro τ _
  have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top τ
  refine (Submonoid.closure_le (S := (weylPerm hk hπ).range.toSubmonoid)).2 ?_ hτ
  rintro _ ⟨i, rfl⟩
  exact ⟨_, weylPerm_wAdj hk hπ i⟩

theorem ker_weylPerm : (weylPerm hk hπ).ker = (torusLin π).subgroupOf (monoLin π) := by
  have hTk : (torusLin π).subgroupOf (monoLin π) ≤ (weylPerm hk hπ).ker := fun g hg =>
    weylPerm_of_mem_torusLin hk hπ (Subgroup.mem_subgroupOf.1 hg)
  refine le_antisymm ?_ hTk
  have := normal_torusLin_subgroupOf hk hπ
  obtain ⟨f, hf⟩ : ∃ f : Fin m → monoLin π ⧸ (torusLin π).subgroupOf (monoLin π),
      ∀ i, f i = ((⟨wAdj π i.castSucc, wAdj_mem_monoLin π _⟩ : monoLin π) :
        monoLin π ⧸ (torusLin π).subgroupOf (monoLin π)) := ⟨_, fun _ => rfl⟩
  have hlift : (coxeterMatrix (isFiniteType_A m)).IsLiftable f := by
    intro i j
    rw [hf, hf, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_mul]
    exact wAdj_coxeter_mem hk hπ i j
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (coxeterMatrix (isFiniteType_A m)).Group →*
      monoLin π ⧸ (torusLin π).subgroupOf (monoLin π),
      ∀ i, ψ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple i) = f i :=
    ⟨_, (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.lift_apply_simple hlift⟩
  obtain ⟨φb, hφb⟩ : ∃ φb : monoLin π ⧸ (torusLin π).subgroupOf (monoLin π) →*
      Equiv.Perm (Fin (m + 1)), ∀ g : monoLin π, φb g = weylPerm hk hπ g :=
    ⟨QuotientGroup.lift _ _ hTk, fun g => QuotientGroup.lift_mk _ hTk g⟩
  have hχs : ∀ i, φb (ψ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple i)) =
      Equiv.swap i.castSucc i.succ := fun i => by
    rw [hψ, hf, hφb, weylPerm_wAdj hk hπ i]
  have hstd : ∀ (w : (coxeterMatrix (isFiniteType_A m)).Group) (v : Fin m → ℤ),
      toStd m (weylAction (isFiniteType_A m) w v) = toStd m v ∘ ⇑(φb (ψ w))⁻¹ := by
    intro w
    obtain ⟨ω, rfl⟩ := (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd_surjective w
    induction ω with
    | nil =>
      intro v
      rw [CoxeterSystem.wordProd_nil, map_one, map_one, map_one, inv_one, Module.End.one_apply,
        Equiv.Perm.coe_one, Function.comp_id]
    | cons i ω ih =>
      intro v
      rw [CoxeterSystem.wordProd_cons, map_mul (weylAction (isFiniteType_A m)),
        Module.End.mul_apply, weylAction_simple, toStd_reflection, ih, map_mul ψ, map_mul φb,
        hχs, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul]
      rfl
  have hχ : Function.Injective (φb.comp ψ) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    apply weylAction_injective (isFiniteType_A m)
    rw [map_one]
    refine LinearMap.ext fun v => toStd_injective m ?_
    rw [hstd, show φb (ψ w) = 1 from hw, inv_one, Equiv.Perm.coe_one, Function.comp_id,
      Module.End.one_apply]
  have hle : monoLin π ≤ (ψ.range.comap
      (QuotientGroup.mk' ((torusLin π).subgroupOf (monoLin π)))).map (monoLin π).subtype := by
    show Subgroup.closure ((torusLin π : Set E) ∪ Set.range (wAdj π)) ≤ _
    rw [Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · refine ⟨⟨x, torusLin_le_monoLin π hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact one_mem _
    · refine ⟨⟨wAdj π i, wAdj_mem_monoLin π i⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply]
      by_cases hi : i = Fin.last m
      · subst hi
        rw [show (⟨wAdj π (Fin.last m), wAdj_mem_monoLin π _⟩ : monoLin π) = 1 from
          Subtype.ext wAdj_last, QuotientGroup.mk_one]
        exact one_mem _
      · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = i :=
          ⟨i.castPred hi, Fin.castSucc_castPred i hi⟩
        exact ⟨_, (hψ j).trans (hf j)⟩
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, hyg⟩ := hle hg
    obtain rfl : y = ⟨g, hg⟩ := Subtype.ext hyg
    exact hy
  intro g hg
  obtain ⟨w, hw⟩ := hψs (g : monoLin π ⧸ (torusLin π).subgroupOf (monoLin π))
  have h1 : (φb.comp ψ) w = 1 := by
    rw [MonoidHom.comp_apply, hw, hφb]
    exact MonoidHom.mem_ker.1 hg
  rw [hχ (h1.trans (map_one _).symm), map_one] at hw
  exact (QuotientGroup.eq_one_iff g).1 hw.symm

theorem injective_monoLin : Function.Injective (π.comp (monoLin π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : π g = 1 := hg
  have h1 : g ∈ (weylPerm hk hπ).ker := by
    refine MonoidHom.mem_ker.2 (weylPerm_eq hk hπ ?_)
    rw [hg', Matrix.SpecialLinearGroup.coe_one]
    exact isLinePerm_one
  rw [ker_weylPerm hk hπ] at h1
  have h2 : (π.comp (torusLin π).subtype) ⟨g, Subgroup.mem_subgroupOf.1 h1⟩ =
      (π.comp (torusLin π).subtype) 1 := by
    rw [map_one]
    exact hg'
  have h3 := congrArg Subtype.val (injective_torusLin hk hπ 0 h2)
  exact Subtype.ext h3

theorem map_monoLin : (monoLin π).map π = monomialSL k (m + 1) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (monoLin_le_comap hk hπ)) fun A hA => ?_
  obtain ⟨g, hg⟩ := weylPerm_surjective hk hπ (coordPerm k (m + 1) ⟨A, hA⟩)
  have hdiag : ((⟨π g, monoLin_le_comap hk hπ g.2⟩ : monomialSL k (m + 1))⁻¹ * ⟨A, hA⟩ :
      monomialSL k (m + 1)).val ∈ diagonalSL k (m + 1) := by
    refine mem_diagonalSL_of_isLinePerm_one ?_
    have h := isLinePerm_coordPerm
      ((⟨π g, monoLin_le_comap hk hπ g.2⟩ : monomialSL k (m + 1))⁻¹ * ⟨A, hA⟩)
    rwa [map_mul, map_inv, show coordPerm k (m + 1) ⟨π g, monoLin_le_comap hk hπ g.2⟩ =
      weylPerm hk hπ g from rfl, hg, inv_mul_cancel] at h
  rw [← map_torusLin hk hπ 0] at hdiag
  obtain ⟨t, ht, hte⟩ := hdiag
  refine ⟨(g : E) * t, mul_mem g.2 (torusLin_le_monoLin π ht), ?_⟩
  rw [map_mul, hte]
  show π g * ((π g)⁻¹ * A) = A
  rw [mul_inv_cancel_left]

end Coxeter

theorem odd_field_linear_central_large_prime_faithful_torus_and_monomial_lift {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (_hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = ℓ ^ f) {n : ℕ} (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* SpecialLinearGroup (Fin n) k) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∀ x ∈ torusLin π, ∀ y ∈ torusLin π, x * y = y * x) ∧
    (∀ i j : Fin n, i ≠ j → ∀ a b : kˣ, hLin π i j (a * b) = hLin π i j a * hLin π i j b) ∧
    (∀ i j : Fin n, i ≠ j → ∀ a : kˣ, hLin π j i a = hLin π i j a⁻¹) ∧
    (∀ i j l : Fin n, i ≠ j → j ≠ l → i ≠ l → ∀ a : kˣ,
      hLin π i l a = hLin π i j a * hLin π j l a) ∧
    (Function.Injective (π.comp (torusLin π).subtype) ∧ (torusLin π).map π = diagonalSL k n) ∧
    (Function.Injective (π.comp (monoLin π).subtype) ∧ (monoLin π).map π = monomialSL k n) ∧
    (torusLin π ≤ monoLin π ∧ ((torusLin π).subgroupOf (monoLin π)).Normal ∧
      ∃ φ : monoLin π →* Equiv.Perm (Fin n),
        (∀ g : monoLin π, IsLinePerm (φ g)
          ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) ∧
        Function.Surjective φ ∧ φ.ker = (torusLin π).subgroupOf (monoLin π)) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), wAdj π i * wAdj π i = hLin π i ⟨i.val + 1, h⟩ (-1)) ∧
    (∀ (g : E) (σ : Equiv.Perm (Fin n)) (c : Fin n → kˣ),
      ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        signedPerm σ (fun x => (c x : k)) →
      ∀ i j : Fin n, i ≠ j →
        (∀ a : k, g * xLift π i j a * g⁻¹ = xLift π (σ i) (σ j) ((c i : k) / c j * a)) ∧
        ∀ a : kˣ, g * hLin π i j a * g⁻¹ = hLin π (σ i) (σ j) a) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have hk2 := ringChar_ne_two_of_card hℓ hℓodd hk
  have hπ' : IsLargeCentralExt π := ⟨hπ, hC, p, hp, hp3, hCp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun x hx y hy => (torusLin_commute hk2 hπ' hx hy).eq,
    fun i j hij a b => hLin_mul hk2 hπ' hij a b,
    fun i j hij a => hLin_swap hk2 hπ' hij a,
    fun i j l hij hjl hil a => hLin_trans hk2 hπ' hij hjl hil a,
    ⟨injective_torusLin hk2 hπ' 0, map_torusLin hk2 hπ' 0⟩,
    ⟨injective_monoLin hk2 hπ', map_monoLin hk2 hπ'⟩,
    ⟨torusLin_le_monoLin π, normal_torusLin_subgroupOf hk2 hπ', weylPerm hk2 hπ',
      isLinePerm_weylPerm hk2 hπ', weylPerm_surjective hk2 hπ', ker_weylPerm hk2 hπ'⟩,
    fun i h => ?_, fun g σ c hg i j hij =>
      ⟨fun a => conj_xLift_of_signedPerm hk2 hπ' hij hg a,
        fun a => conj_hLin_of_signedPerm hk2 hπ' hij hg a⟩⟩
  rw [wAdj, dite_eq_left h]
  exact wLift_one_mul_self hk2 hπ' (ne_fin_succ i h)

end LinearRoots

end CFSG.RankThree.CentralLift
