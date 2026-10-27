module

public import CFSG.RankThree.CentralLift.LargeLift
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.RankThree.CentralLift

namespace LinearRoots

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat pairMat_one pairMat_mul
  pairMat_apply_pair pairMat_cases pairMat_apply_equiv signedPerm_mul_pairMat sl2ConjDiag
  coe_sl2ConjDiag)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)

variable {k : Type} [Field k] {n : ℕ}

section Matrices

theorem pairMat_transvection {i j : Fin n} (hij : i ≠ j) {p q : Fin 2} (hpq : p ≠ q) (c : k) :
    pairMat i j (transvection p q c) = transvection (![i, j] p) (![i, j] q) c := by
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · ext x y
    simp only [pairMat, transvection, of_apply, Matrix.add_apply, one_apply, single_apply]
    split_ifs <;> simp_all [eq_comm]
  · ext x y
    simp only [pairMat, transvection, of_apply, Matrix.add_apply, one_apply, single_apply]
    split_ifs <;> simp_all [eq_comm]
  · exact absurd rfl hpq

theorem det_pairMat {i j : Fin n} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    (pairMat i j (g : Matrix (Fin 2) (Fin 2) k)).det = 1 := by
  let δ : SpecialLinearGroup (Fin 2) k →* k := Matrix.detMonoidHom.comp
    ((CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMatHom (ι := Fin n) hij).comp
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) k)).comp SpecialLinearGroup.toGL))
  have hδ : δ = 1 := by
    refine MonoidHom.eq_of_eqOn_dense
      (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨p, q, hpq, c⟩, rfl⟩
    change (pairMat i j (transvection p q c)).det = 1
    rw [pairMat_transvection hij hpq c, det_transvection_of_ne]
    fin_cases p <;> fin_cases q
    · exact absurd rfl hpq
    · exact hij
    · exact hij.symm
    · exact absurd rfl hpq
  exact DFunLike.congr_fun hδ g

variable (k) in
@[expose] noncomputable def rhoSL (i j : Fin n) :
    SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin n) k :=
  if h : i = j then 1 else
    { toFun := fun g => ⟨pairMat i j (g : Matrix (Fin 2) (Fin 2) k), det_pairMat h g⟩
      map_one' := Subtype.ext (pairMat_one h)
      map_mul' := fun g g' => Subtype.ext (pairMat_mul h (g : Matrix (Fin 2) (Fin 2) k) g') }

theorem coe_rhoSL {i j : Fin n} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    ((rhoSL k i j g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      pairMat i j (g : Matrix (Fin 2) (Fin 2) k) := by
  rw [rhoSL, dite_eq_right hij]
  rfl

theorem rhoSL_injective {i j : Fin n} (hij : i ≠ j) : Function.Injective (rhoSL k i j) := by
  intro g g' h
  have h' := congrArg (fun x : SpecialLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) h
  simp only [coe_rhoSL hij] at h'
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hij (g : Matrix (Fin 2) (Fin 2) k)
  obtain ⟨g1', g2', g3', g4'⟩ := pairMat_apply_pair hij (g' : Matrix (Fin 2) (Fin 2) k)
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  revert a b
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← g1, ← g1', h']
  · rw [← g2, ← g2', h']
  · rw [← g3, ← g3', h']
  · rw [← g4, ← g4', h']

theorem rhoSL_uSL {i j : Fin n} (hij : i ≠ j) (a : k) : rhoSL k i j (uSL a) = rootElt i j a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_rhoSL hij, coe_rootElt_of_ne hij, coe_uSL]
  have h := pairMat_transvection hij (show (0 : Fin 2) ≠ 1 by decide) a
  have hu : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) k) = transvection 0 1 a := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [transvection]
  rw [hu, h]
  rfl

@[expose] def swapSLElt (g : SpecialLinearGroup (Fin 2) k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) k) 1 1, (g : Matrix (Fin 2) (Fin 2) k) 1 0;
      (g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0], by
    have hg := g.2
    rw [det_fin_two] at hg
    rw [det_fin_two_of]
    linear_combination hg⟩

@[expose] def swapSL : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k where
  toFun := swapSLElt
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [swapSLElt]
  map_mul' g h := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases a <;> fin_cases b <;>
      simp [swapSLElt, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_swapSL (g : SpecialLinearGroup (Fin 2) k) :
    ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(g : Matrix (Fin 2) (Fin 2) k) 1 1, (g : Matrix (Fin 2) (Fin 2) k) 1 0;
        (g : Matrix (Fin 2) (Fin 2) k) 0 1, (g : Matrix (Fin 2) (Fin 2) k) 0 0] := rfl

theorem rhoSL_swap {i j : Fin n} (hij : i ≠ j) :
    rhoSL k j i = (rhoSL k i j).comp swapSL := by
  ext g x y
  rw [MonoidHom.comp_apply, coe_rhoSL hij.symm, coe_rhoSL hij]
  have e1 : ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) k) 1 1 := by simp [coe_swapSL]
  have e2 : ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) k) 1 0 := by simp [coe_swapSL]
  have e3 : ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 := by simp [coe_swapSL]
  have e4 : ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) k) 0 0 := by simp [coe_swapSL]
  obtain ⟨h1, h2, h3, h4⟩ := pairMat_apply_pair hij
    ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
  refine pairMat_cases (P := fun x y d => d = pairMat i j
    ((swapSL g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x y) hij.symm ?_ ?_
    ?_ ?_ (fun x y hx hya hyb => ?_) (fun x y hxa hxb hy => ?_)
    (fun x y hxa hxb hya hyb => ?_) x y
  · rw [h4, e4]
  · rw [h3, e3]
  · rw [h2, e2]
  · rw [h1, e1]
  · rcases hx with rfl | rfl
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMat_apply_snd_of_ne hij
        hyb hya]
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMat_apply_fst_of_ne hyb
        hya]
  · rcases hy with rfl | rfl
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMat_apply_of_ne hxb hxa]
      exact (one_apply_ne hxa).symm
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMat_apply_of_ne hxb hxa]
      exact (one_apply_ne hxb).symm
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pairMat_apply_of_ne hxb hxa]

theorem swapSL_uSL (a : k) : swapSL (uSL a) = vSL a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_swapSL, coe_uSL, coe_vSL]
  fin_cases x <;> fin_cases y <;> simp

theorem signedPerm_mul_rhoSL {i j : Fin n} (hij : i ≠ j) (σ : Equiv.Perm (Fin n))
    (c : Fin n → kˣ) (g : SpecialLinearGroup (Fin 2) k) :
    signedPerm σ (fun x => (c x : k)) * (rhoSL k i j g : Matrix (Fin n) (Fin n) k) =
      (rhoSL k (σ i) (σ j) (sl2ConjDiag (c j * (c i)⁻¹) g) : Matrix (Fin n) (Fin n) k) *
        signedPerm σ (fun x => (c x : k)) := by
  rw [coe_rhoSL hij, coe_rhoSL (fun h => hij (σ.injective h)), coe_sl2ConjDiag]
  have hci := (c i).ne_zero
  have hcj := (c j).ne_zero
  refine signedPerm_mul_pairMat σ _ hij ?_ ?_ ?_ ?_
  · simp [mul_comm]
  · simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev]
    field_simp
  · simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · simp [mul_comm]

theorem sl2ConjDiag_uSL (u : kˣ) (a : k) : sl2ConjDiag u (uSL a) = uSL (a * u⁻¹) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_sl2ConjDiag, coe_uSL, coe_uSL]
  fin_cases x <;> fin_cases y <;> simp

theorem uSL_add (a b : k) : uSL (a + b) = uSL a * uSL b := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL, coe_uSL]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem uSL_zero : uSL (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_uSL]
  fin_cases x <;> fin_cases y <;> simp

theorem uSL_injective : Function.Injective (uSL (K := k)) := by
  intro a b h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simpa [coe_uSL] using this

@[expose] def signUnit (A : Finset (Fin n)) (x : Fin n) : kˣ := if x ∈ A then -1 else 1

theorem prod_signUnit {A : Finset (Fin n)} (hA : A.card = 2) :
    ∏ x, ((signUnit A x : kˣ) : k) = 1 := by
  have h : ∀ x, ((signUnit A x : kˣ) : k) = if x ∈ A then -1 else 1 := fun x => by
    by_cases hx : x ∈ A <;> simp [signUnit, hx]
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hA]
  norm_num

@[expose] def signSL {A : Finset (Fin n)} (hA : A.card = 2) : SpecialLinearGroup (Fin n) k :=
  ⟨diagonal fun x => ((signUnit A x : kˣ) : k), by rw [det_diagonal, prod_signUnit hA]⟩

theorem coe_signSL {A : Finset (Fin n)} (hA : A.card = 2) :
    ((signSL (k := k) hA : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm 1 fun x => ((signUnit A x : kˣ) : k) := by
  rw [signedPerm_one]
  rfl

theorem signUnit_mem {A : Finset (Fin n)} {x : Fin n} (hx : x ∈ A) :
    signUnit (k := k) A x = -1 := by simp [signUnit, hx]

theorem signUnit_notMem {A : Finset (Fin n)} {x : Fin n} (hx : x ∉ A) :
    signUnit (k := k) A x = 1 := by simp [signUnit, hx]

end Matrices

section Defs

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

@[expose] noncomputable def rhoLift (i j : Fin n) : SpecialLinearGroup (Fin 2) k →* E :=
  sl2Lift π (rhoSL k i j)

@[expose] noncomputable def xLift (i j : Fin n) (a : k) : E := rhoLift π i j (uSL a)

@[expose] noncomputable def unipotentLift : Subgroup E :=
  Subgroup.closure {x | ∃ (i j : Fin n) (a : k), i < j ∧ xLift π i j a = x}

end Defs

section Relations

variable [Finite k] {E : Type*} [Group E] [Finite E] {π : E →* SpecialLinearGroup (Fin n) k}
  (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem pi_rhoLift (i j : Fin n) (g : SpecialLinearGroup (Fin 2) k) :
    π (rhoLift π i j g) = rhoSL k i j g :=
  map_sl2Lift_large hk hπ _ g

theorem pi_xLift {i j : Fin n} (hij : i ≠ j) (a : k) : π (xLift π i j a) = rootElt i j a := by
  rw [xLift, pi_rhoLift hk hπ, rhoSL_uSL hij]

omit [Finite k] [Finite E] hk hπ in
theorem xLift_add (i j : Fin n) (a b : k) : xLift π i j (a + b) = xLift π i j a * xLift π i j b :=
  by rw [xLift, uSL_add, map_mul]; rfl

omit [Finite k] [Finite E] hk hπ in
theorem xLift_zero (i j : Fin n) : xLift π i j 0 = 1 := by
  rw [xLift, uSL_zero, map_one]

omit [Finite k] [Finite E] hk hπ in
theorem xLift_neg (i j : Fin n) (a : k) : xLift π i j (-a) = (xLift π i j a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← xLift_add, neg_add_cancel, xLift_zero]

theorem xLift_injective {i j : Fin n} (hij : i ≠ j) : Function.Injective (xLift π i j) :=
  (sl2Lift_injective_large hk hπ (rhoSL_injective hij)).comp uSL_injective

theorem rhoLift_swap {i j : Fin n} (hij : i ≠ j) : rhoLift π j i = (rhoLift π i j).comp swapSL := by
  rw [rhoLift, rhoLift, rhoSL_swap hij, sl2Lift_comp_large hk hk hπ]

theorem xLift_swap {i j : Fin n} (hij : i ≠ j) (a : k) : xLift π j i a = rhoLift π i j (vSL a) := by
  rw [xLift, rhoLift_swap hk hπ hij, MonoidHom.comp_apply, swapSL_uSL]

theorem conj_rhoLift_of_signedPerm {i j : Fin n} (hij : i ≠ j) {g : E} {σ : Equiv.Perm (Fin n)}
    {c : Fin n → kˣ} (hg : ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm σ fun x => (c x : k)) (A : SpecialLinearGroup (Fin 2) k) :
    g * rhoLift π i j A * g⁻¹ = rhoLift π (σ i) (σ j) (sl2ConjDiag (c j * (c i)⁻¹) A) := by
  have hconj : (MulAut.conj (π g)).toMonoidHom.comp (rhoSL k i j) =
      (rhoSL k (σ i) (σ j)).comp (sl2ConjDiag (c j * (c i)⁻¹)) := by
    ext B : 1
    change π g * rhoSL k i j B * (π g)⁻¹ = rhoSL k (σ i) (σ j) (sl2ConjDiag (c j * (c i)⁻¹) B)
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext ?_
    change ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        (rhoSL k i j B : Matrix (Fin n) (Fin n) k) =
      (rhoSL k (σ i) (σ j) (sl2ConjDiag (c j * (c i)⁻¹) B) : Matrix (Fin n) (Fin n) k) *
        ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)
    rw [hg]
    exact signedPerm_mul_rhoSL hij σ c B
  rw [rhoLift, conj_sl2Lift_apply_large hk hπ, hconj, ← sl2Lift_comp_large hk hk hπ]
  rfl

theorem conj_xLift_of_signedPerm {i j : Fin n} (hij : i ≠ j) {g : E} {σ : Equiv.Perm (Fin n)}
    {c : Fin n → kˣ} (hg : ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      signedPerm σ fun x => (c x : k)) (a : k) :
    g * xLift π i j a * g⁻¹ = xLift π (σ i) (σ j) ((c i : k) / c j * a) := by
  rw [xLift, conj_rhoLift_of_signedPerm hk hπ hij hg, sl2ConjDiag_uSL, xLift]
  congr 2
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem conj_xLift_signSL {A : Finset (Fin n)} (hA : A.card = 2) {g : E}
    (hg : π g = signSL hA) {i j : Fin n} (hij : i ≠ j) (a : k) :
    g * xLift π i j a * g⁻¹ =
      xLift π i j (((signUnit A i : kˣ) : k) / (signUnit A j : kˣ) * a) := by
  rw [conj_xLift_of_signedPerm hk hπ hij (σ := 1) (by rw [hg, coe_signSL]) a]
  rfl

omit [Finite k] [Finite E] hk in
theorem eq_one_of_mem_ker_of_eq_inv {c : E} (hc : c ∈ π.ker) (h : c = c⁻¹) : c = 1 := by
  obtain ⟨p, hp, hp3, hpk⟩ := hπ.large
  have : Fact p.Prime := ⟨hp⟩
  have h2 : c ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel c
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hpk) ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hm
  have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hm] at hdvd
  rcases m with _ | m
  · rw [pow_zero] at hm
    exact orderOf_eq_one_iff.1 hm
  · exfalso
    have := Nat.le_of_dvd (by norm_num) ((dvd_pow_self p (Nat.succ_ne_zero m)).trans hdvd)
    omega

omit [Finite k] [Finite E] hk in
theorem commutatorElement_eq_one_of_sign {X Y g : E} (hc : ⁅X, Y⁆ ∈ π.ker)
    (hX : g * X * g⁻¹ = X) (hY : g * Y * g⁻¹ = Y⁻¹) : ⁅X, Y⁆ = 1 := by
  have hcen := Subgroup.mem_center_iff.1 (hπ.cen hc)
  have hcen' := Subgroup.mem_center_iff.1 (inv_mem (hπ.cen hc))
  have h1 : g * ⁅X, Y⁆ * g⁻¹ = ⁅X, Y⁻¹⁆ := by
    have h := map_commutatorElement (MulAut.conj g) X Y
    simp only [MulAut.conj_apply] at h
    rw [h, hX, hY]
  have h2 : g * ⁅X, Y⁆ * g⁻¹ = ⁅X, Y⁆ := by
    rw [hcen g, mul_inv_cancel_right]
  have h3 : ⁅X, Y⁻¹⁆ = ⁅X, Y⁆⁻¹ := by
    have h4 : Y⁻¹ * ⁅X, Y⁆⁻¹ * Y = ⁅X, Y⁆⁻¹ := by
      rw [hcen' Y⁻¹, inv_mul_cancel_right]
    rw [← h4]
    simp only [commutatorElement_def]
    group
  refine eq_one_of_mem_ker_of_eq_inv hπ hc ?_
  rw [← h3, ← h1, h2]

theorem commutatorElement_xLift_eq_one {i j k' l : Fin n} (hij : i ≠ j) (hkl : k' ≠ l)
    (hjk : j ≠ k') (hil : i ≠ l) (a b : k) : ⁅xLift π i j a, xLift π k' l b⁆ = 1 := by
  have hker : ⁅xLift π i j a, xLift π k' l b⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, pi_xLift hk hπ hij, pi_xLift hk hπ hkl,
      commutatorElement_eq_one_iff_mul_comm]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt_mul_comm hjk (Ne.symm hil) a b
  by_cases hik : i = k'
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      rw [commutatorElement_eq_one_iff_mul_comm, ← xLift_add, ← xLift_add, add_comm]
    ·
      have hA : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
      obtain ⟨g, hg⟩ := hπ.surj (signSL (k := k) hA)
      refine commutatorElement_eq_one_of_sign hπ hker ?_ ?_ (g := g)
      · rw [conj_xLift_signSL hk hπ hA hg hij, signUnit_mem (by simp), signUnit_mem (by simp)]
        congr 1
        simp
      · rw [conj_xLift_signSL hk hπ hA hg hkl, signUnit_mem (by simp),
          signUnit_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hil, Ne.symm hjl⟩), ← xLift_neg]
        congr 1
        simp
  · by_cases hjl : j = l
    · subst hjl
      have hA : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
      obtain ⟨g, hg⟩ := hπ.surj (signSL (k := k) hA)
      refine commutatorElement_eq_one_of_sign hπ hker ?_ ?_ (g := g)
      · rw [conj_xLift_signSL hk hπ hA hg hij, signUnit_mem (by simp), signUnit_mem (by simp)]
        congr 1
        simp
      · rw [conj_xLift_signSL hk hπ hA hg hkl, signUnit_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hik h.symm, hkl⟩), signUnit_mem (by simp), ← xLift_neg]
        congr 1
        simp
    ·
      have hcomm : ∀ g g' : SpecialLinearGroup (Fin 2) k,
          Commute (rhoSL k i j g) (rhoSL k k' l g') := by
        intro g g'
        have hM := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.isSupp_pairMat
          (a := i) (b := j) (g : Matrix (Fin 2) (Fin 2) k)
        have hN := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.isSupp_pairMat
          (a := k') (b := l) (g' : Matrix (Fin 2) (Fin 2) k)
        have hdisj : Disjoint ({i, j} : Set (Fin n)) {k', l} := by
          rw [Set.disjoint_left]
          rintro x (rfl | rfl) (h | h)
          · exact hik h
          · exact hil h
          · exact hjk h
          · exact hjl h
        have h := hM.commute hN hdisj
        refine Subtype.ext ?_
        change (rhoSL k i j g : Matrix (Fin n) (Fin n) k) * (rhoSL k k' l g' : Matrix _ _ k) =
          (rhoSL k k' l g' : Matrix (Fin n) (Fin n) k) * (rhoSL k i j g : Matrix _ _ k)
        rw [coe_rhoSL hij, coe_rhoSL hkl]
        exact h.eq
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (commute_sl2Lift_large hk hk hπ _ _ hcomm (uSL a) (uSL b)).eq

theorem commutatorElement_xLift {i j k' : Fin n} (hij : i ≠ j) (hjk : j ≠ k') (hik : i ≠ k')
    (a b : k) : ⁅xLift π i j a, xLift π j k' b⁆ = xLift π i k' (a * b) := by
  obtain ⟨d, hd⟩ : ∃ d : k → E, ∀ a, d a =
      ⁅xLift π i j a, xLift π j k' b⁆ * xLift π i k' (-(a * b)) := ⟨_, fun _ => rfl⟩
  have hdker : ∀ a, d a ∈ π.ker := fun a => by
    rw [MonoidHom.mem_ker, hd, map_mul, map_commutatorElement, pi_xLift hk hπ hij,
      pi_xLift hk hπ hjk, pi_xLift hk hπ hik,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.commutatorElement_rootElt hij hjk hik,
      ← CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt_add, add_neg_cancel,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt_zero]
  have hdc : ∀ a g, g * d a = d a * g := fun a => Subgroup.mem_center_iff.1 (hπ.cen (hdker a))
  have hcf : ∀ a, ⁅xLift π i j a, xLift π j k' b⁆ = d a * xLift π i k' (a * b) := fun a => by
    rw [hd, mul_assoc, ← xLift_add, neg_add_cancel, xLift_zero, mul_one]
  have hxz : ∀ a c, xLift π i j a * xLift π i k' c = xLift π i k' c * xLift π i j a := fun a c =>
    commutatorElement_eq_one_iff_mul_comm.1
      (commutatorElement_xLift_eq_one hk hπ hij hik hij.symm hik a c)
  have hadd : ∀ a a', d (a + a') = d a * d a' := by
    intro a a'
    have e : ⁅xLift π i j a * xLift π i j a', xLift π j k' b⁆ =
        xLift π i j a * ⁅xLift π i j a', xLift π j k' b⁆ * (xLift π i j a)⁻¹ *
          ⁅xLift π i j a, xLift π j k' b⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : xLift π i j a * (d a' * xLift π i k' (a' * b)) * (xLift π i j a)⁻¹ =
        d a' * xLift π i k' (a' * b) := by
      calc xLift π i j a * (d a' * xLift π i k' (a' * b)) * (xLift π i j a)⁻¹
          = xLift π i j a * d a' * xLift π i k' (a' * b) * (xLift π i j a)⁻¹ := by
            rw [← mul_assoc]
        _ = d a' * (xLift π i j a * xLift π i k' (a' * b)) * (xLift π i j a)⁻¹ := by
            rw [hdc a' (xLift π i j a), mul_assoc (d a')]
        _ = d a' * (xLift π i k' (a' * b) * xLift π i j a) * (xLift π i j a)⁻¹ := by
            rw [hxz]
        _ = d a' * xLift π i k' (a' * b) := by group
    have hc : ⁅xLift π i j (a + a'), xLift π j k' b⁆ =
        d a * d a' * xLift π i k' ((a + a') * b) := by
      rw [xLift_add, e, hcf a', e2, hcf a]
      calc d a' * xLift π i k' (a' * b) * (d a * xLift π i k' (a * b))
          = (d a' * xLift π i k' (a' * b) * d a) * xLift π i k' (a * b) := by
            rw [← mul_assoc]
        _ = (d a * (d a' * xLift π i k' (a' * b))) * xLift π i k' (a * b) := by
            rw [← hdc a (d a' * xLift π i k' (a' * b))]
        _ = d a * d a' * (xLift π i k' (a' * b) * xLift π i k' (a * b)) := by group
        _ = d a * d a' * xLift π i k' ((a + a') * b) := by
            rw [← xLift_add, add_mul, add_comm (a * b)]
    rw [hd, hc, mul_assoc, ← xLift_add, add_neg_cancel, xLift_zero, mul_one]
  have hd0 : d 0 = 1 := by
    rw [hd, xLift_zero, zero_mul, neg_zero, xLift_zero, commutatorElement_one_left, one_mul]
  have hneg : d (-a) = (d a)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hadd, neg_add_cancel, hd0]
  have hA : ({j, k'} : Finset (Fin n)).card = 2 := Finset.card_pair hjk
  obtain ⟨g, hg⟩ := hπ.surj (signSL (k := k) hA)
  have hi : i ∉ ({j, k'} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hij, hik⟩
  have hgx : g * xLift π i j a * g⁻¹ = xLift π i j (-a) := by
    rw [conj_xLift_signSL hk hπ hA hg hij, signUnit_notMem hi, signUnit_mem (by simp)]
    congr 1
    simp
  have hgy : g * xLift π j k' b * g⁻¹ = xLift π j k' b := by
    rw [conj_xLift_signSL hk hπ hA hg hjk, signUnit_mem (by simp), signUnit_mem (by simp)]
    congr 1
    simp
  have hgz : g * xLift π i k' (-(a * b)) * g⁻¹ = xLift π i k' (-(-a * b)) := by
    rw [conj_xLift_signSL hk hπ hA hg hik, signUnit_notMem hi, signUnit_mem (by simp)]
    congr 1
    simp
  have hgd : g * d a * g⁻¹ = d (-a) := by
    have h := map_commutatorElement (MulAut.conj g) (xLift π i j a) (xLift π j k' b)
    simp only [MulAut.conj_apply] at h
    have e : g * (⁅xLift π i j a, xLift π j k' b⁆ * xLift π i k' (-(a * b))) * g⁻¹ =
        (g * ⁅xLift π i j a, xLift π j k' b⁆ * g⁻¹) * (g * xLift π i k' (-(a * b)) * g⁻¹) := by
      group
    rw [hd, hd, e, h, hgx, hgy, hgz]
  have hda : d a = (d a)⁻¹ := by
    rw [← hneg, ← hgd, hdc a g, mul_inv_cancel_right]
  rw [hcf a, eq_one_of_mem_ker_of_eq_inv hπ (hdker a) hda, one_mul]

theorem map_unipotentLift :
    (unipotentLift π).map π = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n k := by
  apply le_antisymm
  · rw [unipotentLift, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, a, hij, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, pi_xLift hk hπ hij.ne]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt_mem_unitriangular hij a
  · refine CFSG.LocalAnalysis.ComponentInitial.LinearCover.unitriangular_le_closure_rootElt.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, a, hij, rfl⟩
    exact ⟨xLift π i j a, Subgroup.subset_closure ⟨i, j, a, hij, rfl⟩, pi_xLift hk hπ hij.ne a⟩

omit hk hπ [Finite k] [Finite E] in
theorem card_sup_le_of_le_normalizer {H N : Subgroup E} (h : H ≤ Subgroup.normalizer (N : Set E)) :
    Nat.card (H ⊔ N : Subgroup E) ≤ Nat.card H * Nat.card N := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right H N h
  change Nat.card (((H ⊔ N : Subgroup E) : Set E)) ≤ _
  rw [e]
  exact Set.natCard_mul_le

end Relations

section Filtration

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

@[expose] noncomputable def colLift (m : ℕ) : Subgroup E :=
  Subgroup.closure {x | ∃ (i j : Fin n) (a : k), i < j ∧ (j : ℕ) < m ∧ xLift π i j a = x}

@[expose] noncomputable def colRoots (c : Fin n) : Subgroup E :=
  Subgroup.closure {x | ∃ (i : Fin n) (a : k), i < c ∧ xLift π i c a = x}

@[expose] def uSLHom : Multiplicative k →* SpecialLinearGroup (Fin 2) k where
  toFun a := uSL a.toAdd
  map_one' := uSL_zero
  map_mul' a b := uSL_add a.toAdd b.toAdd

theorem colLift_zero : colLift π 0 = ⊥ := by
  rw [colLift, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨i, j, a, -, hj, -⟩
  exact absurd hj (Nat.not_lt_zero _)

theorem colLift_succ (c : Fin n) : colLift π ((c : ℕ) + 1) = colLift π c ⊔ colRoots π c := by
  rw [colLift, colLift, colRoots, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨i, j, a, hij, hjm, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjm with h | h
    · exact Or.inl ⟨i, j, a, hij, h, rfl⟩
    · have : j = c := Fin.ext h
      subst this
      exact Or.inr ⟨i, a, hij, rfl⟩
  · rintro (⟨i, j, a, hij, hjm, rfl⟩ | ⟨i, a, hic, rfl⟩)
    · exact ⟨i, j, a, hij, Nat.lt_succ_of_lt hjm, rfl⟩
    · exact ⟨i, c, a, hic, Nat.lt_succ_self _, rfl⟩

theorem colLift_eq_unipotentLift : colLift π n = unipotentLift π := by
  rw [colLift, unipotentLift]
  congr 1
  ext x
  constructor
  · rintro ⟨i, j, a, hij, -, rfl⟩
    exact ⟨i, j, a, hij, rfl⟩
  · rintro ⟨i, j, a, hij, rfl⟩
    exact ⟨i, j, a, hij, j.2, rfl⟩

variable [Finite k] [Finite E] {π} (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem colLift_le_normalizer (c : Fin n) :
    colLift π c ≤ Subgroup.normalizer (colRoots π c : Set E) := by
  rw [colLift, Subgroup.closure_le]
  rintro _ ⟨i, j, a, hij, hjc, rfl⟩
  have hjc' : j < c := hjc
  have hic : i < c := hij.trans hjc'
  have key : ∀ b : k, ∀ y ∈ colRoots π c,
      xLift π i j b * y * (xLift π i j b)⁻¹ ∈ colRoots π c := by
    intro b y hy
    suffices h : colRoots π c ≤
        (colRoots π c).comap (MulAut.conj (xLift π i j b)).toMonoidHom from h hy
    rw [colRoots, Subgroup.closure_le]
    rintro _ ⟨l, b', hlc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change xLift π i j b * xLift π l c b' * (xLift π i j b)⁻¹ ∈ colRoots π c
    by_cases hjl : j = l
    · subst hjl
      have h := commutatorElement_xLift hk hπ hij.ne hlc.ne hic.ne b b'
      have e : xLift π i j b * xLift π j c b' * (xLift π i j b)⁻¹ =
          ⁅xLift π i j b, xLift π j c b'⁆ * xLift π j c b' := by
        simp only [commutatorElement_def]
        group
      rw [e, h]
      exact mul_mem (Subgroup.subset_closure ⟨i, b * b', hic, rfl⟩)
        (Subgroup.subset_closure ⟨j, b', hlc, rfl⟩)
    · have h := commutatorElement_xLift_eq_one hk hπ hij.ne hlc.ne hjl hic.ne b b'
      rw [commutatorElement_eq_one_iff_mul_comm] at h
      rw [h, mul_inv_cancel_right]
      exact Subgroup.subset_closure ⟨l, b', hlc, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key a y
  · intro hy
    have h := key (-a) _ hy
    rw [xLift_neg, inv_inv] at h
    simpa [mul_assoc] using h

theorem card_colRoots_le (c : Fin n) : Nat.card (colRoots π c) ≤ Nat.card k ^ (c : ℕ) := by
  let φ : {i : Fin n // i < c} → Multiplicative k →* E := fun i => (rhoLift π i c).comp uSLHom
  have hcomm : Pairwise fun i i' : {i : Fin n // i < c} => ∀ x y, Commute (φ i x) (φ i' y) := by
    intro i i' _ x y
    exact commutatorElement_eq_one_iff_mul_comm.1 (commutatorElement_xLift_eq_one hk hπ
      (ne_of_lt i.2) (ne_of_lt i'.2) (ne_of_gt i'.2) (ne_of_lt i.2) x.toAdd y.toAdd)
  have hrange : (MonoidHom.noncommPiCoprod φ hcomm).range = colRoots π c := by
    rw [MonoidHom.noncommPiCoprod_range, Subgroup.iSup_eq_closure, colRoots]
    congr 1
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, y, rfl⟩
      exact ⟨i, y.toAdd, i.2, rfl⟩
    · rintro ⟨i, a, hi, rfl⟩
      exact ⟨⟨i, hi⟩, Multiplicative.ofAdd a, rfl⟩
  have hcard : Nat.card {i : Fin n // i < c} = c := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [show (Finset.univ.filter fun i : Fin n => i < c) = Finset.Iio c by ext; simp]
    exact Fin.card_Iio c
  rw [← hrange]
  calc Nat.card (MonoidHom.noncommPiCoprod φ hcomm).range
      ≤ Nat.card ({i : Fin n // i < c} → Multiplicative k) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)
    _ = Nat.card k ^ (c : ℕ) := by
        rw [Nat.card_fun, hcard]
        rfl

theorem card_colLift_le : ∀ m : ℕ, m ≤ n → Nat.card (colLift π m) ≤ Nat.card k ^ (m * (m - 1) / 2)
  | 0, _ => by rw [colLift_zero, Subgroup.card_bot]; exact Nat.one_le_pow _ _ Nat.card_pos
  | m + 1, hm => by
    have h := colLift_succ π ⟨m, hm⟩
    simp only at h
    rw [h, Nat.triangle_succ, pow_add]
    exact (card_sup_le_of_le_normalizer (colLift_le_normalizer hk hπ ⟨m, hm⟩)).trans
      (Nat.mul_le_mul (card_colLift_le m (by omega)) (card_colRoots_le hk hπ ⟨m, hm⟩))

theorem injective_unipotentLift : Function.Injective (π.comp (unipotentLift π).subtype) := by
  have hmap := map_unipotentLift hk hπ
  have hmem : ∀ x : unipotentLift π, (π.comp (unipotentLift π).subtype) x ∈
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n k := fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem π x.2
  let ψ := (π.comp (unipotentLift π).subtype).codRestrict _ hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hle : Nat.card (unipotentLift π) ≤
      Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n k) := by
    rw [← colLift_eq_unipotentLift,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular]
    exact card_colLift_le hk hπ n le_rfl
  have hge := Nat.card_le_card_of_surjective ψ hψ
  have hbij := (Nat.bijective_iff_surjective_and_card ψ).2 ⟨hψ, le_antisymm hle hge⟩
  exact fun x y h => hbij.1 (Subtype.ext h)

end Filtration

theorem ringChar_ne_two_of_card {k : Type} [Field k] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hk : Nat.card k = ℓ ^ f) : ringChar k ≠ 2 := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fintype k := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  rw [ringChar.eq k ℓ]
  exact hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)

theorem odd_field_linear_central_large_prime_root_relations_and_unipotent_lift {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (_hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = ℓ ^ f) {n : ℕ} (_hn : 2 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* SpecialLinearGroup (Fin n) k) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∀ i j : Fin n, i ≠ j → ∀ β : SpecialLinearGroup (Fin 2) k →* E,
      π.comp β = rhoSL k i j ↔ β = rhoLift π i j) ∧
    (∀ i j : Fin n, i ≠ j → ∀ a b : k, xLift π i j a * xLift π i j b = xLift π i j (a + b)) ∧
    (∀ i j : Fin n, i ≠ j → Function.Injective (xLift π i j)) ∧
    (∀ i j : Fin n, i ≠ j → ∀ a : k, xLift π j i a = rhoLift π i j (vSL a)) ∧
    (∀ i j k' l : Fin n, i ≠ j → k' ≠ l → j ≠ k' → i ≠ l → ∀ a b : k,
      ⁅xLift π i j a, xLift π k' l b⁆ = 1) ∧
    (∀ i j k' : Fin n, i ≠ j → j ≠ k' → i ≠ k' → ∀ a b : k,
      ⁅xLift π i j a, xLift π j k' b⁆ = xLift π i k' (a * b)) ∧
    ((unipotentLift π).map π = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n k ∧
      Function.Injective (π.comp (unipotentLift π).subtype)) ∧
    (∀ (g : E) (σ : Equiv.Perm (Fin n)) (c : Fin n → kˣ),
      ((π g : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        signedPerm σ (fun x => (c x : k)) →
      ∀ i j : Fin n, i ≠ j → ∀ a : k,
        g * xLift π i j a * g⁻¹ = xLift π (σ i) (σ j) ((c i : k) / c j * a)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have hk2 := ringChar_ne_two_of_card hℓ hℓodd hk
  have hπ' : IsLargeCentralExt π := ⟨hπ, hC, p, hp, hp3, hCp⟩
  refine ⟨fun i j _ β => ⟨eq_sl2Lift_large hk2 hπ', fun h => h ▸ comp_sl2Lift_large hk2 hπ' _⟩,
    fun i j _ a b => (xLift_add i j a b).symm, fun i j hij => xLift_injective hk2 hπ' hij,
    fun i j hij a => xLift_swap hk2 hπ' hij a,
    fun i j k' l hij hkl hjk hil a b => commutatorElement_xLift_eq_one hk2 hπ' hij hkl hjk hil a b,
    fun i j k' hij hjk hik a b => commutatorElement_xLift hk2 hπ' hij hjk hik a b,
    ⟨map_unipotentLift hk2 hπ', injective_unipotentLift hk2 hπ'⟩,
    fun g σ c hg i j hij a => conj_xLift_of_signedPerm hk2 hπ' hij hg a⟩

end LinearRoots

end CFSG.RankThree.CentralLift
