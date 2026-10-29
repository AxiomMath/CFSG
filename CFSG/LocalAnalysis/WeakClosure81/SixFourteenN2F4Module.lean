module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4
public import CFSG.GroupTheory.GL52.OrderThreeFour
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E15FF
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
public import CFSG.Monster.B.TwoA.Base.Subspaces
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.ExceptionalSL3

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.GroupTheory.GL52 (F4 F4poly F4poly_natDegree F4poly_ne_zero)
open Polynomial

variable {W : Type*} [CommGroup W] [Finite W]

def addModTwo (hw2 : ∀ w : W, w ^ 2 = 1) : Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (n := 2) (fun v => by
    have hv : Additive.ofMul (Additive.toMul v) = v := rfl
    rw [← hv, two_nsmul]
    simpa [pow_two] using congrArg Additive.ofMul (hw2 (Additive.toMul v)))

section Module

variable (hw2 : ∀ w : W, w ^ 2 = 1)
variable (x : MulAut W)

@[expose] def autAddHom : Additive W →+ Additive W where
  toFun v := Additive.ofMul (x (Additive.toMul v))
  map_zero' := by
    show Additive.ofMul (x (Additive.toMul (0 : Additive W))) = 0
    simp
  map_add' a b := by
    show Additive.ofMul (x (Additive.toMul (a + b))) =
      Additive.ofMul (x (Additive.toMul a)) + Additive.ofMul (x (Additive.toMul b))
    rw [toMul_add, map_mul]
    rfl

@[simp] theorem autAddHom_apply (v : Additive W) :
    autAddHom x v = Additive.ofMul (x (Additive.toMul v)) := rfl

def autEnd : @Module.End (ZMod 2) (Additive W) _ _ (addModTwo hw2) :=
  @AddMonoidHom.toZModLinearMap 2 (Additive W) (Additive W) _ _
    (addModTwo hw2) (addModTwo hw2) (autAddHom x)

variable {x}

theorem autEnd_ofMul (w : W) :
    autEnd hw2 x (Additive.ofMul w) = Additive.ofMul (x w) := by
  change autAddHom x (Additive.ofMul w) = Additive.ofMul (x w)
  rfl

theorem autEnd_sq_add_self_add_one (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (v : Additive W) :
    autEnd hw2 x (autEnd hw2 x v) + autEnd hw2 x v + v = 0 := by
  let w : W := Additive.toMul v
  change autEnd hw2 x (autEnd hw2 x (Additive.ofMul w)) +
    autEnd hw2 x (Additive.ofMul w) + Additive.ofMul w = 0
  rw [autEnd_ofMul hw2, autEnd_ofMul hw2]
  change Additive.ofMul (x (x w) * x w * w) = 0
  rw [mulAut_norm_mul_eq_one hx3 hfix w]
  rfl

section Matrix

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

def linearEquivUnit (g : M ≃ₗ[R] M) : (M →ₗ[R] M)ˣ where
  val := g.toLinearMap
  inv := g.symm.toLinearMap
  val_inv := by
    ext v
    simp
  inv_val := by
    ext v
    simp

theorem linearEquivUnit_trans (e f : M ≃ₗ[R] M) :
    linearEquivUnit (e.trans f) = linearEquivUnit f * linearEquivUnit e := by
  apply Units.ext
  change (e.trans f).toLinearMap = f.toLinearMap * e.toLinearMap
  ext v
  simp [LinearEquiv.trans_apply, Module.End.mul_apply]

theorem linearEquivUnit_refl :
    linearEquivUnit (LinearEquiv.refl R M) = 1 := by
  apply Units.ext
  change (LinearEquiv.refl R M).toLinearMap = 1
  ext v
  rfl

theorem linearEquivUnit_injective : Function.Injective (linearEquivUnit (R := R) (M := M)) := by
  intro e f h
  ext v
  have hv := congrArg (fun u : (M →ₗ[R] M)ˣ => (u : M →ₗ[R] M) v) h
  simpa [linearEquivUnit] using hv

noncomputable def matrixOfLinearEquiv {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (g : (n → K) ≃ₗ[K] (n → K)) :
    Matrix.GeneralLinearGroup n K :=
  (Matrix.GeneralLinearGroup.toLin).symm (linearEquivUnit g)

theorem matrixOfLinearEquiv_trans {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (e f : (n → K) ≃ₗ[K] (n → K)) :
    matrixOfLinearEquiv (e.trans f) =
      matrixOfLinearEquiv f * matrixOfLinearEquiv e := by
  unfold matrixOfLinearEquiv
  rw [linearEquivUnit_trans]
  exact map_mul (Matrix.GeneralLinearGroup.toLin).symm _ _

theorem matrixOfLinearEquiv_refl {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] :
    matrixOfLinearEquiv (LinearEquiv.refl K (n → K)) = 1 := by
  unfold matrixOfLinearEquiv
  rw [linearEquivUnit_refl]
  exact map_one (Matrix.GeneralLinearGroup.toLin).symm

theorem matrixOfLinearEquiv_injective {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] :
    Function.Injective (matrixOfLinearEquiv (n := n) (K := K)) := by
  intro e f h
  apply linearEquivUnit_injective
  exact (Matrix.GeneralLinearGroup.toLin).symm.injective h

theorem matrixOfLinearEquiv_mul {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (g h : (n → K) ≃ₗ[K] (n → K)) :
    matrixOfLinearEquiv (g * h) =
      matrixOfLinearEquiv g * matrixOfLinearEquiv h := by
  have hgh : g * h = h.trans g := by
    ext v
    rfl
  rw [hgh, matrixOfLinearEquiv_trans]

theorem conj_mul {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] (n → K)) (L₁ L₂ : V ≃ₗ[K] V) :
    (e.symm.trans (L₁.trans e)) * (e.symm.trans (L₂.trans e)) =
      e.symm.trans ((L₂.trans L₁).trans e) := by
  ext v
  simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply]

def fixedSubmodule {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : V →ₗ[K] V) : Submodule K V :=
  LinearMap.ker (g - LinearMap.id)

theorem mem_fixedSubmodule {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {g : V →ₗ[K] V} {v : V} : v ∈ fixedSubmodule g ↔ g v = v := by
  simp [fixedSubmodule, sub_eq_zero]

theorem fixedSubmodule_eq_of_card_four {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hK : Nat.card K = 4) (hV : Module.finrank K V = 2)
    {Y : Submodule K V} (hY : Nat.card Y = 4)
    (g : V ≃ₗ[K] V) (hgY : Y ≤ fixedSubmodule g.toLinearMap) (hg : g ≠ 1) :
    fixedSubmodule g.toLinearMap = Y := by
  have hYfin : Module.finrank K Y = 1 := by
    have hc := Module.natCard_eq_pow_finrank (K := K) (V := Y)
    rw [hY, hK] at hc
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 4)
    exact hc.symm.trans (by norm_num : (4 : ℕ) = 4 ^ 1)
  by_contra hne
  have hlt : Y < fixedSubmodule g.toLinearMap := lt_of_le_of_ne hgY (Ne.symm hne)
  have hlt_fin : Module.finrank K Y < Module.finrank K (fixedSubmodule g.toLinearMap) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hFle : Module.finrank K (fixedSubmodule g.toLinearMap) ≤ 2 := by
    rw [← hV]
    exact Submodule.finrank_le _
  have hF2 : Module.finrank K (fixedSubmodule g.toLinearMap) = 2 := by omega
  have htop : fixedSubmodule g.toLinearMap = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hF2, hV])
  apply hg
  ext v
  have hv : v ∈ fixedSubmodule g.toLinearMap := htop ▸ Submodule.mem_top
  rw [mem_fixedSubmodule] at hv
  exact hv

def frobMatrixHom :
    Matrix (Fin 2) (Fin 2) (GaloisField 2 2) →*
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2) where
  toFun A := A.map (frobenius (GaloisField 2 2) 2)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' A B := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]

theorem frobMatrixHom_apply (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) (i j : Fin 2) :
    frobMatrixHom A i j = (A i j) ^ 2 := by
  simp [frobMatrixHom, frobenius_def]

theorem frobenius_f4_sq (x : GaloisField 2 2) :
    frobenius (GaloisField 2 2) 2 (frobenius (GaloisField 2 2) 2 x) = x := by
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  rw [frobenius_def, frobenius_def]
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h4 : x ^ 4 = x := by
    have := FiniteField.pow_card (K := GaloisField 2 2) x
    rwa [hcard] at this
  rw [← pow_mul]
  norm_num
  exact h4

theorem hroot_f4 (c : GaloisField 2 2) : (c ^ 2) ^ 2 = c := by
  simpa [frobenius_def] using frobenius_f4_sq c

theorem frobMatrixHom_involutive (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    frobMatrixHom (frobMatrixHom A) = A := by
  ext i j
  simp [frobMatrixHom, frobenius_f4_sq]

def frobGL : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) →*
    Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
  Units.map frobMatrixHom

theorem frobGL_involutive (A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
    frobGL (frobGL A) = A := by
  apply Units.ext
  exact frobMatrixHom_involutive (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))

def twist (S : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
    Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) →*
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
  (MulAut.conj S).toMonoidHom.comp frobGL

theorem twist_involutive (S : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))
    (hS : S * frobGL S = 1)
    (A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
    twist S (twist S A) = A := by
  have hS2 : frobGL S = S⁻¹ := by
    have h := congrArg (fun x => S⁻¹ * x) hS
    simpa [mul_assoc] using h
  change S * frobGL (S * frobGL A * S⁻¹) * S⁻¹ = A
  rw [map_mul, map_mul, map_inv, frobGL_involutive, hS2]
  group

theorem frobGL_coe (A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
    (frobGL A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      frobMatrixHom (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := by
  simp [frobGL]

theorem twist_apply (S A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
    twist S A = S * frobGL A * S⁻¹ := by
  simp [twist, MulAut.conj_apply]

theorem twist_scalar (S : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))
    (u : (GaloisField 2 2)ˣ) :
    twist S (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (u ^ 2) := by
  have hfrob : frobGL (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (u ^ 2) := by
    apply Units.ext
    change frobMatrixHom (Matrix.scalar (Fin 2) (u : GaloisField 2 2)) =
      Matrix.scalar (Fin 2) ((u ^ 2 : (GaloisField 2 2)ˣ) : GaloisField 2 2)
    ext i j
    rw [frobMatrixHom_apply]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_pow_eq_pow_val, pow_two]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  rw [twist_apply]
  rw [hfrob]
  have hcomm : S * Matrix.GeneralLinearGroup.scalar (Fin 2) (u ^ 2) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (u ^ 2) * S := by
    apply Units.ext
    exact (Matrix.scalar_comm ((u ^ 2 : (GaloisField 2 2)ˣ) : GaloisField 2 2)
      (fun _ => Commute.all _ _) (S : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).symm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem matrixOfLinearEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (g : (n → K) ≃ₗ[K] (n → K)) (v : n → K) :
    g v = Matrix.mulVec (matrixOfLinearEquiv g) v := by
  change g v = ((Matrix.GeneralLinearGroup.toLin (matrixOfLinearEquiv g) :
    (n → K) →ₗ[K] (n → K)) v)
  have h : Matrix.GeneralLinearGroup.toLin (matrixOfLinearEquiv g) = linearEquivUnit g := by
    unfold matrixOfLinearEquiv
    exact MulEquiv.apply_symm_apply _ _
  rw [h]
  rfl

theorem eq_one_of_sq_eq_one {K : Type*} [Field K] [CharP K 2] {c : K} (h : c ^ 2 = 1) :
    c = 1 := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c + 1) ^ 2 = 0 := by
    rw [add_sq, h, one_pow, mul_one, htwo, zero_mul, add_zero]
    exact CharTwo.add_self_eq_zero 1
  have hzero : c + 1 = 0 := sq_eq_zero_iff.mp hsq
  calc c = -1 := eq_neg_of_add_eq_zero_left hzero
    _ = 1 := CharTwo.neg_eq 1

theorem involution_eq_one_of_two_lines {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) {d : V ≃ₗ[K] V} (hd2 : d * d = 1)
    {Y L : Submodule K V} (hY : Module.finrank K Y = 1) (hL : Module.finrank K L = 1)
    (hne : Y ≠ L) (hYfix : ∀ y ∈ Y, d y = y) (hLstab : ∀ x ∈ L, d x ∈ L) :
    d = 1 := by
  have hYatom : IsAtom Y := Submodule.isAtom_iff_finrank_eq_one.mpr hY
  have hLatom : IsAtom L := Submodule.isAtom_iff_finrank_eq_one.mpr hL
  have hinf : Y ⊓ L = ⊥ := by
    by_contra h
    have hnebot : Y ⊓ L ≠ ⊥ := h
    have hYL : Y ⊓ L = Y := (hYatom.le_iff_eq hnebot).mp inf_le_left
    have hLL : Y ⊓ L = L := (hLatom.le_iff_eq hnebot).mp inf_le_right
    exact hne (hYL.symm.trans hLL)
  have hsup : Y ⊔ L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq Y L
    rw [hinf, finrank_bot, add_zero, hY, hL] at hfr
    omega
  ext v
  have hv : v ∈ Y ⊔ L := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y, hy, l, hl, rfl⟩ := Submodule.mem_sup.mp hv
  have hdl : d l = l := by
    by_cases hl0 : l = 0
    · rw [hl0, map_zero]
    · have hdlL : d l ∈ L := hLstab l hl
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := K) (V := ↥L) hL
        (x := ⟨l, hl⟩) (by simpa using hl0) ⟨d l, hdlL⟩
      have hc' : c • l = d l := congrArg Subtype.val hc
      have hd2l : d (d l) = l := by
        have := congrArg (fun e : V ≃ₗ[K] V => e l) hd2
        simpa using this
      have hc2 : c ^ 2 = 1 := by
        have hsl : (c ^ 2) • l = l := by
          calc (c ^ 2) • l = c • (c • l) := by rw [pow_two, smul_smul]
            _ = c • d l := by rw [hc']
            _ = d (c • l) := by rw [map_smul]
            _ = d (d l) := by rw [hc']
            _ = l := hd2l
        have hzero : (c ^ 2 - 1) • l = 0 := by
          rw [sub_smul, hsl, one_smul, sub_self]
        rcases smul_eq_zero.mp hzero with hc0 | hlzero
        · exact sub_eq_zero.mp hc0
        · exact absurd hlzero hl0
      rw [eq_one_of_sq_eq_one hc2, one_smul] at hc'
      exact hc'.symm
  calc d (y + l) = d y + d l := map_add d y l
    _ = y + l := by rw [hYfix y hy, hdl]

theorem involution_eq_one_of_mem_stabilizer {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) {H : Subgroup (V ≃ₗ[K] V)} {d : V ≃ₗ[K] V}
    (hdH : d ∈ H) (hd2 : d * d = 1)
    {Y L : Submodule K V} (hY : Module.finrank K Y = 1) (hL : Module.finrank K L = 1)
    (hne : Y ≠ L) (hYfix : ∀ y ∈ Y, d y = y)
    (hLH : ∀ h ∈ H, ∀ x ∈ L, h x ∈ L) : d = 1 :=
  involution_eq_one_of_two_lines hV hd2 hY hL hne hYfix (hLH d hdH)

theorem false_of_involution_two_invariant_lines {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) {H : Subgroup (V ≃ₗ[K] V)} {d : V ≃ₗ[K] V}
    (hdH : d ∈ H) (hd2 : d * d = 1) (hdne : d ≠ 1)
    {Y L M : Submodule K V} (hY : Module.finrank K Y = 1)
    (hL : Module.finrank K L = 1) (hM : Module.finrank K M = 1) (hLM : L ≠ M)
    (hYfix : ∀ y ∈ Y, d y = y)
    (hLstab : ∀ h ∈ H, ∀ x ∈ L, h x ∈ L)
    (hMstab : ∀ h ∈ H, ∀ x ∈ M, h x ∈ M) : False := by
  have hd1 : d = 1 := by
    by_cases hYL : Y = L
    · apply involution_eq_one_of_mem_stabilizer hV hdH hd2 hY hM
      · intro hYM
        exact hLM (hYL.symm.trans hYM)
      · exact hYfix
      · exact hMstab
    · exact involution_eq_one_of_mem_stabilizer hV hdH hd2 hY hL hYL hYfix hLstab
  exact hdne hd1

noncomputable def semilinearImage {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] (σ : V ≃+ V)
    (hσ : ∀ (c : K) (v : V), σ (c • v) = c ^ 2 • σ v)
    (hroot : ∀ c : K, (c ^ 2) ^ 2 = c) (L : Submodule K V) : Submodule K V where
  carrier := {y | ∃ v ∈ L, σ v = y}
  zero_mem' := ⟨0, L.zero_mem, map_zero σ⟩
  add_mem' := by
    rintro y z ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, L.add_mem ha hb, map_add σ a b⟩
  smul_mem' := by
    rintro c y ⟨a, ha, rfl⟩
    refine ⟨(c ^ 2) • a, L.smul_mem (c ^ 2) ha, ?_⟩
    rw [hσ, hroot]

def autAddEquiv {W : Type*} [CommGroup W] (s : MulAut W) : Additive W ≃+ Additive W where
  toFun := autAddHom s
  invFun := autAddHom s⁻¹
  left_inv v := by
    let w : W := Additive.toMul v
    have hv : Additive.ofMul w = v := rfl
    rw [← hv]
    change Additive.ofMul (s⁻¹ (s w)) = Additive.ofMul w
    simp
  right_inv v := by
    let w : W := Additive.toMul v
    have hv : Additive.ofMul w = v := rfl
    rw [← hv]
    change Additive.ofMul (s (s⁻¹ w)) = Additive.ofMul w
    simp
  map_add' := map_add (autAddHom s)

theorem card_semilinearImage {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] (σ : V ≃+ V)
    (hσ : ∀ (c : K) (v : V), σ (c • v) = c ^ 2 • σ v)
    (hroot : ∀ c : K, (c ^ 2) ^ 2 = c) (L : Submodule K V) :
    Nat.card (semilinearImage σ hσ hroot L) = Nat.card L := by
  let e : L ≃ semilinearImage σ hσ hroot L := Equiv.ofBijective
    (f := fun v : L => (⟨σ v, ⟨v, v.2, rfl⟩⟩ : semilinearImage σ hσ hroot L))
    ⟨fun a b hab => Subtype.ext (σ.injective (congrArg Subtype.val hab)),
      fun y : semilinearImage σ hσ hroot L => by
        obtain ⟨v, hv, hvy⟩ := y.2
        exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩
  exact Nat.card_congr e.symm

def submoduleToSubgroup {W : Type*} [CommGroup W]
    [Module (GaloisField 2 2) (Additive W)]
    (Z : Submodule (GaloisField 2 2) (Additive W)) : Subgroup W where
  carrier := {w | Additive.ofMul w ∈ Z}
  one_mem' := Z.zero_mem
  mul_mem' := by
    intro a b ha hb
    change Additive.ofMul (a * b) ∈ Z
    rw [ofMul_mul]
    exact Z.add_mem ha hb
  inv_mem' := by
    intro a ha
    change Additive.ofMul a⁻¹ ∈ Z
    rw [ofMul_inv]
    exact Z.neg_mem ha

theorem mem_submoduleToSubgroup {W : Type*} [CommGroup W]
    [Module (GaloisField 2 2) (Additive W)]
    {Z : Submodule (GaloisField 2 2) (Additive W)} {w : W} :
    w ∈ submoduleToSubgroup Z ↔ Additive.ofMul w ∈ Z := Iff.rfl

theorem hirr_submodule_of_hirr_subgroup {W : Type*} [CommGroup W]
    [Module (GaloisField 2 2) (Additive W)] {G : Subgroup (MulAut W)}
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤) :
    ∀ Z : Submodule (GaloisField 2 2) (Additive W),
      (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
  intro Z hZ
  have hsub : ∀ g ∈ G, ∀ z ∈ submoduleToSubgroup Z, g z ∈ submoduleToSubgroup Z := by
    intro g hg z hz
    rw [mem_submoduleToSubgroup] at hz ⊢
    exact hZ g hg (Additive.ofMul z) hz
  rcases hirr (submoduleToSubgroup Z) hsub with hbot | htop
  · left
    apply bot_unique
    intro z hz
    have hz' : Additive.ofMul (Additive.toMul z) ∈ Z := hz
    have hmem : Additive.toMul z ∈ submoduleToSubgroup Z := hz'
    rw [hbot] at hmem
    rw [Subgroup.mem_bot] at hmem
    simpa using congrArg Additive.ofMul hmem
  · right
    apply top_unique
    intro z hz
    have hmem : Additive.ofMul (Additive.toMul z) ∈ Z := by
      change Additive.toMul z ∈ submoduleToSubgroup Z
      rw [htop]
      exact Subgroup.mem_top _
    simpa using hmem

section LineAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev LineOf := {L : Submodule K V // Module.finrank K L = 1}

@[expose] def lineMap (g : V ≃ₗ[K] V) (L : LineOf (K := K) (V := V)) : LineOf (K := K) (V := V) :=
  ⟨L.1.map (g : V →ₗ[K] V), by
    rw [LinearEquiv.finrank_map_eq]
    exact L.2⟩

theorem lineMap_apply (g : V ≃ₗ[K] V) (L : LineOf (K := K) (V := V)) :
    (lineMap g L).1 = L.1.map (g : V →ₗ[K] V) := rfl

instance lineMulAction : MulAction (V ≃ₗ[K] V) (LineOf (K := K) (V := V)) where
  smul g L := lineMap g L
  one_smul L := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  mul_smul g h L := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨h w, ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩

open Pointwise in
theorem exists_small_invariant_set_of_card_five {G α : Type*} [Group G] [MulAction G α]
    [Fintype α] (hα : Fintype.card α = 5) :
    (∀ a b : α, ∃ g : G, g • a = b) ∨
      ∃ S : Set α, S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ g : G, g • (S : Set α) = S) ∧ S.ncard ≤ 2 := by
  classical
  by_cases htrans : ∀ a b : α, ∃ g : G, g • a = b
  · exact Or.inl htrans
  · right
    push Not at htrans
    obtain ⟨a, b, hab⟩ := htrans
    let O : Set α := MulAction.orbit G a
    have hOa : a ∈ O := MulAction.mem_orbit_self a
    have hOne : O.Nonempty := ⟨a, hOa⟩
    have hOproper : O ≠ Set.univ := by
      intro h
      have hb : b ∈ O := by rw [h]; exact Set.mem_univ b
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hb
      exact hab g hg
    have hOinv : ∀ g : G, g • (O : Set α) = O := fun g => MulAction.smul_orbit g a
    have hOpos : 0 < O.ncard := (Set.ncard_pos (s := O)).mpr hOne
    have hncard : O.ncard + Oᶜ.ncard = 5 := by
      simpa [hα] using Set.ncard_add_ncard_compl O
    by_cases hOle : O.ncard ≤ 2
    · exact ⟨O, hOne, hOproper, hOinv, hOle⟩
    · have hOge : 3 ≤ O.ncard := Nat.succ_le_of_lt (Nat.lt_of_not_ge hOle)
      have hbO : b ∉ O := by
        intro hb
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hb
        exact hab g hg
      have hcnonempty : Oᶜ.Nonempty := ⟨b, hbO⟩
      have hcpos : 0 < Oᶜ.ncard := (Set.ncard_pos (s := Oᶜ)).mpr hcnonempty
      have hn' : Oᶜ.ncard + O.ncard = 5 := by
        rw [Nat.add_comm]; exact hncard
      have hceq : Oᶜ.ncard = 5 - O.ncard := Nat.eq_sub_of_add_eq hn'
      have hcle : Oᶜ.ncard ≤ 2 := by
        calc Oᶜ.ncard = 5 - O.ncard := hceq
          _ ≤ 5 - 3 := Nat.sub_le_sub_left hOge 5
          _ = 2 := by norm_num
      have hcproper : Oᶜ ≠ Set.univ := by
        intro h
        have hOempty : O = ∅ := by
          rw [← compl_compl O, h]
          simp
        exact hOne.ne_empty hOempty
      refine ⟨Oᶜ, hcnonempty, hcproper, ?_, hcle⟩
      intro g
      rw [Set.smul_set_compl, hOinv g]

end LineAction

end Matrix

section Field

variable (hw2 : ∀ w : W, w ^ 2 = 1)
variable (x : MulAut W)
variable (hx3 : x ^ 3 = 1)
variable (hfix : fixV (Subgroup.zpowers x) = ⊥)

include hx3 hfix

theorem aeval_F4poly_autEnd :
    letI := addModTwo hw2
    Polynomial.aeval (R := ZMod 2) (A := Module.End (ZMod 2) (Additive W))
      (autEnd hw2 x) F4poly = 0 := by
  letI := addModTwo hw2
  ext v
  let w : W := Additive.toMul v
  change Polynomial.aeval (R := ZMod 2) (A := Module.End (ZMod 2) (Additive W))
      (autEnd hw2 x) F4poly (Additive.ofMul w) = 0
  have hpoly : Polynomial.aeval (R := ZMod 2) (A := Module.End (ZMod 2) (Additive W))
      (autEnd hw2 x) F4poly = (autEnd hw2 x) ^ 2 + autEnd hw2 x + 1 := by
    simp [F4poly, map_add, map_pow, aeval_X]
  rw [hpoly]
  change ((autEnd hw2 x) ^ 2) (Additive.ofMul w) +
    (autEnd hw2 x) (Additive.ofMul w) + Additive.ofMul w = 0
  rw [pow_two, Module.End.mul_apply, autEnd_ofMul hw2, autEnd_ofMul hw2]
  exact autEnd_sq_add_self_add_one (hw2 := hw2) (x := x) hx3 hfix (Additive.ofMul w)

def f4RingHom :
    letI := addModTwo hw2
    AdjoinRoot F4poly →+* Module.End (ZMod 2) (Additive W) := by
  letI := addModTwo hw2
  exact Ideal.Quotient.lift (Ideal.span {F4poly})
    (Polynomial.aeval (R := ZMod 2) (A := Module.End (ZMod 2) (Additive W))
      (autEnd hw2 x)).toRingHom (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
        change Polynomial.aeval (autEnd hw2 x) (b * F4poly) = 0
        rw [map_mul, aeval_F4poly_autEnd hw2 x hx3 hfix, mul_zero])

def f4AlgEquivGalois : AdjoinRoot F4poly ≃ₐ[ZMod 2] GaloisField 2 2 := by
  letI : Fintype (AdjoinRoot F4poly) := Fintype.ofFinite _
  exact GaloisField.algEquivGaloisFieldOfFintype (p := 2) (n := 2) (by
    rw [← Nat.card_eq_fintype_card, CFSG.GroupTheory.GL52.card_F4]
    norm_num)

def galoisModule : Module (GaloisField 2 2) (Additive W) :=
  Module.compHom (Additive W)
    ((f4RingHom hw2 x hx3 hfix).comp f4AlgEquivGalois.symm.toRingHom)

theorem finrank_galoisModule (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    Module.finrank (GaloisField 2 2) (Additive W) = 2 := by
  letI := galoisModule hw2 x hx3 hfix
  have hcard : Nat.card (Additive W) = 16 := by
    change Nat.card W = 16
    exact hW
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h : Nat.card (Additive W) =
      Nat.card (GaloisField 2 2) ^ Module.finrank (GaloisField 2 2) (Additive W) :=
    Module.natCard_eq_pow_finrank
  rw [hcard, hK] at h
  have hd : 4 ^ Module.finrank (GaloisField 2 2) (Additive W) = 16 := h.symm
  have hle : Module.finrank (GaloisField 2 2) (Additive W) ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h3 : 4 ^ 3 ≤ 4 ^ Module.finrank (GaloisField 2 2) (Additive W) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h3
    omega
  have hge : 1 ≤ Module.finrank (GaloisField 2 2) (Additive W) := by
    by_contra hlt
    push Not at hlt
    have h0 : Module.finrank (GaloisField 2 2) (Additive W) = 0 := by omega
    rw [h0] at hd
    norm_num at hd
  interval_cases Module.finrank (GaloisField 2 2) (Additive W) <;> norm_num at hd
  all_goals rfl

noncomputable def galoisBasis (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    Module.Basis (Fin 2) (GaloisField 2 2) (Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  exact (Module.finBasis (GaloisField 2 2) (Additive W)).reindex
    (finCongr (finrank_galoisModule hw2 x hx3 hfix hW))

noncomputable def galoisEquivFun (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    Additive W ≃ₗ[GaloisField 2 2] (Fin 2 → GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact (galoisBasis hw2 x hx3 hfix hW).equivFun

noncomputable def psiMul (hW : Nat.card W = 16) :
    W ≃* Multiplicative (Fin 2 → GaloisField 2 2) where
  toFun w := Multiplicative.ofAdd (galoisEquivFun hw2 x hx3 hfix hW (Additive.ofMul w))
  invFun v := Additive.toMul (galoisEquivFun hw2 x hx3 hfix hW |>.symm (Multiplicative.toAdd v))
  left_inv w := by
    simp
  right_inv v := by
    simp
  map_mul' a b := by
    simp only [ofMul_mul, map_add, ofAdd_add]

section Commute

omit hx3 hfix

theorem autAddHom_iterate_commute (h g : MulAut W) (hcomm : h * g = g * h)
    (n : ℕ) (v : Additive W) :
    autAddHom h ((autAddHom g)^[n] v) = (autAddHom g)^[n] (autAddHom h v) := by
  have hcomm' : ∀ y : Additive W,
      autAddHom h (autAddHom g y) = autAddHom g (autAddHom h y) := by
    intro y
    let w : W := Additive.toMul y
    change Additive.ofMul (h (g w)) = Additive.ofMul (g (h w))
    have hw : h (g w) = g (h w) := by
      have := congrArg (fun f : MulAut W => f w) hcomm
      simpa [MulAut.mul_apply] using this
    rw [hw]
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      calc autAddHom h ((autAddHom g) ^[n + 1] v)
          = autAddHom h (autAddHom g ((autAddHom g) ^[n] v)) := by
              rw [Function.iterate_succ_apply']
        _ = autAddHom g (autAddHom h ((autAddHom g) ^[n] v)) := hcomm' _
        _ = autAddHom g ((autAddHom g) ^[n] (autAddHom h v)) := by rw [ih]
        _ = (autAddHom g) ^[n + 1] (autAddHom h v) := by
              rw [Function.iterate_succ_apply']

end Commute

section AdjoinRoot

theorem f4RingHom_mk (p : (ZMod 2)[X]) :
    letI := addModTwo hw2
    f4RingHom hw2 x hx3 hfix (AdjoinRoot.mk F4poly p) =
      Polynomial.aeval (R := ZMod 2) (A := Module.End (ZMod 2) (Additive W))
        (autEnd hw2 x) p := by
  letI := addModTwo hw2
  rfl

end AdjoinRoot

section Commuting

omit hx3 hfix

variable (h : MulAut W)

theorem autAddHom_algebraMap_comm (c : ZMod 2) (v : Additive W) :
    letI := addModTwo hw2
    autAddHom h
        ((algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c) v) =
      (algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c) (autAddHom h v) := by
  letI := addModTwo hw2
  simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  have hc : c • v = c.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) c.val, ZMod.natCast_zmod_val]
  rw [hc]
  exact map_nsmul (autAddHom h) c.val v

def commutingSubalgebra :
    letI := addModTwo hw2
    Subalgebra (ZMod 2) (Module.End (ZMod 2) (Additive W)) := by
  letI := addModTwo hw2
  exact
  { carrier := {f | ∀ v : Additive W,
      autAddHom h (f v) = f (autAddHom h v)}
    mul_mem' := by
      intro f g hf hg v
      change autAddHom h ((f * g) v) = (f * g) (autAddHom h v)
      rw [Module.End.mul_apply, Module.End.mul_apply, hf (g v), hg v]
    one_mem' := by
      intro v
      change autAddHom h ((1 : Module.End (ZMod 2) (Additive W)) v) =
        (1 : Module.End (ZMod 2) (Additive W)) (autAddHom h v)
      rw [Module.End.one_apply, Module.End.one_apply]
    add_mem' := by
      intro f g hf hg v
      change autAddHom h ((f + g) v) = (f + g) (autAddHom h v)
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hf v, hg v]
    zero_mem' := by
      intro v
      change autAddHom h ((0 : Module.End (ZMod 2) (Additive W)) v) =
        (0 : Module.End (ZMod 2) (Additive W)) (autAddHom h v)
      rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
    algebraMap_mem' := by
      intro c
      exact autAddHom_algebraMap_comm hw2 h c }

theorem autEnd_mem_commutingSubalgebra (hcomm : h * x = x * h) :
    letI := addModTwo hw2
    autEnd hw2 x ∈ commutingSubalgebra hw2 h := by
  letI := addModTwo hw2
  intro v
  change autAddHom h (autEnd hw2 x v) = autEnd hw2 x (autAddHom h v)
  simpa [autEnd] using autAddHom_iterate_commute h x hcomm 1 v

include hx3 hfix

theorem f4RingHom_algebraMap (c : ZMod 2) :
    letI := addModTwo hw2
    f4RingHom hw2 x hx3 hfix (algebraMap (ZMod 2) (AdjoinRoot F4poly) c) =
      algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c := by
  letI := addModTwo hw2
  rw [AdjoinRoot.algebraMap_eq]
  change f4RingHom hw2 x hx3 hfix (AdjoinRoot.mk F4poly (Polynomial.C c)) = _
  rw [f4RingHom_mk, Polynomial.aeval_C]

def f4AlgHom :
    letI := addModTwo hw2
    AdjoinRoot F4poly →ₐ[ZMod 2] Module.End (ZMod 2) (Additive W) := by
  letI := addModTwo hw2
  exact
  { toRingHom := f4RingHom hw2 x hx3 hfix
    commutes' c := f4RingHom_algebraMap hw2 x hx3 hfix c }

theorem f4AlgHom_root :
    letI := addModTwo hw2
    f4AlgHom hw2 x hx3 hfix (AdjoinRoot.root F4poly) = autEnd hw2 x := by
  letI := addModTwo hw2
  change f4RingHom hw2 x hx3 hfix (AdjoinRoot.mk F4poly Polynomial.X) = autEnd hw2 x
  rw [f4RingHom_mk, Polynomial.aeval_X]

theorem f4AlgHom_range :
    letI := addModTwo hw2
    (f4AlgHom hw2 x hx3 hfix).range =
      Algebra.adjoin (ZMod 2) ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) := by
  letI := addModTwo hw2
  rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top (f := F4poly)]
  rw [AlgHom.map_adjoin]
  simp [f4AlgHom_root]

theorem f4RingHom_mem_commutingSubalgebra (hcomm : h * x = x * h)
    (c : AdjoinRoot F4poly) :
    letI := addModTwo hw2
    f4RingHom hw2 x hx3 hfix c ∈ commutingSubalgebra hw2 h := by
  letI := addModTwo hw2
  have hS : Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) ≤
        commutingSubalgebra hw2 h := by
    rw [Algebra.adjoin_le_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact autEnd_mem_commutingSubalgebra hw2 x h hcomm
  have hgen : f4RingHom hw2 x hx3 hfix c ∈ Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) := by
    rw [← f4AlgHom_range hw2 x hx3 hfix]
    exact ⟨c, rfl⟩
  exact hS hgen

theorem autAddHom_f4RingHom_comm (hcomm : h * x = x * h)
    (c : AdjoinRoot F4poly) (v : Additive W) :
    letI := addModTwo hw2
    autAddHom h ((f4RingHom hw2 x hx3 hfix c) v) =
      (f4RingHom hw2 x hx3 hfix c) (autAddHom h v) := by
  letI := addModTwo hw2
  exact f4RingHom_mem_commutingSubalgebra hw2 x hx3 hfix h hcomm c v

def hGaloisLinearEquiv (hcomm : h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    Additive W ≃ₗ[GaloisField 2 2] Additive W := by
  letI := galoisModule hw2 x hx3 hfix
  exact
  { toFun := autAddHom h
    map_add' := fun a b => (autAddHom h).map_add a b
    map_smul' := by
      intro c v
      change autAddHom h
          ((f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm c)) v) =
        (f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm c)) (autAddHom h v)
      exact autAddHom_f4RingHom_comm hw2 x hx3 hfix h hcomm _ v
    invFun := autAddHom h⁻¹
    left_inv := by
      intro v
      let w : W := Additive.toMul v
      have hv : Additive.ofMul w = v := rfl
      rw [← hv]
      simp [autAddHom]
    right_inv := by
      intro v
      let w : W := Additive.toMul v
      have hv : Additive.ofMul w = v := rfl
      rw [← hv]
      simp [autAddHom] }

theorem hGaloisLinearEquiv_apply (hcomm : h * x = x * h) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix h hcomm v = autAddHom h v := by
  simp [hGaloisLinearEquiv]

noncomputable def hGL (hcomm : h * x = x * h) (hW : Nat.card W = 16) :
    Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact matrixOfLinearEquiv
    ((galoisEquivFun hw2 x hx3 hfix hW).symm.trans
      ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm).trans
        (galoisEquivFun hw2 x hx3 hfix hW)))

end Commuting

theorem hGaloisLinearEquiv_mul (h₁ h₂ : MulAut W)
    (hc₁ : h₁ * x = x * h₁) (hc₂ : h₂ * x = x * h₂)
    (hc : (h₁ * h₂) * x = x * (h₁ * h₂)) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix (h₁ * h₂) hc =
      (hGaloisLinearEquiv hw2 x hx3 hfix h₂ hc₂).trans
        (hGaloisLinearEquiv hw2 x hx3 hfix h₁ hc₁) := by
  letI := galoisModule hw2 x hx3 hfix
  ext v
  rfl

theorem hGL_mul (h₁ h₂ : MulAut W)
    (hc₁ : h₁ * x = x * h₁) (hc₂ : h₂ * x = x * h₂)
    (hc : (h₁ * h₂) * x = x * (h₁ * h₂)) (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    hGL hw2 x hx3 hfix (h₁ * h₂) hc hW =
      hGL hw2 x hx3 hfix h₁ hc₁ hW * hGL hw2 x hx3 hfix h₂ hc₂ hW := by
  letI := galoisModule hw2 x hx3 hfix
  dsimp only [hGL]
  rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix h₁ h₂ hc₁ hc₂ hc]
  rw [← conj_mul (galoisEquivFun hw2 x hx3 hfix hW)
    (hGaloisLinearEquiv hw2 x hx3 hfix h₁ hc₁)
    (hGaloisLinearEquiv hw2 x hx3 hfix h₂ hc₂)]
  exact matrixOfLinearEquiv_mul _ _

end Field

section CentralizerExplicit

theorem hcommOf {W : Type*} [CommGroup W] [Finite W] (x : MulAut W)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (h : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W)))) :
    (h : MulAut W) * x = x * (h : MulAut W) := by
  have hxX : x ∈ X := by
    rw [hxgen]
    exact Subgroup.mem_zpowers x
  have hC : (h : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
    (Subgroup.mem_inf.mp h.2).2
  exact ((Subgroup.mem_centralizer_iff.mp hC) x hxX).symm

noncomputable def hGLOnCentralizer {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16)
    (h : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W)))) :
    Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
  hGL hw2 x hx3 hfix (h : MulAut W) (hcommOf x G X hxgen h) hW

theorem hGaloisLinearEquiv_one {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hc : (1 : MulAut W) * x = x * 1) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix 1 hc = LinearEquiv.refl (GaloisField 2 2) (Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  ext v
  rfl

theorem hGL_one {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hc : (1 : MulAut W) * x = x * 1) (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    hGL hw2 x hx3 hfix 1 hc hW = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  dsimp only [hGL]
  rw [hGaloisLinearEquiv_one, LinearEquiv.refl_trans, LinearEquiv.symm_trans_self,
    matrixOfLinearEquiv_refl]

noncomputable def hGLHom {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16) :
    ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) →*
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) where
  toFun := hGLOnCentralizer hw2 x hx3 hfix G X hxgen hW
  map_one' := by
    change hGL hw2 x hx3 hfix (1 : MulAut W) (hcommOf x G X hxgen 1) hW = 1
    exact hGL_one hw2 x hx3 hfix (hcommOf x G X hxgen 1) hW
  map_mul' := by
    intro h₁ h₂
    change hGL hw2 x hx3 hfix ((h₁ * h₂ : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W)))) : MulAut W)
        (hcommOf x G X hxgen (h₁ * h₂)) hW =
      hGL hw2 x hx3 hfix (h₁ : MulAut W) (hcommOf x G X hxgen h₁) hW *
        hGL hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW
    exact hGL_mul hw2 x hx3 hfix (h₁ : MulAut W) (h₂ : MulAut W)
      (hcommOf x G X hxgen h₁) (hcommOf x G X hxgen h₂)
      (hcommOf x G X hxgen (h₁ * h₂)) hW

theorem hGLHom_injective {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16) :
    Function.Injective (hGLHom hw2 x hx3 hfix G X hxgen hW) := by
  intro h₁ h₂ hEq
  letI := galoisModule hw2 x hx3 hfix
  let e := galoisEquivFun hw2 x hx3 hfix hW
  have hM : matrixOfLinearEquiv
      (e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
        (hcommOf x G X hxgen h₁)).trans e)) =
      matrixOfLinearEquiv
      (e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
        (hcommOf x G X hxgen h₂)).trans e)) := by
    simpa [hGLHom, hGLOnCentralizer, hGL] using hEq
  have hC := matrixOfLinearEquiv_injective hM
  have hcomp : ∀ L : Additive W ≃ₗ[GaloisField 2 2] Additive W,
      e.trans ((e.symm.trans (L.trans e)).trans e.symm) = L := by
    intro L
    ext v
    simp [LinearEquiv.trans_apply]
  have hL : hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W) (hcommOf x G X hxgen h₁) =
      hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) := by
    calc hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W) (hcommOf x G X hxgen h₁)
        = e.trans ((e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
            (hcommOf x G X hxgen h₁)).trans e)).trans e.symm) := (hcomp _).symm
      _ = e.trans ((e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
            (hcommOf x G X hxgen h₂)).trans e)).trans e.symm) := by rw [hC]
      _ = hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) := hcomp _
  apply Subtype.ext
  ext w
  have hv := congrArg (fun (g : Additive W ≃ₗ[GaloisField 2 2] Additive W) =>
    g (Additive.ofMul w)) hL
  simpa [hGaloisLinearEquiv, autAddHom] using hv

theorem apply_eq_self_of_le_fixV {W : Type*} [CommGroup W]
    {D : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : Y ≤ fixV D) {d : MulAut W} (hd : d ∈ D) {y : W} (hy : y ∈ Y) :
    d y = y :=
  (mem_fixV.mp (hY hy)) d hd

theorem autEnd_maps_y {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {x : MulAut W} {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) {y : W} (hy : y ∈ Y) :
    Additive.toMul (autEnd hw2 x (Additive.ofMul y)) ∈ Y := by
  rw [autEnd_ofMul]
  exact hYinv x hxX y hy

theorem algebraMap_maps_y {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (c : ZMod 2) {Y : Subgroup W} {y : W} (hy : y ∈ Y) :
    letI := addModTwo hw2
    Additive.toMul ((algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c)
      (Additive.ofMul y)) ∈ Y := by
  letI := addModTwo hw2
  simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, toMul_nsmul]
  exact Subgroup.pow_mem Y hy c.val

def mapsYSubalgebra {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (Y : Subgroup W) :
    letI := addModTwo hw2
    Subalgebra (ZMod 2) (Module.End (ZMod 2) (Additive W)) := by
  letI := addModTwo hw2
  exact
  { carrier := {f | ∀ y ∈ Y, Additive.toMul (f (Additive.ofMul y)) ∈ Y}
    zero_mem' := by
      intro y hy
      change Additive.toMul (0 : Additive W) ∈ Y
      simp
    one_mem' := by
      intro y hy
      change y ∈ Y
      exact hy
    add_mem' := by
      intro f g hf hg y hy
      rw [LinearMap.add_apply, toMul_add]
      exact Y.mul_mem (hf y hy) (hg y hy)
    mul_mem' := by
      intro f g hf hg y hy
      change Additive.toMul (f (g (Additive.ofMul y))) ∈ Y
      let y' : W := Additive.toMul (g (Additive.ofMul y))
      have hy' : y' ∈ Y := hg y hy
      change Additive.toMul (f (Additive.ofMul y')) ∈ Y
      exact hf y' hy'
    algebraMap_mem' := by
      intro c y hy
      exact algebraMap_maps_y hw2 c hy }

theorem autEnd_mem_mapsY {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {x : MulAut W} {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) :
    letI := addModTwo hw2
    autEnd hw2 x ∈ mapsYSubalgebra hw2 Y := by
  letI := addModTwo hw2
  intro y hy
  exact autEnd_maps_y hw2 hxX hYinv hy

theorem f4RingHom_maps_y {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (c : AdjoinRoot F4poly) {y : W} (hy : y ∈ Y) :
    letI := addModTwo hw2
    Additive.toMul ((f4RingHom hw2 x hx3 hfix c) (Additive.ofMul y)) ∈ Y := by
  letI := addModTwo hw2
  have hS : Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) ≤
        mapsYSubalgebra hw2 Y := by
    rw [Algebra.adjoin_le_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact autEnd_mem_mapsY hw2 hxX hYinv
  have hmem : f4AlgHom hw2 x hx3 hfix c ∈ Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) := by
    rw [← f4AlgHom_range hw2 x hx3 hfix]
    exact ⟨c, rfl⟩
  exact hS hmem y hy

theorem card_of_rkIdx_two {W : Type*} [CommGroup W] [Finite W]
    {Y : Subgroup W} (hY : rkIdx Y = 2) (hW : Nat.card W = 16) :
    Nat.card Y = 4 := by
  have hcard : Nat.card Y * Y.index = 16 := by
    rw [← hW]
    exact Y.card_mul_index
  have hdvd : Y.index ∣ 16 := ⟨Nat.card Y, by rw [mul_comm]; exact hcard.symm⟩
  have hdvd' : Y.index ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact hdvd
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  change padicValNat 2 Y.index = 2 at hY
  rw [hk] at hY
  rw [padicValNat.pow, padicValNat_self] at hY
  norm_num at hY
  rw [hY] at hk
  rw [hk] at hcard
  norm_num at hcard
  omega

def YSubmodule {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) :
    letI := galoisModule hw2 x hx3 hfix
    Submodule (GaloisField 2 2) (Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  refine
  { carrier := {v : Additive W | Additive.toMul v ∈ Y}
    zero_mem' := by
      change (1 : W) ∈ Y
      exact Y.one_mem
    add_mem' := by
      intro a b ha hb
      change Additive.toMul (a + b) ∈ Y
      rw [toMul_add]
      exact Y.mul_mem ha hb
    smul_mem' := by
      intro c v hv
      change Additive.toMul (c • v) ∈ Y
      change Additive.toMul ((f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm c)) v) ∈ Y
      exact f4RingHom_maps_y hw2 x hx3 hfix hxX hYinv _ hv }

def YSubmoduleEquiv {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) :
    letI := galoisModule hw2 x hx3 hfix
    Y ≃ YSubmodule hw2 x hx3 hfix hxX hYinv where
  toFun y := ⟨Additive.ofMul y, y.2⟩
  invFun v := ⟨Additive.toMul v, v.2⟩
  left_inv y := by
    ext
    rfl
  right_inv v := by
    ext
    rfl

theorem card_YSubmodule {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4) :
    letI := galoisModule hw2 x hx3 hfix
    Nat.card (YSubmodule hw2 x hx3 hfix hxX hYinv) = 4 := by
  letI := galoisModule hw2 x hx3 hfix
  rw [← hYcard]
  exact Nat.card_congr (YSubmoduleEquiv hw2 x hx3 hfix hxX hYinv).symm

theorem hGaloisLinearEquiv_ne_one {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {d : MulAut W}
    (hc : d * x = x * d) (hd : d ≠ 1) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix d hc ≠ 1 := by
  letI := galoisModule hw2 x hx3 hfix
  intro h
  apply hd
  ext w
  have hv := congrArg (fun (g : Additive W ≃ₗ[GaloisField 2 2] Additive W) =>
    Additive.toMul (g (Additive.ofMul w))) h
  simpa [hGaloisLinearEquiv, autAddHom] using hv

theorem YSubmodule_le_fixedSubmodule {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {X : Subgroup (MulAut W)}
    (hxX : x ∈ X) {Y : Subgroup W}
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y)
    {D : Subgroup (MulAut W)} {d : MulAut W} (hdD : d ∈ D)
    (hYfix : Y ≤ fixV D) (hc : d * x = x * d) :
    letI := galoisModule hw2 x hx3 hfix
    YSubmodule hw2 x hx3 hfix hxX hYinv ≤
      fixedSubmodule (hGaloisLinearEquiv hw2 x hx3 hfix d hc).toLinearMap := by
  letI := galoisModule hw2 x hx3 hfix
  intro v hv
  rw [mem_fixedSubmodule]
  change Additive.toMul v ∈ Y at hv
  have hfixd : d (Additive.toMul v) = Additive.toMul v :=
    apply_eq_self_of_le_fixV hYfix hdD hv
  change Additive.ofMul (d (Additive.toMul v)) = v
  rw [hfixd]
  rfl

theorem apply_x_eq_sq_apply {W : Type*} [CommGroup W] {x s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (v : W) :
    s (x v) = x (x (s v)) := by
  have h : s * x = x ^ 2 * s := by
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x ^ 2 * s := by rw [hsx]
  have hv := congrArg (fun f : MulAut W => f v) h
  simpa [pow_two, MulAut.mul_apply] using hv

theorem toMul_algebraMap_apply {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (c : ZMod 2) (w : W) :
    letI := addModTwo hw2
    Additive.toMul ((algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c)
      (Additive.ofMul w)) = w ^ c.val := by
  letI := addModTwo hw2
  simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, toMul_nsmul,
    ZMod.val_natCast_of_lt (ZMod.val_lt c)]
  rfl

def Semilinear {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (s : MulAut W)
    (f : @Module.End (ZMod 2) (Additive W) _ _ (addModTwo hw2)) : Prop :=
  ∀ w : W, s (Additive.toMul (f (Additive.ofMul w))) =
    Additive.toMul ((f ^ 2) (Additive.ofMul (s w)))

theorem adjoin_singleton_commute {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {a f g : A} (hf : f ∈ Algebra.adjoin R ({a} : Set A))
    (hg : g ∈ Algebra.adjoin R ({a} : Set A)) : f * g = g * f := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hf hg
  obtain ⟨p, rfl⟩ := hf
  obtain ⟨q, rfl⟩ := hg
  rw [← map_mul, ← map_mul, mul_comm]

theorem Semilinear_add {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {s : MulAut W}
    {f g : @Module.End (ZMod 2) (Additive W) _ _ (addModTwo hw2)}
    (hf : Semilinear hw2 s f) (hg : Semilinear hw2 s g) (hfg : f * g = g * f) :
    Semilinear hw2 s (f + g) := by
  letI := addModTwo hw2
  intro w
  have hsq : (f + g) ^ 2 = f ^ 2 + g ^ 2 := by
    calc (f + g) ^ 2 = f * f + f * g + g * f + g * g := by noncomm_ring
      _ = f * f + f * g + f * g + g * g := by rw [hfg]
      _ = f * f + (f * g + f * g) + g * g := by abel
      _ = f * f + g * g := by rw [ZModModule.add_self, add_zero]
      _ = f ^ 2 + g ^ 2 := by rw [pow_two, pow_two]
  rw [hsq, LinearMap.add_apply, toMul_add, map_mul, hf w, hg w, LinearMap.add_apply, toMul_add]

theorem Semilinear_mul {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {s : MulAut W}
    {f g : @Module.End (ZMod 2) (Additive W) _ _ (addModTwo hw2)}
    (hf : Semilinear hw2 s f) (hg : Semilinear hw2 s g) (hfg : f * g = g * f) :
    Semilinear hw2 s (f * g) := by
  letI := addModTwo hw2
  intro w
  have hsq : (f * g) ^ 2 = f ^ 2 * g ^ 2 := by
    calc (f * g) ^ 2 = f * (g * f) * g := by noncomm_ring
      _ = f * (f * g) * g := by rw [hfg]
      _ = f ^ 2 * g ^ 2 := by rw [pow_two, pow_two]; noncomm_ring
  rw [hsq, Module.End.mul_apply, Module.End.mul_apply]
  let y : W := Additive.toMul (g (Additive.ofMul w))
  change s (Additive.toMul (f (Additive.ofMul y))) =
    Additive.toMul ((f ^ 2) ((g ^ 2) (Additive.ofMul (s w))))
  rw [hf y]
  have hy : s y = Additive.toMul ((g ^ 2) (Additive.ofMul (s w))) := hg w
  rw [hy]
  rfl

def semilinearSubalgebra {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x s : MulAut W) :
    letI := addModTwo hw2
    Subalgebra (ZMod 2) (Module.End (ZMod 2) (Additive W)) := by
  letI := addModTwo hw2
  exact
  { carrier := {f | f ∈ Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) ∧ Semilinear hw2 s f}
    zero_mem' := by
      refine ⟨Subalgebra.zero_mem _, ?_⟩
      intro w
      change s (1 : W) = 1
      simp
    one_mem' := by
      refine ⟨Subalgebra.one_mem _, ?_⟩
      intro w
      rfl
    add_mem' := by
      intro f g hf hg
      exact ⟨Subalgebra.add_mem _ hf.1 hg.1,
        Semilinear_add hw2 hf.2 hg.2 (adjoin_singleton_commute hf.1 hg.1)⟩
    mul_mem' := by
      intro f g hf hg
      exact ⟨Subalgebra.mul_mem _ hf.1 hg.1,
        Semilinear_mul hw2 hf.2 hg.2 (adjoin_singleton_commute hf.1 hg.1)⟩
    algebraMap_mem' := by
      intro c
      refine ⟨Subalgebra.algebraMap_mem _ c, ?_⟩
      intro w
      rw [toMul_algebraMap_apply hw2 c w]
      have hc : c * c = c := by fin_cases c <;> rfl
      rw [show (algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c) ^ 2 =
          algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive W)) c by
        rw [pow_two, ← map_mul, hc]]
      rw [toMul_algebraMap_apply hw2 c (s w)]
      exact map_pow s w c.val }

theorem autEnd_mem_semilinearSubalgebra {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {x s : MulAut W} (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := addModTwo hw2
    autEnd hw2 x ∈ semilinearSubalgebra hw2 x s := by
  letI := addModTwo hw2
  refine ⟨Algebra.subset_adjoin (Set.mem_singleton _), ?_⟩
  intro w
  change s (Additive.toMul (autEnd hw2 x (Additive.ofMul w))) =
    Additive.toMul ((autEnd hw2 x ^ 2) (Additive.ofMul (s w)))
  rw [autEnd_ofMul, pow_two, Module.End.mul_apply, autEnd_ofMul, autEnd_ofMul]
  simpa using apply_x_eq_sq_apply hsx w

theorem apply_f4RingHom_eq_sq {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (c : AdjoinRoot F4poly) :
    Semilinear hw2 s (f4RingHom hw2 x hx3 hfix c) := by
  letI := addModTwo hw2
  have hS : Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) ≤
        semilinearSubalgebra hw2 x s := by
    rw [Algebra.adjoin_le_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact autEnd_mem_semilinearSubalgebra hw2 hsx
  have hmem : f4AlgHom hw2 x hx3 hfix c ∈ Algebra.adjoin (ZMod 2)
      ({autEnd hw2 x} : Set (Module.End (ZMod 2) (Additive W))) := by
    rw [← f4AlgHom_range hw2 x hx3 hfix]
    exact ⟨c, rfl⟩
  exact (hS hmem).2

theorem apply_galois_smul_eq_sq {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (c : GaloisField 2 2) (w : W) :
    letI := galoisModule hw2 x hx3 hfix
    s (Additive.toMul (c • Additive.ofMul w)) =
      Additive.toMul ((c ^ 2) • Additive.ofMul (s w)) := by
  letI := galoisModule hw2 x hx3 hfix
  change s (Additive.toMul ((f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm c))
      (Additive.ofMul w))) =
    Additive.toMul ((f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm (c ^ 2)))
      (Additive.ofMul (s w)))
  rw [show f4AlgEquivGalois.symm (c ^ 2) = (f4AlgEquivGalois.symm c) ^ 2 by rw [map_pow]]
  rw [map_pow]
  exact apply_f4RingHom_eq_sq hw2 x hx3 hfix hsx (f4AlgEquivGalois.symm c) w

noncomputable def sMatrix {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) (s : MulAut W) :
    letI := galoisModule hw2 x hx3 hfix
    Matrix (Fin 2) (Fin 2) (GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact fun i j =>
    (galoisBasis hw2 x hx3 hfix hW).repr
      (Additive.ofMul (s (Additive.toMul ((galoisBasis hw2 x hx3 hfix hW) j)))) i

theorem sMatrix_expansion {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) (s : MulAut W)
    (j : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    Additive.ofMul (s (Additive.toMul ((galoisBasis hw2 x hx3 hfix hW) j))) =
      ∑ i, (sMatrix hw2 x hx3 hfix hW s) i j •
        (galoisBasis hw2 x hx3 hfix hW) i := by
  letI := galoisModule hw2 x hx3 hfix
  exact (Module.Basis.sum_repr (galoisBasis hw2 x hx3 hfix hW)
    (Additive.ofMul (s (Additive.toMul ((galoisBasis hw2 x hx3 hfix hW) j))))).symm

theorem autAddHom_sum_smul_sq {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (c : Fin 2 → GaloisField 2 2) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom s (∑ k, c k • (galoisBasis hw2 x hx3 hfix hW) k) =
      ∑ k, (c k) ^ 2 • autAddHom s ((galoisBasis hw2 x hx3 hfix hW) k) := by
  letI := galoisModule hw2 x hx3 hfix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change Additive.ofMul (s (Additive.toMul (c k • (galoisBasis hw2 x hx3 hfix hW) k))) =
    Additive.ofMul (c k ^ 2 • Additive.ofMul (s (Additive.toMul ((galoisBasis hw2 x hx3 hfix hW) k))))
  exact congrArg Additive.ofMul
    (apply_galois_smul_eq_sq hw2 x hx3 hfix hsx (c k)
      (Additive.toMul ((galoisBasis hw2 x hx3 hfix hW) k)))

theorem autAddHom_autAddHom_eq {W : Type*} [CommGroup W] {s : MulAut W}
    (hs2 : s * s = 1) (v : Additive W) :
    autAddHom s (autAddHom s v) = v := by
  let w : W := Additive.toMul v
  have hv : Additive.ofMul w = v := rfl
  rw [← hv]
  change Additive.ofMul (s (s w)) = Additive.ofMul w
  rw [show s (s w) = w by
    simpa using congrArg (fun f : MulAut W => f w) hs2]

theorem equivFun_autAddHom_autAddHom_basis {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (j i : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    (galoisBasis hw2 x hx3 hfix hW).equivFun
        (autAddHom s (autAddHom s ((galoisBasis hw2 x hx3 hfix hW) j))) i =
      ∑ k, (sMatrix hw2 x hx3 hfix hW s) i k *
        ((sMatrix hw2 x hx3 hfix hW s) k j) ^ 2 := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let S := sMatrix hw2 x hx3 hfix hW s
  change b.equivFun (Additive.ofMul (s (Additive.toMul
    (Additive.ofMul (s (Additive.toMul (b j))))))) i = _
  rw [sMatrix_expansion hw2 x hx3 hfix hW s j]
  change b.equivFun (autAddHom s (∑ k, S k j • b k)) i = _
  rw [autAddHom_sum_smul_sq hw2 x hx3 hfix hW hsx (fun k => S k j)]
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show b.equivFun (autAddHom s (b k)) i = S i k by
    rw [Module.Basis.equivFun_apply]
    rfl]
  rw [mul_comm]

theorem sMatrix_mul_frob {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    sMatrix hw2 x hx3 hfix hW s * frobMatrixHom (sMatrix hw2 x hx3 hfix hW s) = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let S := sMatrix hw2 x hx3 hfix hW s
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 : (∑ k, S i k * (S k j) ^ 2) = if i = j then 1 else 0 := by
    rw [← equivFun_autAddHom_autAddHom_basis hw2 x hx3 hfix hW hsx j i]
    rw [autAddHom_autAddHom_eq hs2]
    rw [Module.Basis.equivFun_self]
    by_cases h : i = j <;> simp [h, eq_comm]
  simpa [S, frobMatrixHom, frobenius_def] using h1

noncomputable def sUnit {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact Units.mkOfMulEqOne (sMatrix hw2 x hx3 hfix hW s)
    (frobMatrixHom (sMatrix hw2 x hx3 hfix hW s))
    (sMatrix_mul_frob hw2 x hx3 hfix hW hs2 hsx)

theorem sUnit_val {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    (sUnit hw2 x hx3 hfix hW hs2 hsx :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      sMatrix hw2 x hx3 hfix hW s := by
  letI := galoisModule hw2 x hx3 hfix
  exact Units.val_mkOfMulEqOne _

theorem sUnit_mul_frob {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    sUnit hw2 x hx3 hfix hW hs2 hsx * frobGL (sUnit hw2 x hx3 hfix hW hs2 hsx) = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  apply Units.ext
  change (sUnit hw2 x hx3 hfix hW hs2 hsx :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
      (frobGL (sUnit hw2 x hx3 hfix hW hs2 hsx) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = 1
  rw [sUnit_val, frobGL_coe, sUnit_val]
  exact sMatrix_mul_frob hw2 x hx3 hfix hW hs2 hsx

theorem hGL_equivFun_basis {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {h : MulAut W}
    (hcomm : h * x = x * h) (j : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    (galoisEquivFun hw2 x hx3 hfix hW)
        (autAddHom h ((galoisBasis hw2 x hx3 hfix hW) j)) =
      fun i => (hGL hw2 x hx3 hfix h hcomm hW) i j := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let e := galoisEquivFun hw2 x hx3 hfix hW
  let C := e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm).trans e)
  have hC : (hGL hw2 x hx3 hfix h hcomm hW) = matrixOfLinearEquiv C := rfl
  have h1 : e (autAddHom h (b j)) = C (e (b j)) := by
    change e (autAddHom h (b j)) =
      e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) (e.symm (e (b j))))
    rw [e.symm_apply_apply]
    rfl
  rw [h1]
  have h2 : e (b j) = Pi.single j 1 := by
    change b.equivFun (b j) = Pi.single j 1
    ext i
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  rw [h2, hC, matrixOfLinearEquiv_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem hGL_expansion {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {h : MulAut W}
    (hcomm : h * x = x * h) (j : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom h ((galoisBasis hw2 x hx3 hfix hW) j) =
      ∑ i, (hGL hw2 x hx3 hfix h hcomm hW) i j •
        (galoisBasis hw2 x hx3 hfix hW) i := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  have hcoord := hGL_equivFun_basis hw2 x hx3 hfix hW hcomm j
  calc autAddHom h (b j) = b.equivFun.symm (b.equivFun (autAddHom h (b j))) := by simp
    _ = b.equivFun.symm (fun i => (hGL hw2 x hx3 hfix h hcomm hW) i j) := by
      rw [show b.equivFun = galoisEquivFun hw2 x hx3 hfix hW from rfl]
      rw [hcoord]
    _ = ∑ i, (hGL hw2 x hx3 hfix h hcomm hW) i j • b i :=
      Module.Basis.equivFun_symm_apply b _

theorem conj_commutes_x {W : Type*} [Group W] {x s h : MulAut W}
    (hs2 : s * s = 1) (hx3 : x ^ 3 = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    (hh : h * x = x * h) :
    (s * h * s⁻¹) * x = x * (s * h * s⁻¹) := by
  have hs_inv : s⁻¹ = s := by
    calc s⁻¹ = s⁻¹ * (s * s) := by rw [hs2, mul_one]
      _ = (s⁻¹ * s) * s := by group
      _ = s := by rw [inv_mul_cancel, one_mul]
  have hsx' : s * x * s = x ^ 2 := by simpa [hs_inv] using hsx
  have hsx_mul : s * x = x ^ 2 * s := by
    calc s * x = s * x * (s * s) := by rw [hs2, mul_one]
      _ = (s * x * s) * s := by group
      _ = x ^ 2 * s := by rw [hsx']
  have hsx2_mul : s * x ^ 2 = x * s := by
    calc s * x ^ 2 = s * (x * x) := by rw [pow_two]
      _ = (s * x) * x := by group
      _ = (x ^ 2 * s) * x := by rw [hsx_mul]
      _ = x ^ 2 * (s * x) := by group
      _ = x ^ 2 * (x ^ 2 * s) := by rw [hsx_mul]
      _ = x ^ 4 * s := by group
      _ = x * s := by rw [show x ^ 4 = x by rw [pow_succ, hx3, one_mul]]
  have hsinvx : s⁻¹ * x = x ^ 2 * s⁻¹ := by simpa [hs_inv] using hsx_mul
  have hh2 : h * x ^ 2 = x ^ 2 * h := by
    rw [pow_two]
    calc h * (x * x) = (h * x) * x := by group
      _ = (x * h) * x := by rw [hh]
      _ = x * (h * x) := by group
      _ = x * (x * h) := by rw [hh]
      _ = x * x * h := by group
  calc (s * h * s⁻¹) * x = s * h * (s⁻¹ * x) := by group
    _ = s * h * (x ^ 2 * s⁻¹) := by rw [hsinvx]
    _ = (s * (h * x ^ 2)) * s⁻¹ := by group
    _ = (s * (x ^ 2 * h)) * s⁻¹ := by rw [hh2]
    _ = (s * x ^ 2) * h * s⁻¹ := by group
    _ = (x * s) * h * s⁻¹ := by rw [hsx2_mul]
    _ = x * (s * h * s⁻¹) := by group

theorem equivFun_h'_s_basis {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s h' : MulAut W}
    (hcomm' : h' * x = x * h') (j i : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    (galoisBasis hw2 x hx3 hfix hW).equivFun
        (autAddHom h' (autAddHom s ((galoisBasis hw2 x hx3 hfix hW) j))) i =
      ∑ k, (hGL hw2 x hx3 hfix h' hcomm' hW) i k *
        (sMatrix hw2 x hx3 hfix hW s) k j := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let S := sMatrix hw2 x hx3 hfix hW s
  let A' := hGL hw2 x hx3 hfix h' hcomm' hW
  change b.equivFun (autAddHom h' (Additive.ofMul (s (Additive.toMul (b j))))) i = _
  rw [sMatrix_expansion hw2 x hx3 hfix hW s j]
  change b.equivFun (autAddHom h' (∑ k, S k j • b k)) i = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change b.equivFun ((hGaloisLinearEquiv hw2 x hx3 hfix h' hcomm')
    (S k j • b k)) i = _
  rw [map_smul, map_smul]
  change S k j * b.equivFun (autAddHom h' (b k)) i = _
  rw [hGL_expansion hw2 x hx3 hfix hW hcomm' k]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Module.Basis.equivFun_self]
    simp [A', S]
    rw [mul_comm]
  · intro l hl hne
    rw [Module.Basis.equivFun_self]
    simp [hne]
  · intro hi
    simp at hi

theorem equivFun_s_h_basis {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s h : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (hcomm : h * x = x * h) (j i : Fin 2) :
    letI := galoisModule hw2 x hx3 hfix
    (galoisBasis hw2 x hx3 hfix hW).equivFun
        (autAddHom s (autAddHom h ((galoisBasis hw2 x hx3 hfix hW) j))) i =
      ∑ k, (sMatrix hw2 x hx3 hfix hW s) i k *
        ((hGL hw2 x hx3 hfix h hcomm hW) k j) ^ 2 := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let S := sMatrix hw2 x hx3 hfix hW s
  let A := hGL hw2 x hx3 hfix h hcomm hW
  change b.equivFun (autAddHom s (autAddHom h (b j))) i = _
  rw [hGL_expansion hw2 x hx3 hfix hW hcomm j]
  change b.equivFun (autAddHom s (∑ k, A k j • b k)) i = _
  rw [autAddHom_sum_smul_sq hw2 x hx3 hfix hW hsx (fun k => A k j)]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show b.equivFun (autAddHom s (b k)) i = S i k by
    rw [Module.Basis.equivFun_apply]
    rfl]
  rw [mul_comm]

theorem hGL_conj_mul_sUnit {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s h : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) (hcomm : h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    (hGL hw2 x hx3 hfix (s * h * s⁻¹)
        (conj_commutes_x hs2 hx3 hsx hcomm) hW :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
      (sUnit hw2 x hx3 hfix hW hs2 hsx :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      (sUnit hw2 x hx3 hfix hW hs2 hsx :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
      (frobGL (hGL hw2 x hx3 hfix h hcomm hW) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := by
  letI := galoisModule hw2 x hx3 hfix
  let b := galoisBasis hw2 x hx3 hfix hW
  let A' := hGL hw2 x hx3 hfix (s * h * s⁻¹)
    (conj_commutes_x hs2 hx3 hsx hcomm) hW
  let A := hGL hw2 x hx3 hfix h hcomm hW
  let S := sMatrix hw2 x hx3 hfix hW s
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hact : autAddHom (s * h * s⁻¹) (autAddHom s (b j)) =
      autAddHom s (autAddHom h (b j)) := by
    change Additive.ofMul ((s * h * s⁻¹) (s (Additive.toMul (b j)))) =
      Additive.ofMul (s (h (Additive.toMul (b j))))
    simp [MulAut.mul_apply]
  have hcoord := congrArg (fun v : Additive W => b.equivFun v i) hact
  rw [equivFun_h'_s_basis hw2 x hx3 hfix hW
      (conj_commutes_x hs2 hx3 hsx hcomm) j i,
    equivFun_s_h_basis hw2 x hx3 hfix hW hsx hcomm j i] at hcoord
  simpa [A', A, S, sUnit_val, frobGL, frobMatrixHom, frobenius_def] using hcoord

theorem hGL_conj {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s h : MulAut W}
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) (hcomm : h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    hGL hw2 x hx3 hfix (s * h * s⁻¹) (conj_commutes_x hs2 hx3 hsx hcomm) hW =
      twist (sUnit hw2 x hx3 hfix hW hs2 hsx)
        (hGL hw2 x hx3 hfix h hcomm hW) := by
  letI := galoisModule hw2 x hx3 hfix
  let A' := hGL hw2 x hx3 hfix (s * h * s⁻¹)
    (conj_commutes_x hs2 hx3 hsx hcomm) hW
  let A := hGL hw2 x hx3 hfix h hcomm hW
  let S := sUnit hw2 x hx3 hfix hW hs2 hsx
  have hmul : A' * S = S * frobGL A := by
    apply Units.ext
    exact hGL_conj_mul_sUnit hw2 x hx3 hfix hW hs2 hsx hcomm
  calc A' = (A' * S) * S⁻¹ := by group
    _ = (S * frobGL A) * S⁻¹ := by rw [hmul]
    _ = twist S A := by
      rfl

theorem hGL_congr {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {h₁ h₂ : MulAut W}
    (hc₁ : h₁ * x = x * h₁) (hc₂ : h₂ * x = x * h₂) (heq : h₁ = h₂) :
    letI := galoisModule hw2 x hx3 hfix
    hGL hw2 x hx3 hfix h₁ hc₁ hW = hGL hw2 x hx3 hfix h₂ hc₂ hW := by
  cases heq
  rfl

theorem le_inf_centralizer_self {G : Type*} [Group G] {X G₀ : Subgroup G}
    (hXG : X ≤ G₀) (hXcard : Nat.card X = 3) :
    X ≤ G₀ ⊓ Subgroup.centralizer (X : Set G) := by
  apply le_inf hXG
  rw [Subgroup.le_centralizer_iff_isMulCommutative]
  haveI : Fact (Nat.Prime (Nat.card X)) := ⟨by rw [hXcard]; norm_num⟩
  haveI : IsCyclic X := isCyclic_of_prime_card (p := 3) (by rw [hXcard])
  infer_instance

theorem fixV_eq_bot_or_top_of_central {W : Type*} [CommGroup W]
    {G : Subgroup (MulAut W)} {d : MulAut W}
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hd : ∀ g ∈ G, g * d = d * g) :
    fixV (Subgroup.zpowers d) = ⊥ ∨ fixV (Subgroup.zpowers d) = ⊤ := by
  apply hirr
  intro g hg z hz
  have hconj : MulAut.conj g d = d := by
    ext w
    simp [MulAut.conj_apply, hd g hg]
  have hmap : (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    simpa using congrArg Subgroup.zpowers hconj
  rw [← hmap, CFSG.Quasithin.H13.Ch4.E443.fixV_map_conj]
  exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩

theorem autAddHom_smul_eq_sq {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) (c : GaloisField 2 2) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    autAddHom s (c • v) = (c ^ 2) • autAddHom s v := by
  letI := galoisModule hw2 x hx3 hfix
  let w : W := Additive.toMul v
  have hv : Additive.ofMul w = v := rfl
  rw [← hv]
  change Additive.ofMul (s (Additive.toMul (c • Additive.ofMul w))) =
    (c ^ 2) • Additive.ofMul (s w)
  rw [show (c ^ 2) • (Additive.ofMul (s w) : Additive W) =
      Additive.ofMul (c ^ 2 • Additive.ofMul (s w)) from rfl]
  exact congrArg Additive.ofMul
    (apply_galois_smul_eq_sq hw2 x hx3 hfix hsx c w)

noncomputable def sImage {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    Submodule (GaloisField 2 2) (Additive W) → Submodule (GaloisField 2 2) (Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  intro L
  exact semilinearImage (autAddEquiv s)
    (fun c v => by
      change autAddHom s (c • v) = c ^ 2 • autAddHom s v
      exact autAddHom_smul_eq_sq hw2 x hx3 hfix hsx c v)
    hroot_f4 L

theorem card_sImage {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ L : Submodule (GaloisField 2 2) (Additive W),
      Nat.card (sImage hw2 x hx3 hfix hsx L) = Nat.card L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L
  change Nat.card (semilinearImage (autAddEquiv s)
    (fun c v => by
      change autAddHom s (c • v) = c ^ 2 • autAddHom s v
      exact autAddHom_smul_eq_sq hw2 x hx3 hfix hsx c v)
    hroot_f4 L) = Nat.card L
  exact card_semilinearImage (autAddEquiv s) _ hroot_f4 L

theorem finrank_eq_one_of_card_four {W : Type*} [CommGroup W] [Finite W]
    [Module (GaloisField 2 2) (Additive W)]
    [FiniteDimensional (GaloisField 2 2) (Additive W)]
    {L : Submodule (GaloisField 2 2) (Additive W)} (hL : Nat.card L = 4) :
    Module.finrank (GaloisField 2 2) L = 1 := by
  have hpow := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := L)
  rw [hL] at hpow
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [hk] at hpow
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) hpow.symm

theorem finrank_sImage {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ L : Submodule (GaloisField 2 2) (Additive W),
      Module.finrank (GaloisField 2 2) L = 1 →
      Module.finrank (GaloisField 2 2) (sImage hw2 x hx3 hfix hsx L) = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  haveI : FiniteDimensional (GaloisField 2 2) (Additive W) :=
    (galoisBasis hw2 x hx3 hfix hW).finiteDimensional_of_finite
  intro L hL
  apply finrank_eq_one_of_card_four
  rw [card_sImage hw2 x hx3 hfix hsx L]
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := L), hL, hk]
  norm_num

theorem mulAut_conj_commute {W : Type*} [Group W] {s h h' : MulAut W}
    (hs2 : s * s = 1) (hconj : s * h * s⁻¹ = h') : h * s = s * h' := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have h'eq : h' = s * h * s := by
    rw [← hconj, hs_inv]
  rw [h'eq]
  calc h * s = (s * s) * h * s := by rw [hs2, one_mul]
    _ = s * (s * h * s) := by group

theorem mem_sImage {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {s : MulAut W}
    (hsx : s * x * s⁻¹ = x ^ 2) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (L : Submodule (GaloisField 2 2) (Additive W)) (y : Additive W),
      y ∈ sImage hw2 x hx3 hfix hsx L ↔ ∃ v ∈ L, autAddHom s v = y := by
  letI := galoisModule hw2 x hx3 hfix
  intro L y
  rfl

theorem sImage_mem_of_conj {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {s h h' : MulAut W} (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    (hconj : s * h * s⁻¹ = h') :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (L : Submodule (GaloisField 2 2) (Additive W)),
      (∀ v ∈ L, autAddHom h' v ∈ L) →
      ∀ y ∈ sImage hw2 x hx3 hfix hsx L,
        autAddHom h y ∈ sImage hw2 x hx3 hfix hsx L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L h'L y hy
  rw [mem_sImage hw2 x hx3 hfix hsx L y] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [mem_sImage hw2 x hx3 hfix hsx L (autAddHom h (autAddHom s v))]
  refine ⟨autAddHom h' v, h'L v hv, ?_⟩
  have hcomm : h * s = s * h' := mulAut_conj_commute hs2 hconj
  have hpoint := congrArg (fun f : MulAut W => f (Additive.toMul v)) hcomm
  simpa [autAddHom, MulAut.mul_apply] using congrArg Additive.ofMul hpoint.symm

theorem sImage_stabilized_of_forall_conj {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {s : MulAut W} (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    {H : Subgroup (MulAut W)} (hconjH : ∀ h ∈ H, s * h * s⁻¹ ∈ H) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (L : Submodule (GaloisField 2 2) (Additive W)),
      (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) →
      ∀ h ∈ H, ∀ y ∈ sImage hw2 x hx3 hfix hsx L,
        autAddHom h y ∈ sImage hw2 x hx3 hfix hsx L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L hL h hh y hy
  exact sImage_mem_of_conj hw2 x hx3 hfix hW hs2 hsx rfl L
    (hL (s * h * s⁻¹) (hconjH h hh)) y hy

noncomputable def HLin {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    Subgroup (Additive W ≃ₗ[GaloisField 2 2] Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  refine
  { carrier := {g | ∃ (h : MulAut W) (hh : h ∈ H),
      g = hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh)}
    one_mem' := ⟨1, H.one_mem,
      (hGaloisLinearEquiv_one hw2 x hx3 hfix (hcommH 1 H.one_mem)).symm⟩
    mul_mem' := by
      rintro g₁ g₂ ⟨h₁, hh₁, rfl⟩ ⟨h₂, hh₂, rfl⟩
      refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
      rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix h₁ h₂
        (hcommH h₁ hh₁) (hcommH h₂ hh₂) (hcommH (h₁ * h₂) (H.mul_mem hh₁ hh₂))]
      rfl
    inv_mem' := by
      rintro g ⟨h, hh, rfl⟩
      refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
      ext v
      change (hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh)).symm v =
        hGaloisLinearEquiv hw2 x hx3 hfix h⁻¹ (hcommH h⁻¹ (H.inv_mem hh)) v
      simp [hGaloisLinearEquiv, autAddHom] }

theorem mem_HLin {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ g : Additive W ≃ₗ[GaloisField 2 2] Additive W,
      g ∈ HLin hw2 x hx3 hfix H hcommH ↔
        ∃ (h : MulAut W) (hh : h ∈ H),
          g = hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh) := by
  letI := galoisModule hw2 x hx3 hfix
  intro g
  rfl

theorem hGaloisLinearEquiv_mem_HLin {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) {h : MulAut W} (hh : h ∈ H) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh) ∈
      HLin hw2 x hx3 hfix H hcommH := by
  letI := galoisModule hw2 x hx3 hfix
  exact ⟨h, hh, rfl⟩

theorem hGaloisLinearEquiv_mul_self {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) {h : MulAut W} (hh : h ∈ H)
    (h2 : h * h = 1) :
    letI := galoisModule hw2 x hx3 hfix
    hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh) *
      hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh) = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  change (hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh)).trans
    (hGaloisLinearEquiv hw2 x hx3 hfix h (hcommH h hh)) = 1
  rw [← hGaloisLinearEquiv_mul hw2 x hx3 hfix h h
    (hcommH h hh) (hcommH h hh) (hcommH (h * h) (H.mul_mem hh hh))]
  convert hGaloisLinearEquiv_one hw2 x hx3 hfix (hcommH 1 H.one_mem) using 2

theorem HLin_stabilizes {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (L : Submodule (GaloisField 2 2) (Additive W)),
      (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) →
      ∀ g ∈ HLin hw2 x hx3 hfix H hcommH, ∀ v ∈ L, g v ∈ L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L hL g hg v hv
  rw [mem_HLin hw2 x hx3 hfix H hcommH g] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  exact hL h hh v hv

theorem false_of_two_invariant_lines_HLin {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {s : MulAut W} (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    {H : Subgroup (MulAut W)} (hcommH : ∀ h ∈ H, h * x = x * h)
    {d : MulAut W} (hdH : d ∈ H) (hd2 : d * d = 1) (hdne : d ≠ 1) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (Y L : Submodule (GaloisField 2 2) (Additive W)),
      Module.finrank (GaloisField 2 2) Y = 1 →
      Module.finrank (GaloisField 2 2) L = 1 →
      Module.finrank (GaloisField 2 2) (sImage hw2 x hx3 hfix hsx L) = 1 →
      L ≠ sImage hw2 x hx3 hfix hsx L →
      (∀ y ∈ Y, autAddHom d y = y) →
      (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) →
      (∀ h ∈ H, ∀ v ∈ sImage hw2 x hx3 hfix hsx L,
        autAddHom h v ∈ sImage hw2 x hx3 hfix hsx L) →
      False := by
  letI := galoisModule hw2 x hx3 hfix
  intro Y L hY hL hsL hne hYfix hLstab hsLstab
  have hcommd : d * x = x * d := hcommH d hdH
  let dLin := hGaloisLinearEquiv hw2 x hx3 hfix d hcommd
  have hdLin_mem : dLin ∈ HLin hw2 x hx3 hfix H hcommH :=
    hGaloisLinearEquiv_mem_HLin hw2 x hx3 hfix H hcommH hdH
  have hdLin_sq : dLin * dLin = 1 :=
    hGaloisLinearEquiv_mul_self hw2 x hx3 hfix H hcommH hdH hd2
  have hdLin_ne : dLin ≠ 1 :=
    hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hcommd hdne
  have hYfixLin : ∀ y ∈ Y, dLin y = y := by
    intro y hy
    exact hYfix y hy
  have hLstabLin : ∀ g ∈ HLin hw2 x hx3 hfix H hcommH, ∀ v ∈ L, g v ∈ L :=
    HLin_stabilizes hw2 x hx3 hfix H hcommH L hLstab
  have hsLstabLin : ∀ g ∈ HLin hw2 x hx3 hfix H hcommH,
      ∀ v ∈ sImage hw2 x hx3 hfix hsx L, g v ∈ sImage hw2 x hx3 hfix hsx L :=
    HLin_stabilizes hw2 x hx3 hfix H hcommH (sImage hw2 x hx3 hfix hsx L) hsLstab
  exact false_of_involution_two_invariant_lines
    (finrank_galoisModule hw2 x hx3 hfix hW) hdLin_mem hdLin_sq hdLin_ne
    hY hL hsL hne hYfixLin hLstabLin hsLstabLin

theorem G_stabilizes_of_sImage_eq {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {s : MulAut W} (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    {G H : Subgroup (MulAut W)} (hHG : H ≤ G)
    (hcover : ∀ g ∈ G, g ∈ H ∨ s⁻¹ * g ∈ H) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (L : Submodule (GaloisField 2 2) (Additive W)),
      sImage hw2 x hx3 hfix hsx L = L →
      (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) →
      ∀ g ∈ G, ∀ v ∈ L, g v ∈ L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L hsLeq hLstab g hg v hv
  rcases hcover g hg with hgH | hgH
  · exact hLstab g hgH v hv
  · let h : MulAut W := s⁻¹ * g
    have hh : h ∈ H := hgH
    have hg_eq : g = s * h := by
      dsimp [h]
      group
    rw [hg_eq]
    have hv' : autAddHom h v ∈ L := hLstab h hh v hv
    have hsv : autAddHom s (autAddHom h v) ∈ sImage hw2 x hx3 hfix hsx L :=
      (mem_sImage hw2 x hx3 hfix hsx L (autAddHom s (autAddHom h v))).mpr ⟨autAddHom h v, hv', rfl⟩
    rw [hsLeq] at hsv
    change Additive.ofMul (s (h (Additive.toMul v))) ∈ L
    exact hsv

theorem no_invariant_line_HLin {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {s : MulAut W} (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2)
    {G H : Subgroup (MulAut W)} (hHG : H ≤ G)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hconjH : ∀ h ∈ H, s * h * s⁻¹ ∈ H)
    (hcover : ∀ g ∈ G, g ∈ H ∨ s⁻¹ * g ∈ H)
    {d : MulAut W} (hdH : d ∈ H) (hd2 : d * d = 1) (hdne : d ≠ 1) :
    letI := galoisModule hw2 x hx3 hfix
    (∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤) →
    ∀ (Y : Submodule (GaloisField 2 2) (Additive W)),
      Module.finrank (GaloisField 2 2) Y = 1 →
      (∀ y ∈ Y, autAddHom d y = y) →
      ∀ L : Submodule (GaloisField 2 2) (Additive W),
        Module.finrank (GaloisField 2 2) L = 1 →
        (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) → False := by
  letI := galoisModule hw2 x hx3 hfix
  intro hirr Y hY hYfix L hL hLstab
  have hirr' : ∀ Z : Submodule (GaloisField 2 2) (Additive W),
      (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤ :=
    hirr_submodule_of_hirr_subgroup (G := G) hirr
  have hV : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  have hsL : Module.finrank (GaloisField 2 2) (sImage hw2 x hx3 hfix hsx L) = 1 :=
    finrank_sImage hw2 x hx3 hfix hW hsx L hL
  have hsLstab : ∀ h ∈ H, ∀ v ∈ sImage hw2 x hx3 hfix hsx L,
      autAddHom h v ∈ sImage hw2 x hx3 hfix hsx L :=
    sImage_stabilized_of_forall_conj hw2 x hx3 hfix hW hs2 hsx hconjH L hLstab
  by_cases hne : L = sImage hw2 x hx3 hfix hsx L
  · have hsLeq : sImage hw2 x hx3 hfix hsx L = L := hne.symm
    have hGstab : ∀ g ∈ G, ∀ v ∈ L, g v ∈ L :=
      G_stabilizes_of_sImage_eq hw2 x hx3 hfix hW hs2 hsx hHG hcover L hsLeq hLstab
    rcases hirr' L hGstab with hbot | htop
    · rw [hbot, finrank_bot] at hL
      omega
    · rw [htop, finrank_top] at hL
      omega
  · exact false_of_two_invariant_lines_HLin hw2 x hx3 hfix hW hs2 hsx hcommH
      hdH hd2 hdne Y L hY hL hsL hne hYfix hLstab hsLstab

theorem conj_mem_centralizer_of_normal_in_G {G : Type*} [Group G] {X G₀ : Subgroup G} {s h : G}
    (hXconj : ∀ g ∈ G₀, ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (hsG : s ∈ G₀) (hsInv : s⁻¹ ∈ G₀) (hhG : h ∈ G₀)
    (hhC : h ∈ Subgroup.centralizer (X : Set G)) :
    s * h * s⁻¹ ∈ G₀ ⊓ Subgroup.centralizer (X : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact G₀.mul_mem (G₀.mul_mem hsG hhG) (G₀.inv_mem hsG)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : s⁻¹ * x * s ∈ X := by
      simpa using hXconj s⁻¹ hsInv x hx
    have hc := (Subgroup.mem_centralizer_iff.mp hhC) (s⁻¹ * x * s) hx'
    calc x * (s * h * s⁻¹) = s * ((s⁻¹ * x * s) * h) * s⁻¹ := by group
      _ = s * (h * (s⁻¹ * x * s)) * s⁻¹ := by rw [hc]
      _ = s * h * s⁻¹ * x := by group

theorem conj_eq_sq_of_zpowers_three_of_mem {G : Type*} [Group G] {X : Subgroup G} {x s : G}
    (hxgen : X = Subgroup.zpowers x) (hx3 : orderOf x = 3)
    (hmem : s * x * s⁻¹ ∈ X) (hsx : s * x * s⁻¹ ≠ x) :
    s * x * s⁻¹ = x ^ 2 := by
  have hxX : x ∈ X := by
    rw [hxgen]
    exact Subgroup.mem_zpowers x
  rw [hxgen] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkmod : x ^ (k % 3) = s * x * s⁻¹ := by
    rw [← hk]
    conv_rhs => rw [← zpow_mod_orderOf x k, hx3]
    norm_num
  have hxne : x ≠ 1 := by
    intro hx1
    rw [hx1] at hx3
    simp at hx3
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases k % 3
  · simp at hkmod
    have hx1 : x = 1 := by
      have h : s * x * s⁻¹ = 1 := hkmod.symm
      calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
        _ = s⁻¹ * 1 * s := by rw [h]
        _ = 1 := by group
    exact absurd hx1 hxne
  · exfalso
    exact hsx (by simpa using hkmod.symm)
  · simpa using hkmod.symm

theorem mem_centralizer_of_conj_eq_self {G : Type*} [Group G] {X : Subgroup G} {x h : G}
    (hxgen : X = Subgroup.zpowers x) (hconj : h * x * h⁻¹ = x) :
    h ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hxgen] at hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hk]
  have : h * x ^ k * h⁻¹ = (h * x * h⁻¹) ^ k := by
    rw [show h * x ^ k * h⁻¹ = (MulAut.conj h) (x ^ k) by rfl]
    rw [map_zpow]
    rfl
  have hcomm : h * x ^ k = x ^ k * h := by
    calc h * x ^ k = h * x ^ k * (h⁻¹ * h) := by simp
      _ = (h * x ^ k * h⁻¹) * h := by group
      _ = x ^ k * h := by rw [this, hconj]
  exact hcomm.symm

theorem cover_inf_centralizer {G : Type*} [Group G] {X H : Subgroup G} {x s : G}
    (hH : H = Subgroup.centralizer (X : Set G))
    (hXconj : ∀ g : G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x) (hx3 : orderOf x = 3)
    (hs2 : s * s = 1)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set G)) :
    ∀ g : G, g ∈ H ∨ s⁻¹ * g ∈ H := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hxX : x ∈ X := by
    rw [hxgen]; exact Subgroup.mem_zpowers x
  have hsx_ne : s * x * s⁻¹ ≠ x := by
    intro h
    apply hs_not_cent
    exact mem_centralizer_of_conj_eq_self hxgen h
  have hs_sq : s * x * s⁻¹ = x ^ 2 :=
    conj_eq_sq_of_zpowers_three_of_mem hxgen hx3 (hXconj s x hxX) hsx_ne
  intro g
  by_cases hfix : g * x * g⁻¹ = x
  · left
    rw [hH]
    exact mem_centralizer_of_conj_eq_self hxgen hfix
  · right
    have hg_sq : g * x * g⁻¹ = x ^ 2 :=
      conj_eq_sq_of_zpowers_three_of_mem hxgen hx3 (hXconj g x hxX) hfix
    rw [hH]
    apply mem_centralizer_of_conj_eq_self hxgen
    calc (s⁻¹ * g) * x * (s⁻¹ * g)⁻¹ = s⁻¹ * (g * x * g⁻¹) * s := by group
      _ = s⁻¹ * x ^ 2 * s := by rw [hg_sq]
      _ = x := by
        rw [← hs_sq]
        group

theorem galoisEquivFun_hGL_apply {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {h : MulAut W} (hcomm : h * x = x * h) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    galoisEquivFun hw2 x hx3 hfix hW
        (hGaloisLinearEquiv hw2 x hx3 hfix h hcomm v) =
      Matrix.mulVec (hGL hw2 x hx3 hfix h hcomm hW)
        (galoisEquivFun hw2 x hx3 hfix hW v) := by
  letI := galoisModule hw2 x hx3 hfix
  let e := galoisEquivFun hw2 x hx3 hfix hW
  let C := e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm).trans e)
  have hC : hGL hw2 x hx3 hfix h hcomm hW = matrixOfLinearEquiv C := rfl
  have h1 : e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) v) = C (e v) := by
    change e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) v) =
      e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) (e.symm (e v)))
    rw [e.symm_apply_apply]
  rw [h1, hC, matrixOfLinearEquiv_apply]

theorem isNatGL4_of_surjective {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16)
    (hsurj : Function.Surjective (hGLHom hw2 x hx3 hfix G X hxgen hW)) :
    IsNatGL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) 2 := by
  let φ : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
    MulEquiv.ofBijective (hGLHom hw2 x hx3 hfix G X hxgen hW)
      ⟨hGLHom_injective hw2 x hx3 hfix G X hxgen hW, hsurj⟩
  let ψ : W ≃* Multiplicative (Fin 2 → GaloisField 2 2) :=
    psiMul hw2 x hx3 hfix hW
  refine ⟨φ, ψ, ?_⟩
  intro a w
  have hv := galoisEquivFun_hGL_apply hw2 x hx3 hfix hW
    (hcommOf x G X hxgen a) (Additive.ofMul w)
  have hφ : (φ a : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      hGL hw2 x hx3 hfix (a : MulAut W) (hcommOf x G X hxgen a) hW := rfl
  change Multiplicative.ofAdd
      (galoisEquivFun hw2 x hx3 hfix hW (Additive.ofMul ((a : MulAut W) w))) =
    Multiplicative.ofAdd
      ((φ a : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
        (galoisEquivFun hw2 x hx3 hfix hW (Additive.ofMul w)))
  rw [hφ]
  rw [show Additive.ofMul ((a : MulAut W) w) =
      hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
        (hcommOf x G X hxgen a) (Additive.ofMul w) from rfl]
  rw [hv]

theorem inf_centralizer_normal_in_G {W : Type*} [CommGroup W]
    {G X H : Subgroup (MulAut W)}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXconj : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
  intro g hg h hh
  have hhG : h ∈ G := (Subgroup.mem_inf.mp (hH ▸ hh)).1
  have hhC : h ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
    (Subgroup.mem_inf.mp (hH ▸ hh)).2
  rw [hH]
  exact conj_mem_centralizer_of_normal_in_G hXconj hg (G.inv_mem hg) hhG hhC

theorem inf_centralizer_sconj {W : Type*} [CommGroup W]
    {G X H : Subgroup (MulAut W)} {s : MulAut W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXconj : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (hsG : s ∈ G) (hsInv : s⁻¹ ∈ G) :
    H ≤ G ∧ ∀ h ∈ H, s * h * s⁻¹ ∈ H := by
  refine ⟨?_, ?_⟩
  · intro h hh
    exact (Subgroup.mem_inf.mp (hH ▸ hh)).1
  · intro h hh
    have hhG : h ∈ G := (Subgroup.mem_inf.mp (hH ▸ hh)).1
    have hhC : h ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp (hH ▸ hh)).2
    rw [hH]
    exact conj_mem_centralizer_of_normal_in_G hXconj hsG hsInv hhG hhC

theorem cover_H_MulAut {W : Type*} [CommGroup W] [Finite W]
    {G X H : Subgroup (MulAut W)} {x s : MulAut W}
    (hXG : X ≤ G)
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXconj : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x) (hx3 : orderOf x = 3)
    (hsG : s ∈ G) (hs2 : s * s = 1)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W))) :
    ∀ g ∈ G, g ∈ H ∨ s⁻¹ * g ∈ H := by
  have hxX : x ∈ X := by
    rw [hxgen]; exact Subgroup.mem_zpowers x
  let x' : ↥G := ⟨x, hXG hxX⟩
  let s' : ↥G := ⟨s, hsG⟩
  let X' : Subgroup ↥G := X.subgroupOf G
  let H' : Subgroup ↥G := H.subgroupOf G
  have hH' : H' = Subgroup.centralizer (X' : Set ↥G) := by
    ext u
    change (u : MulAut W) ∈ H ↔ u ∈ Subgroup.centralizer (X' : Set ↥G)
    constructor
    · intro hu
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hu' : (u : MulAut W) ∈
          G ⊓ Subgroup.centralizer (X : Set (MulAut W)) := by
        rwa [hH] at hu
      have hC : (u : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
        (Subgroup.mem_inf.mp hu').2
      have hyX : (y : MulAut W) ∈ X := hy
      simpa using (Subgroup.mem_centralizer_iff.mp hC) (y : MulAut W) hyX
    · intro hu
      have hu' : (u : MulAut W) ∈
          G ⊓ Subgroup.centralizer (X : Set (MulAut W)) := by
        refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (⟨y, hXG hy⟩ : ↥G) ∈ X' := by
          change (⟨y, hXG hy⟩ : ↥G) ∈ X.subgroupOf G
          exact hy
        have hcomm := hu ⟨y, hXG hy⟩ hy'
        have := congrArg (fun v : ↥G => (v : MulAut W)) hcomm
        simpa using this
      rwa [hH]
  have hXconj' : ∀ g : ↥G, ∀ y ∈ X', g * y * g⁻¹ ∈ X' := by
    intro g y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hXconj (g : MulAut W) g.2 (y : ↥G) hy
  have hxgen' : X' = Subgroup.zpowers x' := by
    ext u
    rw [Subgroup.mem_subgroupOf, hxgen, Subgroup.mem_zpowers_iff,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa [x'] using hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := congrArg (fun v : ↥G => (v : MulAut W)) hk
      simpa [x'] using this
  have hx3' : orderOf x' = 3 := by
    dsimp [x']
    rw [Subgroup.orderOf_mk, hx3]
  have hs2' : s' * s' = 1 := by
    apply Subtype.ext
    simpa [s'] using hs2
  have hs_not_cent' : s' ∉ Subgroup.centralizer (X' : Set ↥G) := by
    intro hc
    apply hs_not_cent
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hc' := (Subgroup.mem_centralizer_iff.mp hc) ⟨y, hXG hy⟩ (by
      change (⟨y, hXG hy⟩ : ↥G) ∈ X.subgroupOf G
      exact hy)
    have := congrArg (fun v : ↥G => (v : MulAut W)) hc'
    simpa [s'] using this
  intro g hg
  have hcover := cover_inf_centralizer hH' hXconj' hxgen' hx3' hs2' hs_not_cent' (⟨g, hg⟩ : ↥G)
  rcases hcover with hgH | hgH
  · left
    exact Subgroup.mem_subgroupOf.mp hgH
  · right
    have hgH' : ((s'⁻¹ * (⟨g, hg⟩ : ↥G) : ↥G) : MulAut W) ∈ H :=
      Subgroup.mem_subgroupOf.mp hgH
    simpa [s', Subgroup.coe_mul, Subgroup.coe_inv] using hgH'

theorem exists_involution_of_card_two {W : Type*} [CommGroup W] [Finite W]
    {D : Subgroup (MulAut W)} (hD2 : Nat.card D = 2)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) :
    ∃ d ∈ D, d * d = 1 ∧ d ≠ 1 := by
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨d, hd, hdne⟩ := D.exists_ne_one_of_nontrivial
  refine ⟨d, hd, ?_, hdne⟩
  have h2 : d ^ 2 = 1 := hElem.2 d hd
  simpa [pow_two] using h2

theorem fixed_of_le_fixV {W : Type*} [CommGroup W] {D : Subgroup (MulAut W)}
    {Y : Subgroup W} (hY : Y ≤ fixV D) {d : MulAut W} (hd : d ∈ D) :
    ∀ y ∈ Y, d y = y := by
  intro y hy
  exact hY hy d hd

theorem no_invariant_line_Hyp139_n2 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ L : Submodule (GaloisField 2 2) (Additive W),
      Module.finrank (GaloisField 2 2) L = 1 →
      (∀ h ∈ H, ∀ v ∈ L, autAddHom h v ∈ L) → False := by
  letI := galoisModule hw2 x hx3 hfix
  haveI : FiniteDimensional (GaloisField 2 2) (Additive W) :=
    (galoisBasis hw2 x hx3 hfix hW).finiteDimensional_of_finite
  intro L hL hLstab
  have hxX : x ∈ X := by
    rw [hxgen]; exact Subgroup.mem_zpowers x
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs_ord2] at this
    simpa [pow_two] using this
  obtain ⟨d, hdD, hd2, hdne⟩ := exists_involution_of_card_two hDcard hElem
  have hdH : d ∈ H := by
    rw [hH]
    refine Subgroup.mem_inf.mpr ⟨hD hdD, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hDCX d hdD y hy).symm
  have hcommH : ∀ h ∈ H, h * x = x * h := by
    intro h hh
    rw [hH] at hh
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2) x hxX).symm
  have hHG : H ≤ G := by
    intro h hh
    rw [hH] at hh
    exact (Subgroup.mem_inf.mp hh).1
  have hsInv : s⁻¹ ∈ G := G.inv_mem hsG
  have hconjH : ∀ h ∈ H, s * h * s⁻¹ ∈ H :=
    (inf_centralizer_sconj hH hXnorm hsG hsInv).2
  have hcover : ∀ g ∈ G, g ∈ H ∨ s⁻¹ * g ∈ H :=
    cover_H_MulAut hXG hH hXnorm hxgen hx_ord3 hsG hs2 hs_not_cent
  have hsx_ne : s * x * s⁻¹ ≠ x := by
    intro h
    apply hs_not_cent
    exact mem_centralizer_of_conj_eq_self hxgen h
  have hsx : s * x * s⁻¹ = x ^ 2 :=
    conj_eq_sq_of_zpowers_three_of_mem hxgen hx_ord3 (hXnorm s hsG x hxX) hsx_ne
  have hYfinrank : Module.finrank (GaloisField 2 2)
      (YSubmodule hw2 x hx3 hfix hxX hYinv) = 1 :=
    finrank_eq_one_of_card_four
      (card_YSubmodule hw2 x hx3 hfix hxX hYinv hYcard)
  have hYfix : ∀ y ∈ YSubmodule hw2 x hx3 hfix hxX hYinv, autAddHom d y = y := by
    intro y hy
    have hyY : Additive.toMul y ∈ Y := hy
    have := fixed_of_le_fixV hYD hdD (Additive.toMul y) hyY
    simpa [autAddHom] using congrArg Additive.ofMul this
  exact no_invariant_line_HLin hw2 x hx3 hfix hW hs2 hsx hHG hcommH hconjH hcover
    hdH hd2 hdne hirr (YSubmodule hw2 x hx3 hfix hxX hYinv) hYfinrank hYfix L hL hLstab

theorem card_f4Line {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    Nat.card {L : Submodule (GaloisField 2 2) (Additive W) //
      Module.finrank (GaloisField 2 2) L = 1} = 5 := by
  letI := galoisModule hw2 x hx3 hfix
  have hV : Nat.card (Additive W) = 16 := by
    rw [Nat.card_congr Additive.toMul, hW]
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcard := Projectivization.card' (k := GaloisField 2 2) (V := Additive W)
  rw [hV, hk] at hcard
  have hproj : Nat.card (Projectivization (GaloisField 2 2) (Additive W)) = 5 := by
    omega
  rw [← hproj]
  exact Nat.card_congr
    (Projectivization.equivSubmodule (GaloisField 2 2) (Additive W)).symm

noncomputable def HLinHom {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    ↥H →* (Additive W ≃ₗ[GaloisField 2 2] Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  refine
  { toFun := fun h => hGaloisLinearEquiv hw2 x hx3 hfix (h : MulAut W)
      (hcommH h h.2)
    map_one' := ?_
    map_mul' := ?_ }
  · exact hGaloisLinearEquiv_one hw2 x hx3 hfix (hcommH 1 H.one_mem)
  · intro h₁ h₂
    change hGaloisLinearEquiv hw2 x hx3 hfix ((h₁ : MulAut W) * (h₂ : MulAut W))
        (hcommH (h₁ * h₂) (H.mul_mem h₁.2 h₂.2)) =
      hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W) (hcommH h₁ h₁.2) *
        hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W) (hcommH h₂ h₂.2)
    rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix (h₁ : MulAut W) (h₂ : MulAut W)
      (hcommH h₁ h₁.2) (hcommH h₂ h₂.2)
      (hcommH (h₁ * h₂) (H.mul_mem h₁.2 h₂.2))]
    rfl

theorem HLinHom_apply {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) (h : ↥H) :
    letI := galoisModule hw2 x hx3 hfix
    HLinHom hw2 x hx3 hfix H hcommH h =
      hGaloisLinearEquiv hw2 x hx3 hfix (h : MulAut W) (hcommH h h.2) := by
  simp [HLinHom]

theorem H_action_or_small_set {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    (H : Subgroup (MulAut W)) (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    (∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) ∨
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.Nonempty ∧ S ≠ Set.univ ∧
          (∀ h : ↥H,
            S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S) ∧
          S.ncard ≤ 2 := by
  letI := galoisModule hw2 x hx3 hfix
  letI : MulAction ↥H (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
  { smul := fun h L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L
    one_smul := by
      intro L
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH 1) L = L
      rw [map_one]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro hv
        exact ⟨v, hv, rfl⟩
    mul_smul := by
      intro h₁ h₂ L
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH (h₁ * h₂)) L =
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h₁)
          (lineMap (HLinHom hw2 x hx3 hfix H hcommH h₂) L)
      rw [map_mul]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(HLinHom hw2 x hx3 hfix H hcommH h₂) w,
          ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩ }
  haveI : Fintype (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
    Fintype.ofFinite _
  have hcard : Fintype.card (LineOf (K := GaloisField 2 2) (V := Additive W)) = 5 := by
    rw [Fintype.card_eq_nat_card, card_f4Line hw2 x hx3 hfix hW]
  exact exists_small_invariant_set_of_card_five hcard

theorem H_transitive_or_pair {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    (H : Subgroup (MulAut W)) (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    (∀ L : LineOf (K := GaloisField 2 2) (V := Additive W),
      ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L ≠ L) →
    (∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) ∨
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
          (∀ h : ↥H,
            S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S) := by
  letI := galoisModule hw2 x hx3 hfix
  intro hno
  rcases H_action_or_small_set hw2 x hx3 hfix hW H hcommH with htrans | ⟨S, hne, hproper, hS, hcard⟩
  · exact Or.inl htrans
  · right
    have hpos : 0 < S.ncard := (Set.ncard_pos (s := S)).mpr hne
    have hle : S.ncard ≤ 2 := hcard
    have h1or2 : S.ncard = 1 ∨ S.ncard = 2 := by
      have hlt : S.ncard < 3 := Nat.lt_succ_of_le hle
      have hge : 1 ≤ S.ncard := Nat.succ_le_of_lt hpos
      interval_cases S.ncard <;> simp
    rcases h1or2 with h1 | h2
    · exfalso
      obtain ⟨L, hLS⟩ := Set.ncard_eq_one.mp h1
      obtain ⟨h, hh⟩ := hno L
      have hmem : lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L ∈
          S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) :=
        ⟨L, by simp [hLS], rfl⟩
      rw [hS h, hLS] at hmem
      exact hh (by simpa using hmem)
    · exact ⟨S, h2, hne, hproper, hS⟩

theorem exists_moving_line_Hyp139_n2 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ L : LineOf (K := GaloisField 2 2) (V := Additive W),
      ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L ≠ L := by
  letI := galoisModule hw2 x hx3 hfix
  intro L
  by_contra hmove
  push Not at hmove
  have hLstab : ∀ h ∈ H, ∀ v ∈ L.1, autAddHom h v ∈ L.1 := by
    intro h hh v hv
    let g := HLinHom hw2 x hx3 hfix H hcommH (⟨h, hh⟩ : ↥H)
    have hg : L.1.map (g : Additive W →ₗ[GaloisField 2 2] Additive W) = L.1 := by
      have := congrArg Subtype.val (hmove ⟨h, hh⟩)
      simpa [lineMap, g] using this
    have hv' : (g : Additive W →ₗ[GaloisField 2 2] Additive W) v ∈ L.1 := by
      rw [← hg]
      exact ⟨v, hv, rfl⟩
    simpa [g, HLinHom, hGaloisLinearEquiv] using hv'
  exact no_invariant_line_Hyp139_n2 hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen
    hsG hs_ord2 hs_not_cent hirr hD hDCX hElem hDcard hYD hYinv hYcard L L.2 hLstab

theorem H_transitive_or_pair_Hyp139_n2 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    (∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M) ∨
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
          (∀ h : ↥H,
            S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S) := by
  letI := galoisModule hw2 x hx3 hfix
  exact H_transitive_or_pair hw2 x hx3 hfix hW H hcommH
    (exists_moving_line_Hyp139_n2 hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen
      hsG hs_ord2 hs_not_cent hirr hD hDCX hElem hDcard hYD hYinv hYcard hcommH)

theorem card_inf_centralizer_dvd_180 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16) :
    Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) ∣ 180 := by
  let f := hGLHom hw2 x hx3 hfix G X hxgen hW
  have hinj : Function.Injective f := hGLHom_injective hw2 x hx3 hfix G X hxgen hW
  have hcard : Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) =
      Nat.card (MonoidHom.range f) := by
    exact Nat.card_congr (Equiv.ofInjective f hinj)
  have hdvd := (MonoidHom.range f).card_subgroup_dvd_card
  rw [← hcard] at hdvd
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) = 180 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, hq]
  simpa [hGL] using hdvd

theorem card_div_three_inf_centralizer_dvd_60 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16) (hXG : X ≤ G) (hXcard : Nat.card X = 3) :
    Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) / 3 ∣ 60 := by
  let H := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hXH : X ≤ H := le_inf_centralizer_self hXG hXcard
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsubcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have h3dvd : 3 ∣ Nat.card ↥H := by
    rw [← hXcard, ← hXsubcard]
    exact (X.subgroupOf H).card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := h3dvd
  have hHdvd : Nat.card ↥H ∣ 180 :=
    card_inf_centralizer_dvd_180 hw2 x hx3 hfix G X hxgen hW
  have hkdvd : k ∣ 60 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 3)
    rwa [hk, show (180 : ℕ) = 3 * 60 by norm_num] at hHdvd
  change Nat.card ↥H / 3 ∣ 60
  rw [hk]
  simpa using hkdvd

end CentralizerExplicit

end Module

end CFSG.LocalAnalysis.WeakClosure81
