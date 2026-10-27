module

public import CFSG.Monster.B.Classical.UnitarySixForm
public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Monster.B.TwoA.Unitary.NData
public import Mathlib.GroupTheory.SemidirectProduct
import all CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  bar_eq_zero_iff mul_bar_of_ne_zero)

abbrev V6 : Type := Fin 6 → F4

@[expose] def lo (i : Fin 3) : Fin 6 := ⟨i, by omega⟩

@[expose] def hi (i : Fin 3) : Fin 6 := ⟨i + 3, by omega⟩

@[expose] def hU (s t : V6) : F4 :=
  ∑ i : Fin 3, (s (lo i) * bar (t (hi i)) + s (hi i) * bar (t (lo i)))

@[expose] def partner (i : Fin 6) : Fin 6 := ⟨((i : ℕ) + 3) % 6, Nat.mod_lt _ (by norm_num)⟩

theorem partner_partner : ∀ i : Fin 6, partner (partner i) = i := by decide

theorem hU_eq_sum (s t : V6) : hU s t = ∑ i : Fin 6, s i * bar (t (partner i)) := by
  simp only [hU, Fin.sum_univ_three, Fin.sum_univ_six]
  have e : ∀ a b c d e f : F4, a + b + (c + d) + (e + f) = a + c + e + b + d + f := by
    intro a b c d e f; ring
  rw [e]
  rfl

theorem hU_add_left (s s' t : V6) : hU (s + s') t = hU s t + hU s' t := by
  simp only [hU_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hU_add_right (s t t' : V6) : hU s (t + t') = hU s t + hU s t' := by
  simp only [hU_eq_sum, Pi.add_apply, bar_add, mul_add, Finset.sum_add_distrib]

theorem hU_smul_left (c : F4) (s t : V6) : hU (c • s) t = c * hU s t := by
  simp only [hU_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hU_smul_right (c : F4) (s t : V6) : hU s (c • t) = bar c * hU s t := by
  simp only [hU_eq_sum, Pi.smul_apply, smul_eq_mul, bar_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem hU_zero_left (t : V6) : hU 0 t = 0 := by simp [hU_eq_sum]

@[simp] theorem hU_zero_right (s : V6) : hU s 0 = 0 := by simp [hU_eq_sum]

theorem bar_sum' {ι : Type*} (S : Finset ι) (f : ι → F4) :
    bar (∑ i ∈ S, f i) = ∑ i ∈ S, bar (f i) :=
  CFSG.Monster.B.Classical.UnitarySix.bar_sum S f

theorem hU_swap (s t : V6) : hU t s = bar (hU s t) := by
  rw [hU, hU, bar_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bar_add, bar_mul, bar_mul, bar_bar, bar_bar]
  ring

theorem hU_single_right (s : V6) (j : Fin 6) : hU s (Pi.single j 1) = s (partner j) := by
  rw [hU_eq_sum, Finset.sum_eq_single (partner j)]
  · rw [partner_partner, Pi.single_eq_same, bar_one, mul_one]
  · intro i _ hi
    have : partner i ≠ j := fun h => hi (by rw [← h, partner_partner])
    rw [Pi.single_eq_of_ne this, bar_zero, mul_zero]
  · simp

theorem eq_zero_of_hU {s : V6} (h : ∀ t, hU s t = 0) : s = 0 := by
  funext i
  have := h (Pi.single (partner i) 1)
  rwa [hU_single_right, partner_partner] at this

@[expose] def hGram : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i j => if j = partner i then 1 else 0

theorem hGram_apply (i j : Fin 6) : hGram i j = hU (Pi.single i 1) (Pi.single j 1) := by
  rw [hU_single_right, hGram, of_apply, Pi.single_apply]
  by_cases h : j = partner i
  · rw [ite_eq_left h, ite_eq_left (by rw [h, partner_partner])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [← h', partner_partner]))]

@[expose] def barV (s : V6) : V6 := fun i => bar (s i)

theorem barV_barV (s : V6) : barV (barV s) = s := funext fun i => bar_bar (s i)

theorem barV_add (s t : V6) : barV (s + t) = barV s + barV t := funext fun _ => bar_add _ _

theorem barV_smul (c : F4) (s : V6) : barV (c • s) = bar c • barV s :=
  funext fun _ => bar_mul _ _

theorem barV_zero : barV 0 = 0 := funext fun _ => bar_zero

theorem hU_eq_dotProduct (s t : V6) : hU s t = s ⬝ᵥ (hGram *ᵥ barV t) := by
  rw [hU_eq_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [mulVec, dotProduct, Finset.sum_eq_single (partner i)]
  · simp [hGram, barV]
  · intro j _ hj
    simp [hGram, hj]
  · simp

theorem hU_barV (s t : V6) : hU (barV s) (barV t) = bar (hU s t) := by
  rw [hU_eq_sum, hU_eq_sum, bar_sum']
  exact Finset.sum_congr rfl fun i _ => by rw [bar_mul]; rfl

@[expose] def barHom : F4 →+* F4 where
  toFun := bar
  map_one' := bar_one
  map_mul' := bar_mul
  map_zero' := bar_zero
  map_add' := bar_add

theorem barHom_apply (z : F4) : barHom z = bar z := rfl

theorem barV_vecMul (s : V6) (A : Matrix (Fin 6) (Fin 6) F4) :
    barV (s ᵥ* A) = barV s ᵥ* A.map bar := by
  funext j
  exact RingHom.map_vecMul barHom A s j

@[expose] def barM (A : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4 := A.map bar

theorem barM_barM (A : Matrix (Fin 6) (Fin 6) F4) : barM (barM A) = A := by
  ext i j
  exact bar_bar _

theorem barM_mul (A B : Matrix (Fin 6) (Fin 6) F4) : barM (A * B) = barM A * barM B :=
  Matrix.map_mul (f := barHom)

theorem barM_one : barM (1 : Matrix (Fin 6) (Fin 6) F4) = 1 :=
  Matrix.map_one _ bar_zero bar_one

theorem det_barM (A : Matrix (Fin 6) (Fin 6) F4) : (barM A).det = bar A.det :=
  (RingHom.map_det barHom A).symm

@[expose] def SUh : Subgroup (GL (Fin 6) F4) where
  carrier := {A | (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
    ∀ s t : V6, hU (s ᵥ* (A : Matrix (Fin 6) (Fin 6) F4)) (t ᵥ* (A : Matrix (Fin 6) (Fin 6) F4)) =
      hU s t}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], fun s t => ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, hB.2, hA.2]
  one_mem' := ⟨by simp, fun s t => by simp⟩
  inv_mem' {A} hA := by
    have hAB : ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (A : Matrix (Fin 6) (Fin 6) F4) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, fun s t => ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, mul_one] at this
      exact this
    · rw [← hA.2, vecMul_vecMul, vecMul_vecMul, hAB, vecMul_one, vecMul_one]

theorem mem_SUh {A : GL (Fin 6) F4} :
    A ∈ SUh ↔ (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      ∀ s t : V6, hU (s ᵥ* (A : Matrix (Fin 6) (Fin 6) F4)) (t ᵥ* (A : Matrix (Fin 6) (Fin 6) F4)) =
        hU s t :=
  Iff.rfl

theorem hU_vecMul (A : Matrix (Fin 6) (Fin 6) F4) (s t : V6) :
    hU (s ᵥ* A) (t ᵥ* A) = s ⬝ᵥ ((A * hGram * (barM A)ᵀ) *ᵥ barV t) := by
  rw [hU_eq_dotProduct, barV_vecMul, ← mulVec_transpose (A.map bar), ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec]
  rfl

theorem eq_of_dotProduct_barV {A B : Matrix (Fin 6) (Fin 6) F4}
    (h : ∀ s t : V6, s ⬝ᵥ (A *ᵥ barV t) = s ⬝ᵥ (B *ᵥ barV t)) : A = B := by
  ext i j
  have := h (Pi.single i 1) (barV (Pi.single j 1))
  rw [barV_barV] at this
  simpa [mulVec_single, single_dotProduct] using this

theorem mem_SUh_iff_gram {A : GL (Fin 6) F4} :
    A ∈ SUh ↔ (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      (A : Matrix (Fin 6) (Fin 6) F4) * hGram * (barM (A : Matrix (Fin 6) (Fin 6) F4))ᵀ =
        hGram := by
  rw [mem_SUh]
  refine and_congr_right fun _ => ⟨fun h => eq_of_dotProduct_barV fun s t => ?_,
    fun h s t => ?_⟩
  · rw [← hU_vecMul, h, hU_eq_dotProduct]
  · rw [hU_vecMul, h, hU_eq_dotProduct]

theorem pow_six_eq_one : ∀ c : F4, c ≠ 0 → c ^ 6 = 1 := by decide

theorem scalar_mem_SUh (c : F4ˣ) : GeneralLinearGroup.scalar (Fin 6) c ∈ SUh := by
  refine ⟨?_, fun s t => ?_⟩
  · rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact pow_six_eq_one _ c.ne_zero
  · rw [GeneralLinearGroup.coe_scalar]
    have hv : ∀ x : V6, x ᵥ* Matrix.scalar (Fin 6) (c : F4) = (c : F4) • x := fun x => by
      funext j
      simp [vecMul_diagonal, Matrix.scalar_apply, mul_comm]
    rw [hv, hv, hU_smul_left, hU_smul_right, ← mul_assoc, mul_bar_of_ne_zero c.ne_zero, one_mul]

@[expose] def Zh : Subgroup SUh where
  carrier := {g | ∃ c : F4ˣ, (g : GL (Fin 6) F4) = GeneralLinearGroup.scalar (Fin 6) c}
  mul_mem' := by
    rintro g g' ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [Subgroup.coe_mul, hc, hd, map_mul]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    exact ⟨c⁻¹, by rw [Subgroup.coe_inv, hc, map_inv]⟩

theorem mem_Zh {g : SUh} :
    g ∈ Zh ↔ ∃ c : F4ˣ, (g : GL (Fin 6) F4) = GeneralLinearGroup.scalar (Fin 6) c := Iff.rfl

theorem scalar_commute (c : F4ˣ) (g : GL (Fin 6) F4) :
    g * GeneralLinearGroup.scalar (Fin 6) c = GeneralLinearGroup.scalar (Fin 6) c * g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute (c : F4) (fun r => Commute.all (c : F4) r) _)).eq.symm

theorem Zh_le_center : Zh ≤ Subgroup.center SUh := by
  rintro z ⟨c, hc⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact scalar_commute c g

instance Zh_normal : Zh.Normal where
  conj_mem z hz g := by
    have hc := Subgroup.mem_center_iff.1 (Zh_le_center hz) g
    rw [hc, mul_inv_cancel_right]
    exact hz

@[expose] def frobGL : GL (Fin 6) F4 →* GL (Fin 6) F4 := GeneralLinearGroup.map barHom

theorem coe_frobGL (A : GL (Fin 6) F4) :
    ((frobGL A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = barM A := rfl

theorem frobGL_frobGL (A : GL (Fin 6) F4) : frobGL (frobGL A) = A :=
  Units.ext (by rw [coe_frobGL, coe_frobGL, barM_barM])

theorem frobGL_mem {A : GL (Fin 6) F4} (hA : A ∈ SUh) : frobGL A ∈ SUh := by
  refine ⟨by rw [coe_frobGL, det_barM, hA.1, bar_one], fun s t => ?_⟩
  rw [coe_frobGL]
  have e : ∀ x : V6, x ᵥ* barM (A : Matrix (Fin 6) (Fin 6) F4) =
      barV (barV x ᵥ* (A : Matrix (Fin 6) (Fin 6) F4)) := fun x => by
    rw [barV_vecMul, barV_barV]
    rfl
  rw [e, e, hU_barV, hA.2, ← hU_barV, barV_barV, barV_barV]

@[expose] def frobSU : SUh →* SUh where
  toFun g := ⟨frobGL g, frobGL_mem g.2⟩
  map_one' := Subtype.ext (map_one frobGL)
  map_mul' a b := Subtype.ext (map_mul frobGL (a : GL (Fin 6) F4) (b : GL (Fin 6) F4))

theorem coe_frobSU (g : SUh) : ((frobSU g : SUh) : GL (Fin 6) F4) = frobGL g := rfl

theorem frobSU_frobSU (g : SUh) : frobSU (frobSU g) = g :=
  Subtype.ext (frobGL_frobGL _)

theorem frobGL_scalar (c : F4ˣ) :
    frobGL (GeneralLinearGroup.scalar (Fin 6) c) =
      GeneralLinearGroup.scalar (Fin 6) (Units.map barHom.toMonoidHom c) := by
  refine Units.ext ?_
  rw [coe_frobGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [barM, map_apply, Matrix.scalar_apply, diagonal_apply]
  split_ifs <;> simp [bar_zero]
  rfl

theorem Zh_le_comap_frobSU : Zh ≤ Zh.comap frobSU := by
  rintro g ⟨c, hc⟩
  exact ⟨Units.map barHom.toMonoidHom c, by rw [coe_frobSU, hc, frobGL_scalar]⟩

@[expose] def frobQ : MulAut (SUh ⧸ Zh) where
  toFun := QuotientGroup.map Zh Zh frobSU Zh_le_comap_frobSU
  invFun := QuotientGroup.map Zh Zh frobSU Zh_le_comap_frobSU
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [QuotientGroup.map_mk, frobSU_frobSU]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g => simp [QuotientGroup.map_mk, frobSU_frobSU]
  map_mul' := map_mul _

theorem frobQ_mk (g : SUh) : frobQ (g : SUh ⧸ Zh) = (frobSU g : SUh ⧸ Zh) := rfl

theorem frobQ_mul_self : frobQ * frobQ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => simp [MulAut.mul_apply, frobQ_mk, frobSU_frobSU]

@[expose] def frobPowQ (ε : ZMod 2) : MulAut (SUh ⧸ Zh) := if ε = 0 then 1 else frobQ

theorem zmod2_cases' : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem frobPowQ_zero : frobPowQ 0 = 1 := ite_eq_left rfl

theorem frobPowQ_one : frobPowQ 1 = frobQ := ite_eq_right (by decide)

theorem frobPowQ_add (x y : ZMod 2) : frobPowQ (x + y) = frobPowQ x * frobPowQ y := by
  rcases zmod2_cases' x with rfl | rfl <;> rcases zmod2_cases' y with rfl | rfl
  · rw [add_zero, frobPowQ_zero, mul_one]
  · rw [zero_add, frobPowQ_zero, one_mul]
  · rw [add_zero, frobPowQ_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, frobPowQ_zero, frobPowQ_one, frobQ_mul_self]

@[expose] def frobHomU : Multiplicative (ZMod 2) →* MulAut (SUh ⧸ Zh) where
  toFun ε := frobPowQ (Multiplicative.toAdd ε)
  map_one' := frobPowQ_zero
  map_mul' _ _ := frobPowQ_add _ _

theorem frobHomU_apply (ε : Multiplicative (ZMod 2)) :
    frobHomU ε = frobPowQ (Multiplicative.toAdd ε) := rfl

abbrev SigmaU6 : Type := (SUh ⧸ Zh) ⋊[frobHomU] Multiplicative (ZMod 2)

@[expose] def vec6 (n : ℕ) : V6 := fun i => ⟨⟨(n / 4 ^ (i : ℕ)) % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def planeRow (j : Fin 891) (r : Fin 3) : V6 := vec6 (b6PlaneArr[(j : ℕ)]!)[(r : ℕ)]!

@[expose] def plane (j : Fin 891) : Submodule F4 V6 := Submodule.span F4 (Set.range (planeRow j))

@[expose] def b6Iso (j : Fin 891) : Fin 891 :=
  ⟨b6IsoArr[(j : ℕ)]! % 891, Nat.mod_lt _ (by norm_num)⟩

@[expose] def b6Mat (k : Fin 17) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => vec6 (b6MatArr[(k : ℕ)]!)[(i : ℕ)]!

@[expose] def b6Frob (k : Fin 17) : ZMod 2 := ((b6FrobArr[(k : ℕ)]! : ℕ) : ZMod 2)

@[expose] def n6perm (k : Fin 17) (j : Fin 891) : Fin 891 :=
  ⟨(n6PermsArr[(k : ℕ)]!)[(j : ℕ)]! % 891, Nat.mod_lt _ (by norm_num)⟩

@[expose] def barPowV (ε : ZMod 2) (s : V6) : V6 := if ε = 0 then s else barV s

@[expose] def b6Map (k : Fin 17) (s : V6) : V6 := barPowV (b6Frob k) s ᵥ* b6Mat k

@[expose] def IsMaxIso (P : Submodule F4 V6) : Prop :=
  Module.finrank F4 P = 3 ∧ ∀ s ∈ P, ∀ t ∈ P, hU s t = 0

end CFSG.Monster.B.TwoA.Unitary
