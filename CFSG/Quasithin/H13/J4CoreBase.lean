
module

public import CFSG.Quasithin.H13.J4WordsBase
public import CFSG.Certificates.ExtraspecialNormalForm
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4CoreInputs
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Certificates.ExtraspecialNF

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section NF

variable {G : Type*} [Group G] {n : ℕ} {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

theorem bil_sub_left (c : Fin n → Fin n → ZMod 2) (v w u : Fin n → ZMod 2) :
    bil c (v - w) u = bil c v u - bil c w u := by
  unfold bil
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem zpow_val_inj (hz : z ≠ 1) {a b : ZMod 2}
    (h : z ^ a.val = z ^ b.val) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · exact absurd (by simpa [val_one_two] using h.symm) hz
  · exact absurd (by simpa [val_one_two] using h) hz
  · rfl

theorem injective_nf (h : Rel z q c) (hz : z ≠ 1) (hnd : Nondegenerate c) :
    Function.Injective (Function.uncurry (nf z q)) := by
  have hsymm := h.symm_of_ne_one hz
  have hdiag := h.diag_eq_zero hz
  rintro ⟨s, v⟩ ⟨s', w⟩ hst
  change nf z q s v = nf z q s' w at hst
  have hbil : ∀ u, bil c v u = bil c w u := by
    intro u
    have h1 := nf_mul_comm h hsymm hdiag s 0 v u
    have h2 := nf_mul_comm h hsymm hdiag s' 0 w u
    rw [← hst] at h2
    rw [h1] at h2
    exact zpow_val_inj hz (mul_left_cancel h2)
  have hvw : v = w := by
    by_contra hne
    obtain ⟨u, hu⟩ := hnd (v - w) (sub_ne_zero.2 hne)
    rw [bil_sub_left, hbil u, sub_self] at hu
    exact hu rfl
  subst hvw
  have hs : z ^ s.val = z ^ s'.val := mul_right_cancel hst
  rw [zpow_val_inj hz hs]

end NF

@[expose] def cInvRows : List ℕ := [966, 3153, 3769, 3524, 2918, 1428, 155, 365, 697, 277, 46, 30]

@[expose] def cMat (a b : Fin 12) : ZMod 2 := if (cRows.getD a 0).testBit b then 1 else 0

@[expose] def cInvMat : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun a b => if (cInvRows.getD a 0).testBit b then 1 else 0

@[expose] def rConjN (i : ℕ) : GL (Fin 112) (ZMod 2) := if h : i < 12 then rConj ⟨i, h⟩ else 1

@[expose] def qGen (a : Fin 12) : GL (Fin 112) (ZMod 2) := ((qIdx.getD a []).map rConjN).prod

@[expose] def rProd (l : List ℕ) : GL (Fin 112) (ZMod 2) := (l.map rConjN).prod

@[expose] def qProd (l : List ℕ) : GL (Fin 112) (ZMod 2) :=
  (l.map fun a => rProd (qIdx.getD a [])).prod

theorem qGen_eq (a : Fin 12) : qGen a = rProd (qIdx.getD a []) := rfl

theorem rConjN_mem_W (i : ℕ) : rConjN i ∈ W := by
  unfold rConjN
  split_ifs
  · exact rConj_mem_W _
  · exact W.one_mem

theorem rProd_mem_W (l : List ℕ) : rProd l ∈ W :=
  W.list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact rConjN_mem_W i

theorem qGen_mem_W (a : Fin 12) : qGen a ∈ W := rProd_mem_W _

theorem cMat_mul_cInv : Matrix.of cMat * cInvMat = 1 := by decide

theorem nondegenerate_cMat : Nondegenerate cMat := .of_mul_eq_one cMat_mul_cInv

end CFSG.Quasithin.H13.J4
