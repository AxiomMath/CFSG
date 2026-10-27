
module

public import CFSG.Sporadic.Th.Max3.RelationsBase1
import all CFSG.Sporadic.Th.Max3.RelationsBase
import all CFSG.Sporadic.Th.Max3.RelationsBase1

public import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate10092
public meta import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Certificates.Kernel.Th.SoundnessMax3Base
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.OddCaseInputsBase
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import Certificates.Certificate10092Base

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

private theorem native_relation_facts :
    eqRows (powRows Slp.rowsT8 3) idRows = true ∧
    eqRows (powRows Slp.rowsS8' 19) idRows = true ∧
    eqRows (mulRows rowsX rowsX) idRows = true ∧
    eqRows (powRows rowsY 6) idRows = true ∧
    eqRows rowsZ rowsA = true ∧
    eqRows rowsZ idRows = false ∧
    eqRows (mulRows rowsZ rowsZ) idRows = true ∧
    eqRows (mulRows rowsZ rowsX) (mulRows rowsX rowsZ) = true ∧
    eqRows (mulRows rowsZ rowsY) (mulRows rowsY rowsZ) = true ∧
    (∀ i : Fin 8, eqRows (mulRows (rowsQ i) (rowsQ i)) idRows = true) ∧
    (∀ i : Fin 8, eqRows (mulRows rowsZ (rowsQ i)) (mulRows (rowsQ i) rowsZ) = true) ∧
    (∀ i j : Fin 8, eqRows (mulRows (rowsQ i) (rowsQ j))
      (mulRows (mulRows (rowsQ j) (rowsQ i)) (powRows rowsZ (c i j).val)) = true) ∧
    (∀ i : Fin 8, eqRows (mulRows (mulRows rowsX (rowsQ i)) rowsX)
      (rowsNf (xz i).val fun j => (xv i j).val) = true) ∧
    (∀ i : Fin 8, eqRows (mulRows (mulRows rowsY (rowsQ i)) (powRows rowsY 5))
      (rowsNf (yz i).val fun j => (yv i j).val) = true) :=
  Certificates.certificate10092.1

private theorem native_nf_distinct :
    ∀ k l : Fin 512, l < k → eqRows (rowsNfAt k) (rowsNfAt l) = false :=
  Certificates.certificate10092.2

theorem t8_pow_three :
    Slp.t8 ^ 3 = 1 := by
  obtain ⟨h, -⟩ := native_relation_facts
  exact (Slp.isRows_t8.pow 3).eq_of_eqRows IsRows.one h

theorem t8_inv :
    Slp.t8⁻¹ = Slp.t8 ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact t8_pow_three)

theorem s8'_pow_nineteen :
    Slp.s8' ^ 19 = 1 := by
  obtain ⟨-, h, -⟩ := native_relation_facts
  exact (Slp.isRows_s8'.pow 19).eq_of_eqRows IsRows.one h

theorem s8'_inv :
    Slp.s8'⁻¹ = Slp.s8' ^ 18 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact s8'_pow_nineteen)

theorem isRows_u :
    IsRows Slp.rowsU Slp.u := by
  have h := (Slp.isRows_t8.pow 2).mul Slp.isRows_t7
  rw [← t8_inv] at h
  exact h

theorem isRows_v :
    IsRows Slp.rowsV Slp.v := by
  have h := (Slp.isRows_s8'.pow 18).mul Slp.isRows_s7
  rw [← s8'_inv] at h
  exact h

theorem isRows_y :
    IsRows rowsY y := Slp.isRows_t7.mul (isRows_u.pow 9)

theorem isRows_x :
    IsRows rowsX x := isRows_v.pow 14

theorem x_mul_self : x * x = 1 := by
  obtain ⟨-, -, h, -⟩ := native_relation_facts
  exact (isRows_x.mul isRows_x).eq_of_eqRows IsRows.one h

theorem x_inv :
    x⁻¹ = x := inv_eq_of_mul_eq_one_right x_mul_self

theorem y_pow_six : y ^ 6 = 1 := by
  obtain ⟨-, -, -, h, -⟩ := native_relation_facts
  exact (isRows_y.pow 6).eq_of_eqRows IsRows.one h

theorem y_inv : y⁻¹ = y ^ 5 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact y_pow_six)

theorem isRows_z :
    IsRows rowsZ z := (IsRows.word isRows_x isRows_y zWord).pow zExp

theorem z_eq_a : z = a := by
  obtain ⟨-, -, -, -, h, -⟩ := native_relation_facts
  exact isRows_z.eq_of_eqRows isRows_a h

theorem z_ne_one : z ≠ 1 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := native_relation_facts
  exact isRows_z.ne_of_eqRows IsRows.one h

theorem z_mul_self : z * z = 1 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact (isRows_z.mul isRows_z).eq_of_eqRows IsRows.one h

theorem z_mul_x : z * x = x * z := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact (isRows_z.mul isRows_x).eq_of_eqRows (isRows_x.mul isRows_z) h

theorem z_mul_y : z * y = y * z := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact (isRows_z.mul isRows_y).eq_of_eqRows (isRows_y.mul isRows_z) h

theorem isRows_q
    (i : Fin 8) : IsRows (rowsQ i) (q i) := by
  rw [rowsQ_eq]
  exact (IsRows.word isRows_x isRows_y (qWord i)).pow (qExp i)

theorem q_mul_self
    (i : Fin 8) : q i * q i = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact ((isRows_q i).mul (isRows_q i)).eq_of_eqRows IsRows.one (h i)

theorem z_mul_q
    (i : Fin 8) : z * q i = q i * z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact (isRows_z.mul (isRows_q i)).eq_of_eqRows ((isRows_q i).mul isRows_z) (h i)

theorem q_mul_q
    (i j : Fin 8) : q i * q j = q j * q i * z ^ (c i j).val := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  exact ((isRows_q i).mul (isRows_q j)).eq_of_eqRows
    (((isRows_q j).mul (isRows_q i)).mul (isRows_z.pow _)) (h i j)

theorem isRows_nfN
    (s : ℕ) (e : Fin 8 → ℕ) : IsRows (rowsNf s e) (nfN s e) :=
  (isRows_z.pow s).mul (IsRows.prod (forall₂_ofFn _ _ _ fun i => (isRows_q i).pow (e i)))

theorem x_conj_q
    (i : Fin 8) : x * q i * x⁻¹ = nf (xz i) (xv i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := native_relation_facts
  rw [x_inv]
  exact ((isRows_x.mul (isRows_q i)).mul isRows_x).eq_of_eqRows (isRows_nfN _ _) (h i)

theorem y_conj_q
    (i : Fin 8) : y * q i * y⁻¹ = nf (yz i) (yv i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := native_relation_facts
  rw [y_inv]
  exact ((isRows_y.mul (isRows_q i)).mul (isRows_y.pow 5)).eq_of_eqRows
    (isRows_nfN _ _) (h i)

theorem isRows_nfAt
    (k : Fin 512) : IsRows (rowsNfAt k) (nfAt k) := by
  rw [rowsNfAt_eq]
  exact isRows_nfN _ _

theorem nf_injective :
    Function.Injective fun p : ZMod 2 × (Fin 8 → ZMod 2) => nf p.1 p.2 := by
  rintro ⟨s, v⟩ ⟨s', v'⟩ h
  simp only at h
  rw [nf_eq_nfAt, nf_eq_nfAt] at h
  have hk : nfIdx s v = nfIdx s' v' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (isRows_nfAt _).ne_of_eqRows (isRows_nfAt _) (native_nf_distinct _ _ hlt) h.symm
    · exact (isRows_nfAt _).ne_of_eqRows (isRows_nfAt _) (native_nf_distinct _ _ hgt) h
  have hs : s = s' := ZMod.val_injective 2 (by rw [← nfIdx_mod s v, ← nfIdx_mod s' v', hk])
  have hv : v = v' := funext fun i => ZMod.val_injective 2 (by
    rw [← nfIdx_div s v i, ← nfIdx_div s' v' i, hk])
  rw [hs, hv]

theorem x_conj_mem_Q
    {g : J} (hg : g ∈ Q) : x * g * x⁻¹ ∈ Q := by
  refine conj_mem_Q ?_ (fun i => ?_) hg
  · rw [← z_mul_x, mul_inv_cancel_right]
    exact z_mem_Q
  · rw [x_conj_q]
    exact nf_mem_Q _ _

theorem y_conj_mem_Q
    {g : J} (hg : g ∈ Q) : y * g * y⁻¹ ∈ Q := by
  refine conj_mem_Q ?_ (fun i => ?_) hg
  · rw [← z_mul_y, mul_inv_cancel_right]
    exact z_mem_Q
  · rw [y_conj_q]
    exact nf_mem_Q _ _

theorem x_mem_normalizer_Q :
    x ∈ Subgroup.normalizer (Q : Set J) :=
  mem_normalizer_of_pow (n := 1) (by rw [pow_two]; exact x_mul_self) fun _ hg => x_conj_mem_Q hg

theorem y_mem_normalizer_Q :
    y ∈ Subgroup.normalizer (Q : Set J) :=
  mem_normalizer_of_pow (n := 5) y_pow_six fun _ hg => y_conj_mem_Q hg

theorem M_le_normalizer_Q :
    M ≤ Subgroup.normalizer (Q : Set J) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact x_mem_normalizer_Q
  · exact y_mem_normalizer_Q

theorem normal_Q_subgroupOf_M :
    (Q.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Q_le_M).2 M_le_normalizer_Q

theorem commute_z_of_mem_M
    {m : J} (hm : m ∈ M) : Commute z m := by
  induction hm using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact z_mul_x
    · exact z_mul_y
  | one => exact Commute.one_right z
  | mul g h _ _ hg hh => exact hg.mul_right hh
  | inv g _ hg => exact Commute.inv_right hg

theorem z_mem_center_M :
    (⟨z, z_mem_M⟩ : M) ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (commute_z_of_mem_M g.2).symm.eq

end CFSG.Sporadic.Th.Max3
