
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public import Certificates.Certificate2313
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public meta import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.Th.Chain
public meta import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.AutCore
public meta import Certificates.Certificate10088Base
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public meta import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public meta import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem isRows_localX : IsRows rowsLX localX := by
  rw [localX_eq]
  exact isRows_abRows xWord

theorem isRows_localY : IsRows rowsLY localY := by
  rw [localY_eq]
  exact isRows_abRows yWord

private theorem native_row_facts :
    (∀ i < 2457, ∀ j < 2457, i < j → localRowNats.getD i 0 ≠ localRowNats.getD j 0) ∧
    localRowNats.getD 0 0 = 0x6accc40834b0cc5bb7315609695cfa8d6f195e2ac39c3b4260e97d31187fa2 ∧
    (∀ i < 2457, localPermX[i]! < 2457 ∧ localPermY[i]! < 2457 ∧
      (frApply (frTable rowsLX) (localRowV4 i)).beq (localRowV4 localPermX[i]!) = true ∧
      (frApply (frTable (mulRows rowsLY rowsLY)) (localRowV4 i)).beq
        (localRowV4 localPermY[i]!) = true) :=
  Certificates.certificate2313.1

private theorem native_tree_facts :
    localTreePts[0]! = 0 ∧ (∀ k < 2457, localTreePts[k]! < 2457) ∧
    (∀ i < 2457, ∃ k < 2457, localTreePts[k]! = i) ∧
    (∀ k < 2457, 1 ≤ k → localTreePar[k]! < k ∧
      ((localTreeLab[k]! = 1 ∧ localPermX[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!) ∨
       (localTreeLab[k]! = 2 ∧ localPermY[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!))) :=
  Certificates.certificate2313.2.1

private theorem native_matrix_facts :
    eqRows (mulRows rowsLX rowsLX) idRows = true ∧ eqRows rowsLX idRows = false ∧
    eqRows (mulRows (mulRows rowsLY rowsLY) rowsLY) idRows = true ∧
    eqRows rowsLY idRows = false ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 21) idRows = true ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 3) idRows = false ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 7) idRows = false ∧
    imageKey (frTable rowsLX) wKeyRow = wKeyRow ∧
    imageKey (frTable (mulRows rowsLY rowsLY)) wKeyRow = wKeyRow :=
  Certificates.certificate2313.2.2

theorem localX_mul_self : localX * localX = 1 :=
  eq_one_of_isRows (isRows_localX.mul isRows_localX) native_matrix_facts.1

theorem localY_cube : localY * localY * localY = 1 :=
  eq_one_of_isRows ((isRows_localY.mul isRows_localY).mul isRows_localY)
    native_matrix_facts.2.2.1

theorem orderOf_localX : orderOf localX = 2 :=
  orderOf_eq_prime (by rw [sq]; exact localX_mul_self)
    (ne_one_of_isRows isRows_localX native_matrix_facts.2.1)

theorem orderOf_localY : orderOf localY = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by rw [pow_three, ← mul_assoc]; exact localY_cube)
    (ne_one_of_isRows isRows_localY native_matrix_facts.2.2.2.1)

theorem orderOf_localX_mul_localY : orderOf (localX * localY) = 21 := by
  obtain ⟨-, -, -, -, h21, h3, h7, -⟩ := native_matrix_facts
  have hxy := isRows_localX.mul isRows_localY
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (eq_one_of_isRows (hxy.pow 21) h21)
    fun p hp hpd => ?_
  have hp' : p = 3 ∨ p = 7 := by
    have h21' : (21 : ℕ) = 3 * 7 := by norm_num
    rw [h21'] at hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  rcases hp' with rfl | rfl
  · exact ne_one_of_isRows (hxy.pow 7) h7
  · exact ne_one_of_isRows (hxy.pow 3) h3

theorem isRows_localX_inv : IsRows rowsLX localX⁻¹ :=
  isRows_inv_of_mul_self isRows_localX localX_mul_self

theorem isRows_localY_inv : IsRows (mulRows rowsLY rowsLY) localY⁻¹ :=
  isRows_inv_of_cube isRows_localY localY_cube

theorem localX_smul_localRow {i : ℕ} (hi : i < 2457) :
    localX • localRow i = localRow localPermX[i]! := by
  rw [← toVec_localRowV4, smul_toVec isRows_localX_inv, ← toVec_localRowV4]
  congr 1
  exact congrArg V4.toVec (V4.beq_iff.1 (native_row_facts.2.2 i hi).2.2.1)

theorem localY_smul_localRow {i : ℕ} (hi : i < 2457) :
    localY • localRow i = localRow localPermY[i]! := by
  rw [← toVec_localRowV4, smul_toVec isRows_localY_inv, ← toVec_localRowV4]
  congr 1
  exact congrArg V4.toVec (V4.beq_iff.1 (native_row_facts.2.2 i hi).2.2.2)

theorem localX_smul_mem {v : RowV} (hv : v ∈ localOmega) : localX • v ∈ localOmega := by
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨_, (native_row_facts.2.2 i hi).1, (localX_smul_localRow hi).symm⟩

theorem localY_smul_mem {v : RowV} (hv : v ∈ localOmega) : localY • v ∈ localOmega := by
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨_, (native_row_facts.2.2 i hi).2.1, (localY_smul_localRow hi).symm⟩

theorem smul_mem_localOmega {h : J} (hh : h ∈ localH) {v : RowV} (hv : v ∈ localOmega) :
    h • v ∈ localOmega := by
  induction hh using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact localX_smul_mem hv
    · exact localY_smul_mem hv
  | one => rwa [one_smul]
  | mul g g' _ _ ih ih' => rw [mul_smul]; exact ih (ih' hv)
  | inv g _ ih => exact inv_smul_mem_of_finite localOmega_finite (fun w hw => ih hw) hv

theorem localRow_mem_orbit {i : ℕ} (hi : i < 2457) :
    localRow i ∈ MulAction.orbit localH (localRow 0) := by
  obtain ⟨h0, hlt, hcov, htree⟩ := native_tree_facts
  have key : ∀ k < 2457, localRow localTreePts[k]! ∈ MulAction.orbit localH (localRow 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [h0]
        exact MulAction.mem_orbit_self _
      · obtain ⟨hpar, hcase⟩ := htree k hk hpos
        have hp := ih _ hpar (by omega)
        have hlt' := hlt _ (lt_trans hpar hk)
        rcases hcase with ⟨-, he⟩ | ⟨-, he⟩
        · rw [← he, ← localX_smul_localRow hlt']
          exact MulAction.mem_orbit_of_mem_orbit (⟨localX, localX_mem_H⟩ : localH) hp
        · rw [← he, ← localY_smul_localRow hlt']
          exact MulAction.mem_orbit_of_mem_orbit (⟨localY, localY_mem_H⟩ : localH) hp
  obtain ⟨k, hk, he⟩ := hcov i hi
  rw [← he]
  exact key k hk

theorem localOmega_eq_orbit : localOmega = MulAction.orbit localH (localRow 0) := by
  apply le_antisymm
  · rintro _ ⟨i, hi, rfl⟩
    exact localRow_mem_orbit hi
  · rintro _ ⟨⟨h, hh⟩, rfl⟩
    exact smul_mem_localOmega hh ⟨0, by norm_num, rfl⟩

theorem localX_smul_planeW : localX • (planeW : Set RowV) = planeW := by
  rw [← rowPlane_wKeyRow, ← rowPlane_imageKey isRows_localX_inv,
    native_matrix_facts.2.2.2.2.2.2.2.1]

theorem localY_smul_planeW : localY • (planeW : Set RowV) = planeW := by
  rw [← rowPlane_wKeyRow, ← rowPlane_imageKey isRows_localY_inv,
    native_matrix_facts.2.2.2.2.2.2.2.2]

theorem smul_planeW {h : J} (hh : h ∈ localH) : h • (planeW : Set RowV) = planeW := by
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact localX_smul_planeW
    · exact localY_smul_planeW
  | one => exact one_smul _ _
  | mul g g' _ _ ih ih' => rw [mul_smul, ih', ih]
  | inv g _ ih => rw [inv_smul_eq_iff, ih]

end CFSG.Sporadic.ThSchreier
