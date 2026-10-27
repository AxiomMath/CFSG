
module

public import CFSG.Sporadic.Co2Cert.Cert
public import CFSG.Sporadic.HS.SmallF2Spec
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Cert

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

abbrev Co2V : Type := Fin 22 → ZMod 2

noncomputable abbrev co2A1 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed1

noncomputable abbrev co2A2 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co2Seed2

theorem co2SeedA_eq : CFSG.Sporadic.Co2.Native.seedA = Blueprint.NativeSporadic.Co2Seed1 := by
  unfold CFSG.Sporadic.Co2.Native.seedA Blueprint.NativeSporadic.Co2Seed1
  rfl

theorem co2SeedB_eq : CFSG.Sporadic.Co2.Native.seedB = Blueprint.NativeSporadic.Co2Seed2 := by
  unfold CFSG.Sporadic.Co2.Native.seedB Blueprint.NativeSporadic.Co2Seed2
  rfl

theorem rowsMatrix_co2RowsA : rowsMatrix 22 co2RowsA = co2A1 := by
  rw [co2RowsA, rowsMatrix_rowsOfPayload, co2SeedA_eq]

theorem rowsMatrix_co2RowsB : rowsMatrix 22 co2RowsB = co2A2 := by
  rw [co2RowsB, rowsMatrix_rowsOfPayload, co2SeedB_eq]

theorem co2PackedVecs_get {i : ℕ} (hi : i < 2300) :
    co2PackedVecs[i]! = packVec (co2Rec.vectors.getD i []) := by
  have hl : i < co2Rec.vectors.length := by rw [co2Shape.vectors_length]; exact hi
  rw [co2PackedVecs, getElem!_pos _ i (by simpa using hl)]
  simp [List.getElem?_eq_getElem hl]

theorem natCast_zmod_two (n : ℕ) : (n : ZMod 2) = if (n % 2 == 1) = true then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem co2Vec_eq
    {i : ℕ} (hi : i < 2300) : co2Vec i = toVecD 22 co2PackedVecs[i]! := by
  funext j
  rw [co2PackedVecs_get hi, packVec, toVecD_ofBits]
  exact natCast_zmod_two _

theorem co2BasisList_lt : ∀ t < 22, co2BasisList.getD t 0 < 2300 := by
  decide

theorem co2BasisRows_get {t : ℕ} (ht : t < 22) :
    co2BasisRows[t]! = co2PackedVecs[co2BasisList.getD t 0]! := by
  have hl : t < co2BasisList.length := by simpa [co2BasisList] using ht
  rw [co2BasisRows, getElem!_pos _ t (by simpa using hl)]
  simp [List.getElem?_eq_getElem hl]

theorem co2X_eq_range : co2X = Set.range fun i : Fin 2300 => co2Vec i := by
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem co2X_finite : co2X.Finite := by
  rw [co2X_eq_range]
  exact Set.finite_range _

@[expose] noncomputable def co2GLLin : GL (Fin 22) (ZMod 2) ≃* (Co2V ≃ₗ[ZMod 2] Co2V) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem co2GLLin_apply (g : GL (Fin 22) (ZMod 2)) (v : Co2V) :
    co2GLLin g v = (g : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ v := by
  simp [co2GLLin, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin]

@[expose] noncomputable def co2GLLinHom : GL (Fin 22) (ZMod 2) →* (Co2V ≃ₗ[ZMod 2] Co2V) := co2GLLin

theorem co2GLLinHom_apply (g : GL (Fin 22) (ZMod 2)) : co2GLLinHom g = co2GLLin g := rfl

theorem co2GLLinHom_injective : Function.Injective co2GLLinHom := co2GLLin.injective

theorem co2P_eq : co2P = Subgroup.closure (Set.range fun k : Fin 2 => co2Gen k) := by
  rw [co2P]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; rfl
    · right; rfl

end CFSG.Sporadic.Co2Cert
