module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Fischer.F4
public import Mathlib

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (diagU diagU_val torusSU mem_torusSU_iff)

variable {K L : Type} [Field K] [Field L]

@[expose] noncomputable def ringEquivF4 [Finite K] (hK : Nat.card K = 4) : K ≃+* F4 :=
  letI : Fintype K := Fintype.ofFinite K
  FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, F4.card])

theorem map_diagU {n : ℕ} (e : K →+* L) (v : Fin n → Kˣ) :
    Matrix.GeneralLinearGroup.map e (diagU v) =
      diagU (fun i => Units.map (e : K →* L) (v i)) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_map_apply, diagU_val, diagU_val,
    Matrix.diagonal_map (map_zero e)]
  rfl

theorem glMap_symm_glMap (e : K ≃+* L) (d : GL (Fin 6) K) :
    Matrix.GeneralLinearGroup.map (e.symm : L →+* K)
      (Matrix.GeneralLinearGroup.map (e : K →+* L) d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.val_map_apply]
  ext i j
  simp

theorem glMap_glMap_symm (e : K ≃+* L) (d : GL (Fin 6) L) :
    Matrix.GeneralLinearGroup.map (e : K →+* L)
      (Matrix.GeneralLinearGroup.map (e.symm : L →+* K) d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.val_map_apply]
  ext i j
  simp

theorem mem_torusSU_map_iff (e : K ≃+* L) (d : GL (Fin 6) K) :
    d ∈ torusSU 3 6 K ↔ Matrix.GeneralLinearGroup.map (e : K →+* L) d ∈ torusSU 3 6 L := by
  constructor
  · intro hd
    obtain ⟨v, hv3, hvprod, rfl⟩ := mem_torusSU_iff.mp hd
    rw [map_diagU]
    refine mem_torusSU_iff.mpr ⟨_, ?_, ?_, rfl⟩
    · intro i
      rw [← map_pow, hv3 i, map_one]
    · rw [← map_prod, hvprod, map_one]
  · intro hd
    obtain ⟨u, hu3, huprod, hu⟩ := mem_torusSU_iff.mp hd
    rw [← glMap_symm_glMap e d, ← hu, map_diagU]
    refine mem_torusSU_iff.mpr ⟨_, ?_, ?_, rfl⟩
    · intro i
      rw [← map_pow, hu3 i, map_one]
    · rw [← map_prod, huprod, map_one]

end CFSG.StandardType.USixTwo

end
