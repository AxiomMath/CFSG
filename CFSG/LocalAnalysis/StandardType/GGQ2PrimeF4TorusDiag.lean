module

public import CFSG.Fischer.F4
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU torusVec torusElt diagU ent)

private theorem exists_f4_unit_of_order_three : ∃ u : F4ˣ, u ^ 3 = 1 ∧ u ≠ 1 ∧ u ^ 2 ≠ 1 := by
  have h1 : (F4.ω : F4) ^ 3 = 1 := by decide
  have h2 : (F4.ω : F4) ≠ 1 := by decide
  have h3 : (F4.ω : F4) ^ 2 ≠ 1 := by decide
  refine ⟨Units.mk0 F4.ω (by decide), Units.ext (by simpa using h1), fun h => h2 ?_,
    fun h => h3 ?_⟩
  · simpa using congrArg Units.val h
  · simpa using congrArg Units.val h

private theorem exists_fin_six_avoiding_four (i j k l : Fin 6) :
    ∃ a : Fin 6, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ a ≠ l := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j, k, l} : Finset (Fin 6))) (t := Finset.univ) (by
      have := Finset.card_le_four (a := i) (b := j) (c := k) (d := l)
      simp only [Finset.card_univ, Fintype.card_fin]
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2⟩

private theorem exists_torus_vec_violating_relation (i j k l : Fin 6) (hij : i ≠ j) (hlj : l ≠ j) :
    ∃ v ∈ torusVec 3 6 F4, v j * v k ≠ v i * v l := by
  obtain ⟨u, hu3, hu1, hu2⟩ := exists_f4_unit_of_order_three
  obtain ⟨a, hai, haj, hak, hal⟩ := exists_fin_six_avoiding_four i j k l
  refine ⟨torusElt j a u, CFSG.RankThree.PartOne.KFU.torusElt_mem haj.symm hu3, ?_⟩
  rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_left haj.symm,
    CFSG.RankThree.PartOne.KFU.torusElt_apply_other hij hai.symm,
    CFSG.RankThree.PartOne.KFU.torusElt_apply_other hlj hal.symm]
  by_cases hkj : k = j
  · subst hkj
    rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_left haj.symm, mul_one, ← sq]
    exact hu2
  · rw [CFSG.RankThree.PartOne.KFU.torusElt_apply_other hkj hak.symm, mul_one, mul_one]
    exact hu1

private theorem torus_entry_relation {w : GL (Fin 6) F4}
    (hw : ∀ d ∈ torusSU 3 6 F4, ∃ c : F4,
      ((w * d * w⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • (d : Matrix (Fin 6) (Fin 6) F4))
    {v : Fin 6 → F4ˣ} (hv : v ∈ torusVec 3 6 F4) {i j k l : Fin 6}
    (hij : ent w i j ≠ 0) (hkl : ent w k l ≠ 0) : v j * v k = v i * v l := by
  obtain ⟨c, hc⟩ := hw (diagU v) (CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mpr
    ⟨v, hv.1, hv.2, rfl⟩)
  have hwd : ((w * diagU v : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (c • ((diagU v : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) *
        (w : Matrix (Fin 6) (Fin 6) F4) := by
    rw [← hc, ← Units.val_mul, inv_mul_cancel_right]
  have key : ∀ {i j : Fin 6}, ent w i j ≠ 0 → (v j : F4) = c * v i := by
    intro i j hij
    have h1 := congrFun (congrFun hwd i) j
    simp only [Units.val_mul, CFSG.RankThree.PartOne.KFU.diagU_val, Matrix.mul_diagonal,
      Matrix.smul_mul, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at h1
    exact mul_left_cancel₀ hij (h1.trans (by ring))
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, key hij, key hkl]
  ring

theorem isDiag_of_conj_torusSU_eq_smul {w : GL (Fin 6) F4}
    (hw : ∀ d ∈ torusSU 3 6 F4, ∃ c : F4,
      ((w * d * w⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • (d : Matrix (Fin 6) (Fin 6) F4)) :
    (w : Matrix (Fin 6) (Fin 6) F4).IsDiag := by
  intro i j hij
  by_contra h0
  obtain ⟨l, hl⟩ := exists_ne j
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartOne.KFU.exists_ent_ne_zero w l
  obtain ⟨v, hv, hne⟩ := exists_torus_vec_violating_relation i j k l hij hl
  exact hne (torus_entry_relation hw hv h0 hk)

end CFSG.GGQ2Prime
