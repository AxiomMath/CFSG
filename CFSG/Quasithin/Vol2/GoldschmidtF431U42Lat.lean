module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Cover

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

theorem Dj_zero : Dj 0 = 1 := by
  apply Subtype.ext
  have h : DW.getD 0 [] = [] := chkLat_spec.2.1
  show wordP (DW.getD 0 []) = 1
  rw [h]
  rfl

theorem D1_mem_P1 : Dj 1 ∈ P1 := by
  rw [mem_P1_iff]
  apply Fin.ext
  rw [← (repL_Dj 1).2 0]
  exact chkLat_spec.2.2.1

theorem D1_not_mem_P2 : Dj 1 ∉ P2 := by
  rw [mem_P2_iff]
  intro h
  have h1 := chkLat_spec.2.2.2.1
  rw [L0S, image_lineSet (repL_Dj 1) L0_lt] at h
  exact lineSet_ne_of_sameSet_false h1 h

theorem D2_mem_P2 : Dj 2 ∈ P2 := by
  rw [mem_P2_iff, L0S, image_lineSet (repL_Dj 2) L0_lt,
    lineSet_eq_of_sameSet chkLat_spec.2.2.2.2.1]

theorem D2_not_mem_P1 : Dj 2 ∉ P1 := by
  rw [mem_P1_iff]
  intro h
  apply chkLat_spec.2.2.2.2.2.1
  show (DL 2).getD ((0 : Fin 45) : ℕ) 0 = 0
  exact ((repL_Dj 2).2 0).trans (congrArg Fin.val h)

@[expose] def alphaE (j a : ℕ) : Y := if a < 5 then gTY a else if a == 5 then c3Y else Dj j

theorem repL_alphaE (j a : ℕ) :
    RepL (alphaL j a) ((alphaE j a : Y) : P45) := by
  unfold alphaL alphaE
  split_ifs
  · exact repL_gTY a
  · exact repL_c3
  · exact repL_Dj j

@[expose] def wordA (j : ℕ) (w : List ℕ) : Y := (w.map (alphaE j)).prod

theorem repL_wordA (j : ℕ) (w : List ℕ) :
    RepL (evalAl j w) ((wordA j w : Y) : P45) := by
  induction w with
  | nil => exact repL_one 45
  | cons a w ih =>
    have : ((wordA j (a :: w) : Y) : P45) = ((alphaE j a : Y) : P45) * ((wordA j w : Y) : P45) := by
      simp [wordA]
    rw [this]
    exact repL_mul (repL_alphaE j a) ih

theorem wordA_mem {H : Subgroup Y} (hB : B0 ≤ H) (j : ℕ)
    (hj : Dj j ∈ H) (w : List ℕ) : wordA j w ∈ H := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  unfold alphaE
  split_ifs
  · exact hB (gTY_mem_B0 a ‹_›)
  · exact hB c3_mem_B0
  · exact hj

theorem far_gen {H : Subgroup Y} (hB : B0 ≤ H) {j : ℕ} (hj3 : 3 ≤ j)
    (hj8 : j < 8) (hD : Dj j ∈ H) : Dj 1 ∈ H ∧ Dj 2 ∈ H := by
  have h := chkLat_spec.2.2.2.2.2.2.1 (j - 3) (by omega)
  have e : j - 3 + 3 = j := by omega
  rw [e] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have : wordA j (farW.getD j ([], [])).1 = Dj 1 :=
      Subtype.ext (eq_of_repL (repL_wordA j _) (h1 ▸ repL_Dj 1))
    rw [← this]
    exact wordA_mem hB j hD _
  · have : wordA j (farW.getD j ([], [])).2 = Dj 2 :=
      Subtype.ext (eq_of_repL (repL_wordA j _) (h2 ▸ repL_Dj 2))
    rw [← this]
    exact wordA_mem hB j hD _

end CFSG.Quasithin.H13.F431.U42
