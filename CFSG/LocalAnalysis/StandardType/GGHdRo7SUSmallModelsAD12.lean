module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD11

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_q9_single_coord (σ : Equiv.Perm (Fin 9)) (a : Fin 8) (c : ZMod 3)
    (k : Fin 8) :
    hdRo7SmAAux_q9 σ (Pi.single a c) k =
      (if σ (Fin.castSucc a) = Fin.castSucc k then c else 0) -
        (if σ (Fin.castSucc a) = Fin.last 8 then c else 0) := by
  change hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 (Pi.single a c))) k = _
  change (coordPerm 3 8 σ (hdRo7SmAAux_ext9 (Pi.single a c))) (Fin.castSucc k) -
    (coordPerm 3 8 σ (hdRo7SmAAux_ext9 (Pi.single a c))) (Fin.last 8) = _
  rw [hdRo7SmAAux_ext9_single]
  simp only [coordPerm_apply, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]


theorem hdRo7SmAAux_single_sub (a b j j' : Fin 8) (hjj : j ≠ j')
    (h : (Pi.single a (1 : ZMod 3) : SMV 8) - (Pi.single b (1 : ZMod 3) : SMV 8) =
      (Pi.single j (1 : ZMod 3) : SMV 8) - (Pi.single j' (1 : ZMod 3) : SMV 8)) :
    a = j := by
  revert a b j j'
  decide

theorem hdRo7SmAAux_exists_two_good (σ : Equiv.Perm (Fin 9)) :
    ∃ j j' : Fin 8, j ≠ j' ∧ σ (Fin.castSucc j) ≠ Fin.last 8 ∧
      σ (Fin.castSucc j') ≠ Fin.last 8 := by
  by_cases h0 : σ (Fin.castSucc 0) = Fin.last 8
  · by_cases h1 : σ (Fin.castSucc 1) = Fin.last 8
    · exact absurd (σ.injective (h0.trans h1.symm)) (by decide)
    · refine ⟨1, 2, by decide, h1, ?_⟩
      intro hh
      exact absurd (σ.injective (hh.trans h0.symm)) (by decide)
  · by_cases h1 : σ (Fin.castSucc 1) = Fin.last 8
    · refine ⟨0, 2, by decide, h0, ?_⟩
      intro hh
      exact absurd (σ.injective (hh.trans h1.symm)) (by decide)
    · exact ⟨0, 1, by decide, h0, h1⟩

theorem hdRo7SmAAux_d9Hom_injective : Function.Injective hdRo7SmAAux_d9Hom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ i : Fin 7, hdRo7SmAAux_q9 σ (hdRo7SmAAux_delEmbed (Pi.single i (1 : ZMod 3))) =
      hdRo7SmAAux_delEmbed (Pi.single i (1 : ZMod 3)) := by
    intro i
    have h1 : hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ
        (hdRo7SmAAux_delEmbed (Pi.single i 1))) = Pi.single i 1 := by
      have h2 := congrArg (fun f : SMGL 7 => f (Pi.single i 1)) hσ
      simpa [hdRo7SmAAux_d9Hom, hdRo7SmAAux_d9] using h2
    have h3 : hdRo7SmAAux_q9 σ (hdRo7SmAAux_delEmbed (Pi.single i 1)) =
        hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj (hdRo7SmAAux_q9 σ
          (hdRo7SmAAux_delEmbed (Pi.single i 1)))) :=
      (hdRo7SmAAux_delEmbed_proj _ (hdRo7SmAAux_q9_sum_zero σ _
        (hdRo7SmAAux_delEmbed_sum_zero _))).symm
    rw [h3, h1]
  obtain ⟨c, hc⟩ : ∃ c : SMV 8, ∀ j : Fin 8,
      hdRo7SmAAux_q9 σ (Pi.single j (1 : ZMod 3)) = (Pi.single j (1 : ZMod 3) : SMV 8) + c := by
    refine ⟨hdRo7SmAAux_q9 σ (Pi.single (Fin.last 7) (1 : ZMod 3)) -
      (Pi.single (Fin.last 7) (1 : ZMod 3) : SMV 8), ?_⟩
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have h3 := hfix i
      rw [hdRo7SmAAux_delEmbed_single i 1, map_sub] at h3
      change hdRo7SmAAux_q9 σ (Pi.single (Fin.castSucc i) 1) =
        (Pi.single (Fin.castSucc i) (1 : ZMod 3) : SMV 8) +
          (hdRo7SmAAux_q9 σ (Pi.single (Fin.last 7) 1) -
            (Pi.single (Fin.last 7) (1 : ZMod 3) : SMV 8))
      linear_combination (norm := abel) h3
    · abel
  have hgood : ∀ j : Fin 8, ∀ hj : σ (Fin.castSucc j) ≠ Fin.last 8,
      ∃ m : Fin 8, σ (Fin.castSucc j) = Fin.castSucc m ∧
        hdRo7SmAAux_q9 σ (Pi.single j (1 : ZMod 3)) = (Pi.single m (1 : ZMod 3) : SMV 8) := by
    intro j hj
    have hlt : (σ (Fin.castSucc j)).val < 8 := by
      have h1 := (σ (Fin.castSucc j)).isLt
      have h2 : (σ (Fin.castSucc j)).val ≠ 8 := by
        intro hh
        exact hj (Fin.ext hh)
      omega
    let m : Fin 8 := ⟨(σ (Fin.castSucc j)).val, hlt⟩
    have hm : σ (Fin.castSucc j) = Fin.castSucc m := Fin.ext rfl
    refine ⟨m, hm, ?_⟩
    ext k
    rw [hdRo7SmAAux_q9_single_coord]
    simp only [hm, Pi.single_apply, Fin.castSucc_inj, eq_comm]
    rw [if_neg (Ne.symm (Fin.castSucc_ne_last m))]
    ring
  obtain ⟨j, j', hjj, hj, hj'⟩ := hdRo7SmAAux_exists_two_good σ
  obtain ⟨mj, hmj, hqj⟩ := hgood j hj
  obtain ⟨mj', hmj', hqj'⟩ := hgood j' hj'
  have e1 : (Pi.single mj (1 : ZMod 3) : SMV 8) = (Pi.single j (1 : ZMod 3) : SMV 8) + c := by
    rw [← hqj, hc j]
  have e2 : (Pi.single mj' (1 : ZMod 3) : SMV 8) = (Pi.single j' (1 : ZMod 3) : SMV 8) + c := by
    rw [← hqj', hc j']
  have hsub : (Pi.single mj (1 : ZMod 3) : SMV 8) - (Pi.single mj' (1 : ZMod 3) : SMV 8) =
      (Pi.single j (1 : ZMod 3) : SMV 8) - (Pi.single j' (1 : ZMod 3) : SMV 8) := by
    rw [e1, e2]; abel
  have hmj_eq : mj = j := hdRo7SmAAux_single_sub mj mj' j j' hjj hsub
  have hc0 : c = 0 := by
    have h : (Pi.single j (1 : ZMod 3) : SMV 8) + c = (Pi.single j (1 : ZMod 3) : SMV 8) := by
      rw [← e1, hmj_eq]
    linear_combination (norm := abel) h
  have hfix8 : ∀ i : Fin 8, σ (Fin.castSucc i) = Fin.castSucc i := by
    intro i
    by_cases hi : σ (Fin.castSucc i) = Fin.last 8
    · exfalso
      have h4 : hdRo7SmAAux_q9 σ (Pi.single i (1 : ZMod 3)) = -(1 : SMV 8) := by
        ext k
        simp only [hdRo7SmAAux_q9_single_coord]
        rw [hi]
        rw [if_neg (Ne.symm (Fin.castSucc_ne_last k))]
        simp [Pi.single_apply]
      have h5 : (Pi.single i (1 : ZMod 3) : SMV 8) = -(1 : SMV 8) := by
        have h := (hc i).symm.trans h4
        rw [hc0, add_zero] at h
        exact h
      exact absurd (by simpa [Pi.single_apply] using congrFun h5 i) (by decide)
    · obtain ⟨m, hm, hq⟩ := hgood i hi
      have h5 : m = i := by
        have h : (Pi.single m (1 : ZMod 3) : SMV 8) = (Pi.single i (1 : ZMod 3) : SMV 8) := by
          rw [← hq, hc i, hc0, add_zero]
        have h1 := congrFun h i
        by_cases hm' : i = m
        · exact hm'.symm
        · exfalso
          simp only [Pi.single_apply, if_neg hm', if_pos rfl] at h1
          revert h1; decide
      rw [hm, h5]
  apply Equiv.ext
  intro x
  rcases Fin.eq_castSucc_or_eq_last x with ⟨i, rfl⟩ | rfl
  · exact hfix8 i
  · rcases Fin.eq_castSucc_or_eq_last (σ (Fin.last 8)) with ⟨i, hi⟩ | hlast
    · exfalso
      have : σ (Fin.last 8) = σ (Fin.castSucc i) := hi.trans (hfix8 i).symm
      exact (Fin.castSucc_ne_last i) (σ.injective this.symm)
    · exact hlast
end CFSG.StandardType.HdRo7SU.Small
