module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSemilin

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {F : Type} [Field F]

theorem mem_Q3_zero_iff {M : Matrix.SpecialLinearGroup (Fin 3) F} :
    M ∈ Q3 F 0 ↔
      (M : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  constructor
  · intro h
    have h' : M ∈ stabilizer (flagSpace 3 F 1) := h
    exact ⟨stabilizer_entries h' (k := 1) (l := 0) (by decide) (by decide),
      stabilizer_entries h' (k := 2) (l := 0) (by decide) (by decide)⟩
  · rintro ⟨h1, h2⟩
    show M ∈ stabilizer (flagSpace 3 F 1)
    refine mem_stabilizer_of_entries fun k l hk hl => ?_
    fin_cases k <;> fin_cases l <;> simp at hk hl ⊢ <;> assumption

theorem mem_Q3_one_iff {M : Matrix.SpecialLinearGroup (Fin 3) F} :
    M ∈ Q3 F 1 ↔
      (M : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (M : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  constructor
  · intro h
    have h' : M ∈ stabilizer (flagSpace 3 F 2) := h
    exact ⟨stabilizer_entries h' (k := 2) (l := 0) (by decide) (by decide),
      stabilizer_entries h' (k := 2) (l := 1) (by decide) (by decide)⟩
  · rintro ⟨h1, h2⟩
    show M ∈ stabilizer (flagSpace 3 F 2)
    refine mem_stabilizer_of_entries fun k l hk hl => ?_
    fin_cases k <;> fin_cases l <;> simp at hk hl ⊢ <;> assumption

theorem not_solvable_sl2 [Finite F] (hK : ∃ s : Finset F, s.card = 4) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro hsolv
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := F) hK
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hder : ∀ k, derivedSeries (Matrix.SpecialLinearGroup (Fin 2) F) k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero _
    | succ k ih =>
      rw [derivedSeries_succ, ih]
      exact Group.isPerfect_def.mp hperf
  rw [hder n] at hn
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hnt : t ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [← hn]; trivial
  have h1 : t = 1 := Subgroup.mem_bot.mp hnt
  have := congrFun (congrFun (congrArg Subtype.val h1) 0) 1
  simp [t] at this

theorem not_solvable_of_projQ3_le [Finite F] (hK : ∃ s : Finset F, s.card = 4) (j : Fin 2)
    {N : Subgroup (projectiveSL 3 F)} (hN : (Q3 F j).map (proj 3 F) ≤ N) :
    ¬ Group.IsSolvable ↥N := by
  intro hsolv
  let φ : ↥(Q3 F j) →* ↥N :=
    ((proj 3 F).comp (Q3 F j).subtype).codRestrict _ (fun x => hN ⟨x, x.2, rfl⟩)
  have hkerc : ∀ a b : ↥φ.ker, a * b = b * a := by
    intro a b
    have ha : (a : ↥(Q3 F j)) ∈ φ.ker := a.2
    have h1 : proj 3 F ((a : ↥(Q3 F j)) : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
      exact this
    have hc := scalars_le_center 3 F (proj_eq_one_iff.mp h1)
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hc _).symm
  have hkerS : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_comm hkerc
  have hQ : Group.IsSolvable ↥(Q3 F j) :=
    Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])
  have hP : Group.IsSolvable ↥(perfectCore (Q3 F j)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (perfectCore_le (Q3 F j))) (Subgroup.inclusion_injective _)
  have hS : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective (blk3_surjective hK j)
  exact not_solvable_sl2 hK hS

end CFSG.Quasithin.H13.F431.L3.P3
