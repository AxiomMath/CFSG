module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LieType.Steinberg.Minuscule.RootOps

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule

section Coordinates

variable {L : Type} [Field L]

theorem rootOp_single_coord (j : Fin Tag.E6.rank) (v : Fin e6Data.d →₀ L) (b : Fin e6Data.d) :
    (e6Data.rootOp L (Pi.single j 1) v) b =
      if e6Data.wt b j = 1 then v (e6Data_valid.sRefl j b) else 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
    split_ifs <;> simp
  | single c r =>
    have e : (Finsupp.single c r : Fin e6Data.d →₀ L) = r • Finsupp.single c 1 := by simp
    rw [e, map_smul, Finsupp.smul_apply, e6Data_valid.rootOp_single_apply, Finsupp.smul_apply]
    rcases eq_or_ne (e6Data_valid.sRefl j c) b with h | h
    · subst h
      have h1 := e6Data_valid.wt_sRefl_self j c
      simp only [e6Data_valid.sRefl_sRefl, Finsupp.single_eq_same, h1]
      by_cases hc : e6Data.wt c j = -1
      · simp [hc]
      · have : ¬ -e6Data.wt c j = 1 := fun h' => hc (by omega)
        simp [hc, this]
    · have h' : c ≠ e6Data_valid.sRefl j b := fun h'' => h (by rw [h'', e6Data_valid.sRefl_sRefl])
      by_cases hc : e6Data.wt c j = -1
      · simp [hc, h, h']
      · simp [hc, h']

theorem rootOp_neg_single_coord (j : Fin Tag.E6.rank) (v : Fin e6Data.d →₀ L)
    (b : Fin e6Data.d) :
    (e6Data.rootOp L (-Pi.single j 1) v) b =
      if e6Data.wt b j = -1 then v (e6Data_valid.sRefl j b) else 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
    split_ifs <;> simp
  | single c r =>
    have e : (Finsupp.single c r : Fin e6Data.d →₀ L) = r • Finsupp.single c 1 := by simp
    rw [e, map_smul, Finsupp.smul_apply, e6Data_valid.rootOp_neg_single_apply, Finsupp.smul_apply]
    rcases eq_or_ne (e6Data_valid.sRefl j c) b with h | h
    · subst h
      have h1 := e6Data_valid.wt_sRefl_self j c
      simp only [e6Data_valid.sRefl_sRefl, Finsupp.single_eq_same, h1]
      by_cases hc : e6Data.wt c j = 1
      · simp [hc]
      · have : ¬ -e6Data.wt c j = -1 := fun h' => hc (by omega)
        simp [hc, this]
    · have h' : c ≠ e6Data_valid.sRefl j b := fun h'' => h (by rw [h'', e6Data_valid.sRefl_sRefl])
      by_cases hc : e6Data.wt c j = 1
      · simp [hc, h, h']
      · simp [hc, h']

theorem coef_commute_E {X : Module.End L (Fin e6Data.d →₀ L)} {j : Fin Tag.E6.rank}
    (h : Commute X (e6Data.rootOp L (Pi.single j 1))) (a b : Fin e6Data.d) :
    (if e6Data.wt a j = -1 then X (Finsupp.single (e6Data_valid.sRefl j a) 1) b else 0) =
      if e6Data.wt b j = 1 then X (Finsupp.single a 1) (e6Data_valid.sRefl j b) else 0 := by
  have h1 := congrArg (fun Y : Module.End L (Fin e6Data.d →₀ L) => Y (Finsupp.single a 1) b) h.eq
  simp only [Module.End.mul_apply] at h1
  rw [e6Data_valid.rootOp_single_apply, rootOp_single_coord] at h1
  by_cases ha : e6Data.wt a j = -1
  · simpa [ha] using h1
  · simpa [ha] using h1

theorem coef_commute_F {X : Module.End L (Fin e6Data.d →₀ L)} {j : Fin Tag.E6.rank}
    (h : Commute X (e6Data.rootOp L (-Pi.single j 1))) (a b : Fin e6Data.d) :
    (if e6Data.wt a j = 1 then X (Finsupp.single (e6Data_valid.sRefl j a) 1) b else 0) =
      if e6Data.wt b j = -1 then X (Finsupp.single a 1) (e6Data_valid.sRefl j b) else 0 := by
  have h1 := congrArg (fun Y : Module.End L (Fin e6Data.d →₀ L) => Y (Finsupp.single a 1) b) h.eq
  simp only [Module.End.mul_apply] at h1
  rw [e6Data_valid.rootOp_neg_single_apply, rootOp_neg_single_coord] at h1
  by_cases ha : e6Data.wt a j = 1
  · simpa [ha] using h1
  · simpa [ha] using h1

variable {X : Module.End L (Fin e6Data.d →₀ L)}
  (hx : ∀ j : Fin Tag.E6.rank, Commute X (e6Data.rootOp L (Pi.single j 1)))
  (hy : ∀ j : Fin Tag.E6.rank, Commute X (e6Data.rootOp L (-Pi.single j 1)))

include hx hy

theorem coef_eq_zero_of_wt_ne {j : Fin Tag.E6.rank} {a b : Fin e6Data.d}
    (hj : e6Data.wt a j ≠ e6Data.wt b j) : X (Finsupp.single a 1) b = 0 := by
  have L1 : e6Data.wt b j = -1 → e6Data.wt a j ≠ -1 → X (Finsupp.single a 1) b = 0 := by
    intro hb ha
    have h1 := coef_commute_E (hx j) a (e6Data_valid.sRefl j b)
    have h2 := e6Data_valid.wt_sRefl_self j b
    rw [e6Data_valid.sRefl_sRefl] at h1
    rw [hb] at h2
    have h3 : e6Data.wt (e6Data_valid.sRefl j b) j = 1 := by omega
    simp only [ha, h3, ↓reduceIte] at h1
    exact h1.symm
  have L2 : e6Data.wt a j = 1 → e6Data.wt b j ≠ 1 → X (Finsupp.single a 1) b = 0 := by
    intro ha hb
    have h1 := coef_commute_E (hx j) (e6Data_valid.sRefl j a) b
    have h2 := e6Data_valid.wt_sRefl_self j a
    rw [e6Data_valid.sRefl_sRefl] at h1
    rw [ha] at h2
    have h3 : e6Data.wt (e6Data_valid.sRefl j a) j = -1 := by omega
    simp only [hb, h3, ↓reduceIte] at h1
    exact h1
  have L3 : e6Data.wt b j = 1 → e6Data.wt a j ≠ 1 → X (Finsupp.single a 1) b = 0 := by
    intro hb ha
    have h1 := coef_commute_F (hy j) a (e6Data_valid.sRefl j b)
    have h2 := e6Data_valid.wt_sRefl_self j b
    rw [e6Data_valid.sRefl_sRefl] at h1
    rw [hb] at h2
    have h3 : e6Data.wt (e6Data_valid.sRefl j b) j = -1 := by omega
    simp only [ha, h3, ↓reduceIte] at h1
    exact h1.symm
  have L4 : e6Data.wt a j = -1 → e6Data.wt b j ≠ -1 → X (Finsupp.single a 1) b = 0 := by
    intro ha hb
    have h1 := coef_commute_F (hy j) (e6Data_valid.sRefl j a) b
    have h2 := e6Data_valid.wt_sRefl_self j a
    rw [e6Data_valid.sRefl_sRefl] at h1
    rw [ha] at h2
    have h3 : e6Data.wt (e6Data_valid.sRefl j a) j = 1 := by omega
    simp only [hb, h3, ↓reduceIte] at h1
    exact h1
  rcases e6Data_valid.wt_mem a j with hA | hA | hA <;>
    rcases e6Data_valid.wt_mem b j with hB | hB | hB
  · exact absurd (hA.trans hB.symm) hj
  · exact L4 hA (by omega)
  · exact L4 hA (by omega)
  · exact L1 hB (by omega)
  · exact absurd (hA.trans hB.symm) hj
  · exact L3 hB (by omega)
  · exact L2 hA (by omega)
  · exact L2 hA (by omega)
  · exact absurd (hA.trans hB.symm) hj

theorem coef_eq_zero_of_ne {a b : Fin e6Data.d} (hab : a ≠ b) : X (Finsupp.single a 1) b = 0 := by
  have : e6Data.wt a ≠ e6Data.wt b := fun h =>
    hab (e6Data_valid.wt_injective h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 this
  exact coef_eq_zero_of_wt_ne hx hy hj

omit hy in
theorem diag_sRefl {j : Fin Tag.E6.rank} {a : Fin e6Data.d} (ha : e6Data.wt a j = -1) :
    X (Finsupp.single (e6Data_valid.sRefl j a) 1) (e6Data_valid.sRefl j a) =
      X (Finsupp.single a 1) a := by
  have h1 := coef_commute_E (hx j) a (e6Data_valid.sRefl j a)
  have h2 := e6Data_valid.wt_sRefl_self j a
  rw [ha] at h2
  rw [e6Data_valid.sRefl_sRefl] at h1
  simpa [ha, h2] using h1

omit hx hy
  in
theorem exists_wt_neg_one_weyl_lt : ∀ a : Fin e6Data.d, a ≠ ⟨0, by decide⟩ →
    ∃ j : Fin Tag.E6.rank, e6Data.wt a j = -1 ∧ e6Data.weyl a j < a.val := by
  decide +kernel

include hx hy in
theorem eq_smul_one_of_commute :
    ∃ c : L, X = c • (1 : Module.End L (Fin e6Data.d →₀ L)) := by
  set a0 : Fin e6Data.d := ⟨0, by decide⟩ with ha0def
  have hconst : ∀ n : ℕ, ∀ a : Fin e6Data.d, a.val = n →
      X (Finsupp.single a 1) a = X (Finsupp.single a0 1) a0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a han
      by_cases ha0 : a = a0
      · rw [ha0]
      · obtain ⟨j, hj, hlt⟩ := exists_wt_neg_one_weyl_lt a ha0
        have e1 := diag_sRefl hx hj
        have hlt' : (e6Data_valid.sRefl j a).val < n := by
          rw [e6Data_valid.sRefl_val, ← han]
          exact hlt
        rw [← e1]
        exact ih _ hlt' _ rfl
  refine ⟨X (Finsupp.single a0 1) a0, ?_⟩
  refine Finsupp.lhom_ext fun a r => ?_
  have e : (Finsupp.single a r : Fin e6Data.d →₀ L) = r • Finsupp.single a 1 := by simp
  have hXa : X (Finsupp.single a 1) =
      (X (Finsupp.single a0 1) a0) • (Finsupp.single a 1 : Fin e6Data.d →₀ L) := by
    ext b
    by_cases hab : a = b
    · subst hab
      rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      exact hconst a.val a rfl
    · rw [coef_eq_zero_of_ne hx hy hab, Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hab),
        smul_zero]
  rw [e, map_smul, hXa, LinearMap.smul_apply, Module.End.one_apply, smul_comm]

end Coordinates

end CFSG.RankThree.PartOne.KE6
