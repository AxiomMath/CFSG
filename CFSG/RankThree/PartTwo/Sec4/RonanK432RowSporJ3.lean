module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Invariant
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open CFSG.RankThree.PartTwo.KFacts.K426 (j3t_fusion j3tXA j3tXB j3tReps_spec)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section J3

set_option linter.unusedSectionVars false

theorem fixN_pow_of_pow_three {c : Equiv.Perm (Fin 6156)} (hc : c ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) : fixN (c ^ e) = fixN c := by
  rcases he with rfl | rfl
  · simp
  · have : c ^ 2 = c⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc)
    rw [this, fixN_inv]

theorem j3tXA_pow : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2

theorem j3tXB_pow : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2

theorem j3_class {x : Equiv.Perm (Fin 6156)} (hx : x ∈ j3P) (hxo : orderOf x = 3) :
    ∃ k ∈ j3P, ∃ c, (c = j3tXA ∨ c = j3tXB) ∧ ∃ e, (e = 1 ∨ e = 2) ∧ x = k * c ^ e * k⁻¹ ∧
      ((c = j3tXA ∧ fixN x = 36) ∨ (c = j3tXB ∧ fixN x = 0)) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := j3t_fusion hx hxo
  refine ⟨k, hk, c, hc, e, he, rfl, ?_⟩
  rcases hc with rfl | rfl
  · exact Or.inl ⟨rfl, by rw [fixN_conj, fixN_pow_of_pow_three j3tXA_pow he, fixN_XA]⟩
  · exact Or.inr ⟨rfl, by rw [fixN_conj, fixN_pow_of_pow_three j3tXB_pow he, fixN_XB]⟩

theorem j3_sep {x y : Equiv.Perm (Fin 6156)} (hx : x ∈ j3P) (hy : y ∈ j3P) (hxo : orderOf x = 3)
    (hyo : orderOf y = 3) (h : fixN x = fixN y) :
    ∃ k ∈ j3P, k * x * k⁻¹ = y ∨ k * x * k⁻¹ = y⁻¹ := by
  obtain ⟨k₁, hk₁, c₁, -, e₁, he₁, hx', hc₁⟩ := j3_class hx hxo
  obtain ⟨k₂, hk₂, c₂, -, e₂, he₂, hy', hc₂⟩ := j3_class hy hyo
  have hcc : c₁ = c₂ := by
    rcases hc₁ with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hc₂ with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · rfl
    · omega
    · omega
    · rfl
  subst hcc
  have hc3 : c₁ ^ 3 = 1 := by
    rcases hc₁ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact j3tXA_pow
    · exact j3tXB_pow
  refine ⟨k₂ * k₁⁻¹, j3P.mul_mem hk₂ (j3P.inv_mem hk₁), ?_⟩
  have hsq : c₁ ^ 2 = (c₁)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc3)
  have hinvsq : (c₁ ^ 2)⁻¹ = c₁ := by rw [hsq, inv_inv]
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · left
    rw [hx', hy']
    group
  · right
    rw [hx', hy', hsq]
    group
  · right
    rw [hx', hy', hsq]
    group
  · left
    rw [hx', hy']
    group

theorem inv_eq_sq_of_pow_three {G : Type} [Group G] {a : G} (h : a ^ 3 = 1) : a⁻¹ = a ^ 2 :=
  (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h)).symm

theorem Eel_zero : Eel 0 = 1 := by simp [Eel]

theorem Eel_nine : Eel 9 = Lp 2 := by simp [Eel]

theorem Eel_three : Eel 3 = Lp 4 := by simp [Eel]

theorem Eel_one : Eel 1 = Lp 0 := by simp [Eel]

theorem Eel_ten : Eel 10 = Lp 2 * Lp 0 := by simp [Eel]

theorem Eel_eighteen : Eel 18 = Lp 2 ^ 2 := by simp [Eel]

theorem Eel_two : Eel 2 = Lp 0 ^ 2 := by simp [Eel]

theorem j3_pair_B : orderOf (Lp 2) = 3 ∧ Lp 4 ^ 3 = 1 ∧ fixN (Lp 2) = 0 ∧ fixN (Lp 4) = 0 ∧
    Lp 2 * Lp 4 = Lp 4 * Lp 2 ∧ Lp 4 ∉ Subgroup.zpowers (Lp 2) := by
  have h2 : Lp 2 ^ 3 = 1 := Lp_pow3 (by norm_num)
  have hne : Lp 2 ≠ 1 := by
    intro h
    have := Eel_ne (m := 9) (m' := 0) (by norm_num) (by norm_num)
    rw [Eel_nine, Eel_zero] at this
    exact this h
  refine ⟨orderOf_eq_prime h2 hne, Lp_pow3 (by norm_num), ?_, ?_, Lp_comm_24, ?_⟩
  · rw [← Eel_nine]
    simpa using fixN_Eel (m := 9) (by norm_num) (by norm_num)
  · rw [← Eel_three]
    simpa using fixN_Eel (m := 3) (by norm_num) (by norm_num)
  · intro hmem
    rcases mem_zpowers_cases_of_pow_three h2 hmem with h | h | h
    · have := Eel_ne (m := 3) (m' := 0) (by norm_num) (by norm_num)
      rw [Eel_three, Eel_zero] at this
      exact this h
    · have := Eel_ne (m := 9) (m' := 3) (by norm_num) (by norm_num)
      rw [Eel_nine, Eel_three] at this
      exact this h.symm
    · rw [inv_eq_sq_of_pow_three h2, ← Eel_eighteen] at h
      have := Eel_ne (m := 18) (m' := 3) (by norm_num) (by norm_num)
      rw [Eel_three] at this
      exact this h.symm

theorem j3_pair_A : orderOf (Lp 0) = 3 ∧ (Lp 2 * Lp 0) ^ 3 = 1 ∧ fixN (Lp 0) = 36 ∧
    fixN (Lp 2 * Lp 0) = 36 ∧ Lp 0 * (Lp 2 * Lp 0) = (Lp 2 * Lp 0) * Lp 0 ∧
    Lp 2 * Lp 0 ∉ Subgroup.zpowers (Lp 0) := by
  have h0 : Lp 0 ^ 3 = 1 := Lp_pow3 (by norm_num)
  have h2 : Lp 2 ^ 3 = 1 := Lp_pow3 (by norm_num)
  have hne : Lp 0 ≠ 1 := by
    intro h
    have := Eel_ne (m := 1) (m' := 0) (by norm_num) (by norm_num)
    rw [Eel_one, Eel_zero] at this
    exact this h
  have hcomm : Lp 2 * Lp 0 = Lp 0 * Lp 2 := Lp_comm_20
  refine ⟨orderOf_eq_prime h0 hne, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(show Commute (Lp 2) (Lp 0) from hcomm).mul_pow, h2, h0, one_mul]
  · rw [← Eel_one]
    simpa using fixN_Eel (m := 1) (by norm_num) (by norm_num)
  · rw [← Eel_ten]
    simpa using fixN_Eel (m := 10) (by norm_num) (by norm_num)
  · calc Lp 0 * (Lp 2 * Lp 0) = (Lp 0 * Lp 2) * Lp 0 := by rw [mul_assoc]
      _ = (Lp 2 * Lp 0) * Lp 0 := by rw [hcomm]
  · intro hmem
    rcases mem_zpowers_cases_of_pow_three h0 hmem with h | h | h
    · have := Eel_ne (m := 10) (m' := 0) (by norm_num) (by norm_num)
      rw [Eel_ten, Eel_zero] at this
      exact this h
    · have := Eel_ne (m := 10) (m' := 1) (by norm_num) (by norm_num)
      rw [Eel_ten, Eel_one] at this
      exact this h
    · rw [inv_eq_sq_of_pow_three h0, ← Eel_two] at h
      have := Eel_ne (m := 10) (m' := 2) (by norm_num) (by norm_num)
      rw [Eel_ten] at this
      exact this h

theorem listRow_j3P : ListRow j3P := by
  refine listRow_of_invariant (fun x : j3P => fixN (x : Equiv.Perm (Fin 6156))) ?_ ?_ ?_
  · intro k x
    simp [fixN_conj]
  · intro x y hx hy h
    obtain ⟨k, hk, hk'⟩ := j3_sep x.2 y.2 (by rwa [Subgroup.orderOf_coe]) (by rwa [Subgroup.orderOf_coe]) h
    refine ⟨⟨k, hk⟩, ?_⟩
    rcases hk' with h' | h'
    · exact Or.inl (Subtype.ext (by simpa using h'))
    · exact Or.inr (Subtype.ext (by simpa using h'))
  · intro z hz
    obtain ⟨-, -, c, -, -, -, -, hc⟩ := j3_class z.2 (by rwa [Subgroup.orderOf_coe])
    rcases hc with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨ha, hb, hfa, hfb, hab, hn⟩ := j3_pair_A
      refine ⟨⟨Lp 0, Lp_mem (Or.inr (Or.inr rfl))⟩,
        ⟨Lp 2 * Lp 0, j3P.mul_mem (Lp_mem (Or.inl rfl)) (Lp_mem (Or.inr (Or.inr rfl)))⟩,
        ?_, Subtype.ext (by simpa using hb), ?_, ?_, Subtype.ext (by simpa using hab), ?_⟩
      · rw [← Subgroup.orderOf_coe]; exact ha
      · show fixN (Lp 0) = fixN (z : Equiv.Perm (Fin 6156)); rw [hfa, h]
      · show fixN (Lp 2 * Lp 0) = fixN (z : Equiv.Perm (Fin 6156)); rw [hfb, h]
      · intro hmem
        apply hn
        have := (Subgroup.mem_zpowers_iff.mp hmem)
        obtain ⟨i, hi⟩ := this
        refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
        have := congrArg (fun t : j3P => (t : Equiv.Perm (Fin 6156))) hi
        simpa using this
    · obtain ⟨ha, hb, hfa, hfb, hab, hn⟩ := j3_pair_B
      refine ⟨⟨Lp 2, Lp_mem (Or.inl rfl)⟩, ⟨Lp 4, Lp_mem (Or.inr (Or.inl rfl))⟩,
        ?_, Subtype.ext (by simpa using hb), ?_, ?_, Subtype.ext (by simpa using hab), ?_⟩
      · rw [← Subgroup.orderOf_coe]; exact ha
      · show fixN (Lp 2) = fixN (z : Equiv.Perm (Fin 6156)); rw [hfa, h]
      · show fixN (Lp 4) = fixN (z : Equiv.Perm (Fin 6156)); rw [hfb, h]
      · intro hmem
        apply hn
        have := (Subgroup.mem_zpowers_iff.mp hmem)
        obtain ⟨i, hi⟩ := this
        refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
        have := congrArg (fun t : j3P => (t : Equiv.Perm (Fin 6156))) hi
        simpa using this

end J3

section J3Row

set_option linter.unusedSectionVars false

theorem listRow_j3 : ListRow NativeSporadic.J3 :=
  ListRow.of_mulEquiv j3PermEquiv.symm listRow_j3P

theorem outerRow_j3 : OuterRow NativeSporadic.J3 :=
  outerRow_of_not_three_dvd_outer not_three_dvd_outer_J3

theorem row_carrier_j3 : RowOf (NativeSporadic.Carrier .J3) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.J3) e.symm ⟨listRow_j3, outerRow_j3⟩

end J3Row

end CFSG.RankThree.PartTwo.Sec4.RonanK432
