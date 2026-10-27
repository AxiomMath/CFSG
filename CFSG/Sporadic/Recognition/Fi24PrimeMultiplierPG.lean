module

public import CFSG.Sporadic.Recognition.PresentedWords
public import CFSG.Sporadic.Recognition.Fi23MultiplierQ432
public import Certificates.Certificate24053
public import Certificates.Certificate9113

public section

namespace CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.PresentedWords
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_append evalWord_cons evalWord_nil)
open CFSG.YGroups (YGroup yGen ngen y432FGen y432FArrays rho432F rho432F_yGen rho432F_evalWord
  card_range_rho432F range_rho432F y432F_check y432FGen_eq F432_check F432Word)
open CFSG.Sporadic.Recognition.Fi23Multiplier (R432 r432EquivRange isPerfect_R432
  noPerfectDoubleCover_R432)

theorem card_PG10_le :
    Finite PG10 ∧ Nat.card PG10 ≤ 4089470473293004800 :=
  Certificates.certificate9113.2

theorem expandX_map {n : ℕ} (hn : 0 < n) (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < n) :
    expandX (w.map fun l => ((⟨l.1 % n, Nat.mod_lt _ hn⟩ : Fin n), l.2)) =
      w.flatMap expandSigned := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have h1 : l.1 < n := hw l List.mem_cons_self
    have h2 := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    simp only [List.map_cons, expandX, List.flatMap_cons] at h2 ⊢
    rw [h2, Nat.mod_eq_of_lt h1]

section Model


theorem y432FGen_mul_self (c : ℕ) : y432FGen c * y432FGen c = 1 := by
  have e : ∀ c, rho432F (yGen 4 3 2 c) = y432FGen c := by
    intro c
    by_cases hc : c < 10
    · exact rho432F_yGen hc
    · rw [CFSG.YGroups.yGen_of_le (by simp only [ngen]; omega), map_one,
        CFSG.YGroups.y432FGen, CFSG.YGroups.arrGen_of_le (by rw [y432F_check.1]; omega)]
  have h := congrArg rho432F (CFSG.YGroups.yGen_mul_self 4 3 2 c)
  rwa [map_mul, map_one, e] at h

noncomputable def img10 {n : ℕ} (j : Fin n) : Equiv.Perm (Fin 31671) :=
  evalWord y432FGen (x1Imgs.getD j.val [])

theorem wprod_img10 {n : ℕ} (w : List (Fin n × Bool)) :
    wprod img10 w = evalWord y432FGen (expandX w) := by
  induction w with
  | nil => simp [expandX, evalWord_nil]
  | cons l w ih =>
    rw [wprod_cons, ih]
    have : expandX (l :: w) = expandSigned (l.1.val, l.2) ++ expandX w := by
      simp [expandX]
    rw [this, evalWord_append]
    congr 1
    obtain ⟨j, b⟩ := l
    cases b
    · simp only [expandSigned, Bool.false_eq_true, ↓reduceIte, img10]
      rw [CFSG.Monster.GMS.R433Cover.evalWord_reverse_inv y432FGen_mul_self]
    · simp [expandSigned, img10]

end Model

section Hom


theorem m0_eq : m0 = 11 := Certificates.certificate24053.1

theorem length_subsetOf : (subsetOf m0 S0).length = 10 :=
  Certificates.certificate24053.2.1

theorem r0_odd : ((X0.getD r0Idx []).filter fun l => l.1.val == 8).length % 2 = 1 :=
  Certificates.certificate24053.2.2.1

theorem img10_rels : ∀ w ∈ X1, wprod (img10 : Fin (subsetOf m0 S0).length → _) w = 1 := by
  intro w hw
  rw [wprod_img10]
  exact Certificates.certificate24053.2.2.2 w hw

noncomputable def rho10 : PG10 →* Equiv.Perm (Fin 31671) := pgHom img10 img10_rels

theorem rho10_of (j : Fin (subsetOf m0 S0).length) :
    rho10 (PresentedGroup.of j) = evalWord y432FGen (x1Imgs.getD j.val []) :=
  pgHom_of _ _ j

theorem range_rho10_le : rho10.range ≤ rho432F.range := by
  rintro _ ⟨x, rfl⟩
  refine PresentedGroup.generated_by _ (rho432F.range.comap rho10) (fun j => ?_) x
  show rho10 (PresentedGroup.of j) ∈ rho432F.range
  rw [rho10_of, ← rho432F_evalWord]
  exact ⟨_, rfl⟩

theorem y432FGen_three_mul_mem {c : ℕ} (hc : c < 10) : y432FGen 3 * y432FGen c ∈ rho10.range := by
  by_cases h3 : c = 3
  · rw [h3, y432FGen_mul_self]
    exact rho10.range.one_mem
  · have hex : ∀ c < 10, c ≠ 3 → ∃ j < 10, x1Imgs.getD j [] = [3, c] := by decide
    obtain ⟨j, hj, hjc⟩ := hex c hc h3
    have hj' : j < (subsetOf m0 S0).length := by rw [length_subsetOf]; exact hj
    refine ⟨PresentedGroup.of ⟨j, hj'⟩, ?_⟩
    rw [rho10_of, hjc]
    simp [evalWord_cons, evalWord_nil]

theorem y432FGen_mul_mem {a b : ℕ} (ha : a < 10) (hb : b < 10) :
    y432FGen a * y432FGen b ∈ rho10.range := by
  have e : y432FGen a * y432FGen b = (y432FGen 3 * y432FGen a)⁻¹ * (y432FGen 3 * y432FGen b) := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (y432FGen_mul_self a),
      inv_eq_of_mul_eq_one_right (y432FGen_mul_self 3), mul_assoc, ← mul_assoc (y432FGen 3),
      y432FGen_mul_self, one_mul]
  rw [e]
  exact rho10.range.mul_mem (rho10.range.inv_mem (y432FGen_three_mul_mem ha))
    (y432FGen_three_mul_mem hb)

theorem evalWord_mem_range_rho10 (n : ℕ) :
    ∀ w : List ℕ, w.length = 2 * n → (∀ c ∈ w, c < 10) → evalWord y432FGen w ∈ rho10.range := by
  induction n with
  | zero =>
    intro w hl _
    rw [List.eq_nil_of_length_eq_zero hl, evalWord_nil]
    exact rho10.range.one_mem
  | succ n ih =>
    intro w hl hw
    match w, hl with
    | [], hl => simp at hl
    | [_], hl => simp only [List.length_cons, List.length_nil] at hl; omega
    | a :: b :: w, hl =>
      rw [evalWord_cons, evalWord_cons, ← mul_assoc]
      refine rho10.range.mul_mem (y432FGen_mul_mem (hw a (by simp)) (hw b (by simp))) ?_
      exact ih w (by simp only [List.length_cons] at hl; omega) fun c hc => hw c (by simp [hc])

theorem y432FGen_three_mem : y432FGen 3 ∈ rho10.range := by
  have hF := (CFSG.YGroups.evalWord_arrGen_eq_iff (n := 31671) (O := y432FArrays) y432F_check.2.1
    F432Word []).2 F432_check.1
  rw [evalWord_nil] at hF
  change evalWord y432FGen F432Word = 1 at hF
  have e : y432FGen 3 = evalWord y432FGen (3 :: F432Word.reverse) := by
    rw [evalWord_cons, CFSG.Monster.GMS.R433Cover.evalWord_reverse_inv y432FGen_mul_self, hF,
      inv_one, mul_one]
  rw [e]
  exact evalWord_mem_range_rho10 32 _ (by decide) (by decide)

theorem y432FGen_mem_range_rho10 {c : ℕ} (hc : c < 10) : y432FGen c ∈ rho10.range := by
  by_cases h3 : c = 3
  · rw [h3]; exact y432FGen_three_mem
  · have hex : ∀ c < 10, c ≠ 3 → ∃ j < 10, x1Imgs.getD j [] = [3, c] := by decide
    obtain ⟨j, hj, hjc⟩ := hex c hc h3
    have hj' : j < (subsetOf m0 S0).length := by rw [length_subsetOf]; exact hj
    have h1 : rho10 (PresentedGroup.of ⟨j, hj'⟩) = y432FGen 3 * y432FGen c := by
      rw [rho10_of, hjc]
      simp [evalWord_cons, evalWord_nil]
    have h2 : y432FGen c = y432FGen 3 * (y432FGen 3 * y432FGen c) := by
      rw [← mul_assoc, y432FGen_mul_self, one_mul]
    rw [h2, ← h1]
    exact rho10.range.mul_mem y432FGen_three_mem ⟨_, rfl⟩

theorem range_rho10 : rho10.range = rho432F.range := by
  refine le_antisymm range_rho10_le ?_
  rw [CFSG.YGroups.range_rho432F, CFSG.YGroups.arrClosure, Subgroup.closure_le]
  rintro g ⟨k, hk, rfl⟩
  have hk10 : k < 10 := by rw [y432F_check.1] at hk; exact hk
  rw [← y432FGen_eq hk10]
  exact y432FGen_mem_range_rho10 hk10

noncomputable def rho10' : PG10 →* rho432F.range :=
  rho10.codRestrict _ fun x => range_rho10_le ⟨x, rfl⟩

theorem rho10'_surjective : Function.Surjective rho10' := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := range_rho10.ge hy
  exact ⟨x, Subtype.ext hx⟩

theorem rho10'_bijective :
    Function.Bijective rho10' := by
  have := card_PG10_le.1
  refine rho10'_surjective.bijective_of_nat_card_le ?_
  rw [card_range_rho432F]
  exact card_PG10_le.2

noncomputable def pg10EquivR432 :
    PG10 ≃* R432 :=
  (MulEquiv.ofBijective rho10' rho10'_bijective).trans r432EquivRange.symm

theorem isPerfect_PG10 :
    Group.IsPerfect PG10 := by
  have := isPerfect_R432
  exact Group.IsPerfect.ofSurjective (f := (pg10EquivR432.symm : R432 →* PG10))
    pg10EquivR432.symm.surjective

theorem noPerfectDoubleCover_PG10 :
    CFSG.Monster.Schur.NoPerfectDoubleCover PG10 :=
  CFSG.Monster.Schur.NoPerfectDoubleCover.of_mulEquiv pg10EquivR432.symm noPerfectDoubleCover_R432

end Hom

end CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
