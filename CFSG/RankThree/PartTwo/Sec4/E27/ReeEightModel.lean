module

public import Certificates.Data.HuppertReeEight.Checker
public import CFSG.Sporadic.Schreier.TitsCert

public noncomputable section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits HuppertReeEight

namespace CFSG.RankThree.PartTwo.Sec4.E27.ReeEight

section Dictionary


theorem titsGen_mem {i : ℕ} (hi : i < 4) : titsGen i ∈ titsA :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

@[expose] def valA (w : List ℤ) : ↥titsA :=
  wordIn 4 (liftFam titsA 4 titsGen fun _ hi => titsGen_mem hi) w

theorem coe_valA (w : List ℤ) : (valA w : Equiv.Perm (Fin 1755)) = wordIn 4 titsGen w :=
  coe_wordIn_liftFam _ w

@[expose] def RepA (a : Array ℕ) (g : ↥titsA) : Prop := Rep 1755 a (g : Equiv.Perm (Fin 1755))

theorem rep_valA {w : List ℤ} (hw : lettersOK 4 w = true) : RepA (aArr w) (valA w) := by
  rw [RepA, coe_valA]
  exact rep_wordArr (by rw [titsGenArrs_size]) (fun i hi => titsGen_rep hi)
    (fun i hi => titsGen_inv hi) hw

variable {a b c : Array ℕ} {g h k : ↥titsA}

theorem RepA.mul (ha : RepA a g) (hb : RepA b h) : RepA (compA 1755 a b) (g * h) := rep_compA ha hb

theorem repA_one : RepA (idA 1755) 1 := rep_idA

theorem eqE_iff (ha : RepA a g) (hb : RepA b h) : eqA 1755 a b = true ↔ g = h :=
  (eqA_iff ha hb).trans Subtype.coe_inj

theorem cubeE_iff (ha : RepA a g) : cubeE a = true ↔ g ^ 3 = 1 := by
  rw [cubeE, eqE_iff ((ha.mul ha).mul ha) repA_one, pow_three']

theorem oneE_iff (ha : RepA a g) : oneE a = true ↔ g = 1 := eqE_iff ha repA_one

theorem commE_iff (ha : RepA a g) (hb : RepA b h) : commE a b = true ↔ g * h = h * g :=
  eqE_iff (ha.mul hb) (hb.mul ha)

theorem memE_pows_iff (ha : RepA a g) (hb : RepA b h) :
    memE (powsE a) b = true ↔ h ∈ ({1, g, g * g} : Set ↥titsA) := by
  simp only [memE, powsE, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    eqE_iff hb repA_one, eqE_iff hb ha, eqE_iff hb (ha.mul ha), Set.mem_insert_iff,
    Set.mem_singleton_iff]

theorem isPairE_iff (ha : RepA a g) (hb : RepA b h) :
    isPairE a b = true ↔ g ≠ 1 ∧ g ^ 3 = 1 ∧ h ^ 3 = 1 ∧ g * h = h * g ∧
      h ∉ ({1, g, g * g} : Set ↥titsA) := by
  have h1 := oneE_iff ha
  have h2 := cubeE_iff ha
  have h3 := cubeE_iff hb
  have h4 := commE_iff ha hb
  have h5 := memE_pows_iff ha hb
  simp only [isPairE, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, h1, h2, h3, h4,
    h5, and_assoc]

theorem exists_pow_of_mem_powsE (ha : RepA a g) {p : Array ℕ} (hp : p ∈ powsE a) :
    ∃ i, i < 3 ∧ RepA p (g ^ i) := by
  simp only [powsE, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp
  · refine ⟨0, by norm_num, ?_⟩
    rw [hp, pow_zero]
    exact repA_one
  · refine ⟨1, by norm_num, ?_⟩
    rw [hp, pow_one]
    exact ha
  · refine ⟨2, by norm_num, ?_⟩
    rw [hp, pow_two]
    exact ha.mul ha

theorem memE_planeE (ha : RepA a g) (hb : RepA b h) (hc : RepA c k)
    (hm : memE (planeE a b) c = true) : ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ k = g ^ i * h ^ j := by
  simp only [memE, planeE, List.any_eq_true, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨d, ⟨p, hp, q, hq, rfl⟩, hcd⟩ := hm
  obtain ⟨i, hi, hpi⟩ := exists_pow_of_mem_powsE ha hp
  obtain ⟨j, hj, hqj⟩ := exists_pow_of_mem_powsE hb hq
  exact ⟨i, j, hi, hj, (eqE_iff hc (hpi.mul hqj)).1 hcd⟩

end Dictionary

section Sylow


theorem valA_nil : valA [] = 1 := rfl

theorem nil_mem_sylWords : ([] : List ℤ) ∈ sylWords :=
  List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), by simp [powWord]⟩

theorem sylowCheck_spec (h : sylowCheck () = true) :
    sylWords.length = 27 ∧ (∀ w ∈ sylWords, lettersOK 4 w = true) ∧ (∀ w ∈ sylWords, valA w ^ 3 = 1) ∧
      (∀ w₁ ∈ sylWords, ∀ w₂ ∈ sylWords, ∃ w₃ ∈ sylWords, valA w₁ * valA w₂ = valA w₃) ∧
      (sylWords.map valA).Pairwise (· ≠ ·) := by
  simp only [sylowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hmem : ∀ w ∈ sylWords, aArr w ∈ sylArrs () := fun w hw => List.mem_map.2 ⟨w, hw, rfl⟩
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro w hw
    exact (cubeE_iff (rep_valA (h2 w hw))).1 (h3 _ (hmem w hw))
  · intro w₁ hw₁ w₂ hw₂
    have h6 := h4 _ (hmem w₁ hw₁) _ (hmem w₂ hw₂)
    simp only [memE, List.any_eq_true] at h6
    obtain ⟨c, hc, hcc⟩ := h6
    obtain ⟨w₃, hw₃, rfl⟩ := List.mem_map.1 hc
    exact ⟨w₃, hw₃, (eqE_iff ((rep_valA (h2 w₁ hw₁)).mul (rep_valA (h2 w₂ hw₂)))
      (rep_valA (h2 w₃ hw₃))).1 hcc⟩
  · have h5' : sylWords.Pairwise (fun w w' => eqA 1755 (aArr w) (aArr w') = false) := by
      simpa only [sylArrs, List.pairwise_map] using h5
    rw [List.pairwise_map]
    refine h5'.imp_of_mem fun {w w'} hw hw' hne heq => ?_
    have := (eqE_iff (rep_valA (h2 w hw)) (rep_valA (h2 w' hw'))).2 heq
    rw [this] at hne
    exact absurd hne (by simp)

@[expose] def sylGrp : Subgroup ↥titsA := Subgroup.closure {g | ∃ w ∈ sylWords, g = valA w}

theorem mem_sylGrp_iff (hs : sylowCheck () = true) {g : ↥titsA} :
    g ∈ sylGrp ↔ ∃ w ∈ sylWords, g = valA w := by
  obtain ⟨-, -, hcube, hmul, -⟩ := sylowCheck_spec hs
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨[], nil_mem_sylWords, valA_nil.symm⟩
    | mul y z _ _ hy hz =>
      obtain ⟨w₁, hw₁, rfl⟩ := hy
      obtain ⟨w₂, hw₂, rfl⟩ := hz
      obtain ⟨w₃, hw₃, h3⟩ := hmul w₁ hw₁ w₂ hw₂
      exact ⟨w₃, hw₃, h3⟩
    | inv y _ hy =>
      obtain ⟨w₁, hw₁, rfl⟩ := hy
      obtain ⟨w₃, hw₃, h3⟩ := hmul w₁ hw₁ w₁ hw₁
      refine ⟨w₃, hw₃, ?_⟩
      rw [← h3]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hcube w₁ hw₁)
  · rintro ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem card_sylGrp (hs : sylowCheck () = true) : Nat.card sylGrp = 27 := by
  obtain ⟨hlen, -, -, -, hnd⟩ := sylowCheck_spec hs
  have hset : (sylGrp : Set ↥titsA) = ((sylWords.map valA).toFinset : Set ↥titsA) := by
    ext g
    simp only [SetLike.mem_coe, mem_sylGrp_iff hs, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  show Nat.card (sylGrp : Set ↥titsA) = 27
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    List.length_map, hlen]

theorem factorization_three_titsA : (35942400 : ℕ).factorization 3 = 3 := by
  have h : (35942400 : ℕ) = 3 ^ 3 * 1331200 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), Nat.add_zero]

theorem card_sylGrp_eq (hs : sylowCheck () = true) :
    Nat.card sylGrp = 3 ^ (Nat.card ↥titsA).factorization 3 := by
  rw [card_sylGrp hs, card_titsA, factorization_three_titsA]
  norm_num

end Sylow

end CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
