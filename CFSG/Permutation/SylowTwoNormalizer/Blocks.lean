module

public import CFSG.Permutation.SylowTwoNormalizer.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_halving_block {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R)
    (htr : MulAction.IsPretransitive R Ω) (h2 : 2 ≤ Nat.card Ω) :
    ∃ B : Set Ω, 2 * Nat.card B = Nat.card Ω ∧ ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ := by
  classical
  haveI htr' : MulAction.IsPretransitive R Ω := htr
  haveI : Nonempty Ω := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨x⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  set H : Subgroup ↥R := MulAction.stabilizer R x with hHdef
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (IsPGroup.to_subgroup hR H)
  have hHidx : H.index = Nat.card Ω := by
    rw [hHdef, MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]
  have hHn : Nat.card ↥H * Nat.card Ω = 2 ^ k := by
    rw [← hHidx, ← hk]
    exact Subgroup.card_mul_index H
  have hk1 : 1 ≤ k := by
    have h2k : 2 ^ 1 ≤ 2 ^ k := by
      calc 2 ^ 1 = 1 * 2 := by norm_num
        _ ≤ Nat.card ↥H * Nat.card Ω := by
          refine Nat.mul_le_mul ?_ h2
          have : 0 < Nat.card ↥H := Nat.card_pos
          omega
        _ = 2 ^ k := hHn
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2k
  have hjk : j ≤ k - 1 := by
    have hle : 2 ^ (j + 1) ≤ 2 ^ k := by
      calc 2 ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
        _ ≤ 2 ^ j * Nat.card Ω := Nat.mul_le_mul_left _ h2
        _ = 2 ^ k := by rw [← hj]; exact hHn
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  obtain ⟨K, hKcard, hHK⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le (G := ↥R) 2 (by
      rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1)) H hj hjk
  have h2k : 2 ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, show k - 1 + 1 = k by omega]
  have hKidx : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    rw [hKcard, hk] at h
    refine Nat.mul_left_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) (k - 1)) ?_
    rw [h2k]
    exact h
  haveI : K.Normal := Subgroup.normal_of_index_eq_two hKidx
  have hstabK : MulAction.stabilizer K x = H.subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hHdef, MulAction.mem_stabilizer_iff]
    rfl
  have hstabKcard : Nat.card ↥(MulAction.stabilizer K x) = 2 ^ j := by
    rw [hstabK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hj]
  have hKidxB : (MulAction.stabilizer K x).index = Nat.card ↥(MulAction.orbit K x) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hBcard : 2 ^ j * Nat.card ↥(MulAction.orbit K x) = 2 ^ (k - 1) := by
    rw [← hstabKcard, ← hKidxB, ← hKcard]
    exact Subgroup.card_mul_index _
  have hHn' : 2 ^ j * Nat.card Ω = 2 ^ k := by
    rw [← hj]
    exact hHn
  have hB : 2 * Nat.card (MulAction.orbit K x) = Nat.card Ω := by
    have e : 2 ^ j * Nat.card Ω = 2 ^ j * (Nat.card ↥(MulAction.orbit K x) * 2) := by
      rw [hHn', ← h2k, ← hBcard]
      ring
    have h := Nat.mul_left_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) j) e
    omega
  refine ⟨MulAction.orbit K x, hB, ?_⟩
  intro g hg
  set g' : ↥R := ⟨g, hg⟩ with hg'def
  by_cases hgK : g' ∈ K
  · exact Or.inl (MulAction.smul_orbit (G := ↥K) (⟨g', hgK⟩ : ↥K) x)
  · refine Or.inr ?_
    have hne : (g' : Perm Ω) • MulAction.orbit K x ≠ MulAction.orbit K x := by
      intro heq
      have hsm : (g' : ↥R) • MulAction.orbit K x = MulAction.orbit K (g' • x) :=
        MulAction.smul_orbit_eq_orbit_smul K x g'
      have hmem : g' • x ∈ MulAction.orbit K x := by
        have hx : x ∈ MulAction.orbit K x := MulAction.mem_orbit_self x
        have h := Set.smul_mem_smul_set (a := (g' : Perm Ω)) hx
        rwa [heq] at h
      obtain ⟨k, hk'⟩ := MulAction.mem_orbit_iff.mp hmem
      have hker : (k : ↥R)⁻¹ * g' ∈ H := by
        rw [hHdef, MulAction.mem_stabilizer_iff]
        have hk'' : (k : ↥R) • x = g' • x := hk'
        rw [mul_smul, ← hk'', ← mul_smul]
        simp
      have hgK' : g' ∈ K := by
        have h := K.mul_mem k.2 (hHK hker)
        rwa [mul_inv_cancel_left] at h
      exact hgK hgK'
    have hdisj : Disjoint (MulAction.orbit K x) ((g' : Perm Ω) • MulAction.orbit K x) := by
      have hsm : (g' : ↥R) • MulAction.orbit K x = MulAction.orbit K (g' • x) :=
        MulAction.smul_orbit_eq_orbit_smul K x g'
      rcases MulAction.orbit.eq_or_disjoint (G := ↥K) x (g' • x) with h | h
      · exact absurd (hsm.trans h.symm) hne
      · rwa [← hsm] at h
    have hunion : MulAction.orbit K x ∪ (g' : Perm Ω) • MulAction.orbit K x = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        Set.ncard_smul_set]
      have hb : Nat.card Ω = 2 * (MulAction.orbit K x).ncard := by
        rw [← Nat.card_coe_set_eq]
        exact hB.symm
      omega
    ext y
    constructor
    · intro hy
      rw [Set.mem_compl_iff]
      intro hyB
      exact Set.disjoint_left.mp hdisj hyB hy
    · intro hy
      have hy' : y ∈ MulAction.orbit K x ∪ (g' : Perm Ω) • MulAction.orbit K x := by
        rw [hunion]; exact Set.mem_univ y
      rcases hy' with h | h
      · exact absurd h hy
      · exact h

theorem two_mul_card_inf_stabilizer {R : Subgroup (Perm Ω)} {B : Set Ω}
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ) (hg : ∃ g ∈ R, g • B = Bᶜ) (hB : B ≠ Bᶜ) :
    2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) = Nat.card R := by
  obtain ⟨g₀, hg₀R, hg₀B⟩ := hg
  set K : Subgroup ↥R := (R ⊓ stabilizer (Perm Ω) B).subgroupOf R with hKdef
  have hbK : ∀ b : ↥R, (b ∈ K ↔ b.val • B = B) := by
    intro b
    rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    simp
  have hbaK : ∀ b : ↥R, (b * ⟨g₀, hg₀R⟩ ∈ K ↔ b.val • B = Bᶜ) := by
    intro b
    rw [hbK, Subgroup.coe_mul, mul_smul, hg₀B, Set.smul_set_compl]
    constructor
    · intro h
      rw [← compl_compl (b.val • B), h]
    · intro h
      rw [h, compl_compl]
  have hKidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g₀, hg₀R⟩, fun b => ?_⟩
    have h1 : b * ⟨g₀, hg₀R⟩ ∈ K ↔ b.val • B = Bᶜ := hbaK b
    have h2 : b ∈ K ↔ b.val • B = B := hbK b
    rw [h1, h2]
    rcases hRB b.val b.2 with hb | hb
    · exact Or.inr ⟨hb, fun h => hB (hb.symm.trans h)⟩
    · exact Or.inl ⟨hb, fun h => hB (hb.symm.trans h).symm⟩
  have hKcard : Nat.card ↥K = Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := R ⊓ stabilizer (Perm Ω) B)
      (K := R) inf_le_left).toEquiv
  have h := Subgroup.card_mul_index K
  rw [hKidx, hKcard] at h
  omega

theorem exists_smul_eq_compl {R : Subgroup (Perm Ω)} (htr : MulAction.IsPretransitive R Ω)
    {B : Set Ω} (hB : 2 * Nat.card B = Nat.card Ω) (hB0 : B.Nonempty)
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ) : ∃ g ∈ R, g • B = Bᶜ := by
  obtain ⟨u, hu⟩ := hB0
  obtain ⟨v, hv⟩ : Bᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    rintro rfl
    have hpos : 0 < Nat.card Ω := Nat.card_pos_iff.2 ⟨⟨u⟩, inferInstance⟩
    rw [Nat.card_coe_set_eq, Set.ncard_univ] at hB
    omega
  obtain ⟨g, hg⟩ := htr.exists_smul_eq u v
  refine ⟨g, g.2, (hRB g g.2).resolve_left fun h => hv ?_⟩
  rw [← hg, Subgroup.smul_def, ← h]
  exact Set.smul_mem_smul_set hu

theorem smul_set_eq_of_smul_set_eq_or_eq_compl {s : Set Ω} (hne : s.Nonempty) {σ : Perm Ω}
    (hσ : Odd (orderOf σ)) (h : σ • s = s ∨ σ • s = sᶜ) : σ • s = s := by
  rcases h with h | h
  · exact h
  exfalso
  have h2 : (σ ^ 2) • s = s := by
    rw [pow_two, mul_smul, h, Set.smul_set_compl, h, compl_compl]
  have h2k : ∀ k : ℕ, (σ ^ 2) ^ k • s = s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, h2, ih]
  obtain ⟨k, hk⟩ := hσ
  have hpow : (σ ^ 2) ^ k * σ = 1 := by
    rw [← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
  have heq : s = sᶜ := by
    calc s = 1 • s := (one_smul (Perm Ω) s).symm
      _ = ((σ ^ 2) ^ k * σ) • s := by rw [hpow]
      _ = (σ ^ 2) ^ k • (σ • s) := by rw [mul_smul]
      _ = (σ ^ 2) ^ k • sᶜ := by rw [h]
      _ = ((σ ^ 2) ^ k • s)ᶜ := by rw [Set.smul_set_compl]
      _ = sᶜ := by rw [h2k]
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ sᶜ := heq ▸ hx
  exact hx' hx

theorem smul_set_halving_of_mem_normalizer {R : Subgroup (Perm Ω)} {B : Set Ω} {σ : Perm Ω}
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ)
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) :
    ∀ g ∈ R, g • (σ • B) = σ • B ∨ g • (σ • B) = (σ • B)ᶜ := by
  intro g hg
  have hconj : σ⁻¹ * g * σ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem (normalizer (R : Set (Perm Ω))) hσR) g).mp hg
  have hmul : g * σ = σ * (σ⁻¹ * g * σ) := by group
  rcases hRB (σ⁻¹ * g * σ) hconj with h | h
  · left
    rw [← mul_smul, hmul, mul_smul, h]
  · right
    rw [← mul_smul, hmul, mul_smul, h, Set.smul_set_compl]

lemma halving_cells_nonempty [Nonempty Ω] {B C : Set Ω}
    (hB : 2 * Nat.card B = Nat.card Ω) (hC : 2 * Nat.card C = Nat.card Ω)
    (hCB : C ≠ B) (hCBc : C ≠ Bᶜ) :
    (B ∩ C).Nonempty ∧ (B ∩ Cᶜ).Nonempty ∧ (Bᶜ ∩ C).Nonempty ∧ (Bᶜ ∩ Cᶜ).Nonempty := by
  have hBsum : B.ncard + Bᶜ.ncard = Nat.card Ω :=
    Set.ncard_add_ncard_compl B (Set.toFinite _) (Set.toFinite _)
  have hCsum : C.ncard + Cᶜ.ncard = Nat.card Ω :=
    Set.ncard_add_ncard_compl C (Set.toFinite _) (Set.toFinite _)
  have hBn : B.ncard = Nat.card B := Nat.card_coe_set_eq B
  have hCn : C.ncard = Nat.card C := Nat.card_coe_set_eq C
  have hBcn : Bᶜ.ncard = Nat.card (Bᶜ : Set Ω) := Nat.card_coe_set_eq Bᶜ
  have hCcn : Cᶜ.ncard = Nat.card (Cᶜ : Set Ω) := Nat.card_coe_set_eq Cᶜ
  have hnBC : Nat.card B = Nat.card C := by omega
  have hCcompl : Nat.card (Cᶜ : Set Ω) = Nat.card C := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    have hsub : B ⊆ Cᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxC
      have hx' : x ∈ B ∩ C := ⟨hx, hxC⟩
      rw [h] at hx'
      exact hx'
    have heq : B = Cᶜ :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hCcn, hBn]; omega) (Set.toFinite _)
    exact hCBc (by rw [heq, compl_compl])
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    have hsub : B ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : x ∈ B ∩ Cᶜ := ⟨hx, by simpa using hxC⟩
      rw [h] at hx'
      exact hx'
    have heq : B = C :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hCn, hBn]; omega) (Set.toFinite _)
    exact hCB heq.symm
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    have hsub : C ⊆ B := by
      intro x hx
      by_contra hxB
      have hx' : x ∈ Bᶜ ∩ C := ⟨by simpa using hxB, hx⟩
      rw [h] at hx'
      exact hx'
    have heq : C = B :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hBn, hCn]; omega) (Set.toFinite _)
    exact hCB heq
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    have hsub : Cᶜ ⊆ B := by
      intro x hx
      by_contra hxB
      have hx' : x ∈ Bᶜ ∩ Cᶜ := ⟨by simpa using hxB, hx⟩
      rw [h] at hx'
      exact hx'
    have heq : Cᶜ = B :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hBn, hCcn]; omega) (Set.toFinite _)
    exact hCBc (by rw [← heq, compl_compl])

lemma card_cells_add {B C : Set Ω} (hB : 2 * Nat.card B = Nat.card Ω)
    (hC : 2 * Nat.card C = Nat.card Ω) :
    (B ∩ C).ncard + (B ∩ Cᶜ).ncard + (Bᶜ ∩ C).ncard + (Bᶜ ∩ Cᶜ).ncard = Nat.card Ω := by
  have h1 : (B ∩ C).ncard + (B ∩ Cᶜ).ncard = B.ncard := by
    rw [← Set.ncard_union_eq (s := B ∩ C) (t := B ∩ Cᶜ) (by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2) (Set.toFinite _) (Set.toFinite _)]
    congr 1
    ext x
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hx, hxC⟩
      · exact Or.inr ⟨hx, by simpa using hxC⟩
  have h2 : (Bᶜ ∩ C).ncard + (Bᶜ ∩ Cᶜ).ncard = Bᶜ.ncard := by
    rw [← Set.ncard_union_eq (s := Bᶜ ∩ C) (t := Bᶜ ∩ Cᶜ) (by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2) (Set.toFinite _) (Set.toFinite _)]
    congr 1
    ext x
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hx, hxC⟩
      · exact Or.inr ⟨hx, by simpa using hxC⟩
  have h3 : B.ncard + Bᶜ.ncard = Nat.card Ω :=
    Set.ncard_add_ncard_compl B (Set.toFinite _) (Set.toFinite _)
  omega

lemma sum_padicValNat_cells_le {n a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (h : a + b + c + d = n) :
    (padicValNat 2 a.factorial + padicValNat 2 b.factorial)
      + (padicValNat 2 c.factorial + padicValNat 2 d.factorial) ≤ n - 4 := by
  have h1 : padicValNat 2 a.factorial ≤ a - 1 := padicValNat_two_factorial_le (by omega)
  have h2 : padicValNat 2 b.factorial ≤ b - 1 := padicValNat_two_factorial_le (by omega)
  have h3 : padicValNat 2 c.factorial ≤ c - 1 := padicValNat_two_factorial_le (by omega)
  have h4 : padicValNat 2 d.factorial ≤ d - 1 := padicValNat_two_factorial_le (by omega)
  omega

noncomputable def cellIndex (B C : Set Ω) (x : Ω) : Bool × Bool := by
  classical
  exact (decide (x ∈ B), decide (x ∈ C))

lemma cellIndex_fibre_true_true (B C : Set Ω) :
    {x : Ω | cellIndex B C x = (true, true)} = B ∩ C := by
  ext x; simp [cellIndex]

lemma cellIndex_fibre_true_false (B C : Set Ω) :
    {x : Ω | cellIndex B C x = (true, false)} = B ∩ Cᶜ := by
  ext x; simp [cellIndex]

lemma cellIndex_fibre_false_true (B C : Set Ω) :
    {x : Ω | cellIndex B C x = (false, true)} = Bᶜ ∩ C := by
  ext x; simp [cellIndex]

lemma cellIndex_fibre_false_false (B C : Set Ω) :
    {x : Ω | cellIndex B C x = (false, false)} = Bᶜ ∩ Cᶜ := by
  ext x; simp [cellIndex]

lemma sum_padicValNat_cellIndex_le [Nonempty Ω] {B C : Set Ω}
    (h1 : (B ∩ C).Nonempty) (h2 : (B ∩ Cᶜ).Nonempty) (h3 : (Bᶜ ∩ C).Nonempty)
    (h4 : (Bᶜ ∩ Cᶜ).Nonempty)
    (hsum : (B ∩ C).ncard + (B ∩ Cᶜ).ncard + (Bᶜ ∩ C).ncard + (Bᶜ ∩ Cᶜ).ncard
      = Nat.card Ω) :
    ∑ i : Bool × Bool, padicValNat 2 (Nat.card {x // cellIndex B C x = i}).factorial
      ≤ Nat.card Ω - 4 := by
  have hTT : Nat.card {x // cellIndex B C x = (true, true)} = (B ∩ C).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(true, true)}) = (B ∩ C).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_true_true B C
  have hTF : Nat.card {x // cellIndex B C x = (true, false)} = (B ∩ Cᶜ).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(true, false)}) = (B ∩ Cᶜ).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_true_false B C
  have hFT : Nat.card {x // cellIndex B C x = (false, true)} = (Bᶜ ∩ C).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(false, true)}) = (Bᶜ ∩ C).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_false_true B C
  have hFF : Nat.card {x // cellIndex B C x = (false, false)} = (Bᶜ ∩ Cᶜ).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(false, false)}) = (Bᶜ ∩ Cᶜ).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_false_false B C
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [hTT, hTF, hFT, hFF]
  refine sum_padicValNat_cells_le ?_ ?_ ?_ ?_ hsum
  · have := (Set.ncard_pos (s := B ∩ C) (Set.toFinite _)).mpr h1; omega
  · have := (Set.ncard_pos (s := B ∩ Cᶜ) (Set.toFinite _)).mpr h2; omega
  · have := (Set.ncard_pos (s := Bᶜ ∩ C) (Set.toFinite _)).mpr h3; omega
  · have := (Set.ncard_pos (s := Bᶜ ∩ Cᶜ) (Set.toFinite _)).mpr h4; omega

lemma card_dvd_two_mul_card_inf_stabilizer {R : Subgroup (Perm Ω)} {B : Set Ω}
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ) (hB : B ≠ Bᶜ) :
    Nat.card R ∣ 2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) := by
  by_cases h : ∃ g ∈ R, g • B = Bᶜ
  · rw [two_mul_card_inf_stabilizer hRB h hB]
  · push Not at h
    have hle : R ≤ stabilizer (Perm Ω) B := by
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      rcases hRB g hg with h' | h'
      · exact h'
      · exact absurd h' (h g hg)
    have hinf : R ⊓ stabilizer (Perm Ω) B = R := inf_eq_left.mpr hle
    rw [hinf]
    exact dvd_mul_left _ _

lemma card_dvd_four_mul_card_inf_stabilizer {R : Subgroup (Perm Ω)} {B C : Set Ω}
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ)
    (hRC : ∀ g ∈ R, g • C = C ∨ g • C = Cᶜ)
    (hB : B ≠ Bᶜ) (hC : C ≠ Cᶜ) :
    Nat.card R ∣ 4 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) := by
  have h1 : Nat.card R ∣ 2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) :=
    card_dvd_two_mul_card_inf_stabilizer hRB hB
  have h2 : Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) ∣
      2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) := by
    refine card_dvd_two_mul_card_inf_stabilizer (R := R ⊓ stabilizer (Perm Ω) B) ?_ hC
    intro g hg
    exact hRC g hg.1
  have h3 : 2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B) ∣
      2 * (2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C)) :=
    Nat.mul_dvd_mul_left 2 h2
  have h4 : 2 * (2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C)) =
      4 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) := by ring
  rw [h4] at h3
  exact h1.trans h3

lemma card_inf_stabilizer_dvd_pow [Nonempty Ω] {R : Subgroup (Perm Ω)} {B C : Set Ω}
    (hR : IsPGroup 2 R)
    (h1 : (B ∩ C).Nonempty) (h2 : (B ∩ Cᶜ).Nonempty) (h3 : (Bᶜ ∩ C).Nonempty)
    (h4 : (Bᶜ ∩ Cᶜ).Nonempty)
    (hsum : (B ∩ C).ncard + (B ∩ Cᶜ).ncard + (Bᶜ ∩ C).ncard + (Bᶜ ∩ Cᶜ).ncard
      = Nat.card Ω) :
    Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) ∣ 2 ^ (Nat.card Ω - 4) := by
  classical
  have hR₀ : IsPGroup 2 ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) :=
    IsPGroup.of_injective hR (Subgroup.inclusion (le_trans inf_le_left inf_le_left))
      (Subgroup.inclusion_injective _)
  have hmem : ∀ g ∈ R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C, ∀ x,
      cellIndex B C (g x) = cellIndex B C x := by
    intro g hg x
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
    have hgB : g • B = B := MulAction.mem_stabilizer_iff.mp hg.1.2
    have hgC : g • C = C := MulAction.mem_stabilizer_iff.mp hg.2
    have hBiff : g x ∈ B ↔ x ∈ B := by
      have hmem : B ∈ fixedBy (Set Ω) g := by rwa [MulAction.mem_fixedBy]
      exact MulAction.smul_mem_of_set_mem_fixedBy hmem
    have hCiff : g x ∈ C ↔ x ∈ C := by
      have hmem : C ∈ fixedBy (Set Ω) g := by rwa [MulAction.mem_fixedBy]
      exact MulAction.smul_mem_of_set_mem_fixedBy hmem
    simp only [cellIndex]
    rw [decide_eq_decide.mpr hBiff, decide_eq_decide.mpr hCiff]
  refine (card_dvd_of_forall_apply_eq (cellIndex B C) hR₀ hmem).trans (Nat.pow_dvd_pow 2 ?_)
  exact sum_padicValNat_cellIndex_le h1 h2 h3 h4 hsum

lemma two_mul_card_inf_stabilizer_dvd_pow [Nonempty Ω] {R : Subgroup (Perm Ω)} {B C : Set Ω}
    (h8 : 8 ≤ Nat.card Ω) (hR : IsPGroup 2 R) (hRA : R ≤ alternatingGroup Ω)
    (h1 : (B ∩ C).Nonempty) (h2 : (B ∩ Cᶜ).Nonempty) (h3 : (Bᶜ ∩ C).Nonempty)
    (h4 : (Bᶜ ∩ Cᶜ).Nonempty)
    (hsum : (B ∩ C).ncard + (B ∩ Cᶜ).ncard + (Bᶜ ∩ C).ncard + (Bᶜ ∩ Cᶜ).ncard
      = Nat.card Ω) :
    2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) ∣
      2 ^ (Nat.card Ω - 4) := by
  classical
  have hR₀ : IsPGroup 2 ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) :=
    IsPGroup.of_injective hR (Subgroup.inclusion (le_trans inf_le_left inf_le_left))
      (Subgroup.inclusion_injective _)
  have hRA₀ : R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C ≤ alternatingGroup Ω :=
    le_trans (le_trans inf_le_left inf_le_left) hRA
  have hmem : ∀ g ∈ R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C, ∀ x,
      cellIndex B C (g x) = cellIndex B C x := by
    intro g hg x
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
    have hgB : g • B = B := MulAction.mem_stabilizer_iff.mp hg.1.2
    have hgC : g • C = C := MulAction.mem_stabilizer_iff.mp hg.2
    have hBiff : g x ∈ B ↔ x ∈ B := by
      have hmem : B ∈ fixedBy (Set Ω) g := by rwa [MulAction.mem_fixedBy]
      exact MulAction.smul_mem_of_set_mem_fixedBy hmem
    have hCiff : g x ∈ C ↔ x ∈ C := by
      have hmem : C ∈ fixedBy (Set Ω) g := by rwa [MulAction.mem_fixedBy]
      exact MulAction.smul_mem_of_set_mem_fixedBy hmem
    simp only [cellIndex]
    rw [decide_eq_decide.mpr hBiff, decide_eq_decide.mpr hCiff]
  have hTT : Nat.card {x // cellIndex B C x = (true, true)} = (B ∩ C).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(true, true)}) = (B ∩ C).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_true_true B C
  have hTF : Nat.card {x // cellIndex B C x = (true, false)} = (B ∩ Cᶜ).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(true, false)}) = (B ∩ Cᶜ).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_true_false B C
  have hFT : Nat.card {x // cellIndex B C x = (false, true)} = (Bᶜ ∩ C).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(false, true)}) = (Bᶜ ∩ C).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_false_true B C
  have hFF : Nat.card {x // cellIndex B C x = (false, false)} = (Bᶜ ∩ Cᶜ).ncard := by
    show Nat.card ↥(cellIndex B C ⁻¹' {(false, false)}) = (Bᶜ ∩ Cᶜ).ncard
    rw [Nat.card_coe_set_eq]
    congr 1
    exact cellIndex_fibre_false_false B C
  have hbig : ∃ i : Bool × Bool, 2 ≤ Nat.card {x // cellIndex B C x = i} := by
    by_contra hcon
    push Not at hcon
    have h1' : (B ∩ C).ncard ≤ 1 := by rw [← hTT]; have := hcon (true, true); omega
    have h2' : (B ∩ Cᶜ).ncard ≤ 1 := by rw [← hTF]; have := hcon (true, false); omega
    have h3' : (Bᶜ ∩ C).ncard ≤ 1 := by rw [← hFT]; have := hcon (false, true); omega
    have h4' : (Bᶜ ∩ Cᶜ).ncard ≤ 1 := by rw [← hFF]; have := hcon (false, false); omega
    omega
  refine (two_mul_card_dvd_of_forall_apply_eq (cellIndex B C) hRA₀ hR₀ hmem hbig).trans
    (Nat.pow_dvd_pow 2 ?_)
  exact sum_padicValNat_cellIndex_le h1 h2 h3 h4 hsum

theorem eq_or_eq_compl_of_halving {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.index) {a : ℕ} (hn : Nat.card Ω = 2 ^ a) {B C : Set Ω}
    (hB : 2 * Nat.card B = Nat.card Ω) (hC : 2 * Nat.card C = Nat.card Ω)
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ) (hRC : ∀ g ∈ R, g • C = C ∨ g • C = Cᶜ) :
    C = B ∨ C = Bᶜ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCB, hCBc⟩ := hcon
  classical
  haveI : Nonempty Ω := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hn]
    exact pow_pos (by norm_num) a
  have hBne : B ≠ Bᶜ := ne_compl_self
  have hCne : C ≠ Cᶜ := ne_compl_self
  obtain ⟨h1, h2, h3, h4⟩ := halving_cells_nonempty hB hC hCB hCBc
  have hsum := card_cells_add hB hC
  have hcardR : Nat.card R = 2 ^ (2 ^ a - 1) := by
    rw [card_eq_of_not_two_dvd_index hR hRi, hn, padicValNat_two_factorial_two_pow]
  have hA : 4 ≤ Nat.card Ω := by
    have h1' : 1 ≤ (B ∩ C).ncard := by
      have := (Set.ncard_pos (s := B ∩ C) (Set.toFinite _)).mpr h1; omega
    have h2' : 1 ≤ (B ∩ Cᶜ).ncard := by
      have := (Set.ncard_pos (s := B ∩ Cᶜ) (Set.toFinite _)).mpr h2; omega
    have h3' : 1 ≤ (Bᶜ ∩ C).ncard := by
      have := (Set.ncard_pos (s := Bᶜ ∩ C) (Set.toFinite _)).mpr h3; omega
    have h4' : 1 ≤ (Bᶜ ∩ Cᶜ).ncard := by
      have := (Set.ncard_pos (s := Bᶜ ∩ Cᶜ) (Set.toFinite _)).mpr h4; omega
    omega
  have hdiv4 := card_dvd_four_mul_card_inf_stabilizer (R := R) hRB hRC hBne hCne
  have hyoung := card_inf_stabilizer_dvd_pow (R := R) hR h1 h2 h3 h4 hsum
  have hlater : 4 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) ∣
      2 ^ (Nat.card Ω - 2) := by
    have h := Nat.mul_dvd_mul_left 4 hyoung
    rw [show 4 * 2 ^ (Nat.card Ω - 4) = 2 ^ (Nat.card Ω - 2) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega] at h
    exact h
  have hunit : Nat.card R ∣ 2 ^ (Nat.card Ω - 2) := hdiv4.trans hlater
  rw [hcardR, hn] at hunit
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hunit
  omega

theorem eq_or_eq_compl_of_halving_of_le_alternatingGroup (h8 : 8 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) {a : ℕ} (hn : Nat.card Ω = 2 ^ a)
    {B C : Set Ω} (hB : 2 * Nat.card B = Nat.card Ω) (hC : 2 * Nat.card C = Nat.card Ω)
    (hRB : ∀ g ∈ R, g • B = B ∨ g • B = Bᶜ) (hRC : ∀ g ∈ R, g • C = C ∨ g • C = Cᶜ) :
    C = B ∨ C = Bᶜ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCB, hCBc⟩ := hcon
  classical
  haveI : Nonempty Ω := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card]
    omega
  have hBne : B ≠ Bᶜ := ne_compl_self
  have hCne : C ≠ Cᶜ := ne_compl_self
  obtain ⟨h1, h2, h3, h4⟩ := halving_cells_nonempty hB hC hCB hCBc
  have hsum := card_cells_add hB hC
  have hcardR : Nat.card R = 2 ^ (2 ^ a - 2) := by
    have h := two_mul_card_eq_of_not_two_dvd_relIndex (by omega : 2 ≤ Nat.card Ω) hRA hR hRi
    rw [hn, padicValNat_two_factorial_two_pow] at h
    have hA3 : 3 ≤ 2 ^ a := by rw [← hn]; omega
    have h2 : 2 * Nat.card R = 2 * 2 ^ (2 ^ a - 2) := by
      rw [h, show 2 ^ a - 1 = 2 ^ a - 2 + 1 by omega, pow_succ]
      ring
    exact Nat.mul_left_cancel (by norm_num) h2
  have hdiv4 := card_dvd_four_mul_card_inf_stabilizer (R := R) hRB hRC hBne hCne
  have hyoung := two_mul_card_inf_stabilizer_dvd_pow (R := R) h8 hR hRA h1 h2 h3 h4 hsum
  have hlater : 2 * (2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C)) ∣
      2 ^ (Nat.card Ω - 3) := by
    have h := Nat.mul_dvd_mul_left 2 hyoung
    rw [show 2 * 2 ^ (Nat.card Ω - 4) = 2 ^ (Nat.card Ω - 3) by
      rw [show 2 * 2 ^ (Nat.card Ω - 4) = 2 ^ (1 + (Nat.card Ω - 4)) by rw [pow_add, pow_one]]
      congr 1
      omega] at h
    exact h
  rw [show 2 * (2 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C)) =
      4 * Nat.card ↥(R ⊓ stabilizer (Perm Ω) B ⊓ stabilizer (Perm Ω) C) by ring] at hlater
  have hunit : Nat.card R ∣ 2 ^ (Nat.card Ω - 3) := hdiv4.trans hlater
  rw [hcardR, hn] at hunit
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hunit
  omega

end CFSG.Permutation.SylowTwoNormalizer
