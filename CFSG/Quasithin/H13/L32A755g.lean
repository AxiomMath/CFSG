module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.L32A755c
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

@[expose] noncomputable def z1 : ↥(quasithinG2 (ZMod 2)) := wordGG [1]

@[expose] def z1Mat : List ℕ := [1, 6, 2, 8, 32, 48, 64, 128]

theorem z1Mat_eq : (List.range 8).map (fun k => applyG [1] (2 ^ k)) = z1Mat := by
  decide +kernel

theorem matCode_z1 : matCode z1.1 = z1Mat := by
  rw [← z1Mat_eq]
  change matCode ⇑(wordG (R := ZMod 2) [1]) = _
  unfold matCode
  refine List.map_congr_left fun k hk => ?_
  have hk8 : 2 ^ k < 256 := by
    have h8 : k < 8 := List.mem_range.1 hk
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) h8
      _ = 256 := by norm_num
  obtain ⟨h1, h2⟩ := decodeZ_applyG (l := [1]) (by simp) hk8
  rw [← h1, encodeZ_decodeZ _ h2]

theorem z1_mem : z1 ∈ g2Derived (ZMod 2) := wordGG_mem_derived [1]

theorem z1_cube : z1 * z1 * z1 = 1 := by
  apply Subtype.ext
  apply linearEquiv_eq_of_matCode
  rw [Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul, matCode_z1, OneMemClass.coe_one,
    matCode_one]
  decide

theorem z1_inv : z1⁻¹ = z1 * z1 := (eq_inv_of_mul_eq_one_left z1_cube).symm

theorem matCode_z1_inv : matCode z1⁻¹.1 = mmul z1Mat z1Mat := by
  rw [z1_inv, Subgroup.coe_mul, matCode_mul, matCode_z1]

theorem g2QAct_z1 : g2QAct (ZMod 2) z1 (ptQ 8) = ptQ 8 := by
  have h8 : (8 : ℕ) ∈ o0Codes := by decide
  rw [g2QAct_ptQ z1 h8, matCode_z1]
  rfl

@[expose] def zConj : List ℕ := [0, 64, 4, 64, 6, 64, 2, 64, 8, 64, 12, 64, 14, 64, 10, 64, 32, 64,
  36, 64, 38, 64, 34, 64, 40, 64, 44, 64, 46, 64, 42, 64, 48, 64, 52, 64, 54, 64, 50, 64, 56, 64,
  60, 64, 62, 64, 58, 64, 16, 64, 20, 64, 22, 64, 18, 64, 24, 64, 28, 64, 30, 64, 26, 64]

theorem zConj_spec : ∀ j < 64,
    (zConj.getD j 64 < 64 →
      mmul (mmul z1Mat (sM j)) (mmul z1Mat z1Mat) = sM (zConj.getD j 64)) ∧
    (zConj.getD j 64 = 64 → ∀ k < 64, mmul (mmul z1Mat (sM j)) (mmul z1Mat z1Mat) ≠ sM k) ∧
    zConj.getD j 64 ≤ 64 := by
  decide +kernel

variable {X : Subgroup ↥(quasithinG2 (ZMod 2))}

theorem zConj_mem (hXS : X ≤ sSubG) (hNz : ∀ x ∈ X, z1 * x * z1⁻¹ ∈ X) {l : ℕ}
    (hl : l ∈ idx X) : zConj.getD l 64 < 64 ∧ zConj.getD l 64 ∈ idx X := by
  have hl64 := (mem_idx.1 hl).1
  have hx : z1 * sEltG l * z1⁻¹ ∈ X := hNz _ (mem_idx.1 hl).2
  obtain ⟨k, hk, hke⟩ := mem_sSubG.1 (hXS hx)
  have hmat : sM k = mmul (mmul z1Mat (sM l)) (mmul z1Mat z1Mat) := by
    rw [← matCode_sEltG hk, hke, Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul,
      matCode_z1, matCode_z1_inv, matCode_sEltG hl64]
  obtain ⟨h1, h2, h3⟩ := zConj_spec l hl64
  by_cases h64 : zConj.getD l 64 = 64
  · exact absurd hmat.symm (h2 h64 k hk)
  · have hlt : zConj.getD l 64 < 64 := lt_of_le_of_ne h3 h64
    have hk' : k = zConj.getD l 64 := sMats_inj k hk _ hlt (hmat.trans (h1 hlt))
    exact ⟨hlt, mem_idx.2 ⟨hlt, hk' ▸ hke ▸ hx⟩⟩

theorem sConj_mem (hXS : X ≤ sSubG) (hN0 : ∀ i ∈ innerS, ∀ x ∈ X, sEltG i * x * (sEltG i)⁻¹ ∈ X)
    {i l k : ℕ} (hi : i ∈ innerS) (hii : mmul (sM i) (sM i) = idMat) (hl : l ∈ idx X)
    (hk : k < 64) (hik : mmul (mmul (sM i) (sM l)) (sM i) = sM k) : k ∈ idx X := by
  have hi64 := innerS_lt i hi
  have hl64 := (mem_idx.1 hl).1
  have hinv : (sEltG i)⁻¹ = sEltG i := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    apply Subtype.ext
    apply linearEquiv_eq_of_matCode
    rw [Subgroup.coe_mul, matCode_mul, matCode_sEltG hi64, OneMemClass.coe_one, matCode_one, hii]
  have hx := hN0 i hi _ (mem_idx.1 hl).2
  rw [hinv] at hx
  obtain ⟨p, hp, hpe⟩ := mem_sSubG.1 (hXS hx)
  have hmat : sM p = sM k := by
    rw [← matCode_sEltG hp, hpe, Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul,
      matCode_sEltG hi64, matCode_sEltG hl64, hik]
  have hpk := sMats_inj p hp k hk hmat
  exact mem_idx.2 ⟨hk, hpk ▸ hpe ▸ hx⟩

theorem mmul_comm_of_mem (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {l k : ℕ} (hl : l ∈ idx X)
    (hk : k ∈ idx X) : mmul (sM l) (sM k) = mmul (sM k) (sM l) := idx_comm hXc hl hk

theorem mul_mem_idx (hXS : X ≤ sSubG) {l k p : ℕ} (hl : l ∈ idx X) (hk : k ∈ idx X)
    (hp : p < 64) (hlk : mmul (sM l) (sM k) = sM p) : p ∈ idx X := by
  obtain ⟨q, hq, hqe⟩ := idx_mul hXS hl hk
  have := sMats_inj q (mem_idx.1 hq).1 p hp (hqe.trans hlk)
  exact this ▸ hq

theorem sq_of_mem (hX2 : ∀ x ∈ X, x ^ 2 = 1) {l : ℕ} (hl : l ∈ idx X) :
    mmul (sM l) (sM l) = idMat := by
  have hl64 := (mem_idx.1 hl).1
  have h : (sEltG l).1 * (sEltG l).1 = 1 := by
    have := congrArg Subtype.val (hX2 _ (mem_idx.1 hl).2)
    rwa [pow_two, Subgroup.coe_mul, OneMemClass.coe_one] at this
  rw [← matCode_sEltG hl64, ← matCode_mul, h, matCode_one]

theorem class_facts :
    (∀ l < 64, zConj.getD l 64 < 64 → l % 2 = 0) ∧
    (∀ l ∈ [24, 26, 28, 30, 40, 42, 44, 46, 56, 58, 60, 62], mmul (sM l) (sM l) ≠ idMat) ∧
    mmul (sM 1) (sM 1) = idMat ∧ mmul (sM 43) (sM 43) = idMat ∧
    (∀ l ∈ [16, 18, 20, 22, 48, 50, 52, 54], ∃ k < 64, mmul (mmul (sM 1) (sM l)) (sM 1) = sM k ∧
      mmul (sM l) (sM k) ≠ mmul (sM k) (sM l)) ∧
    (∀ l ∈ [32, 34, 36, 38], zConj.getD l 64 < 64 ∧
      mmul (sM l) (sM (zConj.getD l 64)) ≠ mmul (sM (zConj.getD l 64)) (sM l)) ∧
    zConj.getD 2 64 = 4 ∧ zConj.getD 4 64 = 6 ∧ zConj.getD 6 64 = 2 ∧
    zConj.getD 10 64 = 12 ∧ zConj.getD 12 64 = 14 ∧ zConj.getD 14 64 = 10 ∧
    mmul (mmul (sM 43) (sM 8)) (sM 43) = sM 12 ∧
    mmul (sM 8) (sM 12) = sM 4 ∧ mmul (sM 10) (sM 12) = sM 6 ∧ mmul (sM 12) (sM 14) = sM 2 ∧
    mmul (sM 14) (sM 10) = sM 4 := by
  decide +kernel

theorem idx_B0_or_A0 (hXS : X ≤ sSubG) (hX2 : ∀ x ∈ X, x ^ 2 = 1)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hX1 : X ≠ ⊥)
    (hN0 : ∀ i ∈ innerS, ∀ x ∈ X, sEltG i * x * (sEltG i)⁻¹ ∈ X)
    (hNz : ∀ x ∈ X, z1 * x * z1⁻¹ ∈ X) :
    (∀ l, l ∈ idx X ↔ l ∈ [0, 2, 4, 6]) ∨ (∀ l, l ∈ idx X ↔ l ∈ [0, 2, 4, 6, 8, 10, 12, 14]) := by
  obtain ⟨heven, hnsq, h11, h4343, hbad1, hbad2, hz2, hz4, hz6, hz10, hz12, hz14, hc8, hp812,
    hp1012, hp1214, hp1410⟩ := class_facts
  have h1i : (1 : ℕ) ∈ innerS := by decide
  have h43i : (43 : ℕ) ∈ innerS := by decide
  have hA0 : ∀ l ∈ idx X, l ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
    intro l hl
    have hl64 := (mem_idx.1 hl).1
    have hev := heven l hl64 (zConj_mem hXS hNz hl).1
    have hsq := sq_of_mem hX2 hl
    have key : ∀ l < 64, l % 2 = 0 → l ∈ [0, 2, 4, 6, 8, 10, 12, 14] ∨
        l ∈ [16, 18, 20, 22, 48, 50, 52, 54] ∨ l ∈ [32, 34, 36, 38] ∨
          l ∈ [24, 26, 28, 30, 40, 42, 44, 46, 56, 58, 60, 62] := by
      decide
    rcases key l hl64 hev with h | h | h | h
    · exact h
    · obtain ⟨k, hk, hke, hkc⟩ := hbad1 l h
      exact absurd (mmul_comm_of_mem hXc hl (sConj_mem hXS hN0 h1i h11 hl hk hke)) hkc
    · obtain ⟨-, hkc⟩ := hbad2 l h
      exact absurd (mmul_comm_of_mem hXc hl (zConj_mem hXS hNz hl).2) hkc
    · exact absurd hsq (hnsq l h)
  have h0 : (0 : ℕ) ∈ idx X := zero_mem_idx
  have hB0 : (2 : ℕ) ∈ idx X ∨ (4 : ℕ) ∈ idx X ∨ (6 : ℕ) ∈ idx X := by
    by_contra hno
    push Not at hno
    obtain ⟨hn2, hn4, hn6⟩ := hno
    have hsub : ∀ l ∈ idx X, l = 0 := by
      intro l hl
      have hlA := hA0 l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlA
      rcases hlA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · exact absurd hl hn2
      · exact absurd hl hn4
      · exact absurd hl hn6
      · have h12 := sConj_mem hXS hN0 h43i h4343 hl (by norm_num) hc8
        exact absurd (mul_mem_idx hXS hl h12 (by norm_num) hp812) hn4
      · have h12 : (12 : ℕ) ∈ idx X := hz10 ▸ (zConj_mem hXS hNz hl).2
        exact absurd (mul_mem_idx hXS hl h12 (by norm_num) hp1012) hn6
      · have h14 : (14 : ℕ) ∈ idx X := hz12 ▸ (zConj_mem hXS hNz hl).2
        exact absurd (mul_mem_idx hXS hl h14 (by norm_num) hp1214) hn2
      · have h10 : (10 : ℕ) ∈ idx X := hz14 ▸ (zConj_mem hXS hNz hl).2
        exact absurd (mul_mem_idx hXS hl h10 (by norm_num) hp1410) hn4
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hXS hx)
    have := hsub i (mem_idx.2 ⟨hi, hx⟩)
    subst this
    rw [sEltG_zero]
    exact Subgroup.one_mem _
  have hz : ∀ l, l ∈ idx X → zConj.getD l 64 ∈ idx X := fun l hl => (zConj_mem hXS hNz hl).2
  have h246 : (2 : ℕ) ∈ idx X ∧ (4 : ℕ) ∈ idx X ∧ (6 : ℕ) ∈ idx X := by
    rcases hB0 with h | h | h
    · have h4 := hz2 ▸ hz 2 h
      exact ⟨h, h4, hz4 ▸ hz 4 h4⟩
    · have h6 := hz4 ▸ hz 4 h
      exact ⟨hz6 ▸ hz 6 h6, h, h6⟩
    · have h2 := hz6 ▸ hz 6 h
      exact ⟨h2, hz2 ▸ hz 2 h2, h⟩
  classical
  have hsubA : idx X ⊆ ([0, 2, 4, 6, 8, 10, 12, 14] : List ℕ).toFinset := fun l hl =>
    List.mem_toFinset.2 (hA0 l hl)
  have hsupB : ([0, 2, 4, 6] : List ℕ).toFinset ⊆ idx X := by
    intro l hl
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton,
      insert_empty_eq] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact h0
    · exact h246.1
    · exact h246.2.1
    · exact h246.2.2
  have hc8 : (idx X).card ≤ 8 := (Finset.card_le_card hsubA).trans (by decide)
  have hc4 : 4 ≤ (idx X).card := (by decide : ([0, 2, 4, 6] : List ℕ).toFinset.card = 4) ▸
    Finset.card_le_card hsupB
  rcases pow_two_cases (card_idx_pow hXS hX2) with h | h | h | h
  · omega
  · omega
  · left
    have heq : idx X = ([0, 2, 4, 6] : List ℕ).toFinset :=
      (Finset.eq_of_subset_of_card_le hsupB (by rw [h]; decide)).symm
    intro l
    rw [heq, List.mem_toFinset]
  · right
    have heq : idx X = ([0, 2, 4, 6, 8, 10, 12, 14] : List ℕ).toFinset :=
      Finset.eq_of_subset_of_card_le hsubA (by
        have : ([0, 2, 4, 6, 8, 10, 12, 14] : List ℕ).toFinset.card = 8 := by decide
        omega)
    intro l
    rw [heq, List.mem_toFinset]

end CFSG.Quasithin.H13.L32A.M755
