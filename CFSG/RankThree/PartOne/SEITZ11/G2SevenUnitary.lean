module

public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.LinearAlgebra.LinearGroups.UnitaryVectorCount
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LieType.Steinberg

section Unitary

variable {L : Type} [Field L] [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

omit [CharP L p] in
theorem unitaryData (hL : Nat.card L = (p ^ f) ^ 2) : UnitaryFieldData p f L := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := L)
      simp at hL
      omega
    · exact hf
  exact ⟨Fact.out, hf, by rw [hL, ← pow_mul, mul_comm]⟩

theorem bar_eq (h : UnitaryFieldData p f L) (c : L) : h.bar c = unitaryInvolution L p f c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

theorem su3_card (hL : Nat.card L = (p ^ f) ^ 2) :
    Nat.card (SUid (unitaryInvolution L p f) 3) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [SUid_eq_statedSU hL 3]
  exact CFSG.SectionRank.OddCover.card_statedSU_three hL

theorem su3_trans (hL : Nat.card L = (p ^ f) ^ 2) (h2 : (2 : L) ≠ 0) {x y : Fin 3 → L}
    (hxy : herm (unitaryInvolution L p f) x x = herm (unitaryInvolution L p f) y y)
    (hx : herm (unitaryInvolution L p f) x x ≠ 0) :
    ∃ U : SUid (unitaryInvolution L p f) 3,
      ((U : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *ᵥ x = y := by
  set σ := unitaryInvolution L p f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hL
  obtain ⟨l, hl⟩ := hσ.exists_norm (herm_self_fixed σ hσ.invol x)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl
    exact hx hl.symm
  have hσl0 : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  have hnorm : ∀ z : Fin 3 → L, herm σ z z = herm σ x x → herm σ (l⁻¹ • z) (l⁻¹ • z) = 1 := by
    intro z hz
    rw [herm_smul_left, herm_smul_right, hz, ← hl, map_inv₀]
    field_simp
  obtain ⟨s, hs0, hs1⟩ : ∃ s : L, s ≠ 0 ∧ σ s * s ≠ 1 := by
    obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
    refine ⟨u, ?_, ?_⟩
    · rintro rfl
      rw [map_zero, zero_mul] at hu
      exact one_ne_zero (neg_eq_zero.mp hu.symm)
    · rw [hu]
      intro h
      apply h2
      linear_combination -h
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inr ⟨le_rfl, s, hs0, hs1⟩)
    (hnorm x rfl) (hnorm y hxy.symm)
  refine ⟨t, ?_⟩
  rw [← smul_def]
  have h1 : t • x = t • (l • (l⁻¹ • x)) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have h2 : y = l • (l⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [h1, smul_comm, ht, ← h2]

@[expose] def pairSet (σ : L ≃+* L) (κ : L) : Set (L × (Fin 3 → L)) :=
  {r | σ r.1 = r.1 ∧ r.1 ^ 2 ≠ 1 ∧ ∑ i, σ (r.2 i) * r.2 i = (r.1 ^ 2 - 1) / κ}

abbrev bSet (σ : L ≃+* L) : Type _ := {b : L // σ b = b ∧ b ^ 2 ≠ 1}

theorem card_bSet (hL : Nat.card L = (p ^ f) ^ 2) :
    p ^ f - 2 ≤ Nat.card (bSet (unitaryInvolution L p f)) := by
  classical
  have := Fintype.ofFinite L
  set σ := unitaryInvolution L p f with hσdef
  have h := unitaryData hL
  have hfix : Nat.card {b : L // σ b = b} = p ^ f := by
    rw [← h.card_fixedField]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
    rw [UnitaryFieldData.mem_fixedField, bar_eq]
  let S : Finset L := Finset.univ.filter fun b => σ b = b
  have hS : S.card = p ^ f := by
    rw [← hfix, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : (S.filter fun b => b ^ 2 = 1).card ≤ 2 := by
    calc (S.filter fun b => b ^ 2 = 1).card ≤ ({1, -1} : Finset L).card :=
          Finset.card_le_card fun b hb => by
            rcases sq_eq_one_iff.mp (Finset.mem_filter.1 hb).2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  have h3 := Finset.card_filter_add_card_filter_not (s := S) (fun b => b ^ 2 = 1)
  have h4 : Nat.card (bSet σ) = (S.filter fun b => ¬ b ^ 2 = 1).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext b
    simp [S, and_comm]
  omega

theorem norm_count (hL : Nat.card L = (p ^ f) ^ 2) {c : L}
    (hc : unitaryInvolution L p f c = c) (hc0 : c ≠ 0) :
    Nat.card {x : Fin 3 → L // ∑ i, unitaryInvolution L p f (x i) * x i = c} =
      (p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1) := by
  have h := unitaryData hL
  have e : Nat.card {x : Fin 3 → L // ∑ i, unitaryInvolution L p f (x i) * x i = c} =
      normSumCount h 3 c := by
    unfold normSumCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [UnitaryFieldData.norm, bar_eq h, mul_comm]
  have hmem : ∀ d : L, unitaryInvolution L p f d = d → d ∈ h.fixedField := fun d hd => by
    rw [UnitaryFieldData.mem_fixedField, bar_eq]
    exact hd
  rw [e, normSumCount_eq_of_mem h (hmem c hc) hc0 (hmem 1 (map_one _)) one_ne_zero]
  have h1 := (normSumCount_closed h 2).1
  have h2 : (normSumCount h 3 1 : ℤ) = (p ^ f : ℕ) ^ 2 * ((p ^ f : ℕ) ^ 3 + 1) := by
    simpa using h1
  exact_mod_cast h2

theorem pairSet_ncard (hL : Nat.card L = (p ^ f) ^ 2) {κ : L} (hκ : κ ≠ 0)
    (hκσ : unitaryInvolution L p f κ = κ) :
    (p ^ f - 2) * ((p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1)) ≤
      (pairSet (unitaryInvolution L p f) κ).ncard := by
  classical
  set σ := unitaryInvolution L p f with hσdef
  have := Fintype.ofFinite (bSet σ)
  let e : pairSet σ κ ≃ Σ b : bSet σ,
      {x : Fin 3 → L // ∑ i, σ (x i) * x i = (b.1 ^ 2 - 1) / κ} :=
    { toFun := fun r => ⟨⟨r.1.1, r.2.1, r.2.2.1⟩, ⟨r.1.2, r.2.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2.1, s.1.2.2, s.2.2⟩
      left_inv := fun r => rfl
      right_inv := fun s => rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ b : bSet σ, Nat.card {x : Fin 3 → L // ∑ i, σ (x i) * x i = (b.1 ^ 2 - 1) / κ} =
      (p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1) := fun b => by
    refine norm_count hL ?_ ?_
    · rw [map_div₀, map_sub, map_pow, b.2.1, map_one, hκσ]
    · exact div_ne_zero (sub_ne_zero.2 b.2.2) hκ
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.mul_le_mul_right _ (card_bSet hL)

theorem surj_of_blocks (hL : Nat.card L = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {W : Type*} [Group W]
    (ψ : W →* Su L p f 3)
    (h12 : ∀ U : SUid (unitaryInvolution L p f) 2,
      embSUid (unitaryInvolution L p f) 2 U ∈ ψ.range)
    (h23 : ∀ U : SUid (unitaryInvolution L p f) 2,
      embSUid (unitaryInvolution L p f) 0 U ∈ ψ.range) :
    Function.Surjective ψ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← B12_sup_B23 hL hq]
  refine sup_le ?_ ?_
  · rintro _ ⟨U, rfl⟩
    exact h12 U
  · rintro _ ⟨U, rfl⟩
    exact h23 U

theorem arith_ineq {q : ℕ} (hq : 5 ≤ q) :
    q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) <
      2 * ((q - 2) * (q ^ 2 * (q ^ 3 + 1))) * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 ≤ q := by omega
  zify [h1, h2, h3]
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have key : 0 < (q : ℤ) ^ 4 - 4 * q ^ 3 + 3 * q - 4 := by
    have : (q : ℤ) ^ 4 - 4 * q ^ 3 + 3 * q - 4 = q ^ 3 * (q - 4) + 3 * q - 4 := by ring
    rw [this]
    nlinarith [pow_pos (show (0 : ℤ) < q by omega) 3]
  have hpos : 0 < (q : ℤ) ^ 5 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) := by
    have : (1 : ℤ) < (q : ℤ) ^ 2 := by nlinarith
    positivity
  have hdiff : 2 * (((q : ℤ) - 2) * ((q : ℤ) ^ 2 * ((q : ℤ) ^ 3 + 1))) *
      ((q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1)) -
      (q : ℤ) ^ 6 * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 2 - 1) =
      (q : ℤ) ^ 5 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) *
        ((q : ℤ) ^ 4 - 4 * q ^ 3 + 3 * q - 4) := by ring
  nlinarith [mul_pos hpos key]

end Unitary

section SU2

variable {L : Type} [Field L] {σ : L ≃+* L}

theorem su2_entries (U : SUid σ 2) :
    ((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        σ (((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
      ((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 =
        -σ (((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1) := by
  obtain ⟨hdet, hU⟩ := mem_SUid.1 U.2
  set X : Matrix (Fin 2) (Fin 2) L := ((U : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
  have hinv : X⁻¹ = conjTr σ X := Matrix.inv_eq_left_inv hU
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two] at hinv
  have h00 := congrFun (congrFun hinv 0) 0
  have h10 := congrFun (congrFun hinv 1) 0
  simp [conjTr] at h00 h10
  exact ⟨h00, by linear_combination -h10⟩

end SU2

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
