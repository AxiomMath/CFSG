module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FT
public import CFSG.Quasithin.Background.F918F1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Orders

theorem sl2_ne_l4_ch615 (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 20160 := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num
  · have h32 : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1023 : 1023 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 1024 ≤ (2 ^ n) ^ 2 := by
        calc 1024 = 32 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h32 2
      omega
    have : 32 * 1023 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h32 h1023
    omega

theorem sp4_ne_l4_ch615 {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) ≠ 20160 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    norm_num
  · have h1 : 2 ^ 8 ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 8 * ((2 ^ 4 - 1) * (2 ^ 8 - 1)) ≤
        2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h1 1))
    norm_num at h3
    omega

theorem g2_ne_l4_ch615 {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 20160 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    norm_num
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 4 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
    have h3 : 4 ^ 6 * ((4 ^ 6 - 1) * (4 ^ 2 - 1)) ≤
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h1 1) (Nat.sub_le_sub_right h2 1))
    norm_num at h3
    omega

end Orders

section B51

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}


theorem b42_l4_cases_ch615 (hc : Nat.card ↥L = 20160) (h : B42ModulePair L U Z) :
    (∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →* ↥L,
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).RealizesVia L U Z π) ∨
      SLExteriorTwo L U Z 4 := by
  rcases h with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ |
    ⟨n, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhat, -, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    h | ⟨π, hπ⟩
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hK] at h1
    exact sl2_ne_l4_ch615 n (h1.symm.trans hc)
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hK] at h1
    rcases LRed5.sl3_cases (EmptyFaithfulMultiple.FFL.one_le_of_card hK) with hm | hm
    · subst hm
      norm_num at h1
      omega
    · omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [Vol2.Ch10.SecA.card_Sp4_pow hK] at h1
    exact sp4_ne_l4_ch615 (EmptyFaithfulMultiple.FFL.one_le_of_card hK) (h1.symm.trans hc)
  ·
    exfalso
    have := FFC.charP_two_of_card_pow hK
    have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 K) :=
      (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hK, hK] at hcard
    exact g2_ne_l4_ch615 (EmptyFaithfulMultiple.FFL.one_le_of_card hK) (hcard.symm.trans hc)
  ·
    exfalso
    have := EmptyFaithfulMultiple.FFL.charP_two_of_card hK
    have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia
      (EmptyFaithfulMultiple.FFL.zornQ_faithful hle) hπ
    change Nat.card ↥L = Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ at h1
    rw [EmptyFaithfulMultiple.FFL.card_commutator_quasithinG2 (by simpa using hK)] at h1
    omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful le_rfl) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 5)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful (by norm_num))
      hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful (by norm_num))
      hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.a7Four_faithful α) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
    omega
  ·
    exact Or.inl ⟨_, FFC.realizesVia_zmod (by simpa using hK) hπ⟩
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d (FFC.realizesVia_zmod (by simpa using hK) hπ)
    rw [card_statedSL_five_zmod1527d] at h1
    omega
  ·
    exact Or.inr h
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (FFC.extSq_faithful (by norm_num))
      hπ
    change Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) at h1
    rw [card_statedSL_five_zmod1527d] at h1
    omega

variable [Finite V] in
theorem b51_l4_cases_ch615 {G : Subgroup (MulAut V)} (hc : Nat.card ↥L = 20160)
    (h : B51Part1 G L) :
    ((∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →* ↥L,
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).RealizesVia L (commV L)
          (fixV L ⊓ commV L) π) ∨
      SLExteriorTwo L (commV L) (fixV L ⊓ commV L) 4) ∨
    SumNatDual L (commV L) 4 ∨
    ∃ k : ℕ, 1 ≤ k ∧ DirectSumOfCopies L (commV L) ⊥
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) k := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hSND⟩ | ⟨-, n, hn, k, hk1, -, hds⟩
  · exact Or.inl (b42_l4_cases_ch615 hc hB)
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at h1
    rcases LRed5.sl3_cases (EmptyFaithfulMultiple.FFL.one_le_of_card hK) with hm | hm
    · subst hm
      norm_num at h1
      omega
    · omega
  ·
    obtain ⟨hn, π, U₁, U₂, hdir, h₁, h₂⟩ := hSND
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨Or.inl rfl, π, U₁, U₂, hdir, h₁, h₂⟩)
    · exfalso
      have h3 := card_eq_of_nat_realizes1527d h₁
      rw [card_statedSL_five_zmod1527d] at h3
      omega
  ·
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr ⟨k, hk1, hds⟩)
    · exfalso
      obtain ⟨I, π, -, -, -, hreal⟩ := hds
      have h3 := card_eq_of_nat_realizes1527d (hreal ⟨0, hk1⟩)
      rw [card_statedSL_five_zmod1527d] at h3
      omega

end B51

section Wedge

open CFSG.Quasithin.JonesParshall

theorem wedge_fix_unitri_ch615 : ∀ c : Fin 6 → ZMod 2,
    wedgeMat4 (transvection (0 : Fin 4) 1 (1 : ZMod 2)) *ᵥ c = c →
    wedgeMat4 (transvection (1 : Fin 4) 2 (1 : ZMod 2)) *ᵥ c = c →
    wedgeMat4 (transvection (2 : Fin 4) 3 (1 : ZMod 2)) *ᵥ c = c →
    c = 0 ∨ c = Pi.single 0 1 := by
  decide

theorem coe_mul_coe_inv_ch615 {k : ℕ} {K : Type*} [Field K] (g : SpecialLinearGroup (Fin k) K) :
    (g : Matrix (Fin k) (Fin k) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

theorem mul_apply_zero_of_col_ch615 {R : Type*} [CommRing R] {m : ℕ} {A B : Matrix (Fin (m + 1))
    (Fin (m + 1)) R} (hB : ∀ l : Fin (m + 1), l ≠ 0 → B l 0 = 0) : (A * B) 0 0 = A 0 0 * B 0 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0 (fun l _ hl => by rw [hB l hl, mul_zero])
    (fun h => absurd (Finset.mem_univ 0) h)]

theorem wedgeMat4_col_of_mem_stabilizer_ch615 {y : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hy : y ∈ stabilizer (flagSpace 4 (ZMod 2) 2)) :
    wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  classical
  have hzero : ∀ z : SpecialLinearGroup (Fin 4) (ZMod 2),
      z ∈ stabilizer (flagSpace 4 (ZMod 2) 2) →
      ∀ i : Fin 4, 2 ≤ (i : ℕ) → ∀ j : Fin 4, (j : ℕ) < 2 →
        (z : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = 0 := by
    intro z hz i hi j hj
    have hej : (Pi.single j 1 : Fin 4 → ZMod 2) ∈ flagSpace 4 (ZMod 2) 2 := by
      rw [mem_flagSpace]
      intro l hl
      have : l ≠ j := fun h => by rw [h] at hl; omega
      simp [this]
    have hxe : (z : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single j 1 ∈ flagSpace 4 (ZMod 2) 2 := by
      rw [← mem_stabilizer.mp hz]
      exact ⟨_, hej, rfl⟩
    have := (mem_flagSpace.mp hxe) i hi
    simpa [mulVec_single_one] using this
  have hcol : ∀ z : SpecialLinearGroup (Fin 4) (ZMod 2),
      z ∈ stabilizer (flagSpace 4 (ZMod 2) 2) → ∀ k : Fin 6, k ≠ 0 →
        wedgeMat4 (z : Matrix (Fin 4) (Fin 4) (ZMod 2)) k 0 = 0 := by
    intro z hz k hk
    have h20 := hzero z hz 2 (by decide) 0 (by decide)
    have h21 := hzero z hz 2 (by decide) 1 (by decide)
    have h30 := hzero z hz 3 (by decide) 0 (by decide)
    have h31 := hzero z hz 3 (by decide) 1 (by decide)
    fin_cases k
    · exact absurd rfl hk
    all_goals simp [wedgeMat4, pr4, h20, h21, h30, h31]
  have hyi : y⁻¹ ∈ stabilizer (flagSpace 4 (ZMod 2) 2) := (stabilizer _).inv_mem hy
  have h00 : wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by
    have hmul : wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        wedgeMat4 ((y⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          1 := by
      rw [← wedgeMat4_mul, coe_mul_coe_inv_ch615, wedgeMat4_one]
    have h1 := congrFun (congrFun hmul 0) 0
    rw [mul_apply_zero_of_col_ch615 (hcol _ hyi), Matrix.one_apply_eq] at h1
    rcases CFSG.QuasithinUnique.Vol2Native.A312L.eq_zero_or_eq_one_of_card_two (Nat.card_zmod 2)
      (wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0) with h0 | h1'
    · rw [h0, zero_mul] at h1
      exact absurd h1 zero_ne_one
    · exact h1'
  ext k
  rw [mulVec_single_one]
  by_cases hk : k = 0
  · subst hk
    simp [Matrix.col_apply, h00]
  · simp [Matrix.col_apply, hcol y hy k hk, hk]

theorem extFix_ch615 {I : Set ℕ} (h2 : 2 ∈ I) {c : Fin 6 → ZMod 2}
    (hc : ∀ u ∈ unitriangular 4 (ZMod 2),
      wedgeMat4 (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c = c)
    {y : SpecialLinearGroup (Fin 4) (ZMod 2)} (hy : y ∈ flagStabilizer 4 (ZMod 2) I) :
    wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c = c := by
  have h01 := hc _ (transvection_mem_unitriangular (show (0 : Fin 4) < 1 by decide) 1)
  have h12 := hc _ (transvection_mem_unitriangular (show (1 : Fin 4) < 2 by decide) 1)
  have h23 := hc _ (transvection_mem_unitriangular (show (2 : Fin 4) < 3 by decide) 1)
  rw [SpecialLinearGroup.transvection_coe] at h01 h12 h23
  rcases wedge_fix_unitri_ch615 c h01 h12 h23 with rfl | rfl
  · exact mulVec_zero _
  · exact wedgeMat4_col_of_mem_stabilizer_ch615 (mem_flagStabilizer.mp hy 2 h2)

end Wedge

section Transport

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [CommGroup V]

theorem coe_conj_ch615 {k : ℕ} {K : Type*} [Field K] (g z : SpecialLinearGroup (Fin k) K) :
    ((g * z * g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      (g : Matrix (Fin k) (Fin k) K) * (z : Matrix (Fin k) (Fin k) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
  rfl

theorem fix_of_dualFix_ch615 {k : ℕ} {K : Type} [Field K] {H : Subgroup (MulAut V)}
    {W : Subgroup V} {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL k K) →* ↥H}
    (h : (FFModel.dualNat (CFSG.Assembly.LowTwoRank.StatedSL k K)).RealizesVia H W ⊥ π)
    (g : SpecialLinearGroup (Fin k) K) {S : Subgroup (MulAut V)}
    (hS : ∀ u ∈ unitriangular k K,
      ((π (specialLinearGroupEquivStatedSL k K (g * u * g⁻¹)) : ↥H) : MulAut V) ∈ S)
    {R : Subgroup (SpecialLinearGroup (Fin k) K)}
    (hR : ∀ v : Fin k → K, (∀ u ∈ unitriangular k K,
        ((u⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v = v) →
      ∀ y ∈ R, ((y⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v = v)
    {w : V} (hwW : w ∈ W) (hw : ∀ s ∈ S, s w = w) :
    ∀ y ∈ R, ((π (specialLinearGroupEquivStatedSL k K (g * y * g⁻¹)) : ↥H) : MulAut V) w = w := by
  set ε := specialLinearGroupEquivStatedSL k K with hε
  set f : SpecialLinearGroup (Fin k) K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL k K) :=
    ε.toMonoidHom.comp (MulAut.conj g).toMonoidHom with hf
  have hfa : ∀ z, f z = ε (g * z * g⁻¹) := fun z => by simp [hf, MulAut.conj_apply]
  have hT : ∀ (z : SpecialLinearGroup (Fin k) K) (v : Fin k → K),
      (((g * z * g⁻¹)⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v =
        ((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ
          (((z⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ
            ((g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v)) := by
    intro z v
    have e : (g * z * g⁻¹)⁻¹ = g * z⁻¹ * g⁻¹ := by group
    rw [e, coe_conj_ch615, Matrix.transpose_mul, Matrix.transpose_mul, ← mulVec_mulVec,
      ← mulVec_mulVec]
  have hgg : ∀ v : Fin k → K, ((g⁻¹ : SpecialLinearGroup (Fin k) K) :
      Matrix (Fin k) (Fin k) K)ᵀ *ᵥ ((g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, ← Matrix.transpose_mul, coe_mul_coe_inv_ch615, Matrix.transpose_one,
      one_mulVec]
  have hgg' : ∀ v : Fin k → K, (g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, ← Matrix.transpose_mul,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe, Matrix.transpose_one,
      one_mulVec]
  have key := fix_of_realizesVia_ch615 h (S' := (unitriangular k K).map f)
    (R' := R.map f) ?_ hwW ?_
  · intro y hy
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa y)).symm.trans
      (key _ ⟨y, hy, rfl⟩)
  · intro m _ hm γ hγ
    obtain ⟨y, hy, rfl⟩ := hγ
    obtain ⟨v, rfl⟩ : ∃ v : Fin k → K,
        (Multiplicative.ofAdd v : Multiplicative (Fin k → K)) = m := ⟨Multiplicative.toAdd m, rfl⟩
    have hact : ∀ z : SpecialLinearGroup (Fin k) K,
        (FFModel.dualNat (CFSG.Assembly.LowTwoRank.StatedSL k K)).act (f z)
            (Multiplicative.ofAdd v) =
          Multiplicative.ofAdd ((((g * z * g⁻¹)⁻¹ : SpecialLinearGroup (Fin k) K) :
            Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v) := fun z => by
      rw [hfa]
      rfl
    have hU : ∀ u ∈ unitriangular k K,
        ((u⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ
          ((g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v) = (g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v := by
      intro u hu
      have h1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hm _ ⟨u, hu, rfl⟩))
      have h2 := Multiplicative.ofAdd.injective ((hact u).symm.trans h1)
      rw [hT] at h2
      have h5 := congrArg (fun x => (g : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ x) h2
      simpa only [hgg'] using h5
    have h4 := hR _ hU y hy
    refine Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr ((hact y).trans ?_))
    rw [hT, h4, hgg]
  · rintro _ ⟨u, hu, rfl⟩
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa u)).trans (hw _ (hS u hu))

open CFSG.Quasithin.JonesParshall in
theorem fix_of_extFix_ch615 {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →* ↥H}
    (h : (FFModel.extSq (ZMod 2) 4).RealizesVia H W ⊥ π)
    (g : SpecialLinearGroup (Fin 4) (ZMod 2)) {S : Subgroup (MulAut V)}
    (hS : ∀ u ∈ unitriangular 4 (ZMod 2),
      ((π (specialLinearGroupEquivStatedSL 4 (ZMod 2) (g * u * g⁻¹)) : ↥H) : MulAut V) ∈ S)
    {R : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))}
    (hR : ∀ c : Fin 6 → ZMod 2, (∀ u ∈ unitriangular 4 (ZMod 2),
        wedgeMat4 (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c = c) →
      ∀ y ∈ R, wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c = c)
    {w : V} (hwW : w ∈ W) (hw : ∀ s ∈ S, s w = w) :
    ∀ y ∈ R, ((π (specialLinearGroupEquivStatedSL 4 (ZMod 2) (g * y * g⁻¹)) : ↥H) :
      MulAut V) w = w := by
  set ε := specialLinearGroupEquivStatedSL 4 (ZMod 2) with hε
  set f : SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
    ε.toMonoidHom.comp (MulAut.conj g).toMonoidHom with hf
  have hfa : ∀ z, f z = ε (g * z * g⁻¹) := fun z => by simp [hf, MulAut.conj_apply]
  have hW : ∀ (z : SpecialLinearGroup (Fin 4) (ZMod 2)) (c : Fin 6 → ZMod 2),
      wedgeMat4 ((g * z * g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c =
      wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (wedgeMat4 (z : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          (wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c)) := by
    intro z c
    rw [coe_conj_ch615, wedgeMat4_mul, wedgeMat4_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have hgg : ∀ c : Fin 6 → ZMod 2, wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c) = c := by
    intro c
    rw [mulVec_mulVec, ← wedgeMat4_mul, coe_mul_coe_inv_ch615, wedgeMat4_one, one_mulVec]
  have hgg' : ∀ c : Fin 6 → ZMod 2, wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c) = c := by
    intro c
    rw [mulVec_mulVec, ← wedgeMat4_mul,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_inv_mul_coe, wedgeMat4_one, one_mulVec]
  have key := fix_of_realizesVia_ch615 h (S' := (unitriangular 4 (ZMod 2)).map f)
    (R' := R.map f) ?_ hwW ?_
  · intro y hy
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa y)).symm.trans
      (key _ ⟨y, hy, rfl⟩)
  · intro m _ hm γ hγ
    obtain ⟨y, hy, rfl⟩ := hγ
    obtain ⟨x, rfl⟩ : ∃ x : ⋀[ZMod 2]^2 (Fin 4 → ZMod 2),
        (Multiplicative.ofAdd x : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) = m :=
      ⟨Multiplicative.toAdd m, rfl⟩
    have hact : ∀ z : SpecialLinearGroup (Fin 4) (ZMod 2),
        (FFModel.extSq (ZMod 2) 4).act (f z) (Multiplicative.ofAdd x) =
          Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin'
            ((g * z * g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
              Matrix (Fin 4) (Fin 4) (ZMod 2))) x) := fun z => by
      rw [hfa]
      rfl
    set c := wedgeCoord4 x with hc
    have hU : ∀ u ∈ unitriangular 4 (ZMod 2), wedgeMat4 (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c) =
        wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c := by
      intro u hu
      have h1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hm _ ⟨u, hu, rfl⟩))
      have h2 := congrArg wedgeCoord4 (Multiplicative.ofAdd.injective ((hact u).symm.trans h1))
      rw [wedgeCoord_map4, hW] at h2
      have h5 := congrArg (fun x => wedgeMat4 ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) h2
      simpa only [hgg'] using h5
    have h4 := hR _ hU y hy
    refine Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr ((hact y).trans ?_))
    congr 1
    apply wedgeCoord4_bijective.1
    rw [wedgeCoord_map4, hW, h4, hgg]
  · rintro _ ⟨u, hu, rfl⟩
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa u)).trans (hw _ (hS u hu))

end Transport

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C


open CFSG.Quasithin.JonesParshall in
theorem false_of_case1_l42_nofix_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) : False := by
  classical
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := CFSG.Quasithin.B69.isSimpleGroup_statedSL_two h2 (by norm_num : 3 ≤ 4)
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple h1.1)
    (Or.inr ⟨4, ZMod 2, inferInstance, inferInstance, by norm_num, h2,
      ⟨e.trans ((CFSG.Quasithin.B69.statedSLEquivStatedProj h2 4).trans
        (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 4 (ZMod 2)))⟩⟩)
  have hZ := center_of_isSimpleGroup_ch615 hs hdl.1
  have hFX : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) ≤ autI hU (borelL T L ⊔ H) :=
    (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  have hc : Nat.card ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
  have htr : ∀ w : IntMod (UX615 T L H) hU,
      (∀ s ∈ autI hU T ⊓ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))), s w = w) →
      w ∈ commV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := fun w hw => by
    have := mem_commV_sup_fixV_ch615 IntMod.sq_eq_one hS.2.2 hw
    rwa [hfix, sup_bot_eq] at this
  have h21 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [h2]; norm_num
  have hNat : ∀ I : Set ℕ, 1 ∈ I → ∀ v : Fin 4 → ZMod 2,
      (∀ u ∈ unitriangular 4 (ZMod 2), (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) →
      ∀ y ∈ flagStabilizer 4 (ZMod 2) I, (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v :=
    fun I h v hv y hy => natFix_ch615 h2 h hv hy
  have hcomb1 : ∀ I J : Set ℕ, (∀ i, 1 ≤ i → i + 1 < 4 → i ∈ I ∨ i + 1 ∈ I) →
      (∀ i, 1 ≤ i → i + 1 < 4 → i ∈ J ∨ i + 1 ∈ J) →
      (∀ d, 1 ≤ d → d < 4 → ¬ (d ∈ I ∧ d ∈ J)) → 1 ∈ I ∨ 1 ∈ J := by
    intro I J hI hJ hd
    have a := hI 1 le_rfl (by norm_num)
    have b := hJ 1 le_rfl (by norm_num)
    have d2 := hd 2 (by norm_num) (by norm_num)
    tauto
  rcases b51_l4_cases_ch615 hc h1.2.1.1 with (⟨π, hπ⟩ | ⟨π, hπ⟩) | hSND | ⟨k, hk1, hds⟩
  ·
    rw [hfix, bot_inf_eq] at hπ
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    set ψ := (specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h21 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF h2 ψ g hg
      (fun R => ∀ v : Fin 4 → ZMod 2,
        (∀ u ∈ unitriangular 4 (ZMod 2), (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) →
          ∀ y ∈ R, (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v)
      (fun R hR w hw y hy => fix_of_natFix_ch615 hπ g (fun u hu => hg u hu) hR (htr w hw) hw y hy)
      fun I J hI hJ hd => ?_
    rcases hcomb1 I J hI hJ hd with h | h
    · exact Or.inl (hNat I h)
    · exact Or.inr (hNat J h)
  ·
    rw [hfix, bot_inf_eq] at hπ
    have hinj := FFC.injective_of_faithful_sec (FFC.extSq_faithful (by norm_num)) hπ
    set ψ := (specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h21 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF h2 ψ g hg
      (fun R => ∀ x : Fin 6 → ZMod 2, (∀ u ∈ unitriangular 4 (ZMod 2),
          wedgeMat4 (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x) →
        ∀ y ∈ R, wedgeMat4 (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x)
      (fun R hR w hw y hy => fix_of_extFix_ch615 hπ g (fun u hu => hg u hu) hR (htr w hw) hw y hy)
      fun I J hI hJ hd => ?_
    have h2IJ : 2 ∈ I ∨ 2 ∈ J := by
      have a := hI 1 le_rfl (by norm_num)
      have b := hJ 1 le_rfl (by norm_num)
      have a2 := hI 2 (by norm_num) (by norm_num)
      have b2 := hJ 2 (by norm_num) (by norm_num)
      have d1 := hd 1 le_rfl (by norm_num)
      have d3 := hd 3 (by norm_num) (by norm_num)
      norm_num at a2 b2
      tauto
    rcases h2IJ with h | h
    · exact Or.inl fun x hx y hy => extFix_ch615 h hx hy
    · exact Or.inr fun x hx y hy => extFix_ch615 h hx hy
  ·
    obtain ⟨-, π, U₁, U₂, ⟨hU12, hU0⟩, h₁, h₂⟩ := hSND
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) h₁
    set ψ := (specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, h₁.1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h21 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF h2 ψ g hg
      (fun R => (∀ v : Fin 4 → ZMod 2,
          (∀ u ∈ unitriangular 4 (ZMod 2), (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) →
            ∀ y ∈ R, (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) ∧
        ∀ v : Fin 4 → ZMod 2, (∀ u ∈ unitriangular 4 (ZMod 2),
          ((u⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ v =
            v) →
          ∀ y ∈ R,
            ((y⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ v =
              v)
      (fun R hR w hw y hy => ?_) fun I J hI hJ hd => ?_
    · have hwW : w ∈ U₁ ⊔ U₂ := hU12 ▸ htr w hw
      refine EmptyFaithfulMultiple.FFL.fix_of_sup hU0
        (T := ((autI hU T ⊓ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) :
          Subgroup _) : Set (MulAut (IntMod (UX615 T L H) hU))))
        (fun t ht v hv => h₁.2.2.2.1 ⟨t, ht.2⟩ v hv) (fun t ht v hv => h₂.2.2.2.1 ⟨t, ht.2⟩ v hv)
        (fun v hv hvS => fix_of_natFix_ch615 h₁ g (fun u hu => hg u hu) hR.1 hv hvS y hy)
        (fun v hv hvS => fix_of_dualFix_ch615 h₂ g (fun u hu => hg u hu) hR.2 hv hvS y hy)
        w hwW hw
    · have h13 : (1 ∈ I ∧ 3 ∈ I) ∨ (1 ∈ J ∧ 3 ∈ J) := by
        have a := hI 1 le_rfl (by norm_num)
        have b := hJ 1 le_rfl (by norm_num)
        have a2 := hI 2 (by norm_num) (by norm_num)
        have b2 := hJ 2 (by norm_num) (by norm_num)
        have d1 := hd 1 le_rfl (by norm_num)
        have d2 := hd 2 (by norm_num) (by norm_num)
        have d3 := hd 3 (by norm_num) (by norm_num)
        norm_num at a2 b2
        tauto
      rcases h13 with ⟨h1', h3'⟩ | ⟨h1', h3'⟩
      · exact Or.inl ⟨hNat I h1', fun v hv y hy => dualFix_ch615 h2 (k := 4) h3' hv hy⟩
      · exact Or.inr ⟨hNat J h1', fun v hv y hy => dualFix_ch615 h2 (k := 4) h3' hv hy⟩
  ·
    obtain ⟨I, π, -, hind, hsup, hreal⟩ := hds
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal ⟨0, hk1⟩)
    set ψ := (specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans
      (MulEquiv.ofBijective π ⟨hinj, (hreal ⟨0, hk1⟩).1⟩) with hψ
    obtain ⟨g, hg⟩ := exists_conj_unitriangular_ch615 (by norm_num) h21 ψ hS
    refine c.false_of_flag_ch615 hU hN hFX hXF hdl hZ hKF h2 ψ g hg
      (fun R => ∀ v : Fin 4 → ZMod 2,
        (∀ u ∈ unitriangular 4 (ZMod 2), (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) →
          ∀ y ∈ R, (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v)
      (fun R hR w hw y hy => ?_) fun I J hI hJ hd => ?_
    · have hw' : w ∈ ⨆ i, I i := by
        have := htr w hw
        rwa [← hsup, bot_sup_eq] at this
      set Rimg : Subgroup (MulAut (IntMod (UX615 T L H) hU)) :=
        (R.map ((MulAut.conj g).trans ψ).toMonoidHom).map
          (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))).subtype with hRimg
      have hyR : ((ψ (g * y * g⁻¹) : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))) :
          MulAut (IntMod (UX615 T L H) hU)) ∈ Rimg :=
        ⟨_, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
      refine fix_of_iSup_ch615 (I := I) (fun i => by simpa using hind i) (S := autI hU T ⊓ _)
        (R := Rimg) (fun s hs i v hv => (hreal i).2.2.2.1 ⟨s, hs.2⟩ v hv)
        (fun i v hv hvS x hx => ?_) hw' hw _ hyR
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
      exact fix_of_natFix_ch615 (hreal i) g (fun u hu => hg u hu) hR hv hvS z hz
    · rcases hcomb1 I J hI hJ hd with h | h
      · exact Or.inl (hNat I h)
      · exact Or.inr (hNat J h)

end Cx615C

end CFSG.Quasithin.H13
