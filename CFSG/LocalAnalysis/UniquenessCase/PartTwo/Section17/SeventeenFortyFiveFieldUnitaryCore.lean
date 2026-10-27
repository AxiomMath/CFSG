module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFieldLinearCore
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.UnitaryBlocks
import CFSG.RankThree.PartOne.SLB4B.ModelU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartOne.CTP (suSub range_subfieldPSU_eq_map)
open CFSG.RankThree.PartOne.SLB4B (blockMat blockGL coe_blockGL suBlock coe_suBlock
  blockMat_inl_inl blockMat_inr_inr blockGL_eq_one_of_scalar)

theorem exists_norm_one_pow_five_not_mem {p f f₀ : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (k : Subfield K) (h₀ : UnitaryFieldData p f₀ k)
    (hf : f = 5 * f₀) (h5 : ¬ 5 ∣ p ^ f + 1) : ∃ c : K, h.norm c = 1 ∧ c ^ 5 ∉ k := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  have hq₀1 : 1 < p ^ f₀ := Nat.one_lt_pow (by have := h₀.one_le; omega) h₀.prime.one_lt
  have hqq : p ^ f = (p ^ f₀) ^ 5 := by rw [hf, mul_comm, pow_mul]
  set q := p ^ f with hq
  set q₀ := p ^ f₀ with hq₀
  have hcardK : Fintype.card K = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, hq, ← pow_mul, mul_comm]
  have hcardk : Fintype.card k = q₀ ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h₀.card, hq₀, ← pow_mul, mul_comm]
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hωo : orderOf ω = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, Nat.card_eq_fintype_card, Fintype.card_units,
      hcardK]
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, (by omega : 1 ≤ q)]
    ring
  refine ⟨((ω ^ (q - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← hq, ← pow_succ',
      ← Units.val_pow_eq_pow_val, ← pow_mul, ← hfac, ← hωo, pow_orderOf_eq_one,
      Units.val_one]
  · intro hmem
    have hne : (⟨_, hmem⟩ : k) ≠ 0 := fun h0 =>
      Units.ne_zero _ ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp (congrArg Subtype.val h0))
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨_, hmem⟩ : k) hne
    rw [hcardk] at h1
    have h2 : ω ^ ((q - 1) * 5 * (q₀ ^ 2 - 1)) = 1 := by
      apply Units.ext
      have := congrArg Subtype.val h1
      simpa [← pow_mul] using this
    have h3 : q ^ 2 - 1 ∣ (q - 1) * 5 * (q₀ ^ 2 - 1) := hωo ▸ orderOf_dvd_of_pow_eq_one h2
    rw [hfac, mul_assoc] at h3
    have h4 : q + 1 ∣ 5 * (q₀ ^ 2 - 1) := Nat.dvd_of_mul_dvd_mul_left (by omega) h3
    have hcop : Nat.Coprime (q + 1) 5 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm
    have h6 : q + 1 ∣ q₀ ^ 2 - 1 := hcop.dvd_of_dvd_mul_left h4
    have h7 : 4 ≤ q₀ ^ 2 := by nlinarith
    have h8 := Nat.le_of_dvd (by omega) h6
    have h9 : q₀ ^ 2 ≤ q₀ ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

private theorem blockMat_map {k K : Type} [Field k] [Field K] (φ : k →+* K) {m : ℕ}
    (A : Matrix (Fin 4) (Fin 4) k) :
    (blockMat (m := m) A).map φ = blockMat (m := m) (A.map φ) := by
  ext a b
  induction a using Fin.addCases with
  | left i => induction b using Fin.addCases with
    | left j => rw [Matrix.map_apply, blockMat_inl_inl, blockMat_inl_inl, Matrix.map_apply]
    | right j => simp [blockMat]
  | right i => induction b using Fin.addCases with
    | left j => simp [blockMat]
    | right j =>
      simp only [Matrix.map_apply, blockMat_inr_inr, Matrix.one_apply]
      split_ifs <;> simp

private theorem torusFive_ne_zero {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ)
    (i : Fin (4 + (m + 1))) : torusFive c m i ≠ 0 := by
  induction i using Fin.addCases with
  | left i => rw [torusFive_castAdd]; exact hc
  | right j =>
    induction j using Fin.cases with
    | zero => rw [torusFive_natAdd_zero]; exact inv_ne_zero (pow_ne_zero 4 hc)
    | succ j => rw [torusFive_natAdd_succ]; exact one_ne_zero

private theorem norm_torusFive {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {c : K}
    (hc : h.norm c = 1) (m : ℕ) (i : Fin (4 + (m + 1))) : h.norm (torusFive c m i) = 1 := by
  induction i using Fin.addCases with
  | left i => rw [torusFive_castAdd]; exact hc
  | right j =>
    induction j using Fin.cases with
    | zero =>
      rw [torusFive_natAdd_zero]
      rw [UnitaryFieldData.norm] at hc ⊢
      rw [map_inv₀, map_pow, ← mul_inv, ← mul_pow, hc, one_pow, inv_one]
    | succ j => rw [torusFive_natAdd_succ, UnitaryFieldData.norm, map_one, mul_one]

@[expose] def permFive (m : ℕ) : Equiv.Perm (Fin (4 + (m + 1))) :=
  Equiv.swap (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) *
    Equiv.swap (Fin.castAdd (m + 1) 1) (Fin.castAdd (m + 1) 2)

private theorem sign_permFive (m : ℕ) : Equiv.Perm.sign (permFive m) = 1 := by
  rw [permFive, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by simp [Fin.ext_iff]),
    Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
  simp

private theorem permFive_apply (m : ℕ) : permFive m (Fin.castAdd (m + 1) 0) = Fin.natAdd 4 0 := by
  have h1 : Equiv.swap (Fin.castAdd (m + 1) (1 : Fin 4)) (Fin.castAdd (m + 1) 2)
      (Fin.castAdd (m + 1) 0) = Fin.castAdd (m + 1) 0 :=
    Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  rw [permFive, Equiv.Perm.mul_apply, h1, Equiv.swap_apply_left]

private theorem coe_unitaryDiagGL_inv {L : Type} [Field L] {n : ℕ} (d : Fin n → Lˣ) :
    (((unitaryDiagGL d)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Lˣ) : L) := rfl

theorem primeFormP_eq_top_of_subfield_le {p f f₀ n : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (k : Subfield K)
    (h₀ : UnitaryFieldData p f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c)
    (hf : f = 5 * f₀) (hn : 5 ≤ n) (hq5 : p ^ f % 5 = 2 ∨ p ^ f % 5 = 3)
    (M : Subgroup (primeFormP h (idGram K n))) (hk : (subfieldPSU h h₀ hbar n).range ≤ M)
    (hcent : ∀ x ∈ M, orderOf x = 5 → ∀ g : primeFormP h (idGram K n), Commute g x → g ∈ M) :
    M = ⊤ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + (m + 1) := ⟨n - 5, by omega⟩
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin (4 + (m + 1))) K) :
    Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)) (4 + (m + 1)))
  have hsu : suSub h h₀ hbar (4 + (m + 1)) ≤ M.comap π := by
    intro g hg
    exact hk (by rw [range_subfieldPSU_eq_map]; exact ⟨g, hg, rfl⟩)
  have hpe : ((5 : ℕ) : ℤ) ∣ ((p ^ f₀ : ℕ) : ℤ) ^ 4 - (-1) ^ 4 := by
    have hr : p ^ f₀ % 5 = 2 ∨ p ^ f₀ % 5 = 3 := by
      have hpow : p ^ f = (p ^ f₀) ^ 5 := by rw [hf, mul_comm, pow_mul]
      have key : ∀ r < 5, r ^ 5 % 5 = r := by decide
      rwa [hpow, Nat.pow_mod, key _ (Nat.mod_lt _ (by norm_num))] at hq5
    have h4 : (p ^ f₀) ^ 4 % 5 = 1 := by
      rcases hr with hr | hr <;> rw [Nat.pow_mod, hr]
    have h1 : 1 ≤ (p ^ f₀) ^ 4 := Nat.one_le_pow _ _ (pow_pos h₀.prime.pos _)
    have h5' : (5 : ℕ) ∣ (p ^ f₀) ^ 4 - 1 := by omega
    have h6 := Int.natCast_dvd_natCast.mpr h5'
    push_cast [h1] at h6
    simpa using h6
  obtain ⟨D, hD⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_orderOf_eq_prime_unitarySU
      h₀ (by norm_num : 2 ≤ 4) hpe
  have hq₀ : 1 ≤ p ^ f₀ := Nat.one_le_pow _ _ h₀.prime.pos
  have hd₀ : blockGL (m := m + 1) (D : GL (Fin 4) k) ∈ gramSU h₀ ((1 : GL (Fin (4 + (m + 1))) k) :
      Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) k) := by
    rw [Units.val_one, ← unitarySU_eq_gramSU h₀]
    exact (suBlock (m := m + 1) hq₀ D).2
  obtain ⟨d, hdeq⟩ : ∃ d, d = subfieldSU h h₀ hbar (4 + (m + 1)) ⟨_, hd₀⟩ := ⟨_, rfl⟩
  have hdcoe : (d : GL (Fin (4 + (m + 1))) K) =
      subfieldGL k (4 + (m + 1)) (blockGL (m := m + 1) (D : GL (Fin 4) k)) := by
    rw [hdeq]
    rfl
  have hdM : π d ∈ M := hsu ⟨_, hdeq.symm⟩
  have hd5 : orderOf (π d) = 5 := by
    apply orderOf_eq_prime
    · have hD5 : D ^ 5 = 1 := hD ▸ pow_orderOf_eq_one D
      have hd5' : d ^ 5 = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, hdcoe, ← map_pow, ← map_pow, ← SubgroupClass.coe_pow, hD5]
        simp
      rw [← map_pow, hd5', map_one]
    · intro h1
      obtain ⟨u, -, -, hu⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff d).mp h1)
      have hblk : (d : GL (Fin (4 + (m + 1))) K) =
          blockGL (m := m + 1) (subfieldGL k 4 (D : GL (Fin 4) k)) := by
        rw [hdcoe]
        apply Units.ext
        simp only [coe_subfieldGL, coe_blockGL, blockMat_map]
      have h1' := blockGL_eq_one_of_scalar (m := m + 1) (by omega) ⟨u, (hblk.symm.trans hu).symm⟩
      have hD1 : D = 1 := Subtype.ext (subfieldGL_injective k 4 (h1'.trans (map_one _).symm))
      rw [hD1, orderOf_one] at hD
      norm_num at hD
  have h5 : ¬ 5 ∣ p ^ f + 1 := by
    intro h5
    generalize p ^ f = q at hq5 h5
    omega
  obtain ⟨c, hc1, hc5⟩ := exists_norm_one_pow_five_not_mem h k h₀ hf h5
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hc1
  let w : Fin (4 + (m + 1)) → Kˣ := fun i => Units.mk0 (torusFive c m i) (torusFive_ne_zero hc0 m i)
  have ht : unitaryDiagGL w ∈ gramSU h ((1 : GL (Fin (4 + (m + 1))) K) :
      Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K) :=
    unitaryDiagGL_mem_gramSU h (fun i => by simpa [w] using norm_torusFive h hc1 m i)
      (by simpa [w] using prod_torusFive hc0 m)
  obtain ⟨t, htw⟩ : ∃ t : gramSU h ((1 : GL (Fin (4 + (m + 1))) K) :
      Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K), (t : GL _ K) = unitaryDiagGL w :=
    ⟨⟨_, ht⟩, rfl⟩
  have htd' : Commute t d := by
    show t * d = d * t
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, htw, hdcoe,
      coe_unitaryDiagGL, coe_subfieldGL, coe_blockGL, blockMat_map]
    have hw : (fun i => ((w i : Kˣ) : K)) = torusFive c m := funext fun i => Units.val_mk0 _
    rw [hw]
    exact diagonal_torusFive_commute_blockMat c m _
  have htM : π t ∈ M := hcent _ hdM hd5 _ (htd'.map π)
  let A : primeFormUnitary h ((1 : GL (Fin (4 + (m + 1))) K) :
      Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K) := ⟨t, t.2.1⟩
  have hne : (suSub h h₀ hbar (4 + (m + 1))).map (primeFormConjSU h _ A).toMonoidHom ≠
      suSub h h₀ hbar (4 + (m + 1)) := by
    intro heq
    let s := subfieldSU h h₀ hbar (4 + (m + 1))
      ⟨unitaryPermGL (permFive m), unitaryPermGL_mem_gramSU h₀ (sign_permFive m)⟩
    have hs0 : s ∈ suSub h h₀ hbar (4 + (m + 1)) := ⟨_, rfl⟩
    have hs : (primeFormConjSU h _ A).toMonoidHom s ∈ suSub h h₀ hbar (4 + (m + 1)) := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ hs0
    obtain ⟨g, hg⟩ := hs
    have hR : (((primeFormConjSU h _ A).toMonoidHom s : GL (Fin (4 + (m + 1))) K) :
        Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)
        (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) = c ^ 5 := by
      change (((t : GL (Fin (4 + (m + 1))) K) * (s : GL (Fin (4 + (m + 1))) K) *
          (t : GL (Fin (4 + (m + 1))) K)⁻¹ : GL (Fin (4 + (m + 1))) K) :
        Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)
        (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) = c ^ 5
      rw [htw, Units.val_mul, Units.val_mul, coe_unitaryDiagGL, coe_unitaryDiagGL_inv,
        Matrix.mul_diagonal, Matrix.diagonal_mul]
      have hsij : ((s : GL (Fin (4 + (m + 1))) K) :
          Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)
          (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) = 1 := by
        change ((subfieldGL k (4 + (m + 1)) (unitaryPermGL (permFive m)) :
            GL (Fin (4 + (m + 1))) K) :
          Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)
          (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) = 1
        rw [coe_subfieldGL, Matrix.map_apply, coe_unitaryPermGL, permMatrix_apply',
          if_pos (permFive_apply m)]
        rfl
      rw [hsij]
      simp only [w, Units.val_mk0, Units.val_inv_eq_inv_val, torusFive_castAdd,
        torusFive_natAdd_zero, inv_inv, mul_one]
      ring
    have hgij : ((subfieldSU h h₀ hbar (4 + (m + 1)) g : GL (Fin (4 + (m + 1))) K) :
        Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K)
        (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0) = c ^ 5 := by
      rw [hg]
      exact hR
    apply hc5
    rw [← hgij, coe_subfieldSU, coe_subfieldGL, Matrix.map_apply]
    exact (((g : GL (Fin (4 + (m + 1))) k) :
      Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) k) (Fin.castAdd (m + 1) 0) (Fin.natAdd 4 0)).2
  have hq0 : p ^ f₀ ≠ 2 := by
    intro h2
    have hdvd : p ∣ 2 := h2 ▸ dvd_pow_self p (by have := h₀.one_le; omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h₀.prime Nat.prime_two).mp hdvd)
  have hgen := CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_ne_two p f f₀ K h k h₀ hbar 5
    (by norm_num) (by norm_num) hf hq0 (4 + (m + 1)) (by omega) A hne
  have hle : Subgroup.closure ((suSub h h₀ hbar (4 + (m + 1)) : Set _) ∪
      ((suSub h h₀ hbar (4 + (m + 1))).map (primeFormConjSU h _ A).toMonoidHom : Set _)) ≤
      M.comap π := by
    rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hsu hx
    · have hy' : (primeFormConjSU h _ A).toMonoidHom y = t * y * t⁻¹ := rfl
      rw [hy']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htM (hsu hy)) (Subgroup.inv_mem _ htM)
  have htop : M.comap π = ⊤ := top_le_iff.mp (hgen ▸ hle)
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hg : g ∈ M.comap π := htop ▸ Subgroup.mem_top g
  exact hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
