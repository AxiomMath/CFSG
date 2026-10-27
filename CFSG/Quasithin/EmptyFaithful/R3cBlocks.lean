module

public import CFSG.Quasithin.EmptyFaithful.R3cSL2
public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
open scoped Matrix

namespace R3c

section GLNine

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem two_le_pRank_three_subgroup_gl [Finite K] (H : Subgroup (GL ι K)) {a b : GL ι K}
    (ha : a ∈ H) (hb : b ∈ H) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    {v₀ v₁ : ι → K} (hav₀ : a ∈ stabVec v₀) (hbv₀ : b ∉ stabVec v₀) (hav₁ : a ∉ stabVec v₁) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := by
  refine two_le_pRank_three_of_commuting (a := (⟨a, ha⟩ : ↥H)) (b := (⟨b, hb⟩ : ↥H)) ?_ ?_ ?_ ?_
    ?_
  · exact Subtype.ext (by simpa using ha3)
  · exact Subtype.ext (by simpa using hb3)
  · exact Subtype.ext hab
  · intro h
    apply hav₁
    have h1 : a = 1 := congrArg Subtype.val h
    rw [h1]
    exact one_mem _
  · exact zpow_ne_of_stabVec H hav₀ hbv₀

@[expose] noncomputable def dglHom (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (ι → Kˣ) →* GL ι K :=
  (Units.map (Matrix.diagonalRingHom ι K).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_dglHom (d : ι → Kˣ) :
    ((dglHom ι K d : GL ι K) : Matrix ι ι K) = Matrix.diagonal fun i => (d i : K) := rfl

theorem dglHom_mulVec_single (d : ι → Kˣ) (i : ι) :
    ((dglHom ι K d : GL ι K) : Matrix ι ι K).mulVec (Pi.single i 1) = Pi.single i (d i : K) := by
  rw [coe_dglHom, Matrix.diagonal_mulVec_single, mul_one]

theorem dglHom_mem_stabVec_single {d : ι → Kˣ} {i : ι} (h : d i = 1) :
    dglHom ι K d ∈ stabVec (Pi.single i (1 : K)) := by
  rw [mem_stabVec, dglHom_mulVec_single, h]
  rfl

theorem dglHom_notMem_stabVec_single {d : ι → Kˣ} {i : ι} (h : d i ≠ 1) :
    dglHom ι K d ∉ stabVec (Pi.single i (1 : K)) := by
  intro hmem
  rw [mem_stabVec, dglHom_mulVec_single] at hmem
  have := congrFun hmem i
  simp only [Pi.single_eq_same] at this
  exact h (Units.ext this)

end GLNine

section SLThree

variable {K : Type} [Field K] [Finite K]

theorem two_le_pRank_three_statedSL_three {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K)) := by
  have hmem : ∀ d : Fin 3 → Kˣ, d 0 * d 1 * d 2 = 1 → dglHom (Fin 3) K d ∈ StatedSL 3 K :=
    fun d hd => (monomialData_statedSL (K := K)).diag_mem d (fun _ => Subgroup.mem_top _) hd
  have hω : ∀ d : Fin 3 → Kˣ, (∀ i, d i ^ 3 = 1) → dglHom (Fin 3) K d ^ 3 = 1 := by
    intro d hd
    rw [← map_pow, ← map_one (dglHom (Fin 3) K)]
    congr 1
    funext i
    exact hd i
  have hωinv : ω⁻¹ ^ 3 = 1 := by rw [inv_pow, h3, inv_one]
  refine two_le_pRank_three_subgroup_gl (StatedSL 3 K)
    (a := dglHom (Fin 3) K ![1, ω, ω⁻¹]) (b := dglHom (Fin 3) K ![ω, ω⁻¹, 1])
    (hmem _ (by simp)) (hmem _ (by simp)) (hω _ ?_) (hω _ ?_) ?_
    (v₀ := Pi.single 0 1) (v₁ := Pi.single 1 1) ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [hωinv, h3]
  · intro i
    fin_cases i <;> simp [hωinv, h3]
  · rw [← map_mul, ← map_mul, mul_comm]
  · exact dglHom_mem_stabVec_single (by simp)
  · exact dglHom_notMem_stabVec_single (by simpa using h1)
  · exact dglHom_notMem_stabVec_single (by simpa using h1)

theorem pRank_three_statedSL_three_odd {n : ℕ} (hn : Odd n) (hK : Nat.card K = 2 ^ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K)) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card K % 3 = 2 := by rw [hK]; exact two_pow_mod_three_of_odd hn
  refine le_antisymm (pRank_three_le_one_of_noElemNine
    (CFSG.Quasithin.F134.noElemNine_of_isCyclic fun Q hQ =>
      isCyclic_of_isPGroup_of_le_GL_three (by omega) (by omega) hQ))
    (one_le_pRank_three_of_dvd ?_)
  rw [card_statedSL_three]
  have h2 : Nat.card K ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by omega
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h3 _) _

theorem pRank_three_statedSL_three_even {n : ℕ} (hn : Even n) (hK : Nat.card K = 2 ^ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K)) = 2 := by
  obtain ⟨ω, h3, h1⟩ := exists_cube_root_of_card_two_pow hn hK
  have hchar : CharP K 2 := charP_two_of_natCard_eq_two_pow hK
  refine le_antisymm ?_ (two_le_pRank_three_statedSL_three h3 h1)
  exact CFSG.RankThree.PartOne.LIT.pRank_le_two_of_det_gl Nat.prime_three
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
    (by simp) (StatedSL 3 K) (fun h hh => det_of_mem_statedSL hh)

end SLThree

theorem pRank_three_specialLinear_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 := by
  refine le_antisymm (pRank_three_le_one_of_noElemNine (noElemNine_specialLinear_two hK))
    (one_le_pRank_three_of_dvd ?_)
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_two_pow hK]
  have h4 : 4 ^ n % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have : 3 ∣ 4 ^ n - 1 := by omega
  exact Dvd.dvd.mul_left this _

section SpFour

variable {K : Type} [Field K]

abbrev symplecticJ2 (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem symplecticJ2_mul_self : symplecticJ2 K * symplecticJ2 K = -1 := by
  rw [symplecticJ2, Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]

theorem symplecticJ2_det_ne_zero : (symplecticJ2 K).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (symplecticJ2_mul_self (K := K))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  norm_num at this

theorem symplecticJ2_alt (v : Fin 2 ⊕ Fin 2 → K) : v ⬝ᵥ (symplecticJ2 K *ᵥ v) = 0 := by
  simp [symplecticJ2, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks,
    Fin.sum_univ_two]
  ring

theorem dglHom_mem_statedSp (d : Fin 2 ⊕ Fin 2 → Kˣ)
    (hd : ∀ i, d (Sum.inr i) * d (Sum.inl i) = 1) :
    dglHom (Fin 2 ⊕ Fin 2) K d ∈ StatedSp 2 K := by
  refine Subgroup.subset_closure ?_
  have hc := coe_dglHom (K := K) d
  have hd' : ∀ i, (d (Sum.inr i) : K) * (d (Sum.inl i) : K) = 1 := fun i => by
    have := congrArg Units.val (hd i)
    rwa [Units.val_mul, Units.val_one] at this
  simp only [Set.mem_ofPred_eq]
  rw [hc, Matrix.diagonal_transpose]
  ext (i | i) (j | j)
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [mul_comm]
      exact hd' i
    · rfl
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact hd' i
    · rfl
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

variable [Finite K]

theorem two_le_pRank_three_statedSp_two {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp 2 K)) := by
  have hωinv : ω⁻¹ ^ 3 = 1 := by rw [inv_pow, h3, inv_one]
  have hω : ∀ d : Fin 2 ⊕ Fin 2 → Kˣ, (∀ i, d i ^ 3 = 1) →
      dglHom (Fin 2 ⊕ Fin 2) K d ^ 3 = 1 := by
    intro d hd
    rw [← map_pow, ← map_one (dglHom (Fin 2 ⊕ Fin 2) K)]
    congr 1
    funext i
    exact hd i
  refine two_le_pRank_three_subgroup_gl (StatedSp 2 K)
    (a := dglHom (Fin 2 ⊕ Fin 2) K (Sum.elim ![ω, 1] ![ω⁻¹, 1]))
    (b := dglHom (Fin 2 ⊕ Fin 2) K (Sum.elim ![1, ω] ![1, ω⁻¹]))
    (dglHom_mem_statedSp _ ?_) (dglHom_mem_statedSp _ ?_) (hω _ ?_) (hω _ ?_) ?_
    (v₀ := Pi.single (Sum.inl 1) 1) (v₁ := Pi.single (Sum.inl 0) 1) ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp
  · rintro (i | i)
    · fin_cases i <;> simp [h3]
    · fin_cases i <;> simp [hωinv]
  · rintro (i | i)
    · fin_cases i <;> simp [h3]
    · fin_cases i <;> simp [hωinv]
  · rw [← map_mul, ← map_mul, mul_comm]
  · exact dglHom_mem_stabVec_single (by simp)
  · exact dglHom_notMem_stabVec_single (by simpa using h1)
  · exact dglHom_notMem_stabVec_single (by simpa using h1)

theorem pRank_three_statedSp_two_le_two [CharP K 2] :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp 2 K)) ≤ 2 := by
  have h := CFSG.RankThree.PartOne.LIT.pRank_le_half_of_form_gl (r := 3) Nat.prime_three
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
    (symplecticJ2 K) symplecticJ2_det_ne_zero symplecticJ2_alt (StatedSp 2 K)
    (fun h hh => CFSG.RankThree.PartOne.LIT.mem_closure_form (fun g hg => hg) h hh)
  simpa using h

theorem pRank_three_statedSp_two_four (hK : Nat.card K = 2 ^ 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp 2 K)) = 2 := by
  obtain ⟨ω, h3, h1⟩ := exists_cube_root_of_card_two_pow (n := 2) (by decide) hK
  have hchar : CharP K 2 := charP_two_of_natCard_eq_two_pow hK
  exact le_antisymm pRank_three_statedSp_two_le_two (two_le_pRank_three_statedSp_two h3 h1)

end SpFour

section LnTwo

theorem mem_statedSL_zmod_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

private def aM4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def aI4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def bM4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

private def bI4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]

private def gA4 : GL (Fin 4) (ZMod 2) := ⟨aM4, aI4, by decide, by decide⟩

private def gB4 : GL (Fin 4) (ZMod 2) := ⟨bM4, bI4, by decide, by decide⟩

private def aM5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

private def aI5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

private def bM5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

private def bI5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

private def gA5 : GL (Fin 5) (ZMod 2) := ⟨aM5, aI5, by decide, by decide⟩

private def gB5 : GL (Fin 5) (ZMod 2) := ⟨bM5, bI5, by decide, by decide⟩

theorem two_le_pRank_three_statedSL_four_two :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 4 (ZMod 2))) := by
  refine two_le_pRank_three_subgroup_gl (StatedSL 4 (ZMod 2)) (a := gA4) (b := gB4)
    (mem_statedSL_zmod_two _) (mem_statedSL_zmod_two _) ?_ ?_ ?_
    (v₀ := ![0, 0, 1, 0]) (v₁ := ![1, 0, 0, 0]) ?_ ?_ ?_
  · exact Units.ext (by simp only [Units.val_pow_eq_pow_val, Units.val_one, gA4]; decide)
  · exact Units.ext (by simp only [Units.val_pow_eq_pow_val, Units.val_one, gB4]; decide)
  · exact Units.ext (by simp only [Units.val_mul, gA4, gB4]; decide)
  · rw [mem_stabVec]
    show aM4.mulVec ![0, 0, 1, 0] = ![0, 0, 1, 0]
    decide
  · rw [mem_stabVec]
    show bM4.mulVec ![0, 0, 1, 0] ≠ ![0, 0, 1, 0]
    decide
  · rw [mem_stabVec]
    show aM4.mulVec ![1, 0, 0, 0] ≠ ![1, 0, 0, 0]
    decide

theorem two_le_pRank_three_statedSL_five_two :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 5 (ZMod 2))) := by
  refine two_le_pRank_three_subgroup_gl (StatedSL 5 (ZMod 2)) (a := gA5) (b := gB5)
    (mem_statedSL_zmod_two _) (mem_statedSL_zmod_two _) ?_ ?_ ?_
    (v₀ := ![0, 0, 1, 0, 0]) (v₁ := ![1, 0, 0, 0, 0]) ?_ ?_ ?_
  · exact Units.ext (by simp only [Units.val_pow_eq_pow_val, Units.val_one, gA5]; decide)
  · exact Units.ext (by simp only [Units.val_pow_eq_pow_val, Units.val_one, gB5]; decide)
  · exact Units.ext (by simp only [Units.val_mul, gA5, gB5]; decide)
  · rw [mem_stabVec]
    show aM5.mulVec ![0, 0, 1, 0, 0] = ![0, 0, 1, 0, 0]
    decide
  · rw [mem_stabVec]
    show bM5.mulVec ![0, 0, 1, 0, 0] ≠ ![0, 0, 1, 0, 0]
    decide
  · rw [mem_stabVec]
    show aM5.mulVec ![1, 0, 0, 0, 0] ≠ ![1, 0, 0, 0, 0]
    decide

theorem card_statedSL_four_two : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five_two : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem pRank_three_statedSL_four_two :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 4 (ZMod 2))) = 2 :=
  le_antisymm (pRank_three_le_two_of_not_dvd (by rw [card_statedSL_four_two]; norm_num))
    two_le_pRank_three_statedSL_four_two

theorem pRank_three_statedSL_five_two :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 5 (ZMod 2))) = 2 :=
  le_antisymm (pRank_three_le_two_of_not_dvd (by rw [card_statedSL_five_two]; norm_num))
    two_le_pRank_three_statedSL_five_two

end LnTwo

end R3c

theorem threeRankBlocks_holds : ThreeRankBlocks := by
  intro G _ _ L
  rw [R3c.pRank_three_eq_pCore_quotient L]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, F, _, _, hF, ⟨e⟩⟩
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact R3c.pRank_three_specialLinear_two hF'
  · rintro n F _ _ hF ⟨e⟩
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact ⟨fun hn => R3c.pRank_three_statedSL_three_odd hn hF',
      fun hn => R3c.pRank_three_statedSL_three_even hn hF'⟩
  · rintro (⟨F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
    · have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact R3c.pRank_three_statedSp_two_four hF'
    · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact R3c.pRank_three_statedSL_four_two
    · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact R3c.pRank_three_statedSL_five_two

end CFSG.Quasithin
