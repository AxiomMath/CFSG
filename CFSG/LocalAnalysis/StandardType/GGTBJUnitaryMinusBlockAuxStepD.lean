module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxStepAMain
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane
open scoped commutatorElement BigOperators

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

@[expose] noncomputable def signVec (Neg : Finset (Fin m)) : Fin m → ZMod p :=
  fun i => if i ∈ Neg then -1 else 1

theorem signVec_of_mem {Neg : Finset (Fin m)} {i : Fin m} (hi : i ∈ Neg) :
    signVec (p := p) Neg i = -1 := if_pos hi

theorem signVec_of_not_mem {Neg : Finset (Fin m)} {i : Fin m} (hi : i ∉ Neg) :
    signVec (p := p) Neg i = 1 := if_neg hi

theorem signVec_mul_self (Neg : Finset (Fin m)) (i : Fin m) :
    signVec (p := p) Neg i * signVec Neg i = 1 := by
  unfold signVec
  split_ifs <;> norm_num

@[expose] noncomputable def signWeyl (Neg : Finset (Fin m)) : hypSU h m ε :=
  weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl Neg)

theorem coe_signWeyl (Neg : Finset (Fin m)) :
    (((signWeyl (h := h) (ε := ε) Neg : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = weylMat h 1 (swapSet Neg) :=
  coe_weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl Neg)

theorem signWeyl_matrix (Neg : Finset (Fin m)) :
    (((signWeyl (h := h) (ε := ε) Neg : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm (weylPerm (ε := ε) (swapSet Neg))
        (fun _ => (1 : F)) := by
  rw [coe_signWeyl, weylMat,
    CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo.weylCoeff_one]

theorem weylPerm_swapSet_inv (Neg : Finset (Fin m)) :
    (weylPerm (ε := ε) (swapSet Neg))⁻¹ = weylPerm (ε := ε) (swapSet Neg) := by
  have hmul : weylPerm (ε := ε) (swapSet Neg) * weylPerm (ε := ε) (swapSet Neg) = 1 := by
    rw [← weylPerm_mul, swapSet_mul_self, weylPerm_one]
  exact inv_eq_of_mul_eq_one_right hmul

theorem weylPerm_swapSet_perm_inl (Neg : Finset (Fin m)) (i : Fin m) :
    weylPerm (ε := ε) (swapSet Neg) (.inl i) =
      if i ∈ Neg then .inr (.inr i) else .inl i :=
  CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo.weylPerm_swapSet_inl Neg i

theorem weylPerm_swapSet_perm_inr_inr (Neg : Finset (Fin m)) (i : Fin m) :
    weylPerm (ε := ε) (swapSet Neg) (.inr (.inr i)) =
      if i ∈ Neg then .inl i else .inr (.inr i) :=
  CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo.weylPerm_swapSet_inr_inr Neg i

theorem signWeyl_conj (hp : p.Prime) {ζ : F} (hζ : ζ ^ p = 1)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    (Neg : Finset (Fin m)) (t : Fin m → ZMod p) :
    signWeyl (h := h) (ε := ε) Neg * τ (Multiplicative.ofAdd t) *
        (signWeyl (h := h) (ε := ε) Neg)⁻¹ =
      τ (Multiplicative.ofAdd fun i => signVec (p := p) Neg i * t i) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hπ := weylPerm_swapSet_inv (ε := ε) Neg
  have hπ' : ∀ a : HypIndex m ε,
      (weylPerm (ε := ε) (swapSet Neg)).symm a = weylPerm (ε := ε) (swapSet Neg) a := by
    intro a
    rw [← hπ]
    rfl
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
  rw [coe_signWeyl, hτ t, hτ (fun i => signVec (p := p) Neg i * t i)]
  rw [weylMat_mul_diagonal]
  have hmul : weylMat (ε := ε) h 1 (swapSet Neg) *
      (weylMat (ε := ε) h 1 (swapSet Neg))⁻¹ = 1 := by
    rw [← coe_signWeyl, ← Matrix.GeneralLinearGroup.coe_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [mul_assoc, hmul, mul_one]
  congr 1
  funext a
  rw [hπ']
  rcases a with i | k | i
  · rw [weylPerm_swapSet_perm_inl]
    by_cases hi : i ∈ Neg
    · rw [if_pos hi]
      simp only [splitEntries, signVec_of_mem hi, neg_one_mul]
      exact (hypEntries_neg hp hζ (t i)).symm
    · rw [if_neg hi]
      simp only [splitEntries, signVec_of_not_mem hi, one_mul]
  · simp [splitEntries]
  · rw [weylPerm_swapSet_perm_inr_inr]
    by_cases hi : i ∈ Neg
    · rw [if_pos hi]
      simp only [splitEntries, signVec_of_mem hi, neg_one_mul]
      rw [hypEntries_neg hp hζ (t i), inv_inv]
    · rw [if_neg hi]
      simp only [splitEntries, signVec_of_not_mem hi, one_mul]


theorem two_ne_zero_zmod' (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

theorem crossEntries_eq_zero
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {g : hypSU h m ε}
    (hg : g ∈ Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E'))) :
    (∀ i ∈ S, ∀ j ∈ S,
        (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) (.inl i) (.inr (.inr j)) = 0) ∧
      ∀ i ∈ S, ∀ j ∈ S,
        (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) (.inr (.inr i)) (.inl j) = 0 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu, i₀, hi₀, hu₀⟩ := hnonzero
  have hmem : Multiplicative.ofAdd u ∈ (Multiplicative.ofAdd '' E' :
      Set (Multiplicative (Fin m → ZMod p))) := ⟨u, hu, rfl⟩
  have hcomm : τ (Multiplicative.ofAdd u) * g = g * τ (Multiplicative.ofAdd u) :=
    (Subgroup.mem_centralizer_iff.mp hg) _ ⟨Multiplicative.ofAdd u, hmem, rfl⟩
  have hmat : (((τ (Multiplicative.ofAdd u) : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *
        (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) =
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) *
        (((τ (Multiplicative.ofAdd u) : hypSU h m ε) : GL (HypIndex m ε) F) :
          Matrix (HypIndex m ε) (HypIndex m ε) F) := by
    simpa only [Subgroup.coe_mul, Units.val_mul] using
      congrArg (fun x : hypSU h m ε => (((x : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F))) hcomm
  have hcne : ∀ i ∈ S, splitEntries (ε := ε) ζ u (.inl i) ≠ (splitEntries (ε := ε) ζ u (.inl i))⁻¹ := by
    intro i hi
    have hc0 : splitEntries (ε := ε) ζ u (.inl i) ≠ 0 := by
      simp only [splitEntries]
      exact pow_ne_zero _ (hζ.ne_zero hp.ne_zero)
    intro hcc
    have hsq : (splitEntries (ε := ε) ζ u (.inl i)) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hcc]
      exact inv_mul_cancel₀ hc0
    have hpow : ζ ^ ((u i).val * 2) = 1 := by
      rw [pow_mul]
      simpa only [splitEntries] using hsq
    have hdvd : p ∣ (u i).val * 2 := (hζ.pow_eq_one_iff_dvd _).mp hpow
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have hm_ne : (u i).val ≠ 0 := by
        intro h0
        have hz : u i = 0 := (ZMod.val_eq_zero (u i)).mp h0
        exact hu₀ (by rw [← hcommon u hu i hi i₀ hi₀]; exact hz)
      have hm_pos : 0 < (u i).val := Nat.pos_of_ne_zero hm_ne
      exact absurd (Nat.le_of_dvd hm_pos h) (by have := ZMod.val_lt (u i); omega)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  constructor
  · intro i hi j hj
    have hentry := congrFun (congrFun hmat (.inl i)) (.inr (.inr j))
    rw [hτ u] at hentry
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hcs : splitEntries (ε := ε) ζ u (.inr (.inr j)) =
        (splitEntries (ε := ε) ζ u (.inl i))⁻¹ := by
      simp only [splitEntries]
      rw [hcommon u hu j hj i hi]
    rw [hcs] at hentry
    have h' : splitEntries (ε := ε) ζ u (.inl i) *
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) (.inl i) (.inr (.inr j)) =
        (splitEntries (ε := ε) ζ u (.inl i))⁻¹ *
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) (.inl i) (.inr (.inr j)) := by
      rw [hentry, mul_comm]
    by_contra hg0
    exact hcne i hi (mul_right_cancel₀ hg0 h')
  · intro i hi j hj
    have hentry := congrFun (congrFun hmat (.inr (.inr i))) (.inl j)
    rw [hτ u] at hentry
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hcu : splitEntries (ε := ε) ζ u (.inl j) = splitEntries (ε := ε) ζ u (.inl i) := by
      simp only [splitEntries]
      rw [hcommon u hu j hj i hi]
    have hcs : splitEntries (ε := ε) ζ u (.inr (.inr i)) =
        (splitEntries (ε := ε) ζ u (.inl i))⁻¹ := rfl
    rw [hcs, hcu] at hentry
    have h' : splitEntries (ε := ε) ζ u (.inl i) *
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) (.inr (.inr i)) (.inl j) =
        (splitEntries (ε := ε) ζ u (.inl i))⁻¹ *
          ((((g : hypSU h m ε) : GL (HypIndex m ε) F) :
            Matrix (HypIndex m ε) (HypIndex m ε) F)) (.inr (.inr i)) (.inl j) := by
      rw [mul_comm, ← hentry]
    by_contra hg0
    exact hcne i hi (mul_right_cancel₀ hg0 h')


theorem leviSU_apply_ne_zero_splitEntries_eq_of_const
    {S : Finset (Fin m)} {A : SpecialLinearGroup (Fin m) F}
    (hA : A ∈ coordBlockSL F S)
    {ζ : F} {t : Fin m → ZMod p} (hconst : ∀ i ∈ S, ∀ j ∈ S, t i = t j)
    {a b : HypIndex m ε}
    (hM : (((leviSU h ε A : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) a b ≠ 0) :
    splitEntries (ε := ε) ζ t a = splitEntries (ε := ε) ζ t b := by
  rw [coe_leviSU, coe_leviGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hM
  rcases a with x | k | x <;> rcases b with y | l | y
  · simp only [blk3_inl_inl] at hM
    by_cases hxy : x = y
    · rw [hxy]
    · by_cases hxJ : x ∈ S
      · by_cases hyJ : y ∈ S
        · simp only [splitEntries]
          rw [hconst x hxJ y hyJ]
        · exfalso
          exact hM (by rw [mem_coordBlockSL_iff.mp hA x y (Or.inr hyJ)]; simp [hxy])
      · exfalso
        exact hM (by rw [mem_coordBlockSL_iff.mp hA x y (Or.inl hxJ)]; simp [hxy])
  · simp only [blk3_inl_inr_inl, Matrix.zero_apply] at hM
    exact absurd rfl hM
  · simp only [blk3_inl_inr_inr, Matrix.zero_apply] at hM
    exact absurd rfl hM
  · simp only [blk3_inr_inl_inl] at hM
    exact absurd rfl hM
  · simp only [blk3_inr_inl_inr_inl, Matrix.one_apply] at hM
    by_cases hkl : k = l
    · rw [hkl]
    · rw [if_neg hkl] at hM
      exact absurd rfl hM
  · simp only [blk3_inr_inl_inr_inr, Matrix.zero_apply] at hM
    exact absurd rfl hM
  · simp only [blk3_inr_inr_inl] at hM
    exact absurd rfl hM
  · simp only [blk3_inr_inr_inr_inl] at hM
    exact absurd rfl hM
  · simp only [blk3_inr_inr_inr_inr] at hM
    by_cases hxy : x = y
    · rw [hxy]
    · by_cases hxJ : x ∈ S
      · by_cases hyJ : y ∈ S
        · simp only [splitEntries]
          rw [hconst x hxJ y hyJ]
        · exfalso
          exact hM (leviDual_apply_eq_zero_of_not_mem h hA hxy (Or.inr hyJ))
      · exfalso
        exact hM (leviDual_apply_eq_zero_of_not_mem h hA hxy (Or.inl hxJ))

theorem diagonal_comm_leviSU_of_const
    {S : Finset (Fin m)} {A : SpecialLinearGroup (Fin m) F}
    (hA : A ∈ coordBlockSL F S)
    {ζ : F} {t : Fin m → ZMod p} (hconst : ∀ i ∈ S, ∀ j ∈ S, t i = t j) :
    diagonal (splitEntries (ε := ε) ζ t) *
      (((leviSU h ε A : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) =
      (((leviSU h ε A : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *
        diagonal (splitEntries (ε := ε) ζ t) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hM : (((leviSU h ε A : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0
  · rw [hM, zero_mul, mul_zero]
  · rw [leviSU_apply_ne_zero_splitEntries_eq_of_const hA hconst hM, mul_comm]

theorem coordBlockSL_map_leviSU_le_centralizer
    {ζ : F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j) :
    (coordBlockSL F S).map (leviSU h ε) ≤
      Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')) := by
  rintro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hz
  have hu' : ∀ i ∈ S, ∀ j ∈ S, u i = u j := hcommon u hu
  have hy : (((τ (Multiplicative.ofAdd u) : hypSU h m ε) :
      GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F) =
      diagonal (splitEntries (ε := ε) ζ u) := hτ u
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hy,
    diagonal_comm_leviSU_of_const hA hu']


@[expose] def pairCoords (S : Finset (Fin m)) : Set (HypIndex m ε) :=
  {x | (∃ i ∈ S, x = .inl i) ∨ ∃ i ∈ S, x = .inr (.inr i)}

theorem mem_pairCoords_inl {S : Finset (Fin m)} {i : Fin m} :
    (.inl i : HypIndex m ε) ∈ pairCoords S ↔ i ∈ S := by
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact Sum.inl.inj h ▸ hj
    · exact absurd h (by simp)
  · exact fun hi => Or.inl ⟨i, hi, rfl⟩

theorem mem_pairCoords_inr_inr {S : Finset (Fin m)} {i : Fin m} :
    (.inr (.inr i) : HypIndex m ε) ∈ pairCoords S ↔ i ∈ S := by
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact absurd h (by simp)
    · exact Sum.inr.inj (Sum.inr.inj h) ▸ hj
  · exact fun hi => Or.inr ⟨i, hi, rfl⟩

theorem inr_inl_not_mem_pairCoords {S : Finset (Fin m)} {k : Fin ε} :
    (.inr (.inl k) : HypIndex m ε) ∉ pairCoords S := by
  rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩) <;> exact absurd h (by simp)

theorem mulVec_hypX_mem_of_mem_pairBlock
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {g : hypSU h m ε}
    (hg : g ∈ Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')))
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) :
    ∀ v ∈ hypX F m ε,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *ᵥ v ∈ hypX F m ε := by
  classical
  obtain ⟨-, hcross⟩ := crossEntries_eq_zero (ε := ε) hp hp2 hζ hτ hcommon hnonzero hg
  have hcol : ∀ i : Fin m,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *ᵥ Pi.single (Sum.inl i) 1 ∈
        hypX F m ε := by
    intro i
    refine ⟨(fun j => (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inl j) (Sum.inl i)), ?_⟩
    funext c
    rcases c with j | k | j
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      rfl
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      show (0 : F) = (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inr (Sum.inl k)) (Sum.inl i)
      have hmem : (Sum.inr (Sum.inl k) : HypIndex m ε) ∉ pairCoords (ε := ε) S :=
        inr_inl_not_mem_pairCoords
      rw [mem_hypBlock.mp hgb _ _ (Or.inl hmem), Matrix.one_apply_ne (by simp)]
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      show (0 : F) = (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inr (Sum.inr j)) (Sum.inl i)
      by_cases hj : j ∈ S
      · by_cases hi : i ∈ S
        · exact (hcross j hj i hi).symm
        · have hmem : (Sum.inl i : HypIndex m ε) ∉ pairCoords (ε := ε) S := by
            simpa [mem_pairCoords_inl] using hi
          rw [mem_hypBlock.mp hgb _ _ (Or.inr hmem), Matrix.one_apply_ne (by simp)]
      · have hmem : (Sum.inr (Sum.inr j) : HypIndex m ε) ∉ pairCoords (ε := ε) S := by
          simpa [mem_pairCoords_inr_inr] using hj
        rw [mem_hypBlock.mp hgb _ _ (Or.inl hmem), Matrix.one_apply_ne (by simp)]
  have hspan : hypX F m ε ≤ Submodule.comap (Matrix.mulVecLin (((g : hypSU h m ε) :
      GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)) (hypX F m ε) := by
    conv_lhs => rw [hypX_eq_span]
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa [Matrix.mulVecLin_apply] using hcol i
  intro v hv
  simpa [Matrix.mulVecLin_apply] using hspan hv

theorem mulVec_hypY_mem_of_mem_pairBlock
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {g : hypSU h m ε}
    (hg : g ∈ Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')))
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) :
    ∀ v ∈ hypY F m ε,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *ᵥ v ∈ hypY F m ε := by
  classical
  obtain ⟨hcross, -⟩ := crossEntries_eq_zero (ε := ε) hp hp2 hζ hτ hcommon hnonzero hg
  have hcol : ∀ i : Fin m,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) *ᵥ Pi.single (Sum.inr (Sum.inr i)) 1 ∈
        hypY F m ε := by
    intro i
    refine ⟨(fun j => (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr i))), ?_⟩
    funext c
    rcases c with j | k | j
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      show (0 : F) = (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inl j) (Sum.inr (Sum.inr i))
      by_cases hj : j ∈ S
      · by_cases hi : i ∈ S
        · exact (hcross j hj i hi).symm
        · have hmem : (Sum.inr (Sum.inr i) : HypIndex m ε) ∉ pairCoords (ε := ε) S := by
            simpa [mem_pairCoords_inr_inr] using hi
          rw [mem_hypBlock.mp hgb _ _ (Or.inr hmem), Matrix.one_apply_ne (by simp)]
      · have hmem : (Sum.inl j : HypIndex m ε) ∉ pairCoords (ε := ε) S := by
          simpa [mem_pairCoords_inl] using hj
        rw [mem_hypBlock.mp hgb _ _ (Or.inl hmem), Matrix.one_apply_ne (by simp)]
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      show (0 : F) = (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inr i))
      have hmem : (Sum.inr (Sum.inl k) : HypIndex m ε) ∉ pairCoords (ε := ε) S :=
        inr_inl_not_mem_pairCoords
      rw [mem_hypBlock.mp hgb _ _ (Or.inl hmem), Matrix.one_apply_ne (by simp)]
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      rfl
  have hspan : hypY F m ε ≤ Submodule.comap (Matrix.mulVecLin (((g : hypSU h m ε) :
      GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)) (hypY F m ε) := by
    conv_lhs => rw [hypY_eq_span]
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa [Matrix.mulVecLin_apply] using hcol i
  intro v hv
  simpa [Matrix.mulVecLin_apply] using hspan hv

theorem mem_xyStab_of_mem_pairBlock
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {g : hypSU h m ε}
    (hg : g ∈ Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')))
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) :
    g ∈ xyStab h m ε := by
  have : Fact p.Prime := ⟨hp⟩
  have hg' : g⁻¹ ∈ Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')) :=
    (Subgroup.centralizer _).inv_mem hg
  have hgb' : g⁻¹ ∈ hypBlock h (pairCoords (ε := ε) S) :=
    (hypBlock h (pairCoords (ε := ε) S)).inv_mem hgb
  refine ⟨smul_eq_of_mulVec_mem (g := ((g : hypSU h m ε) : GL (HypIndex m ε) F))
    (mulVec_hypX_mem_of_mem_pairBlock hp hp2 hζ hτ hcommon hnonzero hg hgb)
    ?_, smul_eq_of_mulVec_mem (g := ((g : hypSU h m ε) : GL (HypIndex m ε) F))
    (mulVec_hypY_mem_of_mem_pairBlock hp hp2 hζ hτ hcommon hnonzero hg hgb) ?_⟩
  · intro v hv
    simpa only [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv] using
      mulVec_hypX_mem_of_mem_pairBlock hp hp2 hζ hτ hcommon hnonzero hg' hgb' v hv
  · intro v hv
    simpa only [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv] using
      mulVec_hypY_mem_of_mem_pairBlock hp hp2 hζ hτ hcommon hnonzero hg' hgb' v hv


theorem zBlock_eq_one_of_mem_pairBlock {S : Finset (Fin m)} {g : hypSU h m ε}
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) :
    zBlock (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = 1 := by
  ext k l
  show (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) (.inr (.inl k)) (.inr (.inl l)) =
    (1 : Matrix (Fin ε) (Fin ε) F) k l
  rw [mem_hypBlock.mp hgb _ _ (Or.inl (inr_inl_not_mem_pairCoords (k := k)))]
  by_cases h : k = l
  · subst h; simp
  · simp [h]

theorem xBlock_apply_of_not_mem_pairBlock {S : Finset (Fin m)} {g : hypSU h m ε}
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) {i j : Fin m} (hij : i ∉ S ∨ j ∉ S) :
    xBlock (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) i j = if i = j then 1 else 0 := by
  rw [xBlock, Matrix.of_apply]
  have hmem : (.inl i : HypIndex m ε) ∉ pairCoords (ε := ε) S ∨
      (.inl j : HypIndex m ε) ∉ pairCoords (ε := ε) S := by
    rcases hij with h | h
    · exact Or.inl (by simpa [mem_pairCoords_inl] using h)
    · exact Or.inr (by simpa [mem_pairCoords_inl] using h)
  rw [mem_hypBlock.mp hgb _ _ hmem, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by simp [h]), if_neg h]

theorem leviSU_eq_of_mem_xyStab_of_mem_pairBlock {S : Finset (Fin m)} {g : hypSU h m ε}
    (hxy : g ∈ xyStab h m ε) (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S))
    {A : SpecialLinearGroup (Fin m) F}
    (hA : (A : Matrix (Fin m) (Fin m) F) = xBlock (((g : hypSU h m ε) :
      GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)) :
    leviSU h ε A = g := by
  have htoGL : SpecialLinearGroup.toGL A = xBlockUnits h m ε ⟨g, hxy⟩ := by
    apply Units.ext
    rw [SpecialLinearGroup.coe_GL_coe_matrix, hA, coe_xBlockUnits]
  apply Subtype.ext
  apply Units.ext
  rw [coe_leviSU, coe_leviGL, htoGL, coe_eq_blk3 h ⟨g, hxy⟩,
    zBlock_eq_one_of_mem_pairBlock hgb]
  congr 2

theorem mem_coordBlockSL_of_xBlock {S : Finset (Fin m)} {g : hypSU h m ε}
    (hgb : g ∈ hypBlock h (pairCoords (ε := ε) S)) {A : SpecialLinearGroup (Fin m) F}
    (hA : (A : Matrix (Fin m) (Fin m) F) = xBlock (((g : hypSU h m ε) :
      GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)) :
    A ∈ coordBlockSL F S := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  rw [hA]
  exact xBlock_apply_of_not_mem_pairBlock hgb hij


theorem coordBlockSL_eq_bot_of_card_le_one {S : Finset (Fin m)} (hS : S.card ≤ 1) :
    coordBlockSL F S = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  have hsupp : ∀ i j, i ≠ j → (A : Matrix (Fin m) (Fin m) F) i j = 0 := by
    intro i j hij
    by_cases hsi : i ∈ S
    · by_cases hsj : j ∈ S
      · exfalso
        have h2 : 2 ≤ S.card := by
          have hle := Finset.card_le_card (s := ({i, j} : Finset (Fin m))) (t := S) (by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption)
          rwa [Finset.card_pair hij] at hle
        omega
      · rw [(mem_coordBlockSL_iff.mp hA) i j (Or.inr hsj), if_neg hij]
    · rw [(mem_coordBlockSL_iff.mp hA) i j (Or.inl hsi), if_neg hij]
  have hdiag : ∀ i, i ∉ S → (A : Matrix (Fin m) (Fin m) F) i i = 1 := by
    intro i hi
    rw [(mem_coordBlockSL_iff.mp hA) i i (Or.inl hi), if_pos rfl]
  have hAeq : (A : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (A : Matrix (Fin m) (Fin m) F) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [hsupp i j hij, Matrix.diagonal_apply_ne _ hij]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hAeq, Matrix.diagonal_apply_eq]
    by_cases hi : i ∈ S
    · have hcard : S.card = 1 := by
        have := Finset.one_le_card.mpr ⟨i, hi⟩
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
      have hia : i = a := by simpa using hi
      subst hia
      have hdet := A.2
      rw [hAeq, Matrix.det_diagonal, Finset.prod_eq_single i] at hdet
      · simpa using hdet
      · intro j _ hji
        exact hdiag j (by simpa using hji)
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [hdiag i hi]
      simp
  · rw [hsupp i j hij]
    simp [Matrix.one_apply_ne hij]

theorem commutator_le_map_coordBlockSL
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {J' : Subgroup (hypSU h m ε)}
    (hJ' : CFSG.Assembly.IsComponentOf J' (Subgroup.centralizer
      (τ '' (Multiplicative.ofAdd '' E'))))
    (hJ'le : J' ≤ hypBlock h (pairCoords (ε := ε) S)) :
    ⁅J',J'⁆ ≤ (coordBlockSL F S).map (leviSU h ε) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hJsub : J' ≤ xyStab h m ε := fun g hg =>
    mem_xyStab_of_mem_pairBlock hp hp2 hζ hτ hcommon hnonzero (hJ'.1 hg) (hJ'le hg)
  let J'' : Subgroup (xyStab h m ε) := J'.comap (xyStab h m ε).subtype
  let δ : xyStab h m ε →* Fˣ := (Matrix.GeneralLinearGroup.det).comp (xBlockUnits h m ε)
  have hδ : ⁅J'',J''⁆ ≤ δ.ker := by
    refine Subgroup.commutator_le.mpr fun u _ v _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hmap : J''.map (xyStab h m ε).subtype = J' := by
    rw [Subgroup.map_comap_eq_self]
    rwa [Subgroup.range_subtype]
  have hcommmap : (⁅J'',J''⁆).map (xyStab h m ε).subtype = ⁅J',J'⁆ := by
    rw [Subgroup.map_commutator, hmap]
  intro g hg
  rw [← hcommmap] at hg
  obtain ⟨g', hg'mem, hg'val⟩ := Subgroup.mem_map.mp hg
  have hJ'mem : g ∈ J' := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨g', Subgroup.commutator_le_self _ hg'mem, hg'val⟩
  have hxy : g ∈ xyStab h m ε := hJsub hJ'mem
  have hgb : g ∈ hypBlock h (pairCoords (ε := ε) S) := hJ'le hJ'mem
  have hdet' : (((xBlockUnits h m ε g' : GL (Fin m) F)) :
      Matrix (Fin m) (Fin m) F).det = 1 := by
    have hδ1 : δ g' = 1 := hδ hg'mem
    have := congrArg Units.val hδ1
    simpa [δ, Matrix.GeneralLinearGroup.det] using this
  have hg'eq : g' = ⟨g, hxy⟩ := Subtype.ext hg'val
  rw [hg'eq] at hdet'
  let A : SpecialLinearGroup (Fin m) F := ⟨(xBlockUnits h m ε ⟨g, hxy⟩ : GL (Fin m) F), hdet'⟩
  have hAmat : (A : Matrix (Fin m) (Fin m) F) =
      xBlock (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) := by
    change (((xBlockUnits h m ε ⟨g, hxy⟩ : GL (Fin m) F)) :
      Matrix (Fin m) (Fin m) F) = _
    rw [coe_xBlockUnits]
  refine Subgroup.mem_map.mpr ⟨A, ?_, ?_⟩
  · exact mem_coordBlockSL_of_xBlock hgb hAmat
  · exact leviSU_eq_of_mem_xyStab_of_mem_pairBlock hxy hgb hAmat

theorem eq_map_coordBlockSL_of_isComponentOf
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E' : Set (Fin m → ZMod p)} {S : Finset (Fin m)}
    (hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j)
    (hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0)
    {J' : Subgroup (hypSU h m ε)}
    (hJ' : CFSG.Assembly.IsComponentOf J' (Subgroup.centralizer
      (τ '' (Multiplicative.ofAdd '' E'))))
    (hJ'le : J' ≤ hypBlock h (pairCoords (ε := ε) S)) :
    J' = (coordBlockSL F S).map (leviSU h ε) := by
  classical
  have hcomm := commutator_le_map_coordBlockSL hp hp2 hζ hτ hcommon hnonzero hJ' hJ'le
  have hperfect : J' = ⁅J',J'⁆ := (commutator_self_eq_of_isQuasisimple hJ'.2.2).symm
  have hJ'Q : J' ≤ (coordBlockSL F S).map (leviSU h ε) := hperfect ▸ hcomm
  have hQle : (coordBlockSL F S).map (leviSU h ε) ≤
      Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')) :=
    coordBlockSL_map_leviSU_le_centralizer hτ hcommon
  have h2S : 2 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hbot : (coordBlockSL F S).map (leviSU h ε) = ⊥ := by
      rw [coordBlockSL_eq_bot_of_card_le_one (by omega), Subgroup.map_bot]
    have hJ'bot : J' = ⊥ := le_bot_iff.mp (hbot ▸ hJ'Q)
    exact LinSemisimple.false_of_isQuasisimple_of_commute hJ'.2.2 (fun u hu v hv => by
      have hu1 : u = 1 := Subgroup.mem_bot.mp (hJ'bot ▸ hu)
      have hv1 : v = 1 := Subgroup.mem_bot.mp (hJ'bot ▸ hv)
      rw [hu1, hv1])
  have h4 : 4 ≤ Nat.card F := by
    have hf : 2 ≤ f := two_le_of_dvd_sub_one hp hpq h.one_le
    rw [h.card]
    have hle : 2 ^ 2 ≤ 2 ^ (2 * f) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    simpa using hle
  have hQ : CFSG.Assembly.IsQuasisimple ((coordBlockSL F S).map (leviSU h ε)) := by
    have : Finite F := h.finite
    have hq := isQuasisimple_coordBlockSL (k := F) (n := m) h2S h4
    let g : ↥(coordBlockSL F S) →* hypSU h m ε :=
      (leviSU h ε).comp (coordBlockSL F S).subtype
    have hg : Function.Injective g := fun A B hab =>
      Subtype.ext (leviSU_injective h hab)
    have hrange : g.range = (coordBlockSL F S).map (leviSU h ε) := by
      rw [MonoidHom.range_eq_map]
      change (⊤ : Subgroup ↥(coordBlockSL F S)).map ((leviSU h ε).comp
        (coordBlockSL F S).subtype) = (coordBlockSL F S).map (leviSU h ε)
      rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    have e : ↥(coordBlockSL F S) ≃* ((coordBlockSL F S).map (leviSU h ε)) :=
      (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hrange)
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (hq.of_mulEquiv e.symm)
  exact eq_of_isComponentOf_le_of_isQuasisimple hJ' hJ'Q hQle hQ

end CFSG.StandardType.SuSplitRootGen


end
