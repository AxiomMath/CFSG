module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUOpp

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU
open Matrix

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def IsUniTriM (ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ) (f : Vm n K →ₗ[K] Vm n K) :
    Prop :=
  ∀ a, f (Pi.single a 1) - Pi.single a 1 ∈ stdFlag (K := K) ℓ (ℓ a)

omit [Finite K] in
theorem sum_single_eq_minus (v : Vm n K) :
    ∑ a, v a • (Pi.single a (1 : K) : Vm n K) = v := by
  ext c'
  simp [Finset.sum_apply, Pi.single_apply]

omit [Finite K] in
theorem IsUniTriM.sub_mem {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    {f : Vm n K →ₗ[K] Vm n K} (hf : IsUniTriM ℓ f) {k : ℕ}
    {v : Vm n K} (hv : v ∈ stdFlag ℓ (k + 1)) : f v - v ∈ stdFlag ℓ k := by
  have e : f v - v = ∑ a, v a • (f (Pi.single a 1) - Pi.single a 1) := by
    conv_lhs => rw [← sum_single_eq_minus v]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_sub]
  rw [e]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : k + 1 ≤ ℓ a
  · rw [hv a ha, zero_smul]
    exact zero_mem _
  · exact Submodule.smul_mem _ _ (stdFlag_mono ℓ (by omega) (hf a))

omit [Finite K] in
theorem isUniTriM_iff_mulVec {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    {A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K} :
    IsUniTriM ℓ (Matrix.mulVecLin A) ↔ ∀ c' a, ¬ ℓ c' < ℓ a → A c' a = (1 : Matrix _ _ K) c' a := by
  constructor
  · intro h c' a hca
    have h1 := h a c' (not_lt.mp hca)
    rw [Matrix.mulVecLin_apply, mulVec_single_one, Pi.sub_apply, col_apply, sub_eq_zero] at h1
    rw [h1, Pi.single_apply, Matrix.one_apply]
  · intro h a c' hc
    rw [Matrix.mulVecLin_apply, mulVec_single_one, Pi.sub_apply, col_apply,
      h c' a (not_lt.mpr hc), Pi.single_apply, Matrix.one_apply, sub_self]

omit [Finite K] in
theorem minusRep_eq_mulVecLin (x : spinGroup (quadMinus n K b c)) :
    minusRep n K b c x = Matrix.mulVecLin (spinMatrix (quadMinus n K b c) x : Matrix _ _ K) :=
  LinearMap.ext fun v => (spinMatrix_mulVec _ x v).symm

variable [CharP K 2]

include hirr in
theorem mem_minusU_iff_isUniTriM {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    {h : spinGroup (quadMinus n K b c)} :
    h ∈ minusU (b := b) (c := c) ℓ ↔ IsUniTriM ℓ (minusRep n K b c h) := by
  have : Finite (spinGroup (quadMinus n K b c)) := finite_spinGroup_quadMinus hirr
  constructor
  · intro hh a
    exact hh.2 _ _ (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
  · intro hh
    exact mem_flagKernel_of_sub_mem _ (stdFlag_mono ℓ) (stdFlag_zero ℓ) fun k v hv => hh.sub_mem hv

theorem perp_stdFlag_minus' {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) (k : ℕ) :
    (minusForm n hirr).polar.perp (stdFlag ℓ k) = stdFlag ℓ (M + 1 - k) := by
  rcases le_total k (M + 1) with hk | hk
  · exact perp_stdFlag_minus hirr hℓ hk
  · rw [stdFlag_eq_top fun a => by have := hℓ.le a; omega, (minusForm n hirr).polar.perp_top,
      Nat.sub_eq_zero_of_le hk, stdFlag_zero]

theorem isMinusLevel_idx {M D' : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) {F' : ℕ → Submodule K (Vm n K)}
    (hF' : IsSelfDual (minusForm n hirr).polar F' (2 * D' + 1))
    (hFs : ∀ j ≤ D', (minusForm n hirr).IsTotallySingular (F' j)) (D : OppData ℓ F') :
    IsMinusLevel (2 * D') D.idx := by
  set N' := 2 * D' + 1 with hN'
  have hdual : ∀ j ≤ N', stdFlag (K := K) ℓ (M + 1 - D.level j) =
      stdFlag ℓ (D.level (N' - j)) := by
    intro j hj
    have h1 := isCompl_perp (minusForm n hirr).polar (D.isCompl_level j)
    rw [perp_stdFlag_minus' hirr hℓ, hF'.perp j hj] at h1
    exact stdFlag_eq_of_isCompl h1 (D.isCompl_level (N' - j))
  have key : ∀ a, ∀ j ≤ N', D.idx (mpr a) < N' - j ↔ ¬ D.idx a < j := by
    intro a j hj
    have h2 : ℓ (mpr a) < D.level (N' - j) ↔ ℓ (mpr a) < M + 1 - D.level j := by
      have e1 := single_mem_stdFlag (K := K) (ℓ := ℓ) (k := D.level (N' - j)) (a := mpr a)
      have e2 := single_mem_stdFlag (K := K) (ℓ := ℓ) (k := M + 1 - D.level j) (a := mpr a)
      rw [← e1, ← e2, hdual j hj]
    rw [D.idx_lt_iff, D.idx_lt_iff, ← not_lt, h2]
    have := hℓ.1 a
    omega
  have hlt : ∀ a, D.idx a < N' := fun a => D.idx_lt_iff.mpr (by
    rw [D.level_eq_zero (hF'.top N' le_rfl)]
    exact Nat.zero_le _)
  have hsum : ∀ a, D.idx a + D.idx (mpr a) = 2 * D' := by
    intro a
    have k1 := (key a (D.idx a) (hlt _).le).mpr (lt_irrefl _)
    have k2 := mt (key a (D.idx a + 1) (hlt _)).mp (not_not.mpr (Nat.lt_succ_self _))
    have := hlt a
    omega
  have hM : ∀ t : Fin 2, 2 * ℓ (.inr (.inr t)) = M := fun t => hℓ.plane t
  have hmid : ∀ j ≤ D', ℓ (.inr (.inr 0)) < D.level j := by
    intro j hj
    by_contra hle
    push Not at hle
    have hsub : stdFlag (K := K) ℓ (D.level j) ≤ stdFlag ℓ (ℓ (.inr (.inr 0))) :=
      stdFlag_mono ℓ hle
    have h1 : finrank K (stdFlag (K := K) ℓ (D.level j)) + finrank K (F' j) =
        finrank K (Vm n K) := Submodule.finrank_add_eq_of_isCompl (D.isCompl_level j)
    have h1' : finrank K (Vm n K) = (n - 1) + ((n - 1) + 2) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
    have h2 : finrank K (stdFlag (K := K) ℓ (D.level j)) ≤
        finrank K (stdFlag (K := K) ℓ (ℓ (.inr (.inr 0)))) := Submodule.finrank_mono hsub
    have h3 : finrank K (F' j) ≤ n - 1 := finrank_le_of_quadMinus hirr (hFs j hj)
    have h4 : finrank K (stdFlag (K := K) ℓ (ℓ (.inr (.inr 0)))) ≤ n - 1 :=
      finrank_le_of_quadMinus hirr fun v hv =>
        quadMinus_eq_zero_of_mem_stdFlag (b := b) (c := c) hℓ (k := ℓ (.inr (.inr 0)))
          (by have := hM 0; omega) hv
    omega
  have hplane : ∀ t : Fin 2, D' ≤ D.idx (.inr (.inr t)) := by
    intro t
    by_contra hlt'
    push Not at hlt'
    have := D.idx_lt_iff.mp (show D.idx (.inr (.inr t)) < D' from hlt')
    have h0 := hmid D' le_rfl
    have : ℓ (.inr (.inr t)) = ℓ (.inr (.inr 0)) := by
      have := hM t
      have := hM 0
      omega
    omega
  refine ⟨hsum, ?_⟩
  have h0 := hplane 0
  have h1 := hplane 1
  have hs := hsum (.inr (.inr 0))
  have : mpr (.inr (.inr 0) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = .inr (.inr 1) := rfl
  rw [this] at hs
  omega

omit [Finite K] in
theorem polar_single_single_minus (a a' : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    polar (quadMinus n K b c) (Pi.single a 1) (Pi.single a' 1) =
      mg b a * (Pi.single a' (1 : K) : Vm n K) (mpr a) :=
  polar_single_minus a _

theorem polar_mulVec_eq {D' : ℕ} {i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hi : IsMinusLevel (2 * D') i)
    {u : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (hu : ∀ c' a, ¬ i a < i c' → u c' a = (1 : Matrix _ _ K) c' a)
    {F' : ℕ → Submodule K (Vm n K)} (hF' : IsSelfDual (minusForm n hirr).polar F' (2 * D' + 1))
    (huF : ∀ a, u *ᵥ Pi.single a 1 ∈ F' (i a + 1)) (x y : Vm n K) :
    polar (quadMinus n K b c) (u *ᵥ x) (u *ᵥ y) = polar (quadMinus n K b c) x y := by
  classical
  have key : ∀ a a', polar (quadMinus n K b c) (u *ᵥ Pi.single a 1) (u *ᵥ Pi.single a' 1) =
      polar (quadMinus n K b c) (Pi.single a 1) (Pi.single a' 1) := by
    intro a a'
    have ha := hi.1 a
    have ha' := hi.1 a'
    by_cases hlt : i a + i a' < 2 * D'
    ·
      have h1 : u *ᵥ Pi.single a 1 ∈ (minusForm n hirr).polar.perp (F' (i a' + 1)) := by
        rw [hF'.perp _ (by omega)]
        exact hF'.mono (by omega) (huF a)
      have h2 := h1 _ (huF a')
      rw [minusForm_β, polar_comm] at h2
      rw [h2, polar_single_single_minus]
      by_cases haa : a' = mpr a
      · subst haa
        rw [mpr_mpr] at ha'
        omega
      · rw [Pi.single_eq_of_ne (Ne.symm haa), mul_zero]
    · rw [polar_sum_single_minus, polar_sum_single_minus]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [mulVec_single_one, mulVec_single_one, col_apply, col_apply]
      have hc := hi.1 c'
      have hmul : u c' a * u (mpr c') a' = (Pi.single a (1 : K) : Vm n K) c' *
          (Pi.single a' (1 : K) : Vm n K) (mpr c') := by
        by_cases h1 : i a < i c'
        · by_cases h2 : i a' < i (mpr c')
          · omega
          · rw [hu _ _ h2, Pi.single_eq_of_ne (fun h => by subst h; omega : c' ≠ a), zero_mul,
              Matrix.one_apply_ne (fun h => by subst h; omega), mul_zero]
        · rw [hu _ _ h1]
          by_cases h2 : i a' < i (mpr c')
          · rw [Pi.single_eq_of_ne (fun h => by rw [h] at h2; omega : mpr c' ≠ a'), mul_zero,
              Matrix.one_apply_ne (fun h => by subst h; omega), zero_mul]
          · rw [hu _ _ h2, Matrix.one_apply, Matrix.one_apply, Pi.single_apply, Pi.single_apply]
      calc u c' a * (mg b c' * u (mpr c') a') = mg b c' * (u c' a * u (mpr c') a') := by ring
        _ = _ := by rw [hmul]; ring
  have hB : (polarBilin (quadMinus n K b c)).compl₁₂ (Matrix.mulVecLin u) (Matrix.mulVecLin u) =
      polarBilin (quadMinus n K b c) :=
    LinearMap.BilinForm.ext_basis (Pi.basisFun K _) fun a a' => by
      simpa [Pi.basisFun_apply] using key a a'
  have := congrArg (fun B => B x y) hB
  simpa using this

omit [Finite K] [CharP K 2] in
theorem quadMinus_single_hyp {a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2}
    (ha : ∀ t, a ≠ .inr (.inr t)) : quadMinus n K b c (Pi.single a 1) = 0 := by
  rcases a with t | t | t
  · rw [quadMinus_apply]
    simp [Pi.single_apply]
  · rw [quadMinus_apply]
    simp [Pi.single_apply]
  · exact absurd rfl (ha t)

omit [CharP K 2] in
theorem quadMinus_mulVec_single {D' : ℕ} {i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hi : IsMinusLevel (2 * D') i)
    {u : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (hu : ∀ c' a, ¬ i a < i c' → u c' a = (1 : Matrix _ _ K) c' a)
    {F' : ℕ → Submodule K (Vm n K)} (huF : ∀ a, u *ᵥ Pi.single a 1 ∈ F' (i a + 1))
    (hFs : ∀ j ≤ D', (minusForm n hirr).IsTotallySingular (F' j))
    (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    quadMinus n K b c (u *ᵥ Pi.single a 1) = quadMinus n K b c (Pi.single a 1) := by
  classical
  have hpl : ∀ t : Fin 2, i (.inr (.inr t)) = D' := fun t => by
    have := hi.plane t
    omega
  by_cases ha : i a < D'
  · have hnp : ∀ t, a ≠ .inr (.inr t) := fun t h => by rw [h, hpl t] at ha; omega
    rw [quadMinus_single_hyp hnp]
    exact hFs (i a + 1) (by omega) _ (huF a)
  · push Not at ha
    rw [quadMinus_apply, quadMinus_apply, mulVec_single_one]
    simp only [col_apply]
    have hplane : ∀ t : Fin 2, u (.inr (.inr t)) a =
        (Pi.single a (1 : K) : Vm n K) (.inr (.inr t)) := by
      intro t
      rw [hu _ _ (by rw [hpl t]; omega), Matrix.one_apply, Pi.single_apply]
    rw [hplane 0, hplane 1]
    congr 3
    refine Finset.sum_congr rfl fun t _ => ?_
    have hs := hi.1 (.inl t)
    simp only [mpr] at hs
    have lhs0 : u (.inl t) a * u (.inr (.inl t)) a = 0 := by
      by_cases h1 : i a < i (.inl t)
      · by_cases h2 : i a < i (.inr (.inl t))
        · omega
        · rw [hu _ _ h2, Matrix.one_apply_ne (fun h => by subst h; omega), mul_zero]
      · rw [hu _ _ h1]
        by_cases hta : (Sum.inl t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = a
        · rw [← hta, hu (.inr (.inl t)) (.inl t) (by rw [← hta] at ha; omega),
            Matrix.one_apply_ne (i := Sum.inr (Sum.inl t)) (j := Sum.inl t) (by simp), mul_zero]
        · rw [Matrix.one_apply_ne hta, zero_mul]
    have rhs0 : (Pi.single a (1 : K) : Vm n K) (.inl t) *
        (Pi.single a (1 : K) : Vm n K) (.inr (.inl t)) = 0 := by
      by_cases hta : (Sum.inl t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = a
      · rw [← hta, Pi.single_eq_of_ne (i := Sum.inl t) (i' := Sum.inr (Sum.inl t)) (by simp),
          mul_zero]
      · rw [Pi.single_eq_of_ne hta, zero_mul]
    rw [lhs0, rhs0]

theorem quadMinus_mulVec_eq {D' : ℕ} {i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hi : IsMinusLevel (2 * D') i)
    {u : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (hu : ∀ c' a, ¬ i a < i c' → u c' a = (1 : Matrix _ _ K) c' a)
    {F' : ℕ → Submodule K (Vm n K)} (hF' : IsSelfDual (minusForm n hirr).polar F' (2 * D' + 1))
    (huF : ∀ a, u *ᵥ Pi.single a 1 ∈ F' (i a + 1))
    (hFs : ∀ j ≤ D', (minusForm n hirr).IsTotallySingular (F' j)) (v : Vm n K) :
    quadMinus n K b c (u *ᵥ v) = quadMinus n K b c v := by
  classical
  have hpol := polar_mulVec_eq hirr hi hu hF' huF
  let L : Vm n K →+ K :=
    { toFun := fun x => quadMinus n K b c (u *ᵥ x) - quadMinus n K b c x
      map_zero' := by simp
      map_add' := fun x y => by
        rw [mulVec_add, QuadraticMap.map_add (quadMinus n K b c),
          QuadraticMap.map_add (quadMinus n K b c), hpol]
        ring }
  have hL : L v = 0 := by
    rw [← sum_single_eq_minus v, map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    change quadMinus n K b c (u *ᵥ (v a • Pi.single a 1)) -
      quadMinus n K b c (v a • Pi.single a 1) = 0
    rw [mulVec_smul, QuadraticMap.map_smul, QuadraticMap.map_smul,
      quadMinus_mulVec_single hirr hi hu huF hFs, sub_self]
  exact sub_eq_zero.mp hL

theorem exists_mem_minusU_flagMap_eq (hn : 4 ≤ n) {M D' : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ)
    {F' : ℕ → Submodule K (Vm n K)} (hF' : IsSelfDual (minusForm n hirr).polar F' (2 * D' + 1))
    (hFs : ∀ j ≤ D', (minusForm n hirr).IsTotallySingular (F' j))
    (hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j)) :
    ∃ (h : spinGroup (quadMinus n K b c)) (i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ),
      IsMinusLevel (2 * D') i ∧ h ∈ minusU (b := b) (c := c) ℓ ∧
      GGOppRad.flagMap (minusRep n K b c) h (stdFlag i) = F' ∧
      minusU (b := b) (c := c) (i ∘ mpr) ≤ minusU ℓ := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  let D : OppData ℓ F' := ⟨hF'.mono, hF'.zero, ⟨_, hF'.top _ le_rfl⟩, hcompl⟩
  have hi : IsMinusLevel (2 * D') D.idx := isMinusLevel_idx hirr hℓ hF' hFs D
  set u := D.elt with hudef
  have hu := mem_stdUop_iff.mp D.elt_mem_stdUop
  have huF : flagMap slRep u (stdFlag D.idx) = F' := D.flagMap_elt
  have huF' : ∀ a, (u : Matrix _ _ K) *ᵥ Pi.single a 1 ∈ F' (D.idx a + 1) := by
    intro a
    have h1 : (stdFlag D.idx (D.idx a + 1)).map (slRep u) = F' (D.idx a + 1) :=
      congrFun huF (D.idx a + 1)
    rw [← h1]
    exact ⟨Pi.single a 1, single_mem_stdFlag.mpr (Nat.lt_succ_self _), by rw [slRep_apply]⟩
  have hQu := quadMinus_mulVec_eq hirr hi hu hF' huF' hFs
  set U := Matrix.SpecialLinearGroup.toLin' u with hU
  have hUv : ∀ v, U v = (u : Matrix _ _ K) *ᵥ v :=
    fun v => Matrix.SpecialLinearGroup.toLin'_apply u v
  have hUO : U ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hUv, hQu]
  have hUlin : (U : Vm n K →ₗ[K] Vm n K) = Matrix.mulVecLin (u : Matrix _ _ K) :=
    LinearMap.ext fun v => hUv v
  have hcond : ∀ c' a, D.idx a < D.idx c' → ℓ c' < ℓ a := fun c' a h => by
    have h1 : ¬ D.level (D.idx a + 1) ≤ ℓ c' := fun h' => by
      have := D.idx_lt_iff.mpr h'
      omega
    have h2 : D.level (D.idx a + 1) ≤ ℓ a := D.idx_lt_iff.mp (Nat.lt_succ_self _)
    omega
  have hstdU : u ∈ stdU (K := K) ℓ := D.stdUop_idx_le D.elt_mem_stdUop
  have hUtri : IsUniTriM ℓ (U : Vm n K →ₗ[K] Vm n K) := by
    rw [hUlin, isUniTriM_iff_mulVec]
    exact mem_stdU_iff.mp hstdU
  set z := M / 2 with hz
  have hM : M = 2 * z := by
    have := hℓ.plane 0
    omega
  have hzs : (minusForm n hirr).IsTotallySingular (stdFlag ℓ z) :=
    isTotallySingular_stdFlag_minus hirr hℓ (by omega)
  have hzperp : (minusForm n hirr).polar.perp (stdFlag ℓ z) ≤ stdFlag ℓ (z + 1) := by
    rw [perp_stdFlag_minus hirr hℓ (by omega), show M + 1 - z = z + 1 by omega]
  have hUΩ : U ∈ omegaGroup (quadMinus n K b c) hQ :=
    mem_omegaGroup_of_triv _ hUO (Z := stdFlag ℓ z) hzs fun v hv => hUtri.sub_mem (hzperp hv)
  obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_minus hirr hn hUΩ
  have hρh : minusRep n K b c h = (U : Vm n K →ₗ[K] Vm n K) :=
    LinearMap.ext fun v => by rw [minusRep_apply, hh]; rfl
  refine ⟨h, D.idx, hi, (mem_minusU_iff_isUniTriM hirr).mpr (hρh ▸ hUtri), ?_, fun x hx => ?_⟩
  · refine Eq.trans ?_ huF
    funext k
    change (stdFlag D.idx k).map (minusRep n K b c h) = (stdFlag D.idx k).map (slRep u)
    have e : minusRep n K b c h = slRep u := by
      refine LinearMap.ext fun v => ?_
      rw [hρh, slRep_apply, LinearEquiv.coe_coe, hUv]
    rw [e]
  · have hx' := (mem_minusU_iff_isUniTriM hirr).mp hx
    rw [minusRep_eq_mulVecLin, isUniTriM_iff_mulVec] at hx'
    refine (mem_minusU_iff_isUniTriM hirr).mpr ?_
    rw [minusRep_eq_mulVecLin, isUniTriM_iff_mulVec]
    intro c' a hca
    refine hx' c' a fun hlt => ?_
    have h1 := hi.1 c'
    have h2 := hi.1 a
    simp only [Function.comp_apply] at hlt
    exact hca (hcond c' a (by omega))

end GGOppRadOmega

end CFSG.StandardType
