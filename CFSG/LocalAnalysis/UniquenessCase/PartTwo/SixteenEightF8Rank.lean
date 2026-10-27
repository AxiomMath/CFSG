module

public import CFSG.GroupTheory.WeirSylow.CrossRankForms
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus
  nondegenerate_polarBilin_quadMinus_of_finite)

private theorem s16g_card_le_pow_of_pRank {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H F : Subgroup G} (hFH : F ≤ H) (hF : IsElemAbelian p F) {r : ℕ}
    (hr : Open.pRank p H ≤ r) : Nat.card F ≤ p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos ((CFSG.SectionRank.le_pRank hp.one_lt hFH hF hk).trans hr)

private theorem s16g_orderOf_eight_zmod_three : orderOf (((8 : ℕ) : ZMod 3)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16g_orderOf_eight_zmod_seven : orderOf (((8 : ℕ) : ZMod 7)) = 1 :=
  orderOf_eq_one_iff.2 (by decide)

theorem s16g_card_le_gl_three {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 8) {F : Subgroup (GL ι K)} (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ (Fintype.card ι / 2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine s16g_card_le_pow_of_pRank Nat.prime_three (le_top : F ≤ ⊤) hF ?_
  rw [pRank_top_gl_eq (by decide) (by rw [hK]; decide), hK, s16g_orderOf_eight_zmod_three]

theorem s16g_card_le_gl_seven {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 8) {F : Subgroup (GL ι K)} (hF : IsElemAbelian 7 F) :
    Nat.card F ≤ 7 ^ Fintype.card ι := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine s16g_card_le_pow_of_pRank (by norm_num) (le_top : F ≤ ⊤) hF ?_
  rw [pRank_top_gl_eq (by decide) (by rw [hK]; decide), hK, s16g_orderOf_eight_zmod_seven,
    Nat.div_one]

theorem s16g_card_le_sp {m : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) {p : ℕ}
    (hp : p = 3 ∨ p = 7) {F : Subgroup (GL (Fin m ⊕ Fin m) K)} (hFS : F ≤ StatedSp m K)
    (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ m := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hdvd : p ∣ Nat.card K ^ 2 - 1 := by rw [hK]; rcases hp with rfl | rfl <;> norm_num
  refine s16g_card_le_pow_of_pRank hpp hFS hF ?_
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_top_statedSp_eq_of_dvd hodd hdvd m]

private instance s16g_finite_orthogonalGroup {ι : Type} [Fintype ι] {K : Type} [Field K]
    [Finite K] (Q : QuadraticForm K (ι → K)) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  haveI : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun f : (ι → K) ≃ₗ[K] (ι → K) => (f : (ι → K) → (ι → K)))
      DFunLike.coe_injective
  infer_instance

private def s16gMinusHalf (n : ℕ) (K : Type) [Field K] :
    (Fin (n - 1) → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun y := Sum.elim y (0 : Fin (n - 1) ⊕ Fin 2 → K)
  map_add' _ _ := by
    funext i
    rcases i with i | i <;> simp
  map_smul' _ _ := by
    funext i
    rcases i with i | i <;> simp

private theorem s16g_isMinusType_quadMinus {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsMinusType (quadMinus n K b c) := by
  refine ⟨?_, not_isPlusType_quadMinus hn hirr⟩
  have hj : Function.Injective (s16gMinusHalf n K) := fun x y hxy =>
    funext fun i => congrFun hxy (.inl i)
  refine ⟨LinearMap.range (s16gMinusHalf n K), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun, finrank_quadMinus_space hn]
    omega
  · rintro _ ⟨y, rfl⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [s16gMinusHalf]

private theorem s16g_pRank_top_eq_of_sylow {p : ℕ} [hp : Fact p.Prime] {G G' : Type}
    [Group G] [Finite G] [Group G'] [Finite G'] (P : Sylow p G) (P' : Sylow p G')
    (φ : P ≃* P') : Open.pRank p (⊤ : Subgroup G) = Open.pRank p (⊤ : Subgroup G') := by
  calc Open.pRank p (⊤ : Subgroup G) = Open.pRank p (P : Subgroup G) :=
        ((CFSG.SectionRank.pRank_sylow P).1).symm
    _ = Open.pRank p (⊤ : Subgroup P) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P : Subgroup G)
    _ = Open.pRank p (⊤ : Subgroup P') :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt φ
    _ = Open.pRank p (P' : Subgroup G') :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P' : Subgroup G')).symm
    _ = Open.pRank p (⊤ : Subgroup G') := (CFSG.SectionRank.pRank_sylow P').1

private theorem s16g_pRank_orthMinus_le {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) {n : ℕ} (hn : 1 ≤ n) {r : ℕ}
    (h : (¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ n + (-1) ∧
        Open.pRank p (⊤ : Subgroup (StatedSp n K)) ≤ r) ∨
      (¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ n - (-1) ∧
        Open.pRank p (⊤ : Subgroup (StatedSp (n - 1) K)) ≤ r)) :
    Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))) ≤ r := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hp1 : Odd p := hp.out.odd_of_ne_two hp2
  have hdim : Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n :=
    finrank_quadMinus_space hn
  have hQ : (QuadraticMap.polarBilin (quadMinus n K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hε : ((-1 : ℤ) = 1 ∧ IsPlusType (quadMinus n K b c)) ∨
      ((-1 : ℤ) = -1 ∧ IsMinusType (quadMinus n K b c)) :=
    Or.inr ⟨rfl, s16g_isMinusType_quadMinus hn hirr⟩
  haveI : Finite ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun f => (f : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))) DFunLike.coe_injective
  obtain ⟨P⟩ : Nonempty (Sylow p (TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))) :=
    inferInstance
  obtain ⟨c1, c2, -⟩ := sylow_orthogonal_even hp1 (by rwa [hcard]) hn hdim (quadMinus n K b c)
    hQ hε P
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
    obtain ⟨φ⟩ := c1 (by rwa [hcard]) P'
    rw [s16g_pRank_top_eq_of_sylow P P' φ]
    exact h2
  · obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) K)) := inferInstance
    obtain ⟨φ⟩ := c2 (by rwa [hcard]) P'
    rw [s16g_pRank_top_eq_of_sylow P P' φ]
    exact h2

private theorem s16g_card_le_isometries {K : Type} [Field K] [Finite K] {m : ℕ} {b c : K}
    {p : ℕ} (hp : p.Prime) {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hF : IsElemAbelian p F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) {r : ℕ}
    (hr : Open.pRank p
      (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c))) ≤ r) :
    Nat.card F ≤ p ^ r := by
  haveI : Finite ((Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) :=
    Finite.of_equiv _ (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).toEquiv
  have hQ : ⇑(quadMinus m K b c) = StatedQuadMinus m K b c := coe_quadMinus m K b c
  have hle : F.map (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c) := by
    rintro _ ⟨x, hx, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]
    exact hFQ x hx v
  have hr' : Open.pRank p (TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c) :
      Subgroup ((Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))) ≤ r := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  have h := s16g_card_le_pow_of_pRank hp hle (hF.map _) hr'
  rwa [Subgroup.card_map_of_injective
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).injective] at h

theorem s16g_card_le_orthMinus_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 2) {p : ℕ}
    (hp : p = 3 ∨ p = 7) {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hF : IsElemAbelian p F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ p := by
  subst hm
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hpK : ¬ p ∣ Nat.card K := by rw [hK]; rcases hp with rfl | rfl <;> decide
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hdvd : p ∣ Nat.card K ^ 2 - 1 := by rw [hK]; rcases hp with rfl | rfl <;> norm_num
  have h1 : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (-1) := by
    rw [hK]; rcases hp with rfl | rfl <;> norm_num
  have h2 : Open.pRank p (⊤ : Subgroup (StatedSp (2 - 1) K)) ≤ 1 :=
    (pRank_top_statedSp_eq_of_dvd hodd hdvd (2 - 1)).le
  have h := s16g_card_le_isometries hpp hF hFQ (r := 1)
    (s16g_pRank_orthMinus_le (n := 2) hirr hp2 hpK (by norm_num) (Or.inr ⟨h1, h2⟩))
  simpa using h

theorem s16g_card_le_orthMinus_three_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)} (hF : IsElemAbelian 3 F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ 3 ^ 3 := by
  subst hm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; norm_num
  have h1 : ¬ ((3 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ 3 + (-1) := by rw [hK]; norm_num
  have h2 : Open.pRank 3 (⊤ : Subgroup (StatedSp 3 K)) ≤ 3 :=
    (pRank_top_statedSp_eq_of_dvd (by decide) hdvd 3).le
  exact s16g_card_le_isometries Nat.prime_three hF hFQ (r := 3)
    (s16g_pRank_orthMinus_le (n := 3) hirr (by norm_num) (by rw [hK]; decide) (by norm_num)
      (Or.inl ⟨h1, h2⟩))

theorem s16g_card_le_orthMinus_three_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 3)
    {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)} (hF : IsElemAbelian 7 F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ 7 ^ 2 := by
  subst hm
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : 7 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; norm_num
  have h1 : ¬ ((7 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ 3 - (-1) := by rw [hK]; norm_num
  have h2 : Open.pRank 7 (⊤ : Subgroup (StatedSp (3 - 1) K)) ≤ 2 :=
    (pRank_top_statedSp_eq_of_dvd (by decide) hdvd (3 - 1)).le
  exact s16g_card_le_isometries (by norm_num) hF hFQ (r := 2)
    (s16g_pRank_orthMinus_le (n := 3) hirr (by norm_num) (by rw [hK]; decide) (by norm_num)
      (Or.inr ⟨h1, h2⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
