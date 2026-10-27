module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.GroupTheory.WeirSylow.CrossRankForms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus
  nondegenerate_polarBilin_quadMinus_of_finite)

variable {K : Type} [Field K] [Finite K]

private theorem s16k_card_le_pow_of_pRank {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H F : Subgroup G} (hFH : F ≤ H) (hF : IsElemAbelian p F) {r : ℕ}
    (hr : Open.pRank p H ≤ r) : Nat.card F ≤ p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos ((CFSG.SectionRank.le_pRank hp.one_lt hFH hF hk).trans hr)

private instance s16k_finite_orthogonalGroup {ι : Type} [Fintype ι]
    (Q : QuadraticForm K (ι → K)) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  haveI : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun f : (ι → K) ≃ₗ[K] (ι → K) => (f : (ι → K) → (ι → K)))
      DFunLike.coe_injective
  infer_instance

private def s16kMinusHalf (n : ℕ) (K : Type) [Field K] :
    (Fin (n - 1) → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun y := Sum.elim y (0 : Fin (n - 1) ⊕ Fin 2 → K)
  map_add' _ _ := by
    funext i
    rcases i with i | i <;> simp
  map_smul' _ _ := by
    funext i
    rcases i with i | i <;> simp

private theorem s16k_isMinusType_quadMinus {n : ℕ} (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsMinusType (quadMinus n K b c) := by
  refine ⟨?_, not_isPlusType_quadMinus hn hirr⟩
  have hj : Function.Injective (s16kMinusHalf n K) := fun x y hxy =>
    funext fun i => congrFun hxy (.inl i)
  refine ⟨LinearMap.range (s16kMinusHalf n K), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun, finrank_quadMinus_space hn]
    omega
  · rintro _ ⟨y, rfl⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [s16kMinusHalf]

private theorem s16k_pRank_top_eq_of_sylow {p : ℕ} [hp : Fact p.Prime] {G G' : Type}
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

private theorem s16k_pRank_orthMinus_le {b c : K}
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
    Or.inr ⟨rfl, s16k_isMinusType_quadMinus hn hirr⟩
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
    rw [s16k_pRank_top_eq_of_sylow P P' φ]
    exact h2
  · obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) K)) := inferInstance
    obtain ⟨φ⟩ := c2 (by rwa [hcard]) P'
    rw [s16k_pRank_top_eq_of_sylow P P' φ]
    exact h2

private theorem s16k_card_le_isometries {m : ℕ} {b c : K}
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
  have h := s16k_card_le_pow_of_pRank hp hle (hF.map _) hr'
  rwa [Subgroup.card_map_of_injective
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).injective] at h

private theorem s16k_card_dvd_orthogonal {m : ℕ} {b c : K}
    {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)) := by
  have hQ : ⇑(quadMinus m K b c) = StatedQuadMinus m K b c := coe_quadMinus m K b c
  have hle : F.map (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c) := by
    rintro _ ⟨x, hx, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]
    exact hFQ x hx v
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).injective] at h

private theorem s16k_not_dvd_of_dvd_sq_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q ^ 2 - 1)
    (hp1 : p ≠ 1) : ¬ p ∣ q := by
  intro hd
  have h2 : p ∣ q ^ 2 := hd.trans (dvd_pow_self q two_ne_zero)
  have h3 : p ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h2 h
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have : q ^ 2 - (q ^ 2 - 1) = 1 := by omega
  rw [this] at h3
  exact hp1 (Nat.dvd_one.1 h3)

private theorem s16k_not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 120 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 3) :=
    Nat.Coprime.pow_right 3 (Nat.Coprime.pow_left 2
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h' : p ^ 2 ∣ 2 ^ 3 * 15 := by
    rw [show 2 ^ 3 * 15 = 120 by norm_num]
    exact h
  have h15 : p ^ 2 ∣ 15 := hcop.dvd_of_dvd_mul_left h'
  have hle : p ^ 2 ≤ 15 := Nat.le_of_dvd (by norm_num) h15
  have hp2lt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hp3 : 3 ≤ p := by omega
  have hp4 : p ≤ 3 := by nlinarith
  interval_cases p
  norm_num at h15

private theorem s16k_not_sq_dvd_8160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 8160 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 5) :=
    Nat.Coprime.pow_right 5 (Nat.Coprime.pow_left 2
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h' : p ^ 2 ∣ 2 ^ 5 * 255 := by
    rw [show 2 ^ 5 * 255 = 8160 by norm_num]
    exact h
  have h255 : p ^ 2 ∣ 255 := hcop.dvd_of_dvd_mul_left h'
  have hle : p ^ 2 ≤ 255 := Nat.le_of_dvd (by norm_num) h255
  have hp2lt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hp3 : 3 ≤ p := by omega
  have hp15 : p ≤ 15 := by nlinarith
  interval_cases p <;> norm_num at h255

theorem s16k_card_le_gl_of_dvd {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) {F : Subgroup (GL ι K)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ Fintype.card ι := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hnot : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hd hpK
    have h2 : Nat.card K - (Nat.card K - 1) = 1 := by omega
    exact hp.not_dvd_one (h2 ▸ h1)
  have hmod : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    have hzero : (((Nat.card K - 1 : ℕ)) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hpK
    rw [show Nat.card K = (Nat.card K - 1) + 1 by omega, Nat.cast_add, Nat.cast_one, hzero,
      zero_add]
  have hord : orderOf (((Nat.card K : ℕ) : ZMod p)) = 1 := orderOf_eq_one_iff.2 hmod
  refine s16k_card_le_pow_of_pRank hp (le_top : F ≤ ⊤) hF ?_
  rw [pRank_top_gl_eq hpodd hnot, hord, Nat.div_one]

theorem s16k_card_le_sp_of_dvd {m : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) {F : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hFS : F ≤ StatedSp m K) (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine s16k_card_le_pow_of_pRank hp hFS hF ?_
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_top_statedSp_eq_of_dvd hodd hpK m]

theorem s16k_card_le_orthMinus_two {b c : K} (hK : Nat.card K = 2 ∨ Nat.card K = 4)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hF : IsElemAbelian p F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ p := by
  subst hm
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
  have hdvd := s16k_card_dvd_orthogonal (m := 2) (b := b) (c := c) (F := F) hFQ
  have hk1 : k ≤ 1 := by
    rcases hK with h2 | h4
    · have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) = 120 := by
        have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
            2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) *
              ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
                ∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
          CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
        have h2' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
            120 := by
          rw [h, h2]
          norm_num [Finset.Icc_self]
        exact_mod_cast h2'
      rw [hk, hO] at hdvd
      by_contra hk
      have hk2 : 2 ≤ k := by omega
      exact s16k_not_sq_dvd_120 hp hp2 ((pow_dvd_pow p hk2).trans hdvd)
    · have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) = 8160 := by
        have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
            2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) *
              ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
                ∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
          CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
        have h2' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
            8160 := by
          rw [h, h4]
          norm_num [Finset.Icc_self]
        exact_mod_cast h2'
      rw [hk, hO] at hdvd
      by_contra hk
      have hk2 : 2 ≤ k := by omega
      exact s16k_not_sq_dvd_8160 hp hp2 ((pow_dvd_pow p hk2).trans hdvd)
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem s16k_card_le_orthMinus_three_six {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (h1 : ¬ p ∣ Nat.card K ^ 3 - 1) {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hF : IsElemAbelian p F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ p ^ 3 := by
  subst hm
  haveI : Fact p.Prime := ⟨hp⟩
  have hpKn : ¬ p ∣ Nat.card K :=
    s16k_not_dvd_of_dvd_sq_sub_one Nat.card_pos hpK hp.ne_one
  have h1' : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 3 + (-1) := by
    intro hd
    apply h1
    have heq : (Nat.card K : ℤ) ^ 3 + (-1) = (((Nat.card K ^ 3 - 1 : ℕ)) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow 3 _ Nat.card_pos), Nat.cast_pow, Nat.cast_one]
      ring
    rw [heq, Int.natCast_dvd_natCast] at hd
    exact hd
  have h2 : Open.pRank p (⊤ : Subgroup (StatedSp 3 K)) ≤ 3 :=
    (pRank_top_statedSp_eq_of_dvd (hp.odd_of_ne_two hp2) hpK 3).le
  exact s16k_card_le_isometries hp hF hFQ (r := 3)
    (s16k_pRank_orthMinus_le (n := 3) hirr hp2 hpKn (by norm_num) (Or.inl ⟨h1', h2⟩))

theorem s16k_card_le_orthMinus_three_four {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {m : ℕ} (hm : m = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (h1 : ¬ p ∣ Nat.card K ^ 3 + 1) {F : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hF : IsElemAbelian p F)
    (hFQ : ∀ x ∈ F, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    Nat.card F ≤ p ^ 2 := by
  subst hm
  haveI : Fact p.Prime := ⟨hp⟩
  have hpKn : ¬ p ∣ Nat.card K :=
    s16k_not_dvd_of_dvd_sq_sub_one Nat.card_pos hpK hp.ne_one
  have h1' : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 3 - (-1) := by
    intro hd
    apply h1
    have heq : (Nat.card K : ℤ) ^ 3 - (-1) = (((Nat.card K ^ 3 + 1 : ℕ)) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      ring
    rw [heq, Int.natCast_dvd_natCast] at hd
    exact hd
  have h2 : Open.pRank p (⊤ : Subgroup (StatedSp (3 - 1) K)) ≤ 2 :=
    (pRank_top_statedSp_eq_of_dvd (hp.odd_of_ne_two hp2) hpK (3 - 1)).le
  exact s16k_card_le_isometries hp hF hFQ (r := 2)
    (s16k_pRank_orthMinus_le (n := 3) hirr hp2 hpKn (by norm_num) (Or.inr ⟨h1', h2⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
