module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParCard
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphAltEightLevi
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

private def s16t3SlCuts (n : ℕ) : Set ℕ := {c | 0 < c ∧ c < n ∧ Even c}

private def s16t3SlStarts (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => Even (a : ℕ) ∧ (a : ℕ) + 2 ≤ n

private theorem s16t3_even_add_two {a : ℕ} (ha : Even a) : Even (a + 2) := by
  rcases ha with ⟨i, rfl⟩
  exact ⟨i + 1, by omega⟩

private theorem s16t3_even_add_two_le {a c : ℕ} (ha : Even a) (hc : Even c) (h : a < c) :
    a + 2 ≤ c := by
  rcases ha with ⟨i, rfl⟩
  rcases hc with ⟨j, rfl⟩
  omega

private theorem s16t3_linBlockLen_slCuts (n : ℕ) (a : Fin n) :
    linBlockLen n (s16t3SlCuts n) a =
      if Even (a : ℕ) then min 2 (n - (a : ℕ)) else 0 := by
  by_cases hev : Even (a : ℕ)
  · rw [if_pos hev]
    have han : (a : ℕ) < n := a.isLt
    have h1 : 1 ≤ min 2 (n - (a : ℕ)) := by omega
    have h2 : (a : ℕ) + min 2 (n - (a : ℕ)) ≤ n := by omega
    have hs : (a : ℕ) = 0 ∨ (a : ℕ) ∈ s16t3SlCuts n := by
      rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, han, hev⟩
    have he : (a : ℕ) + min 2 (n - (a : ℕ)) = n ∨
        (a : ℕ) + min 2 (n - (a : ℕ)) ∈ s16t3SlCuts n := by
      by_cases hle : n - (a : ℕ) ≤ 2
      · left; omega
      · right
        have hlt : (a : ℕ) + 2 < n := by omega
        have hmin : min 2 (n - (a : ℕ)) = 2 := min_eq_left_iff.2 (by omega)
        rw [hmin]
        exact ⟨by omega, hlt, s16t3_even_add_two hev⟩
    have hno : ∀ c ∈ s16t3SlCuts n,
        ¬ ((a : ℕ) < c ∧ c < (a : ℕ) + min 2 (n - (a : ℕ))) := by
      rintro c ⟨-, -, hcev⟩ ⟨hac, hclt⟩
      have := s16t3_even_add_two_le hev hcev hac
      omega
    have hfin := linBlockLen_eq_of_maxBlock (n := n) (I := s16t3SlCuts n)
      (a := (a : ℕ)) (m := min 2 (n - (a : ℕ))) han h2 hs he hno h1
    simpa using hfin.symm
  · rw [if_neg hev]
    have hns : ¬ ((a : ℕ) = 0 ∨ (a : ℕ) ∈ s16t3SlCuts n) := by
      rintro (h | h)
      · exact hev (by rw [h]; norm_num)
      · exact hev h.2.2
    rw [linBlockLen_of_not_start hns]

private theorem s16t3_linBlockLen_slCuts_le_two (n : ℕ) (a : Fin n) :
    linBlockLen n (s16t3SlCuts n) a ≤ 2 := by
  rw [s16t3_linBlockLen_slCuts]
  by_cases hev : Even (a : ℕ)
  · rw [if_pos hev]
    exact min_le_left 2 (n - (a : ℕ))
  · rw [if_neg hev]
    exact Nat.zero_le 2

private theorem s16t3_linBlockLen_slCuts_eq_two (n : ℕ) (a : Fin n) :
    linBlockLen n (s16t3SlCuts n) a = 2 ↔ Even (a : ℕ) ∧ (a : ℕ) + 2 ≤ n := by
  rw [s16t3_linBlockLen_slCuts]
  by_cases hev : Even (a : ℕ)
  · rw [if_pos hev]
    constructor
    · intro h
      have han : (a : ℕ) < n := a.isLt
      exact ⟨hev, by have := min_eq_left_iff.1 h; omega⟩
    · rintro ⟨-, h2⟩
      exact min_eq_left_iff.2 (by omega)
  · rw [if_neg hev]
    constructor
    · intro h; exact absurd h (by norm_num)
    · rintro ⟨h, -⟩; exact absurd h hev

private theorem s16t3SlStarts_card (n : ℕ) : (s16t3SlStarts n).card = n / 2 := by
  classical
  let φ : Fin (n / 2) → Fin n := fun i =>
    ⟨2 * (i : ℕ), by
      have hi : (i : ℕ) < n / 2 := i.isLt
      have h2 : 2 * (i : ℕ) < 2 * (n / 2) := Nat.mul_lt_mul_of_pos_left hi (by norm_num)
      have h3 : 2 * (n / 2) ≤ n := by
        rw [mul_comm]
        exact Nat.div_mul_le_self n 2
      omega⟩
  have hφinj : Function.Injective φ := by
    intro i j hij
    apply Fin.ext
    have h : 2 * (i : ℕ) = 2 * (j : ℕ) := congrArg Fin.val hij
    omega
  have hS : s16t3SlStarts n = Finset.image φ Finset.univ := by
    ext a
    simp only [s16t3SlStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hev, hle⟩
      obtain ⟨i, hi_eq⟩ := hev
      have hi : i < n / 2 := by
        have h2 : (i + 1) * 2 ≤ n := by omega
        have := (Nat.le_div_iff_mul_le (show 0 < 2 by norm_num)).2 h2
        omega
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Fin.ext
      show 2 * i = (a : ℕ)
      rw [hi_eq]
      omega
    · rintro ⟨i, hia⟩
      rw [← hia]
      refine ⟨⟨i, by show 2 * (i : ℕ) = i + i; omega⟩, ?_⟩
      have hi : (i : ℕ) < n / 2 := i.isLt
      have h3 : (i : ℕ) + 1 ≤ n / 2 := by omega
      have h2 : ((i : ℕ) + 1) * 2 ≤ n :=
        (Nat.le_div_iff_mul_le (show 0 < 2 by norm_num)).1 h3
      show 2 * (i : ℕ) + 2 ≤ n
      omega
  rw [hS, Finset.card_image_of_injective Finset.univ hφinj]
  simp

private theorem s16t3_card_gl_le_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {k : ℕ} (hk : k ≤ 2) : Nat.card (GL (Fin k) K) = if k = 2 then 6 else 1 := by
  letI := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [if_neg (by norm_num : ¬ (0 : ℕ) = 2), Matrix.card_GL_field]
    simp
  · rw [if_neg (by norm_num : ¬ (1 : ℕ) = 2), Matrix.card_GL_field, Fin.prod_univ_one]
    norm_num [hq, Fin.val_zero]
  · rw [if_pos rfl, Matrix.card_GL_field, Fin.prod_univ_two]
    norm_num [hq, Fin.val_zero, Fin.val_one]

private theorem s16t3_levi_card {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    Nat.card (∀ a : Fin n, GL (Fin (linBlockLen n (s16t3SlCuts n) a)) K) =
      2 ^ (n / 2) * 3 ^ (n / 2) := by
  classical
  rw [Nat.card_pi]
  have hterm : ∀ a : Fin n,
      Nat.card (GL (Fin (linBlockLen n (s16t3SlCuts n) a)) K) =
        if a ∈ s16t3SlStarts n then 6 else 1 := by
    intro a
    rw [s16t3_card_gl_le_two hK (s16t3_linBlockLen_slCuts_le_two n a)]
    have hiff : linBlockLen n (s16t3SlCuts n) a = 2 ↔ a ∈ s16t3SlStarts n := by
      rw [s16t3_linBlockLen_slCuts_eq_two]
      simp only [s16t3SlStarts, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : linBlockLen n (s16t3SlCuts n) a = 2
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  calc ∏ a : Fin n, Nat.card (GL (Fin (linBlockLen n (s16t3SlCuts n) a)) K)
      = ∏ a : Fin n, (if a ∈ s16t3SlStarts n then 6 else 1) :=
        Finset.prod_congr rfl fun a _ => hterm a
    _ = ∏ a ∈ s16t3SlStarts n, (6 : ℕ) := Fintype.prod_ite_mem _ _
    _ = 6 ^ (s16t3SlStarts n).card := Finset.prod_const 6
    _ = 6 ^ (n / 2) := by rw [s16t3SlStarts_card]
    _ = 2 ^ (n / 2) * 3 ^ (n / 2) := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow]

private theorem s16t3_gl_le_two_exp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {k : ℕ} (hk : k ≤ 2) (g : GL (Fin k) K) {j : ℕ} (hg : g ^ 3 ^ j = 1) : g ^ 3 = 1 := by
  have h6 : g ^ 6 = 1 := by
    by_cases hk2 : k = 2
    · subst hk2
      have hc : Nat.card (GL (Fin 2) K) = 6 := by
        simpa using s16t3_card_gl_le_two hK (show 2 ≤ 2 by norm_num)
      simpa [hc] using pow_card_eq_one' (x := g)
    · have hcard := s16t3_card_gl_le_two hK hk
      rw [if_neg hk2] at hcard
      have h1 : g = 1 := by
        have := pow_card_eq_one' (x := g)
        rwa [hcard, pow_one] at this
      rw [h1, one_pow]
  have hdvd : orderOf g ∣ 3 := by
    obtain ⟨i, -, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (orderOf_dvd_of_pow_eq_one hg)
    have hdvd6 : 3 ^ i ∣ 6 := by
      rw [← hoi]
      exact orderOf_dvd_of_pow_eq_one h6
    have hi1 : i ≤ 1 := by
      by_contra hi
      have h2 : 2 ≤ i := by omega
      have hle : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h2
      have hle6 : 3 ^ i ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
      norm_num at hle
      omega
    rw [hoi]
    exact pow_dvd_pow 3 hi1
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact hdvd

private theorem s16t3_levi_exp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    ∀ h : ∀ a : Fin n, GL (Fin (linBlockLen n (s16t3SlCuts n) a)) K,
      ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1 := by
  intro h k hh
  funext a
  exact s16t3_gl_le_two_exp hK (s16t3_linBlockLen_slCuts_le_two n a) (h a)
    (by simpa using congrFun hh a)

theorem s16t3_sl_std {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ Y P : Subgroup (Matrix.GeneralLinearGroup (Fin n) K),
      CFSG.ABGLocalTools.IsSylowOf 2 Y (StatedSL n K) ∧ Y ≤ P ∧ P ≤ StatedSL n K ∧
      Nat.card ↥P = 3 ^ (n / 2) * 2 ^ (Nat.card ↥(StatedSL n K)).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := K) 2 hn
  let Q : Subgroup (SpecialLinearGroup (Fin n) K) := flagStabilizer n K (s16t3SlCuts n)
  let P : Subgroup (GL (Fin n) K) := Q.map SpecialLinearGroup.toGL
  let Y : Subgroup (GL (Fin n) K) := (unitriangular n K).map SpecialLinearGroup.toGL
  have hYeq : Y = (S : Subgroup (SpecialLinearGroup (Fin n) K)).map
      SpecialLinearGroup.toGL := by
    change (unitriangular n K).map SpecialLinearGroup.toGL = _
    rw [hS]
  have hYp : IsPGroup 2 Y := by
    rw [hYeq]
    exact S.isPGroup'.map SpecialLinearGroup.toGL
  have hPle : P ≤ StatedSL n K := by
    change Q.map SpecialLinearGroup.toGL ≤ StatedSL n K
    rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K]
    exact Subgroup.map_le_range (f := SpecialLinearGroup.toGL) Q
  have hYP : Y ≤ P := by
    change (unitriangular n K).map SpecialLinearGroup.toGL ≤ Q.map SpecialLinearGroup.toGL
    exact Subgroup.map_mono ((unitriangular_le_upperTriangular n K).trans
      (upperTriangular_le_flagStabilizer (s16t3SlCuts n)))
  have hrel : Y.relIndex (StatedSL n K) = (S : Subgroup (SpecialLinearGroup (Fin n) K)).index := by
    rw [hYeq, CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K,
      MonoidHom.range_eq_map (f := SpecialLinearGroup.toGL),
      Subgroup.relIndex_map_map_of_injective (f := SpecialLinearGroup.toGL)
        (S : Subgroup (SpecialLinearGroup (Fin n) K)) ⊤ SpecialLinearGroup.toGL_injective,
      Subgroup.relIndex_top_right]
  have hY : CFSG.ABGLocalTools.IsSylowOf 2 Y (StatedSL n K) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2
      ⟨hYP.trans hPle, hYp, by rw [hrel]; exact S.not_dvd_index⟩
  let eQ : ↥Q ≃* ↥P :=
    Subgroup.equivMapOfInjective Q SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
  let β : ↥P →* (∀ a : Fin n, GL (Fin (linBlockLen n (s16t3SlCuts n) a)) K) :=
    (linLeviHom K n (s16t3SlCuts n)).comp eQ.symm.toMonoidHom
  have hβ : Function.Surjective β := by
    have hβ₀ : Function.Surjective (linLeviHom K n (s16t3SlCuts n)) :=
      MonoidHom.range_eq_top.mp
        (range_linLeviHom_eq_top_of_card_two
          (K := K) hK (s16t3SlCuts n))
    intro y
    obtain ⟨x, hx⟩ := hβ₀ y
    exact ⟨eQ x, by
      change linLeviHom K n (s16t3SlCuts n) (eQ.symm (eQ x)) = y
      rw [MulEquiv.symm_apply_apply]
      exact hx⟩
  have hker : IsPGroup 2 β.ker := by
    have hker₀ : IsPGroup 2 (linLeviHom K n (s16t3SlCuts n)).ker :=
      isPGroup_ker_linLeviHom (K := K) (n := n) (I := s16t3SlCuts n) hn
    have h : β.ker = (linLeviHom K n (s16t3SlCuts n)).ker.comap eQ.symm.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact Iff.rfl
    rw [h]
    exact hker₀.comap_of_injective eQ.symm.toMonoidHom eQ.symm.injective
  have hcardP : Nat.card ↥P = 3 ^ (n / 2) * 2 ^ (Nat.card ↥(StatedSL n K)).factorization 2 :=
    s16t3_card_of_surjective_isPGroup_ker (E := GL (Fin n) K) (G := StatedSL n K)
      (P := P) (Y := Y) (x := n / 2) (a := n / 2) hPle hY hYP β hβ hker (s16t3_levi_card hK n)
  have hexp : ∀ p : ↥P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 :=
    s16t3_pow_three_of_isPGroup_ker β hker (s16t3_levi_exp hK n)
  refine ⟨Y, P, hY, hYP, hPle, hcardP, ?_⟩
  intro p hp k hpk
  have h := hexp ⟨p, hp⟩ k (Subtype.ext (by simpa using hpk))
  simpa using congrArg Subtype.val h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
