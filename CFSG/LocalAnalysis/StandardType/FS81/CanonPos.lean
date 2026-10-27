module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.SplitE
public import CFSG.LocalAnalysis.StandardType.FS81.RowFacts
public import CFSG.LocalAnalysis.StandardType.FS81.OrthRowCanon
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem fs81_exists_isRow {G : Type} [Group G] {K : Subgroup G}
    (h : LargeEvenMarking K (fun lab _ _ _ _ _ => FSLab lab)) : ∃ r : Row, IsRow r K := by
  obtain ⟨lab, ⟨hn1, hcases⟩, hlab⟩ := exists_glaLabel h
  rcases hcases with ⟨hD, hr6⟩ | ⟨htwD, hr7⟩ | ⟨hE7, hr0⟩
  · refine ⟨Row.D6, CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hlab⟩
    intro lab' R _ I F θ hP
    subst hP
    exact ⟨hn1, Or.inl ⟨rfl, hD, hr6⟩⟩
  · refine ⟨Row.twD7, CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hlab⟩
    intro lab' R _ I F θ hP
    subst hP
    exact ⟨hn1, Or.inr (Or.inl ⟨rfl, htwD, hr7⟩)⟩
  · refine ⟨Row.E7, CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hlab⟩
    intro lab' R _ I F θ hP
    subst hP
    exact ⟨hn1, Or.inr (Or.inr ⟨rfl, hE7, hr0⟩)⟩

theorem fs81_isEm_seven_of_isRow_E7 {G : Type} [Group G] {K : Subgroup G}
    (h : IsRow Row.E7 K) : IsEm 7 K := by
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h
  intro lab R _ I F θ hP
  obtain ⟨hn1, hcases⟩ := hP
  rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, ht, hr⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact ⟨Or.inl ⟨rfl, ht⟩, hr, hn1⟩

theorem fs81_L0CanonPosition :
    L0CanonPosition := by
  intro G _ _ b₀ K E m hS
  obtain ⟨⟨hb₀, hKC, hKn, hKz, hmark, hA2, hA3, hA4⟩, hmax, hb₀E, hcard, hm7, hbig⟩ := hS
  obtain ⟨r, hr⟩ := fs81_exists_isRow hmark
  have hOut := fs81_row_out_not_dvd_three hmark hKz
  obtain ⟨hdisj, hsup, hmaxK⟩ := fs81_split_E hb₀ hKC hKn hKz hOut hA2 hmax hb₀E
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hmax.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hnorm : Subgroup.zpowers b₀ ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
    intro x hx
    have hxE : x ∈ E := hsup ▸ Subgroup.mem_sup_left hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhE : h ∈ E := hh.1
      have hxh : x * h * x⁻¹ = h := by rw [hcommE x hxE h hhE, mul_inv_cancel_right]
      rw [hxh]
      exact hh
    · intro hh
      have hE' : x * h * x⁻¹ ∈ E := hh.1
      have hhE : h ∈ E := by
        have h2 := E.mul_mem (E.mul_mem (E.inv_mem hxE) hE') hxE
        simpa [mul_assoc] using h2
      have hxh : x * h * x⁻¹ = h := by rw [hcommE x hxE h hhE, mul_inv_cancel_right]
      rw [hxh] at hh
      exact hh
  have hcardA : Nat.card E = 3 * Nat.card ↥(E ⊓ K) := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hnorm
    rw [hsup, disjoint_iff.mp hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hb₀] at h
    exact h
  have hm_of : ∀ n : ℕ, Nat.card ↥(E ⊓ K) = 3 ^ n → m = n + 1 := by
    intro n hn
    have h3 : 3 ^ m = 3 ^ (n + 1) := by rw [← hcard, hcardA, hn, pow_succ']
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  cases r with
  | D6 =>
    obtain ⟨hA, hC⟩ := fs81_orth_row_canon (r := Row.D6) (by decide) hr hKz hmaxK
    exact ⟨Row.D6, hm_of _ hA, hr, hdisj, hsup, hmaxK, hA, hC⟩
  | twD7 =>
    obtain ⟨hA, hC⟩ := fs81_orth_row_canon (r := Row.twD7) (by decide) hr hKz hmaxK
    exact ⟨Row.twD7, hm_of _ hA, hr, hdisj, hsup, hmaxK, hA, hC⟩
  | E7 =>
    have hApow : Nat.card ↥(E ⊓ K) = 3 ^ (m - 1) := by
      have h3 : 3 * Nat.card ↥(E ⊓ K) = 3 * 3 ^ (m - 1) := by
        rw [← hcardA, hcard, ← pow_succ']
        congr 1
        omega
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    have h36 : 3 ^ 6 ≤ Nat.card ↥(E ⊓ K) := by
      rw [hApow]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hA7, hC7⟩ :=
      fs81_E7_maxElemAb3_card (fs81_isEm_seven_of_isRow_E7 hr) hKz hmaxK h36
    exact ⟨Row.E7, hm_of _ hA7, hr, hdisj, hsup, hmaxK, hA7, by rw [inf_comm]; exact hC7⟩

end CFSG.StandardType.FrameRoute.FS81
