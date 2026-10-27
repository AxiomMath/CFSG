module

import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.Quasithin.H13.NQBlockPRankProduct
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExist
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

section Shapes

variable {X : Type} [Group X]

abbrev S208kQ (P : Subgroup X) (n : ℕ) : Prop :=
  IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n ∨ IsSzL2Product (Bar2 (Hinf P)) n

abbrev S208kGoal [Finite X] (P : Subgroup X) (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧
    CFSG.Open.pRank p (Hinf P) < CFSG.Open.pRank p (⊤ : Subgroup X)

end Shapes

section Orders

variable {Y : Type} [Group Y] {n : ℕ}

theorem s208k_one_lt_card_of_isL2 (h : IsL2 Y n) : 1 < Nat.card Y := by
  have hs := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have hn : 1 ≤ n := hs.1.2.1
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hs]
  have h2 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
  calc 1 < 2 * 3 := by norm_num
    _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h2 (by omega)

theorem s208k_card_of_isSz (h : IsSz Y n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧
      Nat.card Y = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 h
  refine ⟨a, ha, rfl, ?_⟩
  rw [Nat.card_congr (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a ha]

theorem s208k_one_lt_card_of_isSz (h : IsSz Y n) : 1 < Nat.card Y := by
  obtain ⟨a, -, rfl, hc⟩ := s208k_card_of_isSz h
  rw [hc]
  have h2 : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have h4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
  calc 1 < 5 * 4 * 1 := by norm_num
    _ ≤ ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) h4) (by omega)

theorem s208k_not_three_dvd_card_of_isSz (h : IsSz Y n) : ¬ 3 ∣ Nat.card Y := by
  obtain ⟨a, -, rfl, hc⟩ := s208k_card_of_isSz h
  rw [hc]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize 2 ^ (2 * a + 1) = q at hq h1 ⊢
  generalize q ^ 2 = q2 at h1 ⊢
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hd | hd <;> omega
  · omega

end Orders

theorem s208k_nontrivial_of_one_lt_card {Z : Type} (h : 1 < Nat.card Z) : Nontrivial Z := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.mp h

section Ranks

variable {X : Type} [Group X] [Finite X]

theorem s208k_pRank_le_one {P : Subgroup X} {n p : ℕ}
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Hinf P) ≤ 1 := by
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact pRank_le_one_of_isL2_or_isSz hQ hp hp2

theorem s208k_pRank_le_two {P : Subgroup X} {n p : ℕ} (hQ : S208kQ P n) (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (Hinf P) ≤ 2 := by
  rcases hQ with h | h | ⟨A, C, _, _, ⟨e⟩, hA, hC⟩
  · exact (s208k_pRank_le_one (Or.inl h) hp hp2).trans (by norm_num)
  · exact (s208k_pRank_le_one (Or.inr h) hp hp2).trans (by norm_num)
  · have : Finite (A × C) := Finite.of_equiv _ e.toEquiv
    have : Finite A := Finite.prod_left C
    have : Finite C := Finite.prod_right A
    have h1 := pRank_le_one_of_isL2_or_isSz hA.symm hp hp2
    have h2 := pRank_le_one_of_isL2_or_isSz hC.symm hp hp2
    have h3 := CFSG.Quasithin.H13.NQBlock.pRank_prod_le (S := A) (T := C) hp
    rw [← pRank_bar2_eq_of_odd hp hp2, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    omega

theorem s208k_goal_of_two_le {P : Subgroup X} {n p : ℕ}
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n - 1) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : S208kGoal P n := by
  have := s208k_pRank_le_one hQ hp hp2
  exact ⟨p, hp, hp2, hpd, by omega⟩

theorem s208k_goal_of_three_le {P : Subgroup X} {n p : ℕ} (hQ : S208kQ P n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n - 1) (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    S208kGoal P n := by
  have := s208k_pRank_le_two hQ hp hp2
  exact ⟨p, hp, hp2, hpd, by omega⟩

end Ranks

section Residual

variable {X : Type} [Group X]

theorem s208k_le_hinf_of_perfect {P V : Subgroup X} (hVP : V ≤ P) (hV : ⁅V, V⁆ = V) :
    V ≤ Hinf P :=
  CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect
    (isPerfect_iff.mpr hV) hVP

theorem s208k_hinf_eq_bot_of_isSolvable {P : Subgroup X} (h : Group.IsSolvable ↥P) :
    Hinf P = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := ↥P)
  unfold Hinf CFSG.inSubgroup
  rw [map_eq_bot_iff_of_injective _ P.subtype_injective, ← le_bot_iff]
  exact (iInf_le (fun k => derivedSeries ↥P k) n).trans hn.le

theorem s208k_one_lt_card {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) :
    1 < Nat.card (Bar2 (Hinf P)) := by
  rcases hQ with h | h | ⟨A, C, _, _, ⟨e⟩, hA, hC⟩
  · exact s208k_one_lt_card_of_isL2 h
  · exact s208k_one_lt_card_of_isSz h
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hA1 : 1 < Nat.card A := hA.elim s208k_one_lt_card_of_isSz s208k_one_lt_card_of_isL2
    have hC1 : 1 < Nat.card C := hC.elim s208k_one_lt_card_of_isSz s208k_one_lt_card_of_isL2
    calc 1 < Nat.card A := hA1
      _ ≤ Nat.card A * Nat.card C := Nat.le_mul_of_pos_right _ (by omega)

theorem s208k_hinf_ne_bot {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) : Hinf P ≠ ⊥ := by
  intro h
  have h1 := s208k_one_lt_card hQ
  have h2 : Nat.card ↥(Hinf P) = 1 := card_eq_one.mpr h
  have h3 : Nat.card (Bar2 (Hinf P)) ∣ Nat.card ↥(Hinf P) := card_quotient_dvd_card _
  rw [h2] at h3
  have := Nat.le_of_dvd Nat.one_pos h3
  omega

theorem s208k_not_isSolvable {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) :
    ¬ Group.IsSolvable ↥P :=
  fun h => s208k_hinf_ne_bot hQ (s208k_hinf_eq_bot_of_isSolvable h)

end Residual

section ResidualFinite

variable {X : Type} [Group X] [Finite X]

theorem s208k_hinf_isPerfect (P : Subgroup X) : Group.IsPerfect ↥(Hinf P) :=
  CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P

theorem s208k_dvd_card_bar2 {P V : Subgroup X} (hVP : V ≤ P) (hV : ⁅V, V⁆ = V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpV : p ∣ Nat.card V) : p ∣ Nat.card (Bar2 (Hinf P)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : p ∣ Nat.card ↥(Hinf P) :=
    hpV.trans (card_dvd_of_le (s208k_le_hinf_of_perfect hVP hV))
  rw [← (CFSG.pCore 2 ↥(Hinf P)).card_mul_index] at h1
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Hinf P)))
    rw [hk] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · exact h

theorem s208k_hinf_not_isSolvable {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) :
    ¬ Group.IsSolvable ↥(Hinf P) := by
  have : Nontrivial ↥(Hinf P) := (nontrivial_iff_ne_bot _).mpr (s208k_hinf_ne_bot hQ)
  have := s208k_hinf_isPerfect P
  exact Group.IsPerfect.not_isSolvable _

theorem s208k_ne_normalizer {P : Subgroup X} {n : ℕ} (hQ : S208kQ P n) (S : Sylow 2 X) :
    P ≠ normalizer (S : Set X) := by
  rintro rfl
  exact s208k_not_isSolvable hQ
    (CFSG.ComponentClassification.AS76b.isSolvable_normalizer_sylow_two S)

end ResidualFinite

section Products

variable {Y : Type} [Group Y]

theorem s208k_not_le_center {K : Subgroup Y} (hK : CFSG.Open.IsQuasisimple ↥K) :
    ¬ K ≤ center Y := by
  intro hle
  have hc : center ↥K = ⊤ := eq_top_iff.mpr fun z _ => mem_center_iff.mpr fun g =>
    Subtype.ext ((mem_center_iff.mp (hle z.2)) g)
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2
  have : Subsingleton (↥K ⧸ center ↥K) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ this

theorem s208k_not_isQuasisimple_of_isSzL2Product {n : ℕ} (h : IsSzL2Product Y n) :
    ¬ CFSG.Open.IsQuasisimple Y := by
  intro hq
  obtain ⟨A, C, _, _, ⟨e⟩, hA, hC⟩ := h
  have : Nontrivial A := s208k_nontrivial_of_one_lt_card
    (hA.elim s208k_one_lt_card_of_isSz s208k_one_lt_card_of_isL2)
  have : Nontrivial C := s208k_nontrivial_of_one_lt_card
    (hC.elim s208k_one_lt_card_of_isSz s208k_one_lt_card_of_isL2)
  have hcen : ∀ {Z : Type} [Group Z] [Nontrivial Z] (f : Y →* Z), Function.Surjective f →
      f.ker ≤ center Y := by
    intro Z _ _ f hf
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq f.ker with
      h | h
    · exact h
    · obtain ⟨z, hz⟩ := exists_ne (1 : Z)
      obtain ⟨y, rfl⟩ := hf z
      exact absurd (f.mem_ker.mp (h ▸ mem_top y)) hz
  have hsup : ((MonoidHom.snd A C).comp e.toMonoidHom).ker ⊔
      ((MonoidHom.fst A C).comp e.toMonoidHom).ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine mul_mem_sup ?_ ?_
    · show (e (e.symm ((e x).1, 1))).2 = 1
      simp
    · show (e (e.symm (1, (e x).2))).1 = 1
      simp
  have htop : center Y = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le
    (hcen _ fun c => ⟨e.symm (1, c), by simp⟩) (hcen _ fun a => ⟨e.symm (a, 1), by simp⟩))
  have : IsSimpleGroup (Y ⧸ center Y) := hq.2
  have : Subsingleton (Y ⧸ center Y) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ this

theorem s208k_not_isQuasisimple_of_isSU3CentralSquare (h : IsSU3CentralSquare Y) :
    ¬ CFSG.Open.IsQuasisimple Y := by
  intro hq
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  have hK₂c : K₂ ≤ centralizer (K₁ : Set Y) := fun b hb =>
    mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb
  have : K₁.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le le_normalizer (hK₂c.trans (centralizer_le_normalizer _))
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq K₁ with h1 | h1
  · exact s208k_not_le_center hK₁.1 h1
  · refine s208k_not_le_center hK₂.1 fun y hy => mem_center_iff.mpr fun z => ?_
    exact hcomm z (h1 ▸ mem_top z) y hy

end Products

end CFSG.LocalAnalysis.UniquenessCase.UC22
