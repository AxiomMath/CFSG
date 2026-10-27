module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Cover
import CFSG.GroupTheory.QuasisimpleCenterRankOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (K33 K34)
open CFSG.LocalAnalysis.UniquenessCase.UCK (K33 K34 ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (LieSporSimple)

open CFSG.Blueprint (LieModel)

private theorem k891list896_pRank_le_three {G : Type} [Group G] [Finite G]
    (H Z : Subgroup G) (Ys : Subgroup (R891Star H Z))
    (hY3 : CFSG.Open.pRank 3 (R891Y H Z Ys) ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (R891Ybar H Z Ys)) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥(R891Y H Z Ys))) :=
    pPrimeCore_coprime_card
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(R891Y H Z Ys)) :=
    (Fact.out : Nat.Prime 3).coprime_iff_not_dvd.mp hNcop
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3)
    (G := ↥(R891Y H Z Ys)) (CFSG.pPrimeCore 3 ↥(R891Y H Z Ys)) hN
  rw [hq, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (H := R891Y H Z Ys)]
  exact hY3

private theorem k891list896_pRank_ge_two {J : Type} [Group J] [Finite J]
    (hJ : CFSG.Open.IsQuasisimple J) (hZpg : IsPGroup 3 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZc_nt : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
  have hZc_lt : 1 < Nat.card (Subgroup.center J) :=
    Finite.one_lt_card_iff_nontrivial.mpr hZc_nt
  have h3dvd : 3 ∣ Nat.card (Subgroup.center J) := by
    rcases hZpg.card_eq_or_dvd with h1 | h3
    · omega
    · exact h3
  have h2q : 2 ≤ CFSG.pRank 3 (J ⧸ Subgroup.center J) := by
    by_contra hcon
    have hcon' : CFSG.pRank 3 (J ⧸ Subgroup.center J) ≤ 1 := by omega
    exact CFSG.GroupTheory.QuasisimpleCenterRankOne.not_dvd_card_center_of_pRank_le_one
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJ) (by norm_num) hcon' h3dvd
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2q
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) (H := ⊤) h2q
  let P : Subgroup J := E.comap (QuotientGroup.mk' (Subgroup.center J))
  have hPcard : Nat.card P = Nat.card (Subgroup.center J) * Nat.card E :=
    QuotientGroup.card_preimage_mk (Subgroup.center J) (E : Set (J ⧸ Subgroup.center J))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZpg
  have hPp : IsPGroup 3 P :=
    IsPGroup.of_card (n := n + 2) (by rw [hPcard, hn, hEcard, pow_add])
  have hEnotcyc : ¬ IsCyclic E := by
    intro hcycE
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcycE
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hEel.2 (g : J ⧸ Subgroup.center J) g.2
    have hgen : orderOf g = 9 := by
      rw [← Nat.card_zpowers (a := g), hg, Subgroup.card_top, hEcard]
      norm_num
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    rw [hgen] at hdvd
    norm_num at hdvd
  have hPncyc : ¬ IsCyclic P := by
    intro hcycP
    let πP : P →* E :=
      { toFun := fun x =>
          ⟨QuotientGroup.mk' (Subgroup.center J) (x : J), Subgroup.mem_comap.mp x.2⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hsurj : Function.Surjective πP := by
      intro e
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center J)
        (e : J ⧸ Subgroup.center J)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · rw [Subgroup.mem_comap]; rw [hx]; exact e.2
      · ext; exact hx
    exact hEnotcyc (isCyclic_of_surjective πP hsurj)
  obtain ⟨F, hFP, hFel, hFcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_E9_le_of_not_isCyclic (G := J)
      (Y := P) hPp hPncyc
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (hFP.trans le_top) hFel
    (by rw [hFcard]; norm_num)

private theorem k891list896_cover_to_goal {J : Type} [Group J]
    (h : ThreeCover (fun Y _ => IsAlt Y 6) J ∨ ThreeCover (fun Y _ => IsAlt Y 7) J ∨
      ThreeCover (fun Y _ => IsSpor Y .M22) J ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) J) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) J)) :
    R891List896 J := by
  rcases h with hA6 | hA7 | hM22 | hPSL | hPSU
  · exact Or.inl ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hA6.1, hA6.2.1, hA6.2.2⟩
  · exact Or.inr (Or.inl
      ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hA7.1, hA7.2.1, hA7.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hM22.1, hM22.2.1, hM22.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hPSL))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hPSU))))

theorem s891_list896
    {G : Type} [Group G] [Finite G] (H Z : Subgroup G) (Ys : Subgroup (R891Star H Z))
    (hqs : R891YbarQS H Z Ys) (hY3 : CFSG.Open.pRank 3 (R891Y H Z Ys) ≤ 3) :
    R891List896 (R891Ybar H Z Ys) := by
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (R891Ybar H Z Ys)) ≤ 3 :=
    k891list896_pRank_le_three H Z Ys hY3
  have hge : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (R891Ybar H Z Ys)) :=
    k891list896_pRank_ge_two hqs.1 hqs.2.2.1 hqs.2.2.2
  have h3 : 3 ∣ Nat.card (center (R891Ybar H Z Ys)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨e, he⟩ := hqs.2.2.1.exists_card_eq
    have he0 : e ≠ 0 := by
      intro h
      exact hqs.2.2.2 (Subgroup.card_eq_one.mp (by rw [he, h]; rfl))
    rw [he]
    exact dvd_pow_self 3 he0
  have h2or3 : CFSG.Open.pRank 3 (⊤ : Subgroup (R891Ybar H Z Ys)) = 2 ∨
      CFSG.Open.pRank 3 (⊤ : Subgroup (R891Ybar H Z Ys)) = 3 := by omega
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hAlt := CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
  have hSpor := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  rcases h2or3 with h2 | h3rank
  · exact k891list896_cover_to_goal
      (CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.k33_threeCover_of_three_dvd
        hGA hAlt hSpor CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
        (R891Ybar H Z Ys) hqs.1 hqs.2.1 hqs.2.2.1 h3 h2)
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_threeCover_of_three_dvd
        hGA hAlt hSpor (R891Ybar H Z Ys) hqs.1 hqs.2.1 h3 h3rank))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
