module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFSClosed
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLCyc
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLInner

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem ffs_core {G : Type} [Group G] [Finite G] {A : Subgroup G} {a : G} {X : Subgroup G}
    (hpt : Sec21Point G A a X)
    (hmod : StatedClassicalModel (lBar X) .PSL 4 2 1 ∨ StatedClassicalModel (lBar X) .PSL 5 2 1)
    (hXq : CFSG.IsQuasisimple X)
    (hN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({a} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype = A) ∧ Nat.card A = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : IsL4L5Sp6 X := hmod.elim Or.inl fun h => Or.inr (Or.inl h)
  have hQ' : CFSG.IsQuasisimple (lBar X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have hZ3 := ff_not_three_dvd_card_center hXq hX hQ'
  have eZ : lBar X ≃* (↥X ⧸ Subgroup.center ↥X) :=
    QuotientGroup.quotientMulEquivOfEq (ff_aschbacherSolvableCore_eq_center hXq hX hQ')
  obtain ⟨n, hn, hmodn⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL n 2 1 := by
    rcases hmod with h | h
    · exact ⟨4, Or.inl rfl, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ h⟩
    · exact ⟨5, Or.inr rfl, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ h⟩
  have hQ : ∀ R : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 3 R → Nat.card R ≤ 9 := by
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one hmodn
    intro R hR
    obtain ⟨Q, hRQ⟩ := (hR.map e.toMonoidHom).exists_le_sylow
    have h1 : Nat.card (R.map e.toMonoidHom) ≤ Nat.card Q :=
      Subgroup.card_le_of_le hRQ
    have h9 : Nat.card Q = 9 := by
      rcases hn with rfl | rfl
      · exact Hering214.card_sylow_three_four hK Q
      · exact Hering214.card_sylow_three_five hK Q
    rw [Subgroup.card_map_of_injective e.injective] at h1
    exact h1.trans h9.le
  have hE : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E₀, -, hE₀, hE₀9, -⟩ := fFKE9_holds ↥X hXq hZ3 (ff_statedModel_center hXq hX hQ')
    refine ⟨E₀.map X.subtype, Subgroup.map_subtype_le E₀, CFSG.Open.IsElemAbelian.map hE₀ _, ?_⟩
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hE₀9
  have hI : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ k : ℕ, g ^ (3 ^ k) = 1 →
      ∃ x ∈ X, x⁻¹ * g ∈ Subgroup.centralizer (X : Set G) := fun g hg k hgk =>
    exists_mem_inv_mul_mem_centralizer_of_odd hXq hn hmodn hg (Odd.pow (by decide)) hgk
  have hcyc : ∀ P : Sylow 3 ↥(Subgroup.centralizer (X : Set G)),
      IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (X : Set G))) :=
    ffCentCyclic_of_kE9 fFKE9_holds G A a X hpt hX hXq hN
  have hA := hpt.mem_S
  obtain ⟨⟨hAab, hAmax, E, hE27, hEA⟩, -, -⟩ := hA
  have h27 : 27 ≤ Nat.card A := by
    have := Subgroup.card_dvd_of_le hEA
    rw [hE27.2.1] at this
    exact Nat.le_of_dvd Nat.card_pos this
  obtain ⟨hP, hle⟩ := ffs_main hAab hAmax hpt.mem hpt.ne_one
    (Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta) hN hZ3 hE hQ hI hcyc hW
  exact ⟨hP, le_antisymm hle h27⟩

theorem ffSylowIsAL45_holds : FFSylowIsAL45 := by
  intro G _ _ A a X hpt hmod hXq hN hW
  exact (ffs_core hpt hmod hXq hN hW).1

theorem ffPRankL5_holds : FFPRankL5 := by
  intro G _ _ A a X hpt hmod hXq hN hW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨P, hPA⟩, hcard⟩ := ffs_core hpt (Or.inr hmod) hXq hN hW
  rw [hpt.standing.toTheoremFourHyp.localRank_three]
  have hAab := hpt.mem_S.1.1
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨a, hpt.mem⟩))
  have hge : 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
      (Subgroup.centralizer ({a} : Set G))) ⟨A, hAC, hAab, by rw [hcard]; norm_num⟩
  have hle : CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) ≤ 3 := by
    obtain ⟨E, hEC, hEab, hEcard⟩ := CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3
      Nat.prime_three (Subgroup.centralizer ({a} : Set G))
    obtain ⟨c, -, hc⟩ := ffs_exists_conj_map_le P hEC hEab.isPGroup
    rw [hPA] at hc
    have hsub : E.map (MulAut.conj c).toMonoidHom ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    have h1 : Nat.card (E.map (MulAut.conj c).toMonoidHom) ≤ Nat.card A :=
      Subgroup.card_le_of_le hsub
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hEcard, hcard] at h1
    by_contra hlt
    have h4 : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) (not_le.mp hlt)
    omega
  omega

end CFSG.RankThree.PartTwo.Sec21
