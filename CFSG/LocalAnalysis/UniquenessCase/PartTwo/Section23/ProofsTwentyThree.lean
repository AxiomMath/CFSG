module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Ker
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightBasic
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem pRank_Z_eq_of_card (D : Data G) {n : ℕ}
    (hcard : Nat.card D.Z = 2 ^ n) : CFSG.Open.pRank 2 D.Z = n := by
  have hZel : IsElemAbelian 2 D.Z :=
    CFSG.CGT.PushingUpLit.CGT6.isElemAbelian_omegaOneCenterIn D.T
  refine le_antisymm ?_ (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hZel hcard)
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E hE hEel => ?_
  calc Nat.card E ≤ Nat.card D.Z := Subgroup.card_le_of_le hE
    _ = 2 ^ n := hcard

private theorem pCore_le_ker_of_pCore_range_eq_bot {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (f : X →* Y) (hf : CFSG.pCore p f.range = ⊥) : CFSG.pCore p X ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hle : (CFSG.pCore p X).map f.rangeRestrict ≤ CFSG.pCore p f.range :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
      ((inferInstance : (CFSG.pCore p X).Normal).map _ f.rangeRestrict_surjective)
      ((CFSG.pCore_isPGroup (p := p) (G := X)).map _)
  rw [hf, le_bot_iff] at hle
  have hx1 : f.rangeRestrict x ∈ (CFSG.pCore p X).map f.rangeRestrict := ⟨x, hx, rfl⟩
  rw [hle] at hx1
  exact congrArg Subtype.val (show f.rangeRestrict x = 1 from hx1)

private theorem card_barSub_eq_of_simple {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V}
    (hLS : c.L ≤ stabTil (⊥ : Subgroup G) c.V)
    (hO2H : CFSG.pCore 2 ↥(barSub (⊥ : Subgroup G) c.V hV c.L) = ⊥)
    (hNtr : Nontrivial ↥(barSub (⊥ : Subgroup G) c.V hV c.L))
    (hSimple : IsSimpleGroup (Bar2 c.L)) :
    Nat.card ↥(barSub (⊥ : Subgroup G) c.V hV c.L) = Nat.card (Bar2 c.L) := by
  let g : ↥c.L →* MulAut (Vtil (⊥ : Subgroup G) c.V hV) :=
    (actTil (⊥ : Subgroup G) c.V hV).comp (Subgroup.inclusion hLS)
  have hrange : g.range = barSub (⊥ : Subgroup G) c.V hV c.L := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLS x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, congrArg (actTil (⊥ : Subgroup G) c.V hV) (Subtype.ext rfl)⟩
  have hkertop : g.ker ≠ ⊤ := fun htop =>
    (Subgroup.nontrivial_iff_ne_bot _).mp hNtr <| by
      rw [← hrange]
      exact MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp htop)
  haveI : IsSimpleGroup (↥c.L ⧸ CFSG.pCore 2 ↥c.L) := hSimple
  have hker : g.ker = CFSG.pCore 2 ↥c.L :=
    CFSG.Quasithin.S146zU.UF1.ker_eq_of_isSimpleGroup_quotient g
      (pCore_le_ker_of_pCore_range_eq_bot g (by rw [hrange]; exact hO2H)) hkertop
  have h1 : Nat.card (↥c.L ⧸ g.ker) = Nat.card ↥g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  rw [hker, hrange] at h1
  exact h1.symm

private theorem Ctx23L.exists_naturalModule (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (hK : KOrdNatural)
    (h1930 : H1930 D) (hSimple : IsSimpleGroup (Bar2 c.L)) :
    ∃ hV : IsElemAbelian 2 c.V,
      IsNaturalClassicalModule (barSub (⊥ : Subgroup G) c.V hV c.L) (CFSG.Open.pRank 2 D.Z) ∧
        Nat.card ↥(barSub (⊥ : Subgroup G) c.V hV c.L) = Nat.card (Bar2 c.L) := by
  obtain ⟨hV, n', hcardU0, hnat⟩ := h2 h1930 c
  have hU0 : c.U0 = D.Z := (h3 h1930 c).trans (h4 h1930 c).1
  have hcardZ : Nat.card D.Z = 2 ^ n' := by rw [← hU0]; exact hcardU0
  obtain rfl : n' = CFSG.Open.pRank 2 D.Z := (pRank_Z_eq_of_card D hcardZ).symm
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  have hLbot : c.L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  exact ⟨hV, hnat,
    card_barSub_eq_of_simple c (le_stabTil hLV hLbot) (hK.1 hnat) (hK.2.1 hnat) hSimple⟩

theorem Ctx23L.lineSelect (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hL2 : IsL2 (Bar2 c.L) (CFSG.Open.pRank 2 D.Z)) (hK : KOrdNatural)
    (h1930 : H1930 D) :
    ∃ hV : IsElemAbelian 2 c.V, S23_23At c.L c.V hV (CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨hV, hnat, hcard⟩ := Ctx23L.exists_naturalModule D Ch c h2 h3 h4 hK h1930
    (CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2)
  exact ⟨hV, hL2, hK.2.2.1 hnat hL2 hcard⟩

theorem Ctx23L.lineSelectOmega (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hMinus : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) (hK : KOrdNatural)
    (h1930 : H1930 D) :
    ∃ hV : IsElemAbelian 2 c.V,
      NatOmegaMinus (barSub (⊥ : Subgroup G) c.V hV c.L) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) := by
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by
    obtain ⟨-, K, hKfield, hKfinite, b, q, hKcard, -, -⟩ := hMinus
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    have hKgt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hKcard, h0, pow_zero] at hKgt
    exact lt_irrefl 1 hKgt
  obtain ⟨hV, hnat, hcard⟩ := Ctx23L.exists_naturalModule D Ch c h2 h3 h4 hK h1930
    (CFSG.Blueprint.LieModel.isSimpleGroup_psl_two (isL2_two_mul_of_isOmegaMinus_four hn1 hMinus))
  exact ⟨hV, hK.2.2.2 hnat hMinus hcard⟩

theorem false_of_omegaMinus (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hK : KOrdNatural) (hCases : S23_23Cases D Ch) (hCaseA : S23_23CaseA D Ch)
    (hCaseB : S23_23CaseB D Ch) :
    H1930 D → ∀ c : Ctx23L D Ch,
      IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) → False := by
  intro h1930 c hMinus
  obtain ⟨hV, hNat⟩ := Ctx23L.lineSelectOmega D Ch c h2 h3 h4 hMinus hK h1930
  rcases hCases h1930 c hMinus hV hNat with hA | hB
  · exact hCaseA h1930 c hMinus hV hNat hA
  · exact hCaseB h1930 c hMinus hV hNat hB

theorem s23_23Omega_of (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hK : KOrdNatural) (hCases : S23_23Cases D Ch) (hCaseA : S23_23CaseA D Ch)
    (hCaseB : S23_23CaseB D Ch) :
    S23_23Omega D Ch :=
  false_of_omegaMinus D Ch h2 h3 h4 hK hCases hCaseA hCaseB

theorem s23_23_of (D : Data G) (Ch : Choice2011 G)
    (h92 : S23_9_2 D Ch) (h22 : S23_22 D Ch) (h11 : S23_11 D Ch)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hOmega : S23_23Omega D Ch) (hK : KOrdNatural) :
    S23_23 D Ch := by
  intro h1930 c
  rcases h92 h1930 c with hL2 | hPlus | hMinus | hSL3
  · exact Ctx23L.lineSelect D Ch c h2 h3 h4 hL2 hK h1930
  · exact (h22 h1930 c hPlus).elim
  · exact (hOmega h1930 c hMinus).elim
  · exact (h11 h1930 c hSL3).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
