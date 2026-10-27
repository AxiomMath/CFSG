module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Quotient
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofL34
import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddFinal
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VSection
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Sec
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyNine
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddGL2
import CFSG.Adapters.LieModelSmallOrders
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.R869S

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_centralizer_of_pRank_mulAut_le_one
    {M L : Subgroup G} (hLM : L ≤ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1)
    {B : Subgroup G} (hBM : B ≤ M) (hBN : B ≤ normalizer (L : Set G))
    (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 4)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup G}
    (hEL : E ≤ L) (hE : IsPGroup q E) :
    3 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : ↥B →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hBN)
  have hRel : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hBel.subgroupOf B).map φ
  have hR : Nat.card φ.range ≤ p := by
    obtain ⟨k, hk⟩ := hRel.isPGroup.exists_card_eq
    have hk1 := (CFSG.SectionRank.le_pRank hp.one_lt le_top hRel hk).trans hAut
    calc Nat.card φ.range = p ^ k := hk
      _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have hKc : p ^ 3 ≤ Nat.card φ.ker := by
    have hmul : p * p ^ 3 ≤ p * Nat.card φ.ker := calc
      p * p ^ 3 = Nat.card φ.ker * Nat.card φ.range := by
        rw [Subgroup.card_ker_mul_card_range, hBcard]
        ring
      _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hR
      _ = p * Nat.card φ.ker := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left hmul hp.pos
  let B₀ : Subgroup G := φ.ker.map B.subtype
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hB₀card : p ^ 3 ≤ Nat.card B₀ := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hKc
  have hB₀el : IsElemAbelian p B₀ := hBel.mono hB₀B
  have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hp hp2
    (pCoreOf 2 L) B₀ E (UC6S846.isPGroup_pCoreOf L) ((hB₀B.trans hBN).trans hNO)
    ((hEL.trans Subgroup.le_normalizer).trans hNO) hB₀el.isPGroup hE (fun e he a ha => by
      obtain ⟨b, hb, rfl⟩ := ha
      have h1 : UC6S846.rhoL L (Subgroup.inclusion hBN b) = 1 := hb
      have h2 : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ pCoreOf 2 L :=
        (UC6S846.rhoL_fix_iff L (Subgroup.inclusion hBN b) ⟨e, hEL he⟩).1
          (by rw [h1, MulAut.one_apply])
      have h3 : e * (b : G) * e⁻¹ * (b : G)⁻¹ =
          ((b : G) * e * (b : G)⁻¹ * e⁻¹)⁻¹ := by group
      change e * (b : G) * e⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 L
      rw [h3]
      exact inv_mem h2)
  have hA'M : A' ≤ M :=
    hA'le.trans (sup_le (hB₀B.trans hBM) ((Subgroup.map_subtype_le _).trans hLM))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hB₀el
  have hA'c : p ^ 3 ≤ Nat.card A' := by
    rw [Nat.card_congr eA.toEquiv]
    exact hB₀card
  obtain ⟨k, hk⟩ := hA'el.isPGroup.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have hlt : p ^ k < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    rw [hk] at hA'c
    omega
  exact hk3.trans (CFSG.SectionRank.le_pRank hp.one_lt (le_inf hA'M hA'C) hA'el hk)

end CFSG.LocalAnalysis.UniquenessCase.UC6.R869S

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem s7_rank_one_of_three_le
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : CFSG.pPrimeCore p X = ⊥)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ CFSG.AGLEmbedding.IsLinTwoIndex p n d) ∨
        (CFSG.AGLEmbedding.IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
        CFSG.AGLEmbedding.IsReeGTwoIndex p d) ∧
      Nonempty (↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  let K := CFSG.generalizedFitting X
  have : K.Normal := hKn
  have : IsSimpleGroup ↥K := hKs
  have hcat : IsCatalogGroup ↥K :=
    hX.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, hGamma⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hAut : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) := by
    have hinj := CFSG.RankThree.PartOne.CTP.conjNormal_injective_of_centralizer K hKC
    exact h3.trans (by
      simpa only [Subgroup.map_top] using
        (CFSG.SectionRank.pRank_le_map hp.one_lt (MulAut.conjNormal (H := K)) hinj
          (⊤ : Subgroup X)).trans (CFSG.SectionRank.pRank_mono hp.one_lt le_top))
  have hcyc : ¬ IsCyclic (T : Subgroup ↥K) := by
    intro hc
    have hZ := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.center_eq_bot_of_simple_nonabelian
      hKnab
    have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_mulAut_le_two_of_isCyclic_sylow hp hZ T hc
      (hOut ↥K hKs hKnab hcat p hp hp2 T hc)
    omega
  exact hLie ↥K hKs hKnab hcat p hp hp2 T hcyc hGamma (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.L34Odd
open CFSG.GorensteinWalter

theorem s7_not_hasSection_psl_three_four_psl_two
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    ¬ HasSection (projectiveSL 2 K) (projectiveSL 3 (GaloisField 2 2)) := by
  rintro ⟨A, N, hN, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (GaloisField 2 2) 2 := inferInstance
  let E := Census.Res5L34.eOne (GaloisField 2 2)
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => Census.Res5L34.sq_eq_one_of_mem_eOne hx
  have h0 : TwoQuot 2 (projectiveSL 3 (GaloisField 2 2)) E :=
    TwoQuot.of_isPGroup E (isPGroup_two_of_sq_eq_one E hE2)
  have h1 := TwoQuot.of_surjective e.toMonoidHom e.surjective h0
  have h2 := TwoQuot.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h1
  have h3 := TwoQuot.of_subgroup A h2
  have h4 := TwoQuot.of_surjective (proj 2 K) (proj_surjective 2 K) h3
  obtain ⟨S, hS, rho, hrho⟩ := h4
  have hGL := gl2Type_of_injective hK
    (SpecialLinearGroup.toGL.comp S.subtype)
    (SpecialLinearGroup.toGL_injective.comp S.subtype_injective) hS
  obtain ⟨B, hBc, hBi, hB2⟩ := hGL
  have hsq : ∀ x : E, x ^ 2 = 1 := fun x => Subtype.ext (hE2 x x.2)
  have h8 := card_le_eight_of_quotient B hBc hBi hB2 hsq rho hrho
  have hcard : Nat.card E = 16 := by
    rw [Census.Res5L34.card_eOne, CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two]
  omega

theorem s7_not_hasSection_psl_three_four_unitary
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d) :
    ¬ HasSection (CFSG.AGLEmbedding.CatGroup d) (projectiveSL 3 (GaloisField 2 2)) := by
  obtain ⟨q, _, hq, _, hf⟩ := hd.exists_eq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨di, hv, rfl⟩ : ∃ di hv, d = (⟨di, hv⟩ : TauCeti.ValidLieTypeIndex) := ⟨d.1, d.2, rfl⟩
  dsimp only at hq
  subst di
  intro hsec
  let e := CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv
  have hsecU : HasSection (CFSG.Assembly.RankThreeEven.projSU 3 q.p q.exponent)
      (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
    obtain ⟨H, N, hN, ⟨f⟩⟩ := hsec
    let phi : H ≃* H.map e.toMonoidHom := H.equivMapOfInjective e.toMonoidHom e.injective
    have hN' : (N.map phi.toMonoidHom).Normal := hN.map phi.toMonoidHom phi.surjective
    exact ⟨H.map e.toMonoidHom, N.map phi.toMonoidHom, hN',
      ⟨((QuotientGroup.congr N (N.map phi.toMonoidHom) phi rfl).symm.trans f).trans
        (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm⟩⟩
  exact CFSG.RankThree.PartTwo.Sec4.l34SectionPSU3Odd_holds q.p q.exponent (by omega) hf hsecU

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148V
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem hasSection_of_isSec {G S : Type*} [Group G] [Group S] (h : IsSec S G) : HasSection G S := by
  obtain ⟨H, f, hf⟩ := h
  exact ⟨H, f.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

theorem isSec_subgroup_of_solvable_quotient {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (h : IsSec S G) : IsSec S N := by
  obtain ⟨H, f, hf⟩ := h
  have hsec : IsSecOf (⊤ : Subgroup G) S := ⟨H, le_top, f, hf⟩
  have hNsec := hsec.ker_of_solvable hnab (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', inf_top_eq] at hNsec
  obtain ⟨W, hWN, g, hg⟩ := hNsec
  refine ⟨W.subgroupOf N, g.comp (Subgroup.subgroupOfEquivOfLe hWN).toMonoidHom, ?_⟩
  exact hg.comp (Subgroup.subgroupOfEquivOfLe hWN).surjective

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartTwo.Sec4.Ronan148V

theorem s7_876_dataOfSetup4_of_high_rank
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) :
    PartOne.Section8.S7_876 (UC6.dataOfSetup4 hS hU S) := by
  intro hSg h3 L Z Y A g c hA
  have hp := S.hp.1.1
  have hp2 := S.hp.1.2.1
  have hp3 : S.p ≠ 3 := fun h => h3 (h ▸ S.hp)
  have hp5 : 5 ≤ S.p := Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
  have : Fact S.p.Prime := ⟨hp⟩
  have hAut : CFSG.Open.pRank S.p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel c.base.loc.shape
    have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
    refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
    rw [Nat.card_congr (MulAut.congr e).toEquiv, CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hF4]
    exact PartTwo.S17.prime_sq_not_dvd_aut_L34 hp hp2 hp3
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (UC6.four_le_pRank_of_sigma S.hp)
  have hAp : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA.card)
  have hC3 : 3 ≤ CFSG.Open.pRank S.p (S.M ⊓ centralizer (A : Set G)) :=
    UC6.R869S.three_le_pRank_centralizer_of_pRank_mulAut_le_one c.base.loc.le hp hp2
    hAut hBM (hBM.trans c.base.loc.norm) hBel hBc Nat.prime_seven (by norm_num)
    (hA.le.trans inf_le_right) hAp
  have hns : ¬ Group.IsSolvable S.M := by
    intro hs
    have : Group.IsSolvable (UC6.dataOfSetup4 hS hU S).M := hs
    have : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective c.base.loc.le)
    have hsol : Group.IsSolvable (Bar2 L) := inferInstance
    have : IsSimpleGroup (Bar2 L) := c.base.loc.shape.isSimpleGroup_of_mem_classicalTags (by decide)
    have : IsMulCommutative (Bar2 L) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hsol⟩⟩
    have hprime := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup (Bar2 L))
    rw [c.base.loc.shape.card_psl_three_four] at hprime
    norm_num at hprime
  have hsp : IsStronglyPEmbedded S.p S.M := UC6S846.sp_of_mem_sig hSg hns S.hp
  let H := centralizer (A : Set G)
  have hdvd : S.p ∣ Nat.card H := CFSG.GroupTheory.dvd_card_of_one_le_pRank hp
    ((le_trans (by norm_num : 1 ≤ 3) hC3).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right))
  by_cases hHM : H ≤ S.M
  · exact hsp.normalizer_le_of_centralizer_le hHM hdvd
  have hAne : A ≠ ⊥ := by intro h; have hc := hA.card; rw [h, Subgroup.card_bot] at hc; norm_num at hc
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hAne
    rw [← hA.comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mpr (by rw [show centralizer (A : Set G) = ⊤ from htop]; exact le_top)
  let k := Sec7Core4.ofUnique hS hU S.M S.maxLocal S.p S.hp hsp
  have hcfg : Sec7Core4.Config k H := ⟨hHtop, hHM, by simpa [k, Sec7Core4.ofUnique, H, inf_comm] using (le_trans (by norm_num : 2 ≤ 3) hC3)⟩
  have hOdd := k.odd_card_pPrimeCore_of_not_le hHM hcfg.two_le_pRank
  have hsection := PartOne.Section8.s7_section c hA hOdd
  let V := H ⧸ CFSG.pPrimeCore S.p H
  have hO : CFSG.pPrimeCore S.p V = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hN := Sec7Core4.isStronglyPEmbedded_map_quotient_pPrimeCore k hcfg
  have hV : CFSG.Open.IsKGroup V := (hS.kProper.isKGroup H hHtop).quotient (CFSG.pPrimeCore S.p H)
  have hV3 : 3 ≤ CFSG.Open.pRank S.p (⊤ : Subgroup V) := by
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore S.p H)
      ((hp.coprime_iff_not_dvd).1 CFSG.pPrimeCore_coprime_card),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact hC3.trans (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right)
  obtain ⟨d, hd, ⟨eFit⟩⟩ := s7_rank_one_of_three_le hOut hLie hV hp hp2 hO hV3 hN
  obtain ⟨hFit, hFnab, hFnorm, hFc⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  let F := CFSG.generalizedFitting V
  have : F.Normal := hFnorm
  have : IsSimpleGroup F := hFit
  have hFcat : IsCatalogGroup F := hV.isCatalogGroup_of_surjective F hFnab
    (MonoidHom.id _) Function.surjective_id
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer F) :=
    hSch F hFit hFnab hFcat
  have : Group.IsSolvable (V ⧸ F) := CFSG.RankThree.PartOne.CTP.solvable_quotient_of_outer F hFc
  obtain ⟨W, -, R, hR, hModel⟩ := hsection
  have : IsSimpleGroup (W ⧸ R) := hModel.isSimpleGroup_of_mem_classicalTags (by decide)
  have hnab : ¬ ∀ a b : W ⧸ R, a * b = b * a := by
    intro hab
    have : IsMulCommutative (W ⧸ R) := ⟨⟨hab⟩⟩
    have hpS := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup (W ⧸ R))
    rw [hModel.card_psl_three_four] at hpS
    norm_num at hpS
  have hs : IsSec (W ⧸ R) V := ⟨W, QuotientGroup.mk' R, QuotientGroup.mk'_surjective R⟩
  have hsF := isSec_subgroup_of_solvable_quotient hnab F hs
  have hsd := hsF.of_mulEquiv eFit
  obtain ⟨eS⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    (hModel.statedClassicalModel (by decide))
  let eS' := eS.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  have hsd' : IsSec (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2))
      (CFSG.AGLEmbedding.CatGroup d) := by
    obtain ⟨J, rho, hrho⟩ := hsd
    exact ⟨J, eS'.toMonoidHom.comp rho, eS'.surjective.comp hrho⟩
  rcases hd with ⟨n, hn, hlin⟩ | ⟨huni, -⟩ | hree
  · obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField S.p n)) :=
      ⟨S.p, n, hp, hp.odd_of_ne_two hp2, by omega, GaloisField.card S.p n (by omega)⟩
    have hh := hsd'.of_mulEquiv (e2.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 _))
    exact (s7_not_hasSection_psl_three_four_psl_two hodd (hasSection_of_isSec hh)).elim
  · exact (s7_not_hasSection_psl_three_four_unitary hp2 huni (hasSection_of_isSec hsd')).elim
  · have := hree.exists_eq.1
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
