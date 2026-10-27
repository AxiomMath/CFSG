module

public import CFSG.LocalAnalysis.UniquenessCase.UC22C117MCons
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869M
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPBasic
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.OddPGroupNoncyclicChar
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive C76Three)

variable {G : Type} [Group G] [Finite G]

namespace R869S

theorem uniqueMax_of_theoremCAt {M : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M)
    (hC : TheoremCAt M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L Q : Subgroup G} (hLM : L ≤ M)
    (hQL : Q ≤ L) (hQ : IsPGroup q Q) (h2 : 2 ≤ CFSG.Open.pRank q Q)
    (hΓ : rankThreeGamma 1 q Q ≤ M) : UniqueMax M L := by
  show calMOf L = {M}
  ext N
  constructor
  · rintro ⟨hN, hLN⟩
    have hle := hC q hq hq2 Q (hQL.trans hLM) hQ h2 hΓ N hN.1 (hQL.trans hLN)
    exact (hN.2 _ hM.1 hle).symm
  · intro hN
    have hNM : N = M := hN
    subst hNM
    exact ⟨hM, hLM⟩

theorem pRank_mulAut_bar2_le_two (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    {L : Subgroup G} (hLk : CFSG.Open.IsKGroup L) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : CFSG.Open.pRank p L ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hX1 : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 1 := by
    have h3 : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hp hp2
    rw [CFSG.SectionRank.pRank_quotient_eq (p := p) (N := CFSG.pCore 2 ↥L) h3,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact h1
  obtain ⟨T⟩ : Nonempty (Sylow p (Bar2 L)) := inferInstance
  haveI : IsCyclic (T : Subgroup (Bar2 L)) :=
    CFSG.AGLEmbedding.isCyclic_sylow_of_pRank_le_one hp hp2 hX1 T
  have hf : Function.Surjective (QuotientGroup.mk' (center (Bar2 L))) :=
    QuotientGroup.mk'_surjective _
  have hT : IsCyclic ((T.mapSurjective hf : Sylow p (Bar2 L ⧸ center (Bar2 L))) :
      Subgroup (Bar2 L ⧸ center (Bar2 L))) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective ((QuotientGroup.mk' (center (Bar2 L))).subgroupMap _)
      ((QuotientGroup.mk' (center (Bar2 L))).subgroupMap_surjective _)
  have hs : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hq.2
  have hnab :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (Bar2 L) hq
  have hcat := CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
    (hLk.quotient (CFSG.pCore 2 ↥L)) hq
  have hZ := CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_of_nonabelian hs hnab
  exact (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_mulAut_le_of_quasisimple
    hp.one_lt hq).trans
    (CFSG.LocalAnalysis.RankThreeTheoremC.pRank_mulAut_le_two_of_isCyclic_sylow hp hZ _ hT
      (hOut _ hs hnab hcat p hp hp2 _ hT))

theorem two_le_pRank_centralizer_of_pRank_mulAut {M L : Subgroup G} (hLM : L ≤ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 2) {B : Subgroup G}
    (hBM : B ≤ M) (hBN : B ≤ normalizer (L : Set G)) (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup G}
    (hEL : E ≤ L) (hE : IsPGroup q E) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥B →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hBN)
  have hRel : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hBel.subgroupOf B).map φ
  have hR : Nat.card φ.range ≤ p ^ 2 := by
    obtain ⟨k, hk⟩ := hRel.isPGroup.exists_card_eq
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos
      ((CFSG.SectionRank.le_pRank hp.one_lt le_top hRel hk).trans hAut)
  have hKc : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card φ.ker :=
      calc p ^ 2 * p ^ 2 = Nat.card φ.ker * Nat.card φ.range := by
            rw [Subgroup.card_ker_mul_card_range, hBcard]
            ring
        _ ≤ Nat.card φ.ker * p ^ 2 := Nat.mul_le_mul_left _ hR
        _ = p ^ 2 * Nat.card φ.ker := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos 2)
  let B₀ : Subgroup G := φ.ker.map B.subtype
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hB₀card : p ^ 2 ≤ Nat.card B₀ := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hKc
  obtain ⟨A, hAB₀, hAel, hAc⟩ := UC6S846.exists_card_p_sq hp (hBel.mono hB₀B) hB₀card
  have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hp hp2
    (pCoreOf 2 L) A E (UC6S846.isPGroup_pCoreOf L) ((hAB₀.trans (hB₀B.trans hBN)).trans hNO)
    ((hEL.trans Subgroup.le_normalizer).trans hNO) hAel.isPGroup hE (fun e he a ha => by
      obtain ⟨b, hb, rfl⟩ := hAB₀ ha
      have h1 : UC6S846.rhoL L (Subgroup.inclusion hBN b) = 1 := hb
      have h2 : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ pCoreOf 2 L :=
        (UC6S846.rhoL_fix_iff L (Subgroup.inclusion hBN b) ⟨e, hEL he⟩).1
          (by rw [h1, MulAut.one_apply])
      have h3 : e * (b : G) * e⁻¹ * (b : G)⁻¹ = ((b : G) * e * (b : G)⁻¹ * e⁻¹)⁻¹ := by group
      change e * (b : G) * e⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 L
      rw [h3]
      exact inv_mem h2)
  have hA'M : A' ≤ M :=
    hA'le.trans (sup_le (hAB₀.trans (hB₀B.trans hBM)) ((Subgroup.map_subtype_le _).trans hLM))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  exact UC6S846.le_pRank' hp (le_inf hA'M hA'C) hA'el hA'c

theorem uniqueMax_of_normal {M L : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M)
    (hC : TheoremCAt M) (hL : L ∈ calC M) (hN : M ≤ normalizer (L : Set G))
    (hthin : ¬ F08.Thin8 L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h76 : Conclusion76 M p)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 2) {B : Subgroup G}
    (hBM : B ≤ M) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 4) :
    UniqueMax M L := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  obtain ⟨q, hq, hq2, h1q⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 < CFSG.Open.pRank q L := by
    by_contra h
    exact hthin fun q hq hq2 => not_lt.1 fun hlt => h ⟨q, hq, hq2, hlt⟩
  obtain ⟨E, hEL, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) hq (k := 2) (by omega)
  have h2 := two_le_pRank_centralizer_of_pRank_mulAut hLM hp hp2 hAut hBM (hBM.trans hN) hBel
    hBcard hq hq2 hEL hEel.isPGroup
  have hΓ : rankThreeGamma 1 q E ≤ M := by
    refine h76 q hq E (hEL.trans hLM) hEel hEc (by omega) fun Y hYE _ => ?_
    refine lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_))
    exact inf_le_inf_left _ ((Subgroup.centralizer_le hYE).trans
      (Subgroup.centralizer_le_normalizer _))
  exact uniqueMax_of_theoremCAt hM hC hq hq2 hLM hEL hEel.isPGroup
    (UC6S846.le_pRank' hq le_rfl hEel hEc) hΓ

theorem not_dvd_card_conjClosure {M K : Subgroup G} (hK : K ∈ calC M)
    (hnot : ¬ M ≤ normalizer (K : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : CFSG.Open.pRank p (conjClosure M K) ≤ 1) : ¬ p ∣ Nat.card (conjClosure M K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hMM : M ≤ normalizer (M : Set G) := Subgroup.le_normalizer
  have hLM : conjClosure M K ≤ M := (uc22p22u_conjClosure_isProd le_rfl hMM hK).1
  obtain ⟨m, hm, hne⟩ : ∃ m ∈ M, uniqueFourConj m K ≠ K := by
    by_contra h
    exact hnot fun m hm => UC6.uniqueFourConj_eq_self_iff.1 (by
      by_contra hne
      exact h ⟨m, hm, hne⟩)
  have hconj : ∀ m ∈ M, uniqueFourConj m K ≤ conjClosure M K := fun m hm =>
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) (uniqueFourConj m K)
      ⟨m⁻¹, M.inv_mem hm, rfl⟩ le_rfl
  have hKL : K ≤ conjClosure M K := by
    have h1' : uniqueFourConj 1 K = K := UC6.uniqueFourConj_eq_self_iff.2 (Subgroup.one_mem _)
    have := hconj 1 M.one_mem
    rwa [h1'] at this
  have hidx : ¬ p ∣ (center (Bar2 K)).index := fun h => by
    have := UC22.P2214R.two_le_pRank_of_conj hK (uc22p22u_calC_conj hMM hK hm) hne ⟨m, rfl⟩ hKL
      (hconj m hm) hLM hp hp2 h
    omega
  have hbar : ¬ p ∣ Nat.card (Bar2 K) := by
    haveI : Group.IsPerfect (Bar2 K) := Group.isPerfect_def.mpr hK.2.2.1
    exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp
      (by rwa [← Subgroup.index_eq_card])
  have hKp : ¬ p ∣ Nat.card K := by
    have h2 : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥K) :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
        (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) hp hp2
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    exact Nat.Prime.not_dvd_mul hp hbar h2
  classical
  haveI : Fintype ↥M := Fintype.ofFinite _
  let F : ↥M → Subgroup G := fun g => K.map (MulAut.conj (g : G)).toMonoidHom
  have hFC : ∀ g, F g ∈ calC M := fun g => by
    simpa [F, uniqueFourConj] using uc22p22u_calC_conj hMM hK (M.inv_mem g.2)
  have hnorm : ∀ g, (⨆ h, F h) ≤ normalizer (F g : Set G) := fun g => iSup_le fun h => by
    by_cases hgh : F g = F h
    · rw [← hgh]
      exact Subgroup.le_normalizer
    · exact uc22p22u_calC_normalizes (hFC g) (hFC h) hgh
  have hFp : ∀ g, ¬ p ∣ Nat.card (F g) := fun g => by
    rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
    exact hKp
  have hsup : (⨆ g ∈ (Finset.univ : Finset ↥M), F g) = conjClosure M K := by
    refine le_antisymm (iSup₂_le fun g _ => ?_) (iSup₂_le fun A hA => ?_)
    · exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) (F g) ⟨g, g.2, rfl⟩ le_rfl
    · obtain ⟨g, hg, rfl⟩ := hA
      exact le_iSup₂_of_le (f := fun g (_ : g ∈ (Finset.univ : Finset ↥M)) => F g) ⟨g, hg⟩
        (Finset.mem_univ _) le_rfl
  rw [← hsup]
  exact uc22p22v_not_dvd_iSup F hnorm hp hFp Finset.univ

theorem uniqueMax_conjClosure (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hC : TheoremCAt S.M) (h77 : F07.R77E4 (dataOfSetup4 hS hU S)) {K : Subgroup G}
    (hK : K ∈ calC S.M) (hnot : ¬ S.M ≤ normalizer (K : Set G))
    (hthin : ¬ F08.Thin8 (conjClosure S.M K))
    (hσL : ∀ r ∈ uniqueFourSigma S.M, CFSG.Open.pRank r (conjClosure S.M K) ≤ 1) :
    UniqueMax S.M (conjClosure S.M K) := by
  have hpσ := S.hp
  have hp : S.p.Prime := hpσ.1.1
  have hp2 : S.p ≠ 2 := hpσ.1.2.1
  obtain ⟨hLM, hML, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  have hLp := not_dvd_card_conjClosure hK hnot hp hp2 (hσL _ hpσ)
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (four_le_pRank_of_sigma hpσ)
  obtain ⟨q, hq, hq2, h1q⟩ :
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 < CFSG.Open.pRank q (conjClosure S.M K) := by
    by_contra h
    exact hthin fun q hq hq2 => not_lt.1 fun hlt => h ⟨q, hq, hq2, hlt⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨R₀, hR₀⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hq
    hBel.isPGroup (hBM.trans hML) hLp
  have hRp : IsPGroup q ((R₀ : Subgroup ↥(conjClosure S.M K)).map (conjClosure S.M K).subtype) :=
    R₀.isPGroup'.map _
  have hRr : CFSG.Open.pRank q
      ((R₀ : Subgroup ↥(conjClosure S.M K)).map (conjClosure S.M K).subtype) =
        CFSG.Open.pRank q (conjClosure S.M K) :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hq ⟨R₀, rfl⟩
  have hRnc : ¬ IsCyclic
      ((R₀ : Subgroup ↥(conjClosure S.M K)).map (conjClosure S.M K).subtype) :=
    CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hq (by rw [hRr]; omega)
  obtain ⟨D, hDR, -, hDnc, hDexp, hDcl, hND⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized hq2 hRp hRnc
  have hDL : D ≤ conjClosure S.M K := hDR.trans (Subgroup.map_subtype_le _)
  have hDp : IsPGroup q D := hRp.to_le hDR
  have hqσ : q ∉ uniqueFourSigma S.M := fun h => by
    have := hσL q h
    omega
  have hns := UC6S846.not_solvable_of_mem_calC hK
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have h4 : 3 < CFSG.Open.pRank S.p (S.M ⊓ normalizer (D : Set G)) := by
    have := UC6S846.le_pRank' hp (le_inf hBM (hR₀.trans hND)) hBel hBc
    omega
  have hΓ := h77 (UC6S846.sig_subset_sig1 hSg hns) S.p hpσ hp2
    (UC6S846.sp_of_mem_sig hSg hns hpσ) q hq hq2 hqσ D (hDL.trans hLM) hDp hDnc hDexp hDcl h4
  exact uniqueMax_of_theoremCAt S.maxLocal hC hq hq2 hLM hDL hDp
    (two_le_pRank_of_not_isCyclic hq hq2 hDp hDnc) hΓ

end R869S

theorem r869MCons_dataOfSetup4_of_kFactOutCyclic
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (hSE : StronglyEmbeddedFive)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hC76 : C76Three S) (hC : TheoremCAt S.M) (h77 : F07.R77E4 (dataOfSetup4 hS hU S)) :
    F08.R869MCons (dataOfSetup4 hS hU S) := by
  intro L hL hthin
  have hLM : L ≤ S.M := by
    rcases hL with ⟨hL, -⟩ | ⟨K, hK, -, rfl⟩
    · exact CFSG.Quasithin.A3.subnormal_le hL.1
    · exact (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK).1
  by_cases hp : ∃ p ∈ uniqueFourSigma S.M, 2 ≤ CFSG.Open.pRank p L
  · obtain ⟨p, hp, h2⟩ := hp
    exact uniqueMax_of_two_le_pRank_sigma hU S.maxLocal hp hLM h2
  have hσL : ∀ r ∈ uniqueFourSigma S.M, CFSG.Open.pRank r L ≤ 1 := fun r hr => by
    by_contra h
    exact hp ⟨r, hr, by omega⟩
  rcases hL with ⟨hK, hN⟩ | ⟨K, hK, hnot, rfl⟩
  · have hpσ := S.hp
    have hpp : S.p.Prime := hpσ.1.1
    have hp2 : S.p ≠ 2 := hpσ.1.2.1
    obtain ⟨B, hBM, hBel, hBc⟩ :=
      UC6S846.exists_elemAbelian_card_of_le_pRank hpp (four_le_pRank_of_sigma hpσ)
    have hns := UC6S846.not_solvable_of_mem_calC hK
    have hsp := UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hns hpσ
    have h76 : Conclusion76 S.M S.p := by
      by_cases h3 : 3 ∈ uniqueFourBeta G
      · exact hC76 hσ h3 S.p hpσ hsp
      · exact conclusion76_dataOfSetup4 hSE hS hU S h3 hpσ hsp
    have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top (uc22p20a_M_ne_top (dataOfSetup4 hS hU S)) hLM
    exact R869S.uniqueMax_of_normal S.maxLocal hC hK hN hthin hpp hp2 h76
      (R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hK.2.2 hpp hp2
        (hσL _ hpσ)) hBM hBel hBc
  · exact R869S.uniqueMax_conjClosure hS hU S hC h77 hK hnot hthin hσL

end CFSG.LocalAnalysis.UniquenessCase.UC6
