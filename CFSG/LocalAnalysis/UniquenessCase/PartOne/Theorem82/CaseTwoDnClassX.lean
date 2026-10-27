module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.Quasithin.EmptyFaithful.SzPS8S6Class
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.Background.F918V5GRank
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.LocalAnalysis.AGLEmbedding.ClassXLieModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnK11
import CFSG.GroupTheory.AlternatingThreeRank

public section

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem Dn_le_of_inClassXBlock (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N : Subgroup G} (hKN : t.Ky ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) (hO : t.On N ≤ c.S.M)
    (hX : CFSG.AGLEmbedding.InClassXBlock (t.Dn N)) : t.Dn N ≤ c.S.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  have hsimpleDhat : IsSimpleGroup (t.Dhat N) := t.isSimpleGroup_Dhat hZN hrank
  obtain ⟨a, b, hab⟩ := t.exists_mul_ne_mul_Dhat hK32 hGA hSp hKN
  have hO2le : CFSG.pCore 2 ↥(t.Dn N) ≤ CFSG.pPrimeCore 3 ↥(t.Dn N) :=
    CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two Nat.prime_three (by norm_num) _
  have hZdvd : 3 ∣ Nat.card ↥(t.Dn N) := by
    have h := Subgroup.card_dvd_of_le (t.Z_le_Dn hZN)
    rwa [t.card_Z] at h
  have hOne : CFSG.pPrimeCore 3 ↥(t.Dn N) ≠ ⊤ := by
    intro htop
    have hcop : Nat.Coprime 3 (Nat.card ↥(t.Dn N)) := by
      have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(t.Dn N))
      rwa [htop, Subgroup.card_top] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop hZdvd
  have hnotdvd : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥(t.Dn N)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)
      (G := ↥(CFSG.pCore 2 ↥(t.Dn N)))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(t.Dn N)))
    rw [hk]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hQrank : CFSG.pRank 3 (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) = 1 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
      (CFSG.pCore 2 ↥(t.Dn N)) hnotdvd, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hrank
  obtain ⟨-, htype⟩ := hX
  rcases htype with ⟨n, hn1, hlin⟩ | ⟨n, hn1, halt⟩
  ·
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | hn2
    ·
      subst h1
      obtain ⟨F, instF, instFinF, hFcard, α, hαs, hker, -⟩ := hlin
      letI : Field F := instF
      letI : Fintype F := instFinF
      have hF2 : Nat.card F = 2 := by
        rw [Nat.card_eq_fintype_card, hFcard]
        norm_num
      let eQ : (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)
      have hQcard : Nat.card (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) = 6 := by
        rw [Nat.card_congr eQ.toEquiv,
          CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF2]
        norm_num
      have hcard : Nat.card (t.Dhat N) ≤ 12 := by
        calc Nat.card (t.Dhat N)
            ≤ Nat.card (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) :=
              Nat.card_le_card_of_surjective
                (QuotientGroup.map (CFSG.pCore 2 ↥(t.Dn N))
                  (CFSG.pPrimeCore 3 ↥(t.Dn N)) (MonoidHom.id ↥(t.Dn N))
                  (by simpa using hO2le))
                (QuotientGroup.map_surjective_of_surjective _ _ _
                  (by simpa using QuotientGroup.mk_surjective) (by simpa using hO2le))
          _ = 6 := hQcard
          _ ≤ 12 := by norm_num
      haveI := hsimpleDhat
      exfalso
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr
        (CFSG.Quasithin.SzPS8.S6Class.isSolvable_of_card_le_twelve hcard) a b)
    ·
      have hlin0 := hlin
      obtain ⟨F, instF, instFinF, hFcard, α, hαs, hker, -⟩ := hlin
      letI : Field F := instF
      letI : Fintype F := instFinF
      have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFcard]
      haveI hchar : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
      haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (CFSG.Timmesfeld.RankOne.psl2EquivSL2 F).symm.isSimpleGroup
      let eQ : (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)
      have hOle : CFSG.pPrimeCore 3 ↥(t.Dn N) ≤ CFSG.pCore 2 ↥(t.Dn N) :=
        CFSG.GroupTheory.pPrimeCore_le_pCore_of_simple_quotient eQ hOne hO2le
      have hcore : CFSG.pPrimeCore 3 ↥(t.Dn N) = CFSG.pCore 2 ↥(t.Dn N) :=
        le_antisymm hOle hO2le
      have hLieQ : CFSG.Blueprint.LieModel
          (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) .PSL 2 2 n :=
        CFSG.AGLEmbedding.lieModel_PSL_two_of_isLin2Type hn2 hlin0
      have hLieDhat : CFSG.Blueprint.LieModel (t.Dhat N) .PSL 2 2 n :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          (QuotientGroup.quotientMulEquivOfEq hcore).symm hLieQ
      exact t.Dn_le_of_K11 hK11 hK32 hGA hSp hp hN hZ hKN hrank hO
        (Or.inl ⟨2, n, hLieDhat⟩)
  ·
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | hn3
    ·
      subst h1
      obtain ⟨α, hαs, hker, -⟩ := halt
      let eQ : (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) ≃* alternatingGroup (Fin 3) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)
      have hcardAlt : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        norm_num
      have hQcard : Nat.card (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) = 3 := by
        rw [Nat.card_congr eQ.toEquiv, hcardAlt]
      have hcard : Nat.card (t.Dhat N) ≤ 12 := by
        calc Nat.card (t.Dhat N)
            ≤ Nat.card (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) :=
              Nat.card_le_card_of_surjective
                (QuotientGroup.map (CFSG.pCore 2 ↥(t.Dn N))
                  (CFSG.pPrimeCore 3 ↥(t.Dn N)) (MonoidHom.id ↥(t.Dn N))
                  (by simpa using hO2le))
                (QuotientGroup.map_surjective_of_surjective _ _ _
                  (by simpa using QuotientGroup.mk_surjective) (by simpa using hO2le))
          _ = 3 := hQcard
          _ ≤ 12 := by norm_num
      haveI := hsimpleDhat
      exfalso
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr
        (CFSG.Quasithin.SzPS8.S6Class.isSolvable_of_card_le_twelve hcard) a b)
    ·
      subst h2
      have h5 : CFSG.QuasithinUnique.IsAltType (t.Dn N) 5 := halt
      obtain ⟨α, hαs, hker, -⟩ := halt
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; norm_num)
      let eQ : (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) ≃* alternatingGroup (Fin 5) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)
      have hOle : CFSG.pPrimeCore 3 ↥(t.Dn N) ≤ CFSG.pCore 2 ↥(t.Dn N) :=
        CFSG.GroupTheory.pPrimeCore_le_pCore_of_simple_quotient eQ hOne hO2le
      have hcore : CFSG.pPrimeCore 3 ↥(t.Dn N) = CFSG.pCore 2 ↥(t.Dn N) :=
        le_antisymm hOle hO2le
      have hLieQ : CFSG.Blueprint.LieModel
          (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) .PSL 2 2 2 :=
        CFSG.AGLEmbedding.lieModel_PSL_two_two_two_of_isAltType_five h5
      have hLieDhat : CFSG.Blueprint.LieModel (t.Dhat N) .PSL 2 2 2 :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          (QuotientGroup.quotientMulEquivOfEq hcore).symm hLieQ
      exact t.Dn_le_of_K11 hK11 hK32 hGA hSp hp hN hZ hKN hrank hO
        (Or.inl ⟨2, 2, hLieDhat⟩)
    ·
      obtain ⟨α, hαs, hker, -⟩ := halt
      let eQ : (↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) ≃*
          alternatingGroup (Fin (2 * n + 1)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)
      have hm6 : 6 ≤ 2 * n + 1 := by omega
      obtain ⟨P, hP3, hPnc⟩ :=
        CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup
          (n := 2 * n + 1) hm6 eQ
      have h2 := CFSG.Quasithin.F918V5G.two_le_pRank_of_not_cyclic
        (G := ↥(t.Dn N) ⧸ CFSG.pCore 2 ↥(t.Dn N)) (H := ⊤) (Q := P) le_top hP3 hPnc
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
      rw [hQrank] at h2
      exact absurd h2 (by norm_num)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
