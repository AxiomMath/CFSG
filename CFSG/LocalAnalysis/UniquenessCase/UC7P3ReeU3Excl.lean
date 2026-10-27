module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Rows3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.LocalAnalysis.UniquenessCase.UC7P3BorelInv
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3ConclusionPlus Gls3StronglyThreeEmbeddedPlus)

theorem exponent_eq_one_of_isoLie_twistedA {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) (P : Sylow p X) (hPN : (P : Subgroup X) ≤ N)
    (hC : ∀ y : X, orderOf y = 2 →
      y ∈ normalizer (((P : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X) →
      ¬ IsCyclic ↥((P : Subgroup X) ⊓ CFSG.generalizedFitting X ⊓ centralizer ({y} : Set X)) →
        centralizer ({y} : Set X) ≤ N)
    {q : TauCeti.PrimePower} (hq : q.p = p)
    (hI : IsoLie ↥(CFSG.generalizedFitting X) (.twistedA 2 q)) : q.exponent = 1 := by
  obtain ⟨hKs, -, hKn, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Fact.out hO hN
  haveI := hKn
  haveI := hKs
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := CFSG.generalizedFitting X)
  have hTmap : (T : Subgroup ↥(CFSG.generalizedFitting X)).map
      (CFSG.generalizedFitting X).subtype = (P : Subgroup X) ⊓ CFSG.generalizedFitting X := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  have hm := CFSG.Models.lieModel_twistedA 2 q hv e
  rw [hc, hf, hq] at hm
  by_contra hne
  obtain ⟨y, hyN, hy2, hync, hle⟩ := exists_involution_of_lieModel_psu_subgroup hp2
    (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
    (by have := q.exponent_pos; omega) ⟨T, hTmap⟩
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN
    (CFSG.LocalAnalysis.UniquenessCase.UCK.inf_ne_bot_of_pPrimeCore hO
      ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance) P) T hT
    (hle.trans (sup_le (inf_le_left.trans hPN) (hC y hy2 hyN hync)))

theorem not_isoLie_reeG2_of_isStronglyPEmbedded (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) {p : ℕ} (hp3 : p = 3) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) (P : Sylow p X) (hPN : (P : Subgroup X) ≤ N)
    (hC : ∀ y : X, orderOf y = 2 →
      y ∈ normalizer (((P : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X) →
      ¬ IsCyclic ↥((P : Subgroup X) ⊓ CFSG.generalizedFitting X ⊓ centralizer ({y} : Set X)) →
        centralizer ({y} : Set X) ≤ N)
    (m : ℕ) : ¬ IsoLie ↥(CFSG.generalizedFitting X) (.reeG2 m) := by
  rintro ⟨hv, ⟨e⟩⟩
  obtain ⟨hNL, -⟩ := inf_eq_and_le_normalizer_of_isStronglyPEmbedded hG3 hp3 hX hO h2 hN P hPN
  subst hp3
  obtain ⟨-, -, hKn, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  haveI := hKn
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := CFSG.generalizedFitting X)
  have hTmap : (T : Subgroup ↥(CFSG.generalizedFitting X)).map
      (CFSG.generalizedFitting X).subtype = (P : Subgroup X) ⊓ CFSG.generalizedFitting X := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hd : CFSG.AGLEmbedding.IsReeGTwoIndex 3 ⟨.reeG2 m, hv⟩ := ⟨rfl, m, rfl⟩
  obtain ⟨J, hJN, hJ2, -, hJel, hJcard, hJC⟩ :=
    hRee ↥(CFSG.generalizedFitting X) _ hd ⟨e⟩ T
  have hW : ((T : Subgroup ↥(CFSG.generalizedFitting X)) ⊓
      centralizer ({J} : Set ↥(CFSG.generalizedFitting X))).map
        (CFSG.generalizedFitting X).subtype ≤ (P : Subgroup X) ⊓ CFSG.generalizedFitting X ⊓
          centralizer ({(J : X)} : Set X) := by
    rintro _ ⟨c, ⟨hcT, hcJ⟩, rfl⟩
    refine ⟨by rw [← hTmap]; exact ⟨c, hcT, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hcJ)
  have hnc : ¬ IsCyclic ↥((P : Subgroup X) ⊓ CFSG.generalizedFitting X ⊓
      centralizer ({(J : X)} : Set X)) := by
    intro hcyc
    have hcyc' := Subgroup.isCyclic_of_le hW
    refine CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22n_not_isCyclic_of_card Nat.prime_three
      hJel ?_ ((Subgroup.equivMapOfInjective _ _
        (CFSG.generalizedFitting X).subtype_injective).isCyclic.mpr hcyc')
    rw [hJcard]
    exact Nat.pow_le_pow_right (by norm_num)
      ((by norm_num : 2 ≤ 3).trans hd.three_le_fieldExponent)
  have hCN := hC (J : X) ((Subgroup.orderOf_coe J).trans hJ2)
    (by rw [← hTmap]; exact Subgroup.le_normalizer_map _ ⟨J, hJN, rfl⟩) hnc
  refine hJC fun c hc => ?_
  have hcN : (c : X) ∈ N ⊓ CFSG.generalizedFitting X :=
    ⟨hCN (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))), c.2⟩
  rw [hNL, ← hTmap] at hcN
  have h := Subgroup.le_normalizer_comap (CFSG.generalizedFitting X).subtype
    (Subgroup.mem_comap.mpr hcN.2)
  rwa [Subgroup.comap_map_eq_self_of_injective (CFSG.generalizedFitting X).subtype_injective] at h

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem rows3_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Config k H) (P : Sylow k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    Gls3ConclusionPlus (↥H ⧸ CFSG.pPrimeCore k.p ↥H)
        (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
        (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      (∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) (.reeG2 m)) ∧
      ∀ q : TauCeti.PrimePower, q.p = 3 →
        IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) (.twistedA 2 q) →
          q.exponent = 1 := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow k.p ↥(H ⊓ k.M)) := inferInstance
  obtain ⟨P', hP', hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH
    (P := (P₀ : Subgroup ↥(H ⊓ k.M)).map (H ⊓ k.M).subtype) ⟨P₀, rfl⟩
  refine ⟨k.gls3ConclusionPlus_quotient hG3 hp3 hH P,
    not_isoLie_reeG2_of_isStronglyPEmbedded hG3 hRee hp3
      ((k.standing.kProper.isKGroup H hH.ne_top).quotient _)
      (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.two_le_pRank_quotient_pPrimeCore hH)
      (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) P' hP'N (fun y hy hyQ hnc => ?_),
    fun q hq hI => exponent_eq_one_of_isoLie_twistedA k.odd
      (CFSG.pPrimeCore_quotient_eq_bot k.prime)
      (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) P' hP'N (fun y hy hyQ hnc => ?_)
      (hq.trans hp3.symm) hI⟩
  all_goals
    rw [hP'] at hyQ hnc
    exact k.centralizer_le_of_not_isCyclic_inf_fstar hH (Subgroup.map_subtype_le _)
      (P₀.isPGroup'.map _) hy hyQ hnc

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
theorem exists_rows3_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : k.Config H) :
    ∃ P : Subgroup (F07.QuotK7 k.p H),
      Gls3ConclusionPlus (F07.QuotK7 k.p H) (CFSG.generalizedFitting (F07.QuotK7 k.p H)) P ∧
        ∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting (F07.QuotK7 k.p H)) (.reeG2 m) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨P⟩ : Nonempty (Sylow k.p (F07.QuotK7 k.p H)) := Sylow.nonempty
  obtain ⟨h, hR, -⟩ := k.rows3_of_config hG3 hRee hp3 hH P
  exact ⟨P, h, hR⟩

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
