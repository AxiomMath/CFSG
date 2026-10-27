module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmP3
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmSpor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceTorus
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Five


theorem k35Ω_five (hSI : CFSG.AGLEmbedding.KFactSmallIdent)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus) (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hK2 : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hopp : Opp p (⊤ : Subgroup X) = ⊤) (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) {S B : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤)
    (hBS : B ≤ S) (hB : CFSG.Open.IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hΩ : ∀ x ∈ S, x ^ p = 1 → x ∈ B) (hBc : ∀ b ∈ B, ∀ y ∈ S, b * y = y * b) :
    IsSimpleGroup X ∧ (LieModel X .PSL 2 p 2 ∨ IsAlt X (2 * p) ∨
      (p = 3 ∧ (IsSpor X .M11 ∨ LieModel X .PSL 3 2 2)) ∨
      (p = 5 ∧ (LieModel X .Tits 0 2 1 ∨ IsSpor X .Fi22))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hcat : CFSG.Open.IsCatalogGroup ↥K :=
    hX.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  obtain ⟨U, hU⟩ := exists_sylow_coe_eq hS
  obtain ⟨g, hg⟩ := hN.exists_conj_ge (CFSG.ABGLocalTools.isSylowOf_iff.1 hS)
  have hN' := hN.conj g
  have hUN' : (U : Subgroup X) ≤ CFSG.RankThree.PartOne.StrongP.conjSub g N := by
    rw [hU]
    exact hg
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  have hPK := inf_ne_bot_of_pPrimeCore hO hK1 U
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal U (N := K)
  have hE2 : ∀ {E : Subgroup X}, CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p ^ 2 :=
    fun hE => card_le_sq_of_omega hS hBcard hΩ hE
  by_cases hcyc : IsCyclic ↥((U : Subgroup X) ⊓ K)
  ·
    exfalso
    have hrk : 2 ≤ CFSG.Open.pRank p (U : Subgroup X) := by
      rw [hU]
      exact CFSG.SectionRank.le_pRank hp.one_lt hBS hB hBcard
    have hΓ : CFSG.Open.rankThreeGamma 1 p (U : Subgroup X) ≠ ⊤ :=
      ne_top_of_le_ne_top hN'.1 (glbCore_le_of_isStronglyPEmbedded hN' U.isPGroup' hUN')
    rcases hK2 X K hKn hKs hKnab hcat hKC p hp hp2 U hcyc hrk hΓ with ⟨h3, -⟩ | ⟨h5, hiso⟩
    · exact hp3 h3
    · subst h5
      have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
      rw [hU] at hcyc
      have hTsyl : CFSG.ABGLocalTools.IsSylowOf 5 (S ⊓ K) K :=
        hS.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hKn])
      have hTcard : Nat.card ↥(S ⊓ K) = 25 := by
        rw [hTsyl.card_eq, hSz.card, CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
        norm_num
      have hTc : IsMulCommutative ↥(S ⊓ K) := hcyc.isMulCommutative
      have hBT : ¬ B ≤ S ⊓ K := by
        intro hBT
        have hBeq : B = S ⊓ K :=
          Subgroup.eq_of_le_of_card_ge hBT (by rw [hTcard, hBcard]; norm_num)
        obtain ⟨t, ht⟩ := hcyc.exists_generator
        have hord : orderOf t = 25 := by
          rw [orderOf_eq_card_of_forall_mem_zpowers ht]
          exact hTcard
        have ht5 : (t : X) ^ 5 = 1 := hB.2 t (by rw [hBeq]; exact t.2)
        have ht5' : t ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact ht5)
        have h := orderOf_dvd_of_pow_eq_one ht5'
        rw [hord] at h
        omega
      set P' : Subgroup X := S ⊓ K ⊔ B with hP'
      have hP'S : P' ≤ S := sup_le inf_le_left hBS
      have hP'p : IsPGroup 5 ↥P' := hS.isPGroup.to_le hP'S
      have hcen : P' ≤ Subgroup.centralizer ((S ⊓ K : Subgroup X) : Set X) := by
        refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun t ht => ?_)
          (fun b hb => Subgroup.mem_centralizer_iff.2 fun t ht =>
            (hBc b hb t (Subgroup.mem_inf.1 ht).1).symm)
        exact congrArg Subtype.val (hTc.is_comm.comm (⟨t, ht⟩ : ↥(S ⊓ K)) ⟨x, hx⟩)
      have hcomm : ∀ x ∈ P', ∀ t ∈ S ⊓ K, x * t = t * x := fun x hx t ht =>
        (Subgroup.mem_centralizer_iff.1 (hcen hx) t ht).symm
      have hTlt : Nat.card ↥(S ⊓ K) < Nat.card ↥P' := by
        by_contra hle
        push Not at hle
        have hTP : S ⊓ K = P' := Subgroup.eq_of_le_of_card_ge le_sup_left hle
        exact hBT (hTP ▸ le_sup_right)
      obtain ⟨n, hn⟩ := hP'p.exists_card_eq
      rw [hTcard, hn] at hTlt
      have hn3 : 3 ≤ n := by
        by_contra h
        push Not at h
        interval_cases n <;> norm_num at hTlt
      have hP'card : 125 ∣ Nat.card ↥P' := by
        rw [hn, show (125 : ℕ) = 5 ^ 3 by norm_num]
        exact Nat.pow_dvd_pow 5 hn3
      exact CFSG.RankThree.PartOne.K159.SzAbs.sz_core hSz hKs hKC inf_le_right hTcard hP'p le_sup_left
        hP'card hcomm
  ·
    have hTnc : ¬ IsCyclic (T : Subgroup ↥K) := fun h => hcyc (by
      have e : ↥(T : Subgroup ↥K) ≃* ↥((U : Subgroup X) ⊓ K) :=
        (MulEquiv.subgroupCongr hT).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
      exact (MulEquiv.isCyclic e).mp h)
    have hΓ := glbCore_sylow_ne_top hN' U hUN' hPK T hT
    have hrk2 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2 :=
      CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => by
        have h := hE2 (CFSG.SectionRank.isElemAbelian_map hE K.subtype)
        rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
    have hrk2' : CFSG.pRank p ↥(⊤ : Subgroup ↥K) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hrk2
    have hsmall := hSI ↥K hKs hKnab hcat p hp hp2 T hTnc hΓ hrk2'
    have hAut2 := CFSG.AGLEmbedding.kFactSmallOfRankTwo_of
      (CFSG.AGLEmbedding.kFactSmallAutRank_of_torus hTor) ↥K hKs hKnab hcat p hp hp2 T hTnc hΓ hrk2
    have hinn := hOutP ↥K hKs hKnab hcat p hp hp2 T hTnc hΓ hAut2 (fun h => hp3 h.1)
    have hK : K = ⊤ := by
      have h := opp_le_of_forall (p := p) (K := K) fun x n hx => mem_of_forall_inner K hKC hinn hx
      rw [hopp] at h
      exact top_le_iff.1 h
    have e : ↥K ≃* X := mulEquivOfEqTop hK
    refine ⟨e.symm.isSimpleGroup, ?_⟩
    rcases hsmall with ⟨⟨d, hv⟩, ⟨q, hd, hqp, hqe⟩, ⟨f⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hqp, hqe, hd⟩, ⟨f⟩⟩ | hA |
        ⟨h3, -⟩ | ⟨h5, hT5⟩ | ⟨h11, hJ4⟩
    ·
      obtain rfl : d = _ := hd
      have hL := blueprintLieModel_of_models_classical (CFSG.Models.lieModel_A 1 q hv f) (Or.inl rfl)
        (by norm_num)
      rw [hqp, hqe] at hL
      exact Or.inl (hL.of_mulEquiv e)
    ·
      exfalso
      obtain rfl : d = _ := hd
      have hL := blueprintLieModel_of_models_classical (CFSG.Models.lieModel_twistedA 2 q hv f)
        (Or.inr rfl) (by norm_num)
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA 2 q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
      rw [hc, hf, hqp, hqe] at hL
      exact false_of_lieModel_psu3 hp2 (hL.of_mulEquiv e) hS hBcard hΩ
    ·
      obtain ⟨φ⟩ : Nonempty (↥K ≃* alternatingGroup (Fin (2 * p))) := hA
      exact Or.inr (Or.inl (show Nonempty (X ≃* alternatingGroup (Fin (2 * p))) from ⟨e.symm.trans φ⟩))
    · exact absurd h3 hp3
    ·
      subst h5
      rcases hT5 with ⟨⟨d, hv⟩, hd, ⟨f⟩⟩ | hMcL | hFi
      · obtain rfl : d = _ := hd
        exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl
          ((CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_tits hv f).of_mulEquiv e)⟩))
      · obtain ⟨f⟩ : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) := hMcL
        exact (not_omega_central_mcl
          (show Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .McL) from
            ⟨e.symm.trans (f.trans (hbr .McL).some.symm)⟩) hS hBcard hΩ).elim
      · obtain ⟨f⟩ : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) := hFi
        exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr
          (show Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi22) from
            ⟨e.symm.trans (f.trans (hbr .Fi22).some.symm)⟩)⟩))
    ·
      subst h11
      obtain ⟨f⟩ : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) := hJ4
      exact (not_omega_central_j4
        (show Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) from
          ⟨e.symm.trans (f.trans (hbr .J4).some.symm)⟩) hS hBcard hΩ).elim

end Five

end CFSG.LocalAnalysis.UniquenessCase.UCK
