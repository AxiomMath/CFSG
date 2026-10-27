module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3Holds
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement
public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

theorem isPSolvable_of_k35c_reduced (hTor : CFSG.AGLEmbedding.KFactOneLieTorus) (hK631 : K631)
    (hY : CFSG.Open.IsKGroup Y) (hp2 : p ≠ 2) {N : Subgroup Y} (hN : IsStronglyPEmbedded p N)
    (hrk : 2 < CFSG.Open.pRank p (⊤ : Subgroup Y)) (hO : CFSG.pPrimeCore p Y = ⊥) :
    CFSG.HallHigman.IsPSolvable p ↥N := by
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp.out hO hN
  set K := CFSG.generalizedFitting Y with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hcat : CFSG.Open.IsCatalogGroup ↥K :=
    hY.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  obtain ⟨P₀, ⟨-, hP₀p, hP₀i⟩, hP₀N⟩ := hN.exists_isSylowOf_le
  set P : Sylow p Y := hP₀p.toSylow (by simpa [Subgroup.relIndex_top_right] using hP₀i) with hPdef
  have hPN : (P : Subgroup Y) ≤ N := by rw [hPdef, IsPGroup.toSylow_coe]; exact hP₀N
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  have hPK := inf_ne_bot_of_pPrimeCore hO hK1 P
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup Y) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hΓ := glbCore_sylow_ne_top hN P hPN hPK T hT
  have hAut : ¬ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 := fun h => by
    have := pRank_le_pRank_mulAut (p := p) K hKC
    omega
  by_cases hcyc : IsCyclic (T : Subgroup ↥K)
  ·
    exfalso
    have hle1 : CFSG.Open.pRank p K ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine CFSG.SectionRank.pRank_le hp.out.one_lt fun E _ hE => ?_
      rw [pow_one]
      exact CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hcyc hE
    have hge1 : 1 ≤ CFSG.Open.pRank p K :=
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter.one_le_pRank_of_isPGroup
        hp.out P.isPGroup'.to_inf_left hPK).trans
        (CFSG.SectionRank.pRank_mono hp.out.one_lt inf_le_right)
    have hnc : ¬ IsMulCommutative ↥K := fun h => by
      obtain ⟨a, b, hab⟩ := hKnab
      exact hab (h.is_comm.comm a b)
    have h2 := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_le_pRank_add_of_forall_inf_ne_bot
      hp.out K 1 fun D hD hcard hDK => by
        have h := hK631 Y hY p hp.out hp2 K hKn hKs hnc hKC (le_antisymm hle1 hge1) D hD hDK
        rw [hcard, pow_succ, pow_one] at h
        nlinarith [hp.out.two_le]
    omega
  ·
    obtain ⟨n, e, hF⟩ := hTor ↥K hKs hKnab hcat p hp2 T hcyc hΓ hAut
    have hco := hF.borel_coatom
    set Q : Subgroup Y := (P : Subgroup Y) ⊓ K with hQdef
    have hQN : Q ≤ N := inf_le_left.trans hPN
    have hQp : IsPGroup p ↥Q := P.isPGroup'.to_inf_left
    have hNK : N.subgroupOf K = normalizer ((T : Subgroup ↥K) : Set ↥K) := by
      have hle : normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
        intro k hk
        rw [Subgroup.mem_subgroupOf]
        have hk' := Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk)
        rw [hTmap] at hk'
        exact hN.normalizer_le hPK hQp hQN hk'
      have hne : N.subgroupOf K ≠ ⊤ := fun htop =>
        not_le_of_isStronglyPEmbedded hN P hPN hPK T hT fun k hk => by
          have h : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by
            rw [htop]
            exact Subgroup.mem_top _
          rwa [Subgroup.mem_subgroupOf] at h
      exact (hle.eq_or_lt.resolve_right fun hlt => hne (hco.2 _ hlt)).symm
    have hNKQ : N ⊓ K ≤ normalizer (Q : Set Y) := by
      intro y hy
      have hyK : (⟨y, hy.2⟩ : ↥K) ∈ normalizer ((T : Subgroup ↥K) : Set ↥K) := by
        rw [← hNK, Subgroup.mem_subgroupOf]
        exact hy.1
      have h := Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hyK)
      rwa [hTmap] at h
    have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q (N ⊓ K) :=
      (show CFSG.ABGLocalTools.IsSylowOf p Q K from ⟨T, hTmap⟩).of_le (le_inf hQN inf_le_right)
        inf_le_right
    have hNQ : ∀ n ∈ N, Q.map (MulAut.conj n).toMonoidHom = Q := by
      intro n hn
      have hQ'le : Q.map (MulAut.conj n).toMonoidHom ≤ N ⊓ K := by
        rintro _ ⟨q, hq, rfl⟩
        refine ⟨?_, ?_⟩
        · show n * q * n⁻¹ ∈ N
          exact N.mul_mem (N.mul_mem hn (hQN hq)) (N.inv_mem hn)
        · show n * q * n⁻¹ ∈ K
          exact hKn.conj_mem q hq.2 n
      have hcard : Nat.card ↥(Q.map (MulAut.conj n).toMonoidHom) = Nat.card ↥Q :=
        Subgroup.card_map_of_injective (MulAut.conj n).injective
      have hQ'syl : CFSG.ABGLocalTools.IsSylowOf p (Q.map (MulAut.conj n).toMonoidHom) (N ⊓ K) :=
        CFSG.ABGLocalTools.isSylowOf_of_card hQ'le (by rw [hcard, hQsyl.card_eq])
      obtain ⟨k, hk, hkQ⟩ := hQsyl.exists_mem_conj hQ'syl
      have hle : Q.map (MulAut.conj n).toMonoidHom ≤ Q := fun x hx => by
        have h1 := (hkQ x).1 hx
        have h2 := ((Subgroup.mem_normalizer_iff.1 (hNKQ hk)) (k⁻¹ * x * k)).1 h1
        have h3 : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
        rwa [h3] at h2
      exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
    have hsolA := hF.borel_solvable (N.map (MulAut.conjNormal : Y →* MulAut ↥K)) (by
      rintro _ ⟨n, hn, rfl⟩
      apply Subgroup.map_injective K.subtype_injective
      have hcomp : K.subtype.comp ((MulAut.conjNormal n : MulAut ↥K) : ↥K ≃* ↥K).toMonoidHom =
          (MulAut.conj n).toMonoidHom.comp K.subtype := by
        ext k
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hTmap]
      exact hNQ n hn)
    have hinj : Function.Injective ((MulAut.conjNormal : Y →* MulAut ↥K).subgroupMap N) := by
      intro a b hab
      apply Subtype.ext
      apply CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter.conjNormal_injective
        K hKC
      exact congrArg Subtype.val hab
    haveI := hsolA
    haveI : Group.IsSolvable ↥N := solvable_of_solvable_injective hinj
    exact CFSG.RankThree.PartTwo.Sec14.isPSolvable_of_isSolvable hp.out inferInstance

end Reduced

theorem k35c_of_kfacts (hTor : CFSG.AGLEmbedding.KFactOneLieTorus) (hK631 : K631) : K35c := by
  intro X _ _ hX p hp hp2 N hN h2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNq, hrk, hcore⟩ := quotient_of_stronglyPEmbedded hN h2
  have hYN := pPrimeCore_le_of_stronglyPEmbedded hN h2.le
  haveI : (CFSG.pPrimeCore p X).Normal := CFSG.pPrimeCore_normal
  exact isPSolvable_of_quotient_pPrimeCore hYN
    (isPSolvable_of_k35c_reduced hTor hK631 (hX.quotient _) hp2 hNq hrk hcore)

section Holds


theorem k35c_holds
    : K35c :=
  k35c_of_kfacts kFactOneLieTorus_holds k631_holds

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
