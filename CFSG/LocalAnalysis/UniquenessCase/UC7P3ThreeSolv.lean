module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus gammaCore)

section Generic

variable {X : Type} [Group X] [Finite X]

theorem isSolvable_of_pGroup_quotient {Q Γ : Subgroup X} [(Q.subgroupOf Γ).Normal]
    (hQp : IsPGroup 3 Q) (hQΓ : Q ≤ Γ) (hq : Group.IsSolvable (↥Γ ⧸ Q.subgroupOf Γ)) :
    Group.IsSolvable ↥Γ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥Q := hQp.isNilpotent
  haveI : Group.IsSolvable ↥Q := inferInstance
  haveI : Group.IsSolvable ↥(Q.subgroupOf Γ) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQΓ).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI := hq
  exact Group.isSolvable_of_subgroup_quotient (Q.subgroupOf Γ)

theorem isSolvable_of_sup_pGroup {Q S Γ : Subgroup X} (hQp : IsPGroup 3 Q)
    (hΓN : Γ ≤ Subgroup.normalizer (Q : Set X)) (hsup : Q ⊔ S = Γ) (hS : Group.IsSolvable ↥S) :
    Group.IsSolvable ↥Γ := by
  have hQΓ : Q ≤ Γ := hsup ▸ le_sup_left
  have hSΓ : S ≤ Γ := hsup ▸ le_sup_right
  haveI : (Q.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).2 hΓN
  refine isSolvable_of_pGroup_quotient hQp hQΓ ?_
  haveI := hS
  refine Group.isSolvable_of_surjective
    (f := (QuotientGroup.mk' (Q.subgroupOf Γ)).comp (Subgroup.inclusion hSΓ)) ?_
  intro y
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Γ) y
  have hγ : γ ∈ Q.subgroupOf Γ ⊔ S.subgroupOf Γ := by
    rw [← Subgroup.subgroupOf_sup hQΓ hSΓ, hsup, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top γ
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hγ
  obtain ⟨n, hn, s, hs, rfl⟩ := hγ
  refine ⟨⟨(s : X), hs⟩, ?_⟩
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, map_mul]
  rw [(QuotientGroup.eq_one_iff n).2 hn, one_mul]
  rfl

end Generic

theorem isSolvable_of_isStronglyPEmbedded_three (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore 3 X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded 3 N) : Group.IsSolvable ↥N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hcat : CFSG.Open.IsCatalogGroup ↥K :=
    hX.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  have hout : Group.IsSolvable (Outer ↥K) := hSch ↥K hKs hKnab hcat
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hrk : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hN.1 (top_le_iff.1 ?_)
    rw [← h]
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded hN P.isPGroup'
      hPN
  obtain ⟨hlt, hmax, hrows⟩ := hG3 X hX K hKn hKs hKnab hKC P hrk hΓX
  set Q : Subgroup X := (P : Subgroup X) ⊓ K with hQdef
  have hQp : IsPGroup 3 Q := P.isPGroup'.to_inf_left
  have hQN : Q ≤ N := inf_le_left.trans hPN
  have hQK : Q ≤ K := inf_le_right
  have hΓN : ∀ {Γ : Subgroup X}, Γ = K ⊓ Subgroup.normalizer (Q : Set X) →
      Γ ≤ Subgroup.normalizer (Q : Set X) := fun h => h ▸ inf_le_right
  have h2grp : ∀ (S : Subgroup X) (n : ℕ), Nat.card ↥S = 2 ^ n → Group.IsSolvable ↥S :=
    fun S n hS => by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent ↥S := (IsPGroup.of_card hS).isNilpotent
      infer_instance
  have hcyc : ∀ J : Subgroup X, IsCyclic ↥J → gammaCore 3 1 K Q = Q ⊔ J →
      gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) →
      Group.IsSolvable ↥(gammaCore 3 1 K Q) := fun J hJ hΓJ hΓe => by
    haveI := hJ
    exact isSolvable_of_sup_pGroup hQp (hΓN hΓe) hΓJ.symm inferInstance
  have hΓ : gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) ∧
      Group.IsSolvable ↥(gammaCore 3 1 K Q) := by
    rcases hrows with ⟨q, -, -, -, hΓe, ⟨J, hJ, hΓJ⟩, -⟩ | ⟨q, -, -, -, hΓe, ⟨J, hJ, hΓJ⟩, -⟩ |
        ⟨m, -, -, hΓe, ⟨J, hJ, hΓJ⟩, -⟩ | ⟨-, -, -, h9, hΓe, hD, -⟩ |
        ⟨-, -, -, -, hΓe, J, hJ, hΓJ, -⟩ | ⟨-, -, -, -, -, hΓe, S, -, -, hsup, ⟨hQ8⟩, -⟩ |
        ⟨-, -, -, -, hΓe, S, -, hsup, h16, -⟩
    · exact ⟨hΓe, hcyc J hJ hΓJ hΓe⟩
    · exact ⟨hΓe, hcyc J hJ hΓJ hΓe⟩
    · exact ⟨hΓe, hcyc J hJ hΓJ hΓe⟩
    ·
      refine ⟨hΓe, ?_⟩
      have hQΓ : Q ≤ gammaCore 3 1 K Q := hΓe ▸ le_inf hQK Subgroup.le_normalizer
      haveI : (Q.subgroupOf (gammaCore 3 1 K Q)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).2 (hΓN hΓe)
      have hΓcard : Nat.card ↥(gammaCore 3 1 K Q) = 18 := by
        obtain ⟨e⟩ := hD
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
      have hQ'card : Nat.card ↥(Q.subgroupOf (gammaCore 3 1 K Q)) = 9 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv]
        exact h9
      have hqcard : Nat.card (↥(gammaCore 3 1 K Q) ⧸ Q.subgroupOf (gammaCore 3 1 K Q)) = 2 := by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (gammaCore 3 1 K Q))
        rw [hΓcard, hQ'card] at this
        omega
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : IsCyclic (↥(gammaCore 3 1 K Q) ⧸ Q.subgroupOf (gammaCore 3 1 K Q)) :=
        isCyclic_of_prime_card hqcard
      exact isSolvable_of_pGroup_quotient hQp hQΓ inferInstance
    · exact ⟨hΓe, hcyc J hJ hΓJ hΓe⟩
    ·
      refine ⟨hΓe, isSolvable_of_sup_pGroup hQp (hΓN hΓe) hsup (h2grp S 3 ?_)⟩
      rw [Nat.card_congr hQ8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    ·
      exact ⟨hΓe, isSolvable_of_sup_pGroup hQp (hΓN hΓe) hsup (h2grp S 4 (by rw [h16]; norm_num))⟩
  obtain ⟨hΓe, hΓsol⟩ := hΓ
  have hΓK : gammaCore 3 1 K Q ≤ K := hlt.le
  have hNT : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) =
      (gammaCore 3 1 K Q).subgroupOf K := by
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hQK, hΓe, Subgroup.inf_subgroupOf_left]
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK hQp hQN hQK
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.1 h)
  have hmaxT : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    rw [hNT]
    refine ⟨fun h => absurd (Subgroup.subgroupOf_eq_top.1 h) (not_le_of_gt hlt), fun b hb => ?_⟩
    have hmapΓ : ((gammaCore 3 1 K Q).subgroupOf K).map K.subtype = gammaCore 3 1 K Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hΓK]
    have hlt' : gammaCore 3 1 K Q < b.map K.subtype := by
      rw [← hmapΓ]
      exact (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hb
    have hbK : b.map K.subtype = K := hmax _ hlt' (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ b.map K.subtype := by rw [hbK]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hsolT : Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    rw [hNT]
    haveI := hΓsol
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hΓK).symm.toMonoidHom) (MulEquiv.surjective _)
  exact isSolvable_of_isCoatom_normalizer hKC hout hmaxT hsolT hle hne

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
