module

public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.E1.RootLift

open CFSG.Open CFSG.Quasithin A1b
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_kerIn_of_minParabolic {H T M : Subgroup G} (hmin : MinParabolic H T M) :
    Group.IsSolvable ↥(kerIn M H) := by
  have h1 := hmin.subgroupOf.isSolvable_kerIn
  rw [B6.kerIn_subgroupOf_top] at h1
  have hle : kerIn M H ≤ H := hmin.kerIn_le_H
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem star_facts {H T M K A : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) (hmin : MinParabolic H T M) (hKc : K ∈ cComp H)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* SL(2, F)) (hAK : A ≤ K) :
    Nonempty (↥(E2.star M H K) ≃* SL(2, F)) ∧
      Nat.card ↥((A.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H))) =
        Nat.card ↥((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hOK : pCoreOf 2 K ≤ kerIn M H :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)).trans hmin.pCoreOf_le_kerIn
  obtain ⟨φ, hφs, hφk⟩ := Vol2.Ch11.SecB.exists_starHom hKH hOK
  set e₀ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ CFSG.Open.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2) with he₀
  have hSL := isSimpleGroup_SL2 h4
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.Open.pCore 2 ↥K) := (e₀.symm.trans e).isSimpleGroup
  have hker : φ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with h | h
    · exact h
    · exfalso
      apply not_isSolvable_of_mem_cComp hKc
      have hKJ : K ≤ kerIn M H := by
        intro k hk
        have h1 : φ ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.Open.pCore 2 ↥K) = 1 := by
          rw [← MonoidHom.mem_ker, h]
          trivial
        have h2 := congrArg Subtype.val h1
        rw [hφk, QuotientGroup.mk'_apply, OneMemClass.coe_one, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf] at h2
        exact h2
      have := isSolvable_kerIn_of_minParabolic hmin
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKJ)
        (Subgroup.inclusion_injective hKJ)
  have hφi : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  refine ⟨⟨(MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm.trans (e₀.symm.trans e)⟩, ?_⟩
  set A₁ := (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) with hA₁
  have h1 : A₁ = ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map
      e₀.toMonoidHom := by
    rw [Subgroup.map_map]
    try rfl
  have h2 : (A₁.map φ).map (E2.star M H K).subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
      exact ⟨Subgroup.inclusion hKH k, hk, (hφk k).symm⟩
    · rintro ⟨h, hh, rfl⟩
      have hhK : (h : G) ∈ K := hAK hh
      refine ⟨φ ((⟨h, hhK⟩ : ↥K) : ↥K ⧸ CFSG.Open.pCore 2 ↥K),
        ⟨_, ⟨⟨h, hhK⟩, hh, rfl⟩, rfl⟩, ?_⟩
      rw [Subgroup.coe_subtype, hφk]
      try rfl
  rw [← h2, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective hφi, h1, Subgroup.card_map_of_injective e₀.injective]

end CFSG.Quasithin.E1.RootLift
