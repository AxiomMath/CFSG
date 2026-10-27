module

public import CFSG.Quasithin.EmptyFaithful.S146B3
public import CFSG.Quasithin.Background.C2Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem solvableRadical_oTwoQuot_eq_bot {H : Subgroup G} (h : OddCoreModTwoTrivial H) :
    CFSG.solvableRadical (OTwoQuot H) = ⊥ := by
  classical
  by_contra hne
  have hXn : (CFSG.solvableRadical (OTwoQuot H)).Normal := inferInstance
  have hXs : Group.IsSolvable ↥(CFSG.solvableRadical (OTwoQuot H)) := A3.solvableRadical_isSolvable
  obtain ⟨N, hNn, hNle, hNbot, hNmin⟩ :=
    CFSG.exists_minimal_normal_le (CFSG.solvableRadical (OTwoQuot H)) hXn hne
  have : N.Normal := hNn
  have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (hNmin K hK hKN hKb)⟩
  have : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNle)
  obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have : Fact q.Prime := ⟨hq⟩
  have hqg : IsPGroup q ↥N := CFSG.IsElementaryAbelian.isPGroup q ↥N
  have hle : N ≤ CFSG.pCore q (OTwoQuot H) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hqg
  by_cases hq2 : q = 2
  · subst hq2
    rw [pCore_two_quot_eq_bot H, le_bot_iff] at hle
    exact hNbot hle
  · rw [pCore_oTwoQuot_eq_bot_of_oddCore h hq hq2, le_bot_iff] at hle
    exact hNbot hle

theorem le_oTwoFstarIn_of_mem_cComp {H K : Subgroup G} (h : OddCoreModTwoTrivial H)
    (hK : K ∈ cComp H) : K ≤ oTwoFstarIn H := by
  have hrad := solvableRadical_oTwoQuot_eq_bot h
  have hsolv : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥H) := hp.isNilpotent
    infer_instance
  have hNn : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hK' := (cComp_subgroupOf_bijOn H).mapsTo hK
  have hJ := (cComp_quotient_bijOn (CFSG.Open.pCore 2 ↥H) hsolv).mapsTo hK'
  have hcomp := isComponent_of_mem_cComp_top hrad hJ
  have hlayer : (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) ≤
      CFSG.layer (OTwoQuot H) := le_sSup hcomp
  rw [oTwoFstarIn_eq_map_O2Fstar]
  intro x hx
  have hxH : x ∈ H := le_of_mem_cComp hK hx
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hxH⟩ : OTwoQuot H) ∈
      (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  exact (le_sup_right : CFSG.layer (OTwoQuot H) ≤ CFSG.generalizedFitting (OTwoQuot H)) (hlayer h1)

end CFSG.Quasithin
