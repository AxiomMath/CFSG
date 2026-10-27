module

public import CFSG.LocalAnalysis.WeakClosure81.EightDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaSetIn (V K E : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ omegaSet V K E ∧ U ≤ K}

structure Hyp83 (V H T : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  two_lt_card : 2 < Nat.card V
  isTI : CFSG.CGT.Timmesfeld75.IsTI V
  isCalH : IsCalH V H
  not_isCalH0 : ¬ IsCalH0 V H
  sylow : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))

theorem Hyp83.of_hyp7 {V H T : Subgroup G} (hV7 : Hyp7 V) (hH : IsCalH V H)
    (hH0 : ¬ IsCalH0 V H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    Hyp83 V H T :=
  ⟨hV7.1, hV7.2.1, hV7.2.2, hH, hH0, hT⟩

namespace Hyp83

variable {V H T : Subgroup G}

theorem le_H (h : Hyp83 V H T) : V ≤ H :=
  h.isCalH.1

theorem not_le_pCoreOf (h : Hyp83 V H T) : ¬ V ≤ pCoreOf 2 H :=
  fun hV => h.not_isCalH0 ⟨h.isCalH, hV⟩

theorem sylow_H (h : Hyp83 V H T) : IsSylowIn 2 T H :=
  isSylowIn_of_isCalH h.isCalH h.sylow

theorem T_le_H (h : Hyp83 V H T) : T ≤ H :=
  h.sylow.le.trans inf_le_left

theorem T_le_normalizer (h : Hyp83 V H T) : T ≤ Subgroup.normalizer (V : Set G) :=
  h.sylow.le.trans inf_le_right

theorem le_T (h : Hyp83 V H T) : V ≤ T :=
  le_of_isCalH h.elemAbelian h.isCalH h.sylow

theorem pCoreOf_le_T (h : Hyp83 V H T) : pCoreOf 2 H ≤ T :=
  pCoreOf_le_of_isCalH h.isCalH h.sylow

theorem eSub_le_pCoreOf (h : Hyp83 V H T) : eSub V H T ≤ pCoreOf 2 H :=
  CFSG.LocalAnalysis.WeakClosure81.eSub_le_pCoreOf h.elemAbelian h.isCalH h.sylow

theorem eSub_le_H (h : Hyp83 V H T) : eSub V H T ≤ H :=
  h.eSub_le_pCoreOf.trans (CFSG.openPCoreOf_le 2 H)

theorem isElemAbelian_eSub (h : Hyp83 V H T) : IsElemAbelian 2 (eSub V H T) :=
  eSub_isElemAbelian h.elemAbelian h.isCalH h.sylow

theorem eSub_subgroupOf_normal (h : Hyp83 V H T) : ((eSub V H T).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.eSub_le_H).mpr
    (le_normalizer_conjClosure _ H)

theorem ne_bot (h : Hyp83 V H T) : V ≠ ⊥ := by
  intro hV
  have h2 := h.two_lt_card
  rw [hV, Subgroup.card_bot] at h2
  omega

theorem inf_eSub_ne_bot (h : Hyp83 V H T) : V ⊓ eSub V H T ≠ ⊥ :=
  ne_bot_of_le_ne_bot (inf_centralizer_ne_bot h.elemAbelian h.ne_bot h.isCalH h.sylow)
    (le_inf inf_le_left (le_conjClosure _ H))

theorem mem_omegaSet_self (h : Hyp83 V H T) : V ∈ omegaSet V H (eSub V H T) :=
  mem_omegaSet.mpr ⟨1, (conjSubgroup_one V).symm, by rw [inf_comm]; exact h.inf_eSub_ne_bot,
    h.not_le_pCoreOf⟩

theorem isMulCommutative_eSub (h : Hyp83 V H T) : IsMulCommutative (eSub V H T) :=
  h.isElemAbelian_eSub.1

end Hyp83

theorem mem_omegaOrb {V H T U : Subgroup G} :
    U ∈ omegaOrb V H T ↔ ∃ k ∈ kSub V H (eSub V H T), U = conjSubgroup V k :=
  Iff.rfl

theorem conjSubgroup_mem_omegaOrb {V H T : Subgroup G} {k : G}
    (hk : k ∈ kSub V H (eSub V H T)) : conjSubgroup V k ∈ omegaOrb V H T :=
  ⟨k, hk, rfl⟩

theorem self_mem_omegaOrb (V H T : Subgroup G) : V ∈ omegaOrb V H T :=
  ⟨1, (kSub V H (eSub V H T)).one_mem, (conjSubgroup_one V).symm⟩

theorem le_kGen {V H T U : Subgroup G} (hU : U ∈ omegaOrb V H T) : U ≤ kGen V H T :=
  le_iSup₂_of_le U hU le_rfl

theorem le_kGen_self (V H T : Subgroup G) : V ≤ kGen V H T :=
  le_kGen (self_mem_omegaOrb V H T)

theorem kGen_eq_kOrbSub (V H T : Subgroup G) :
    kGen V H T = kOrbSub V H (eSub V H T) V := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, rfl⟩ := hU
    exact le_iSup (fun m : kSub V H (eSub V H T) => conjSubgroup V (m : G)) ⟨k, hk⟩
  · exact iSup_le fun k => le_kGen (conjSubgroup_mem_omegaOrb k.2)

theorem conjSubgroup_kOrbSub {V H E U : Subgroup G} (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) {x : G}
    (hx : x ∈ H) :
    conjSubgroup (kOrbSub V H E U) x = kOrbSub V H E (conjSubgroup U x) := by
  have hKn : x ∈ Subgroup.normalizer (kSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal (kSub_le_of_forall_le hOmH)
      (kSub_subgroupOf_normal hEH hEnorm hOmH) hx
  have hmap : conjSubgroup (kOrbSub V H E U) x =
      ⨆ k : kSub V H E, conjSubgroup U ((k : G) * x) := by
    rw [kOrbSub]
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
    exact iSup_congr fun m => CFSG.Quasithin.conjSubgroup_conjSubgroup U (m : G) x
  rw [hmap, kOrbSub]
  refine le_antisymm (iSup_le fun k => ?_) (iSup_le fun k => ?_)
  · have hk' : x⁻¹ * (k : G) * x ∈ kSub V H E := (Subgroup.mem_normalizer_iff''.mp hKn _).mp k.2
    refine le_iSup_of_le (⟨x⁻¹ * (k : G) * x, hk'⟩ : kSub V H E) (le_of_eq ?_)
    change conjSubgroup U ((k : G) * x) = conjSubgroup (conjSubgroup U x) (x⁻¹ * (k : G) * x)
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup,
      show x * (x⁻¹ * (k : G) * x) = (k : G) * x by group]
  · have hk' : x * (k : G) * x⁻¹ ∈ kSub V H E := (Subgroup.mem_normalizer_iff.mp hKn _).mp k.2
    refine le_iSup_of_le (⟨x * (k : G) * x⁻¹, hk'⟩ : kSub V H E) (le_of_eq ?_)
    change conjSubgroup (conjSubgroup U x) (k : G) = conjSubgroup U (x * (k : G) * x⁻¹ * x)
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup,
      show x * (k : G) * x⁻¹ * x = x * (k : G) by group]

namespace Hyp83

variable {V H T : Subgroup G}

theorem kSub_normal (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    ((kSub V H (eSub V H T)).subgroupOf H).Normal :=
  kSub_subgroupOf_normal h.eSub_le_H h.eSub_subgroupOf_normal hOmH

theorem pCoreOf_kSub_le (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    pCoreOf 2 (kSub V H (eSub V H T)) ≤ pCoreOf 2 H :=
  pCoreOf_kSub_le_pCoreOf h.eSub_le_H h.eSub_subgroupOf_normal hOmH

theorem conjSubgroup_mem_omegaSet' (h : Hyp83 V H T) {W : Subgroup G}
    (hW : W ∈ omegaSet V H (eSub V H T)) {x : G} (hx : x ∈ H) :
    conjSubgroup W x ∈ omegaSet V H (eSub V H T) :=
  conjSubgroup_mem_omegaSet h.eSub_le_H h.eSub_subgroupOf_normal hW hx

theorem conjSubgroup_self_mem_omegaSet (h : Hyp83 V H T) {x : G} (hx : x ∈ H) :
    conjSubgroup V x ∈ omegaSet V H (eSub V H T) :=
  h.conjSubgroup_mem_omegaSet' h.mem_omegaSet_self hx

theorem kGen_le_kSub (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    kGen V H T ≤ kSub V H (eSub V H T) := by
  rw [kGen_eq_kOrbSub]
  exact kOrbSub_le_kSub h.eSub_le_H h.eSub_subgroupOf_normal hOmH h.mem_omegaSet_self

theorem kGen_le_H (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    kGen V H T ≤ H :=
  (h.kGen_le_kSub hOmH).trans (kSub_le_of_forall_le hOmH)

theorem kGen_normal (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    ((kGen V H T).subgroupOf (kSub V H (eSub V H T))).Normal := by
  rw [kGen_eq_kOrbSub]
  exact kOrbSub_subgroupOf_normal h.eSub_le_H h.eSub_subgroupOf_normal hOmH h.mem_omegaSet_self

theorem kSub_le_normalizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    kSub V H (eSub V H T) ≤ Subgroup.normalizer (kGen V H T : Set G) :=
  le_normalizer_of_subgroupOf_normal (h.kGen_le_kSub hOmH) (h.kGen_normal hOmH)

theorem conjSubgroup_kGen (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H)
    {x : G} (hx : x ∈ H) :
    conjSubgroup (kGen V H T) x = kOrbSub V H (eSub V H T) (conjSubgroup V x) := by
  rw [kGen_eq_kOrbSub]
  exact conjSubgroup_kOrbSub h.eSub_le_H h.eSub_subgroupOf_normal hOmH hx

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81
