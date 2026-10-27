module

public import CFSG.GH74.GLS.SP.GlueBN
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Cov
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctDefs

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sup_octH_Ug : octH K a ⊔ Ug K a = (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) := by
  refine le_antisymm (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
  · exact Subgroup.mem_subgroupOf.2 (reeFixedTorus_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hx))
  · exact Subgroup.mem_subgroupOf.2
      (reeFixedPosUnipotent_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hx))
  · have hx' : x.1 ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := Subgroup.mem_subgroupOf.1 hx
    rw [reeFixedBorel_eq_mul] at hx'
    obtain ⟨h, hh, u, hu, hxu⟩ := hx'
    have hhΓ : h ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hh).2
    have huΓ : u ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hu).2
    have e : x = ⟨h, hhΓ⟩ * ⟨u, huΓ⟩ := Subtype.ext hxu.symm
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hh))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hu))

theorem octGen (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a)) :
    (octH K a ⊔ Ug K a) ⊔ hR.N = ⊤ := by
  have hB : F4.reeFixedBorel K a ≤
      (((octH K a ⊔ Ug K a) ⊔ hR.N).map (F4.reeGamma K a).subtype) := by
    intro b hb
    refine ⟨⟨b, reeFixedBorel_le_reeGamma hb⟩, Subgroup.mem_sup_left ?_, rfl⟩
    rw [sup_octH_Ug]
    exact Subgroup.mem_subgroupOf.2 hb
  have hC : Subgroup.closure (Set.range fun j => canonicalRep (coxeterSystem F4.tag) K
      (F4.fixedOrbitElement j)) ≤
      (((octH K a ⊔ Ug K a) ⊔ hR.N).map (F4.reeGamma K a).subtype) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact ⟨octR2 K a, Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr (Or.inr rfl))),
        rfl⟩
    · exact ⟨octR1 K a, Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr (Or.inl rfl))),
        rfl⟩
  have hΓ : F4.reeGamma K a ≤
      (((octH K a ⊔ Ug K a) ⊔ hR.N).map (F4.reeGamma K a).subtype) :=
    (reeGamma_eq_sup_closure (t := F4) (K := K) (a := a)).le.trans (sup_le hB hC)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hΓ x.2
  have e : y = x := Subtype.ext hyx
  rwa [e] at hy

theorem isSylowTwoOf_Ug (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Ug K a) ⊤ :=
  (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK).1

@[expose] noncomputable def octSystemOf
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)] : RankTwoSystem (Gm K a) 8 :=
  (hR.toPre (octGen hR)).toSystemOfSimple

section System

variable (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
  [IsSimpleGroup (Gm K a)]

theorem octSystemOf_root : (octSystemOf hR).root = octRoot K a := rfl

theorem octSystemOf_U : (octSystemOf hR).U = Ug K a := rfl

theorem octSystemOf_B : (octSystemOf hR).B = octH K a ⊔ Ug K a := rfl

theorem octSystemOf_cartan : (octSystemOf hR).B ⊓ (octSystemOf hR).N = octH K a :=
  hR.B_inf_N

end System

end CFSG.Quasithin.H13.F431.TwoF4
