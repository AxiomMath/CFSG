module

import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Final
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1118StepsProof

section Group

variable {G : Type*} [Group G]

theorem le_of_inf_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {A V E : Subgroup G}
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hp : IsPGroup p (A ⊔ V : Subgroup G))
    (hE : E ≤ A) (hVA : V ⊓ Subgroup.normalizer (A : Set G) ≤ E) : V ≤ E := by
  suffices hVA' : V ≤ A by
    intro v hv
    exact hVA ⟨hv, Subgroup.le_normalizer (hVA' hv)⟩
  by_contra hne
  have : Group.IsNilpotent (A ⊔ V : Subgroup G) := hp.isNilpotent
  set A' := A.subgroupOf (A ⊔ V) with hA'
  have hlt : A' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    intro v hv
    have hmem : (⟨v, Subgroup.mem_sup_right hv⟩ : (A ⊔ V : Subgroup G)) ∈ A' :=
      htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨u, hu, hnu⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent A' hlt)
  have huA : (u : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hz' : (⟨z, Subgroup.mem_sup_left hz⟩ : (A ⊔ V : Subgroup G)) ∈ A' :=
      Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hu _).mp hz')
  have huA' : (u : G) ∉ A := fun hA => hnu (Subgroup.mem_subgroupOf.mpr hA)
  have hu' : (u : G) ∈ ((A ⊔ V : Subgroup G) : Set G) := u.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAV] at hu'
  obtain ⟨a', ha', v, hv, hav⟩ := Set.mem_mul.mp hu'
  have hvN : v ∈ Subgroup.normalizer (A : Set G) := by
    have e : v = a'⁻¹ * u := by rw [← hav]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (A.inv_mem ha')) huA
  have hvA : v ∈ A := hE (hVA ⟨hv, hvN⟩)
  exact huA' (by rw [← hav]; exact A.mul_mem ha' hvA)

end Group

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g e : G} {Y' : Subgroup G}

theorem inf_thetaQuotCentralizer_le (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (heA : e ∈ A) (hecd : e ∉ Subgroup.closure {c, d}) (hY' : Y' ∈ thetaComponentsAt 3 e)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q)
    (hW : Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.zpowers e) :
    Q ⊓ Sec4.thetaQuotCentralizer Y' ≤ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have hAQ : A ≤ Q := by
    intro z hz
    refine hTQ ⟨Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hz), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨z, hz⟩ ⟨e, heA⟩))
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hAV : A ≤ Subgroup.normalizer
      ((Q ⊓ Sec4.thetaQuotCentralizer Y' : Subgroup G) : Set G) := fun z hz =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hAQ hz),
      Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y' (hAY' hz)⟩
  have hp : IsPGroup 3 (A ⊔ (Q ⊓ Sec4.thetaQuotCentralizer Y') : Subgroup G) :=
    hQ.isPGroup.to_le (sup_le hAQ inf_le_left)
  have hE : Subgroup.zpowers e ≤ A := Subgroup.zpowers_le.mpr heA
  exact le_of_inf_normalizer_le hAV hp hE hW

end Item1118StepsProof

end CFSG.RankThree.PartTwo.Sec11
