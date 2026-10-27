module

public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

theorem normalCore_subgroupOf_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (H : Subgroup G) :
    ((relPPrimeCore p H).subgroupOf H).normalCore = CFSG.pPrimeCore p ↥H := by
  have h : (relPPrimeCore p H).subgroupOf H = CFSG.pPrimeCore p ↥H := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h]
  exact Subgroup.normalCore_eq_self _

theorem pPrimeCore_quotient_eq_bot_of_eq {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N : Subgroup X} [N.Normal] (h : N = CFSG.pPrimeCore p X) : CFSG.pPrimeCore p (X ⧸ N) = ⊥ := by
  subst h
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

theorem pPrimeCore_three_quot_relPPrimeCore_eq_bot {G : Type} [Group G] [Finite G]
    (H : Subgroup G) :
    CFSG.pPrimeCore 3 (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pPrimeCore_quotient_eq_bot_of_eq (normalCore_subgroupOf_relPPrimeCore Nat.prime_three H)

theorem pRank_three_quot_relPPrimeCore_le {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)) ≤
      CFSG.Open.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := normalCore_subgroupOf_relPPrimeCore Nat.prime_three H
  have hcop : ¬ 3 ∣ Nat.card ((relPPrimeCore 3 H).subgroupOf H).normalCore := by
    rw [hN]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  rw [CFSG.RankThree.PartTwo.Sec20.Res5.pRank_top_quotient_eq _ hcop,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]

theorem isSolvable_of_isCyclic_centralizer_le {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    [IsCyclic Q] (hQ : centralizer (Q : Set X) ≤ Q) : Group.IsSolvable X := by
  have hA : Group.IsSolvable (MulAut Q) := Group.isSolvable_of_comm fun σ τ =>
    (IsCyclic.mulAutMulEquiv Q).injective (by rw [map_mul, map_mul, mul_comm])
  have hC : Group.IsSolvable (centralizer (Q : Set X)) := Group.isSolvable_of_comm fun a b => by
    have h := (IsCyclic.isMulCommutative (α := Q)).is_comm.comm ⟨a, hQ a.2⟩ ⟨b, hQ b.2⟩
    have h' : ((⟨a, hQ a.2⟩ * ⟨b, hQ b.2⟩ : Q) : X) = ((⟨b, hQ b.2⟩ * ⟨a, hQ a.2⟩ : Q) : X) :=
      congrArg Subtype.val h
    exact Subtype.ext h'
  refine Group.isSolvable_of_ker_le_range (centralizer (Q : Set X)).subtype
    (MulAut.conjNormal (H := Q)) ?_
  intro x hx
  rw [Subgroup.range_subtype, Subgroup.mem_centralizer_iff]
  intro q hq
  have h := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : X)) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc q * x = x * q * x⁻¹ * x := by rw [h]
    _ = x * q := by group

section Rank

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_isComponent_of_not_isSolvable (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) (hns : ¬ Group.IsSolvable Y) :
    ∃ E : Subgroup Y, CFSG.IsComponent E := by
  by_contra hex
  have hL : CFSG.layer Y = ⊥ :=
    CFSG.LocalCores.layer_eq_bot_of_forall fun E hE => hex ⟨E, hE⟩
  have hp : IsPGroup 3 (CFSG.generalizedFitting Y) := by
    rw [CFSG.generalizedFitting.eq_sup, hL, sup_bot_eq]
    exact CFSG.pCore_isPGroup.to_le (CFSG.RankThree.PartTwo.Sec20.Res5.fittingSubgroup_le_pCore hO)
  have : IsCyclic (CFSG.generalizedFitting Y) :=
    CFSG.RankThree.PartTwo.Sec20.Res5.isCyclic_of_pRank_le_one hr hp
  have : (CFSG.generalizedFitting Y).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  exact hns (isSolvable_of_isCyclic_centralizer_le _ (CFSG.centralizer_generalizedFitting_le Y))

theorem pCore_three_eq_bot_of_isComponent (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) {E : Subgroup Y} (hE : CFSG.IsComponent E) :
    CFSG.pCore 3 Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := CFSG.pCore 3 Y with hQ
  have hQp : IsPGroup 3 Q := CFSG.pCore_isPGroup
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have hEQ : ⁅E, Q⁆ = ⊥ := (CFSG.LocalCores.component_solvable_centralizer (R := Q)
    inferInstance (CFSG.pCore_normal (p := 3) (G := Y)).isSubnormal).1 E hE
  have hcomm : ∀ a ∈ E, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [hEQ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  rcases hQp.card_eq_or_dvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  exfalso
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 3 h3
  rw [← Subgroup.orderOf_coe] at hx
  obtain ⟨y, hyE, hy⟩ := CFSG.RankThree.PartTwo.Sec20.Res5.exists_orderOf_eq_three hO hE
  have hxy : (x : Y) ∈ Subgroup.zpowers y :=
    CFSG.RankThree.PartTwo.Sec20.Res5.mem_zpowers_of_commute hr hy hx (hcomm y hyE x x.2)
  have hxE : (x : Y) ∈ E := (Subgroup.zpowers_le.mpr hyE) hxy
  have hcen : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 x x.2)
  rw [CFSG.RankThree.PartTwo.Sec20.Res5.center_eq_bot_of_isComponent hO hr hE,
    Subgroup.mem_bot] at hcen
  have hx1 : (x : Y) = 1 := congrArg Subtype.val hcen
  rw [hx1, orderOf_one] at hx
  omega

theorem exists_generalizedFitting_eq_isComponent (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) (hns : ¬ Group.IsSolvable Y) :
    ∃ E : Subgroup Y, CFSG.IsComponent E ∧ CFSG.generalizedFitting Y = E ∧
      IsSimpleGroup ↥E ∧ (∃ a b : ↥E, a * b ≠ b * a) ∧ centralizer (E : Set Y) = ⊥ := by
  obtain ⟨E, hE⟩ := exists_isComponent_of_not_isSolvable hO hr hns
  have hF : CFSG.fittingSubgroup Y = ⊥ := le_bot_iff.mp
    ((CFSG.RankThree.PartTwo.Sec20.Res5.fittingSubgroup_le_pCore hO).trans
      (pCore_three_eq_bot_of_isComponent hO hr hE).le)
  have hL : CFSG.layer Y = E := le_antisymm
    (sSup_le fun E' hE' => (CFSG.RankThree.PartTwo.Sec20.Res5.eq_of_isComponent hO hr hE' hE).le)
    (CFSG.LocalCores.component_le_layer hE)
  have hFE : CFSG.generalizedFitting Y = E := by
    rw [CFSG.generalizedFitting.eq_sup, hF, hL, bot_sup_eq]
  have hcen := CFSG.RankThree.PartTwo.Sec20.Res5.center_eq_bot_of_isComponent hO hr hE
  obtain ⟨-, hsimpQ, a, b, hab⟩ := hE.1
  have e1 : ↥E ≃* ↥E ⧸ Subgroup.center ↥E :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  refine ⟨E, hE, hFE, e1.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  · rw [eq_bot_iff]
    intro c hc
    have hcE : c ∈ E := by
      have h := CFSG.centralizer_generalizedFitting_le Y
      rw [hFE] at h
      exact h hc
    have hcZ : (⟨c, hcE⟩ : ↥E) ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) g g.2)
    rw [hcen, Subgroup.mem_bot] at hcZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcZ

end Rank

theorem genFittingFStar_simple_of_pRank_three_le_one {Y : Type} [Group Y] [Finite Y]
    (hO : CFSG.pPrimeCore 3 Y = ⊥) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    (hns : ¬ Group.IsSolvable Y) :
    IsSimpleGroup ↥(CFSG.Open.genFittingFStar Y) ∧
      (∃ a b : ↥(CFSG.Open.genFittingFStar Y), a * b ≠ b * a) ∧
      Subgroup.centralizer (CFSG.Open.genFittingFStar Y : Set Y) = ⊥ := by
  obtain ⟨E, -, hFE, hsimp, hnab, hcen⟩ := exists_generalizedFitting_eq_isComponent hO hr hns
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hFE]
  exact ⟨hsimp, hnab, hcen⟩

end CFSG.LocalAnalysis.WeakClosure81

end
