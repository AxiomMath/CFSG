module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3EMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinCoverMain
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Order

theorem two_dvd_card_of_isPSL_three_two_two {Q : Type} [Group Q] (hQ : IsPSL 3 2 2 Q) :
    2 ∣ Nat.card Q := by
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hQ
  have h4 : Nat.card F = 4 := by rw [hF]; norm_num
  have hcard : Nat.card Q = 20160 := by
    rw [Nat.card_congr (e.trans (Fin257.statedSLEquiv F)).toEquiv]
    exact LocalAnalysis.ComponentInitial.GL3TwoFixedModel.card_projectiveSL_three_four h4
  rw [hcard]
  norm_num

end Order

variable {G : Type} [Group G]

theorem not_two_dvd_card_pCore_quotient_of_sylow_central {L P : Subgroup G}
    (hSyl : IsSylowTwoOf P L) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hPc : P ≤ Subgroup.centralizer (L : Set G)) :
    ¬ 2 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hcore : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hZ⟩
  have hle : P.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    refine hcore ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPc hx) y y.2)
  have hdvd : (CFSG.pCore 2 ↥L).index ∣ (P.subgroupOf L).index := Subgroup.index_dvd_of_le hle
  exact fun h2 => hSyl.2.2 (h2.trans hdvd)

variable [Finite G]

theorem mem_normalizer_of_centralizes_sylow {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hco : IsComponentOf L X) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hty : IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) {z : G} (hzS : z ∈ S)
    (hzc : ∀ s ∈ S, z * s = s * z) : z ∈ Subgroup.normalizer (L : Set G) := by
  by_contra htn
  have hcomm : ⁅L, conjByElt z L⁆ = ⊥ :=
    L31521E.commutator_conjByElt_eq_bot1521 hco (hStd.sylow.1 hzS) htn
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  refine not_two_dvd_card_pCore_quotient_of_sylow_central hStd.sylowL hZ ?_
    (two_dvd_card_of_isPSL_three_two_two hty)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxz : x ∈ conjByElt z L := by
    rw [mem_conjByElt]
    have h1 : z⁻¹ * x * z = x := by
      have h := hzc x hx.1
      calc z⁻¹ * x * z = z⁻¹ * (x * z) := by group
        _ = z⁻¹ * (z * x) := by rw [h]
        _ = x := by group
    rw [h1]
    exact hx.2
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) x hxz).symm

theorem l3cover_nonElem_false {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hco : IsComponentOf L X) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hty : IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L))
    (hne : ¬ ∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1) (hz : CentralMoving1521 S L) : False := by
  obtain ⟨z, hzS, hzc, l, hl, hzl⟩ := hz
  have hN := mem_normalizer_of_centralizes_sylow hStd hco hZ hty hzS hzc
  have hq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_open1521 hco.2.2
  have hM : IsRank2Model257 L 2 := ⟨le_rfl, Or.inl hty⟩
  have hE : IsRankTwoEvenType L := Or.inr (Or.inr (Or.inr hty))
  have hne' : ¬ IsElemAbelian 2 (centerOf L) := by
    intro hEA
    refine hne fun w hw => ?_
    have hw' : (w : G) ∈ centerOf L := by
      refine ⟨w.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hw) ⟨y, hy⟩)
    exact Subtype.ext (hEA.2 w hw')
  have hcent := Fin257.cover257a G L (S ⊓ L) 2 hq hM hE hStd.sylowL hne' z hN
    (fun y hy => hzc y hy.1)
  exact hzl (Subgroup.mem_centralizer_iff.1 hcent l hl).symm

end CFSG.Quasithin
