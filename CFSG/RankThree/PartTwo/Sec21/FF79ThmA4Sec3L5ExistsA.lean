module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4In
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnCenter
import CFSG.RankThree.PartTwo.Sec21.FF79KOneTwo
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesT
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem jL4_of_odd
    (h : FF79Sec34In4 b J B A P D) : IsLnq 4 2 1 J := by
  have hle : J ≤ Subgroup.centralizer ({b} : Set G) := h.hyp.std.1
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm h.hyp.std.2.1.1
  have hZ := card_center_dvd_two_of_typeLn hq (Or.inl rfl) h.hyp.model
  have hZ1 : Subgroup.center ↥J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    have hord : orderOf z = 2 := by
      have h1 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥J)) ∣ 2 :=
        (orderOf_dvd_natCard _).trans hZ
      rw [Subgroup.orderOf_mk] at h1
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hz1
      · exact h2
    have hBle : B ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
      rw [← h.supB]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact (Subgroup.mem_centralizer_iff.mp (hle z.2) b (Set.mem_singleton b)).symm
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact (congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hz ⟨x, hx.2⟩)).symm
    have hzB : (z : G) ∈ CenS B :=
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        ((Subgroup.mem_centralizer_iff.mp (hBle hx) (z : G) (Set.mem_singleton _)).symm)
    have hdvd : orderOf (z : G) ∣ Nat.card (CenS B) := by
      have := orderOf_dvd_natCard (⟨(z : G), hzB⟩ : CenS B)
      rwa [Subgroup.orderOf_mk] at this
    rw [Subgroup.orderOf_coe, hord] at hdvd
    obtain ⟨m, hm⟩ := h.oddCB
    omega
  have hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 1 := h.hyp.model
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot) hm

theorem exists_a
    (h : FF79Sec34In4 b J B A P D) :
    ∃ a ∈ B ⊓ J, orderOf a = 3 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen a)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : IsLnq 4 2 1 J := jL4_of_odd h
  have hX : IsLnq 4 2 1 (⊤ : Subgroup ↥J) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv Subgroup.topEquiv.symm hJ
  obtain ⟨hSyl, -, ⟨α, -, hα, -, -, -, hLα, -⟩, -⟩ := ff79_1_2_holds ↥J 4 (Or.inl rfl) hX
  obtain ⟨P0⟩ : Nonempty (Sylow 3 ↥J) := inferInstance
  have hP0 : Nat.card ↥(P0 : Subgroup ↥J) = 3 ^ (Nat.card ↥J).factorization 3 :=
    P0.card_eq_multiplicity
  have hP0' : Nat.card ↥(P0 : Subgroup ↥J) = 3 ^ 2 := (hSyl P0).2
  have hfac : 3 ^ 2 = 3 ^ (Nat.card ↥J).factorization 3 := hP0'.symm.trans hP0
  have hR : IsSylowOf 3 (B ⊓ J) J :=
    L41.isSylowOf_of_card_p inf_le_right (by rw [h.elemB0.2]; exact hfac)
  have hα3 : orderOf (α : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hα
  have hQ : IsPGroup 3 (Subgroup.zpowers (α : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hα3]; norm_num)
  obtain ⟨k, hkJ, hk⟩ := L41.exists_conj_le_sylowOf_p hR
    ((Subgroup.zpowers_le).mpr α.2) hQ
  have ha : k * (α : G) * k⁻¹ ∈ B ⊓ J := hk _ (Subgroup.mem_zpowers _)
  refine ⟨k * (α : G) * k⁻¹, ha, ?_, ?_⟩
  · have := (MulAut.conj k).orderOf_eq (α : G)
    rw [MulAut.conj_apply] at this
    rw [this, hα3]
  · rw [isLnq_lay_cen_iff (MulAut.conj (⟨k, hkJ⟩⁻¹ : ↥J)) (k * (α : G) * k⁻¹) ha.2]
    have : (MulAut.conj (⟨k, hkJ⟩⁻¹ : ↥J)) ⟨k * (α : G) * k⁻¹, ha.2⟩ = α := by
      apply Subtype.ext
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact hLα

theorem sec35_exists_a
    (_hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D) :
    ∃ a ∈ B ⊓ J, orderOf a = 3 ∧ IsLnq 2 2 2 (Lay (J ⊓ Cen a)) :=
  exists_a h

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
