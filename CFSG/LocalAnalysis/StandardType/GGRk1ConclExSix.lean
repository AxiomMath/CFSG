module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.LocalAnalysis.StandardType.GGMemberE7TwoRankOne
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem exists_not_comm_ggOTwoPrime_of_card_six {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (h6 : Nat.card (ggOTwoPrime Y) = 6) : ∃ x y : ↥(ggOTwoPrime Y), x * y ≠ y * x := by
  by_contra hcomm
  push Not at hcomm
  have hsq : ∀ g ∈ ggOTwoPrime Y, g ^ 2 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      have hyS : y ∈ ggOTwoPrime Y := Subgroup.subset_closure hy
      obtain ⟨-, k, hk⟩ := hy
      have h6y : orderOf y ∣ 6 := h6 ▸ Subgroup.orderOf_dvd_natCard (ggOTwoPrime Y) hyS
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
      rw [hj] at h6y
      have hj1 : j ≤ 1 := by
        by_contra hj2
        have h4 : 2 ^ 2 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
        exact absurd (h4.trans h6y) (by decide)
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [hj]
      exact Nat.pow_dvd_pow 2 hj1
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [(Commute.mul_pow hab 2), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ggOTwoPrime Y)) 3 (by rw [h6]; norm_num)
  have h2 : g ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hsq g g.2)
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at this
  exact absurd this (by decide)

section Concl


theorem ggRk1ConclEx_of_card_six {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {r : MulAut ↥Bs} (hp3 : p = 3) (hnsX : ¬ GGSplitLie p X) (hrA : r ∈ ggAutomizer X Bs)
    (hr2 : r ^ 2 = 1) (h6 : Nat.card (ggRankOneIn X Bs r) = 6)
    (hlab : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (hn1 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n = 1) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨e₁⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6
    (exists_not_comm_ggOTwoPrime_of_card_six h6)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₂⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin.nonempty_mulEquiv_perm_three_of_card_two
      (K := ZMod 2) (Nat.card_zmod 2)
  let e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* ↥(ggRankOneIn X Bs r) := e₂.trans e₁.symm
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine ⟨ZMod 2, inferInstance, inferInstance, (ggRankOneIn X Bs r).subtype.comp e.toMonoidHom,
    inferInstance, (Subgroup.subtype_injective _).comp e.injective, ?_, ?_, fun h => absurd h hnsX,
    fun _ => by rw [hp3, h2], fun lab hΛ hhas => by rw [hn1 lab hΛ hhas, h2, pow_one], ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · obtain ⟨g, hgS, hgN, hg⟩ := mem_ggAutomizer_iff.mp (mem_ggAutomizer_ggRankOneIn hrA hr2)
    exact ⟨g, hgS, hgN, hg⟩
  · obtain ⟨lab, hΛ, hhas⟩ := hlab
    exact ⟨lab, hΛ, hhas, by rw [hn1 lab hΛ hhas, h2, pow_one]⟩

end Concl

section E7Two


theorem ggRk1ConclEx_of_e7Two_marking (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → GGRk1ConclEx p Bs X r := by
  intro r hrA hrR
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨htag, -⟩, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  refine ggRk1ConclEx_of_card_six (exists_e7Two_frame_of_member_marking hcfg hX hmark).1 hnsX hrA hrR.1
    (card_ggRankOneIn_of_e7Two_member_marking hcfg hX hmark hrA hrR) ⟨lab, hΛ, hhas⟩ fun lab' hΛ' hhas' => ?_
  have := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') (by rw [htag]; decide)
    (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
  omega

end E7Two

end CFSG.StandardType

end
