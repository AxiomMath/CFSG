module

public import CFSG.RankThree.PartTwo.Sec15.Item15Steps
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem isEmpty_mulEquiv_M12_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (h : Sec4.IsoLThreePi X p e) : IsEmpty (X ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  refine ⟨fun φ => KFacts.KS14.not_isoLThreePi_M12 p e ?_⟩
  rcases h with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · exact Or.inl ⟨h1, ⟨φ.symm.trans f⟩⟩
  · exact Or.inr ⟨h2, ⟨φ.symm.trans f⟩⟩

omit [Finite G] in
theorem concl1514_of_concl1515_of_le {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L Y : Subgroup G} (h15 : Concl1515 A c L Y) (hLY : L ≤ Y) : Concl1514 A LB c L Y := by
  obtain ⟨p, e, hp, -, hiso, hprod, hYL, -, hΩ⟩ := h15
  refine Or.inl ⟨by rwa [inf_comm], ?_, hΩ, hprod, isEmpty_mulEquiv_M12_of_isoLThreePi hiso⟩
  rw [inf_eq_left.mpr hLY]
  exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm

end Proof1514

open Proof1514

omit [Finite G] in
theorem Ctx1514.not_le {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L Y : Subgroup G} (hctx : Ctx1514 A LB c L Y) : ¬ L ≤ Y :=
  fun hLY => hctx.not_concl (concl1514_of_concl1515_of_le hctx.concl1515 hLY)

namespace Proof1514

theorem three_dvd_card_inf_of_meetsY4 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {L Y : Subgroup G} (hm : MeetsY4 A LB L Y) : 3 ∣ Nat.card ↥(L ⊓ Y) := by
  obtain ⟨X, hX, hXLY⟩ := hm
  have hO2 : CFSG.pCore 2 ↥X ≠ ⊤ := by
    intro h2
    obtain ⟨-, -, -, hq⟩ := hX
    obtain ⟨-, hs, -⟩ := hq
    have hnt := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : (↥X ⧸ CFSG.pCore 2 ↥X) ⧸
      Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    rw [(QuotientGroup.eq_one_iff y).mpr (h2 ▸ Subgroup.mem_top y)]
    rfl
  have h3X : 3 ∣ Nat.card X := (three_dvd_card_quotient_of_eq_oPrimeResidualOf hX.2.1
    (CFSG.pCore 2 ↥X) hO2).trans (Subgroup.card_quotient_dvd_card _)
  exact h3X.trans (Subgroup.card_dvd_of_le hXLY)

theorem isSimpleGroup_of_isoLThreePi {K : Subgroup G} {a : G} (hK : K ∈ thetaComponentsAt 3 a)
    {p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (K ⧸ aschbacherSolvableCore 3 K) p e) :
    IsSimpleGroup (K ⧸ aschbacherSolvableCore 3 K) := by
  have hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ := by
    rcases hiso with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq3).2
    · by_cases hq2 : 2 < p ^ e
      · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq3 hq2).2
      ·
        exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        have := isSolvable_projSU_two
        have hsol : Group.IsSolvable (K ⧸ aschbacherSolvableCore 3 K) :=
          Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
        have : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) := by
          obtain ⟨x, y, hxy⟩ := hq.2.2
          by_contra hn
          rw [not_nontrivial_iff_subsingleton] at hn
          apply hxy
          have : Subsingleton ((K ⧸ aschbacherSolvableCore 3 K) ⧸
              Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) :=
            QuotientGroup.mk_surjective.subsingleton
          exact Subsingleton.elim _ _
        have := hq.1
        exact Group.IsPerfect.not_isSolvable _ hsol
  obtain ⟨-, hs, -⟩ := hq
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end Proof1514

theorem Ctx1514.not_le_normalizer {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L Y : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) (hctx : Ctx1514 A LB c L Y) :
    ¬ L ≤ Subgroup.normalizer (Y : Set G) := by
  intro hLN
  obtain ⟨p, e, hp, he, hiso, -⟩ := hctx.concl1515
  exact hctx.not_le (le_of_le_normalizer_of_theta (Sec6.isPerfect_of_mem_thetaComponentsAt hL)
    (isSimpleGroup_of_isoLThreePi hL he hiso) hLN (three_dvd_card_inf_of_meetsY4 hctx.meets))

end CFSG.RankThree.PartTwo.Sec15
