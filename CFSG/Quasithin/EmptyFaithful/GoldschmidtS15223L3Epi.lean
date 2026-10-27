module

public import CFSG.Quasithin.EmptyFaithful.S151TCOdd
public import CFSG.Quasithin.EmptyFaithful.S151S9P2A
public import CFSG.Quasithin.H13.GoldschmidtC137L32Blk
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
public import CFSG.Quasithin.H13.GoldschmidtC137L32Red

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open hiding StatedSL
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.U3.GC137

variable {G : Type} [Group G]

section Epi

variable [Finite G]

theorem exists_epi_of_autOn_sl3 {X V : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hker : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G))
    (hnt : ¬ X ≤ Subgroup.centralizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (e : ↥(autOn X V) ≃* ↥(StatedSL 3 F)) :
    ∃ α : ↥X →* ↥(StatedSL 3 (ZMod 2)), IsModO2Surj X α := by
  classical
  have hperf : Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := hq.1
  have hFz : Fintype.card F = Fintype.card (ZMod 2) := by rw [hF, ZMod.card]
  let σ : ↥(StatedSL 3 F) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    statedSLMap (FiniteField.ringEquivOfCardEq hFz)
  let ρ := S153D.autOnQuot hXN hker
  let π : (↥X ⧸ CFSG.pCore 2 ↥X) →* ↥(StatedSL 3 (ZMod 2)) :=
    σ.toMonoidHom.comp (e.toMonoidHom.comp ρ)
  have hπs : Function.Surjective π :=
    σ.surjective.comp (e.surjective.comp (S153D.autOnQuot_surjective hXN hker))
  have hkerπ : π.ker = ρ.ker := by
    ext x
    simp [π, MonoidHom.mem_ker]
  have hC : π.ker ≤ Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [hkerπ]
    exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
      (S153D.exists_autOnQuot_ne_one hXN hker hnt)
  have hodd : Odd (Nat.card π.ker) :=
    Odd.of_dvd_nat (S151TB.Typ.odd_card_center_quotient_pCore (K := ↥X))
      (Subgroup.card_dvd_of_le hC)
  have hbot : π.ker = ⊥ := S151TC.ker_eq_bot_of_statedSL_three_two π hπs hC hodd
  refine ⟨π.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X)), hπs.comp (QuotientGroup.mk'_surjective _),
    ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hbot, Subgroup.mem_bot,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem genByOrderThree_of_epi {Y : Subgroup G} (hperf : ⁅Y, Y⁆ = Y)
    {α : ↥Y →* ↥(StatedSL 3 (ZMod 2))} (hα : IsModO2Surj Y α) : GenByOrderThree Y := by
  have hY : Group.IsPerfect ↥Y := isPerfect_of_commutator_eq_gc hperf
  have hsimple : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := HSRuLoc.Lift.isSimpleGroup_statedSL3
  have h3 : 3 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_surjective hα.1
    rw [HSRuLoc.Lift.card_statedSL3] at this
    exact (show 3 ∣ 168 by norm_num).trans this
  refine genByOrderThree_of_epi_simple ?_ hα.1 hα.2 h3
  intro N _ h2
  have hQp : Group.IsPerfect (↥Y ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hnil : Group.IsNilpotent (↥Y ⧸ N) := h2.isNilpotent
  have hsub : Subsingleton (↥Y ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥Y ⧸ N) hnil
  exact eq_top_iff.mpr fun y _ => (QuotientGroup.eq_one_iff y).mp (Subsingleton.elim _ _)

theorem not_isSolvable_of_epi {Y : Subgroup G} (hperf : ⁅Y, Y⁆ = Y)
    {α : ↥Y →* ↥(StatedSL 3 (ZMod 2))} (hα : IsModO2Surj Y α) : ¬ Group.IsSolvable ↥Y := by
  have hY : Group.IsPerfect ↥Y := isPerfect_of_commutator_eq_gc hperf
  have hnt : Nontrivial ↥Y := by
    have h168 : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 := HSRuLoc.Lift.card_statedSL3
    have hle := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_surjective hα.1)
    rw [h168] at hle
    have : 1 < Nat.card ↥Y := by omega
    exact Finite.one_lt_card_iff_nontrivial.mp this
  exact hY.not_isSolvable

end Epi

end CFSG.Quasithin.S15223
