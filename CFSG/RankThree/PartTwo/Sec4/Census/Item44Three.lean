module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Gaps
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeFour
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem pCore_three_eq_top_of_forall {Y : Type*} [Group Y] [Finite Y]
    (hY : ∀ y : Y, ∃ k : ℕ, y ^ 3 ^ k = 1) : pCore 3 Y = ⊤ :=
  top_le_iff.mp (le_sSup ⟨inferInstance, fun y => by
    obtain ⟨k, hk⟩ := hY y
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩⟩)

theorem primeThreeLinear : PrimeThreeLinear := by
  intro Y _ _ hperf hC hrank hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hperf
  left
  have hQne : pCore 3 Y ≠ ⊥ := by
    intro hbot
    apply hQ
    refine pCore_three_eq_top_of_forall fun y => ⟨0, ?_⟩
    have hy : y ∈ Subgroup.centralizer (pCore 3 Y : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hbot] at hx
      rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one]
    have := hC hy
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, one_pow]
  obtain ⟨D, h⟩ := exists_criticalAt (by norm_num : (3 : ℕ) ≠ 2) hQne
  have hDp : IsPGroup 3 D := pCore_isPGroup.to_le h.le
  have hexpD : ∀ x : D, x ^ 3 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, h.exp x x.2, Subgroup.coe_one])
  let _ : Module (ZMod 3) (Additive (Abelianization D)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexpD)
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod 3) (Additive (Abelianization D)) := Module.Finite.of_finite
  set d := Module.finrank (ZMod 3) (Additive (Abelianization D)) with hd
  have hrankTop : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 := by
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  have hrankD : CFSG.pRank 3 D ≤ 3 := (pRank_le_pRank_top Nat.prime_three D).trans hrankTop
  have hcardV : Nat.card (D ⧸ commutator D) = 3 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive (Abelianization D))
    rw [Nat.card_zmod] at this
    exact this
  have hdrank : CFSG.pRank 3 (D ⧸ commutator D) = d :=
    (CFSG.RankThree.PartTwo.quotient_commutator_rank Nat.prime_three hexpD hcardV).2
  obtain ⟨hb1, hb2, hb3⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexpD
    h.commutator_le_center
  have hd4 : d ≤ 4 := hdrank ▸ hb3 hrankD
  have hker3 : ∀ y : Y, abEnd h y = 1 → ∃ k : ℕ, y ^ 3 ^ k = 1 := fun y hy =>
    exists_pow_eq_one_of_mem_frattiniKer h hC (mem_frattiniKer_of_abEnd_eq_one h hy)
  have hnontriv : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (b : Module.Basis ι (ZMod 3) (Additive (Abelianization D))), (abMat h b).range ≠ ⊥ := by
    intro ι _ _ b hbot
    apply hQ
    refine pCore_three_eq_top_of_forall fun y => hker3 y ?_
    rw [← abMat_eq_one_iff h b]
    have : abMat h b y ∈ (abMat h b).range := ⟨y, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  rcases (show d ≤ 2 ∨ d = 3 ∨ d = 4 by omega) with hd2 | hd3 | hd4'
  ·
    exfalso
    exact hnontriv (Module.finBasisOfFinrankEq (ZMod 3) _ hd.symm)
      (eq_bot_of_isPerfect_of_le_two hd2 (Group.IsPerfect.range _))
  ·
    set b := Module.finBasisOfFinrankEq (ZMod 3) (Additive (Abelianization D)) (hd.symm.trans hd3)
    set ρ := abMat h b with hρ
    have hrange : ρ.range = StatedSL 3 (ZMod 3) :=
      eq_statedSL_of_isPerfect (Group.IsPerfect.range _) (hnontriv b)
    set e := specialLinearGroupEquivStatedSL 3 (ZMod 3) with he
    set π : Y →* SL(3, ZMod 3) :=
      e.symm.toMonoidHom.comp ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp ρ.rangeRestrict)
      with hπ
    have hπsurj : Function.Surjective π :=
      e.symm.surjective.comp ((MulEquiv.subgroupCongr hrange).surjective.comp
        ρ.rangeRestrict_surjective)
    have hπker : ∀ y, π y = 1 ↔ ρ y = 1 := by
      intro y
      simp only [hπ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    have hker : π.ker = pCore 3 Y := by
      apply le_antisymm
      · refine le_sSup ⟨MonoidHom.normal_ker π, fun y => ?_⟩
        obtain ⟨k, hk⟩ := hker3 (y : Y) ((abMat_eq_one_iff h b _).mp
          ((hπker _).mp (MonoidHom.mem_ker.mp y.2)))
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩
      · have hN : ((pCore 3 Y).map π).Normal := Subgroup.Normal.map pCore_normal π hπsurj
        rcases LocalCores.quasisimple_normal_subgroups isQuasisimple_SL3_three hN with htop | hle
        · exfalso
          have hpg : IsPGroup 3 SL(3, ZMod 3) := fun g => by
            have hg : g ∈ (pCore 3 Y).map π := by rw [htop]; exact Subgroup.mem_top g
            obtain ⟨k, hk⟩ := (pCore_isPGroup.map π : IsPGroup 3 ((pCore 3 Y).map π)) ⟨g, hg⟩
            exact ⟨k, congrArg Subtype.val hk⟩
          have := hpg.isNilpotent
          have : Group.IsPerfect SL(3, ZMod 3) := isQuasisimple_SL3_three.1
          have : Nontrivial SL(3, ZMod 3) :=
            Finite.one_lt_card_iff_nontrivial.mp (by rw [card_SL3_three]; norm_num)
          exact Group.IsPerfect.not_isSolvable SL(3, ZMod 3) inferInstance
        · rw [center_SL3_three, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
          exact hle
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπsurj)⟩
  ·
    exfalso
    have hrank3 : CFSG.pRank 3 D = 3 := by
      rcases (show CFSG.pRank 3 D ≤ 2 ∨ CFSG.pRank 3 D = 3 by omega) with h2 | h3
      · have := hb1 h2
        omega
      · exact h3
    obtain ⟨i, hi, -⟩ := hb2 hrank3
    fin_cases i
    · have := hi.2.2
      omega
    · obtain ⟨hD5, hZ3, hZ, -⟩ := hi
      exact hQ (eq_top_of_extraspecial hperf h hC hrankTop hZ.symm hZ3 hD5)
    · have := hi.2.2.2
      omega

end CFSG.RankThree.PartTwo.Sec4.Census
