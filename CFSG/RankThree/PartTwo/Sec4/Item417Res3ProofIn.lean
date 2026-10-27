module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofInTools
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSpor
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestJ3
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestG2
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)


namespace Res417Three

theorem pow_eq_one_of_dvd_zmod {a N : ℕ} (h : a ∣ N) (x : Multiplicative (ZMod a)) :
    x ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff _ _).mpr h, zero_mul]

theorem pow_twelve_multiplier_U43 (x : Multiplier.generic .PSU 4 3 1 ×
    Multiplier.exceptional .PSU 4 3 1) : x ^ 12 = 1 := by
  obtain ⟨⟨a, b⟩, ⟨d, e⟩⟩ := x
  exact Prod.ext (Prod.ext (pow_eq_one_of_dvd_zmod (by decide) a)
    (pow_eq_one_of_dvd_zmod (by decide) b)) (Prod.ext (pow_eq_one_of_dvd_zmod (by decide) d)
    (pow_eq_one_of_dvd_zmod (by decide) e))

theorem pow_twelve_eq_one_of_center_U43 (hGA : GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] (hQ : IsQuasisimple Q) (φ : Q ⧸ Subgroup.center Q ≃* projSU 4 3 1) {z : Q}
    (hz : z ∈ Subgroup.center Q) : z ^ 12 = 1 := by
  have : Group.IsPerfect Q := hQ.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hm := KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSU hadm)
  obtain ⟨eT⟩ := (hGA _ .PSU 4 3 1 hm).2
  set e₀ := MulEquiv.refl (Q ⧸ Subgroup.center Q)
  have hq := PerfectCover.centralQuotientMap_surjective e₀
  have hk := PerfectCover.centralQuotientMap_ker e₀
  set ψ := (PerfectCover.hopfMultiplierToKer (PerfectCover.centralQuotientMap e₀) hq hk.le).comp
    (PerfectCover.hopfMultiplierEquivGriess (Q ⧸ Subgroup.center Q)).toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (PerfectCover.hopfMultiplierToKer_surjective _ hq hk.le).comp
      (PerfectCover.hopfMultiplierEquivGriess _).surjective
  obtain ⟨x, hx⟩ := hψs ⟨z, hk.symm ▸ hz⟩
  have hx12 : x ^ 12 = 1 := by
    apply eT.injective
    rw [map_pow, map_one]
    exact pow_twelve_multiplier_U43 _
  have h1 : ψ (x ^ 12) = 1 := by rw [hx12, map_one]
  rw [map_pow, hx] at h1
  simpa using congrArg Subtype.val h1

end Res417Three

open Res417Three

section Certs


@[expose] def Item417InG2Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m → Nat.card (Subgroup.center L) = 3 →
      ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 3 1 → False

@[expose] def Item417InU43McLRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m → Nat.card (Subgroup.center L) = 3 →
      (Nonempty (L ⧸ Subgroup.center L ≃* projSU 4 3 1) ∨
        Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.McL)) → False

@[expose] def Item417InJ3Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m → Nat.card (Subgroup.center L) = 3 →
      Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) →
      m = 4 ∧ IsExtOf ↥(autIn L A) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))

@[expose] def Item417InONRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m → Nat.card (Subgroup.center L) = 3 →
      Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.ON) → m = 3

theorem item417InG2_of (hGA : GriessMultipliersAllModels) (hR : Item417InG2Rest) :
    Item417InG2 := by
  intro G _ _ L A E c m hconf hM
  exact (hR G L A E c m hconf (hconf.card_center_eq_three
    (Census.CoverCenterThreeRest.card_center_dvd_three_of_G2 hGA hconf.2.2.1.1 hM)) hM).elim

theorem item417InU43McL_of
    (hGA : GriessMultipliersAllModels) (hR : Item417InU43McLRest) : Item417InU43McL := by
  intro G _ _ L A E c m hconf hX
  exfalso
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  refine hR G L A E c m hconf ?_ hX
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨e⟩⟩
  · refine hconf.card_center_eq_three (hconf.card_center_dvd_three_of_exponent fun z hz => ?_)
    have h12 := pow_twelve_eq_one_of_center_U43 hGA hLq φ hz
    exact eq_one_of_mem_center_of_pow_two hconf.2.1 hconf.2.2.1.2 (Subgroup.pow_mem _ hz 3)
      (k := 2) (by rw [← pow_mul]; exact h12)
  · have hXc : Nonempty (NativeSporadic.McL ≃* NativeSporadic.Carrier .McL) :=
      ⟨MulEquiv.refl _⟩
    obtain ⟨eX⟩ := hXc
    have hZ3 := hconf.isPGroup_center fun p hp hp3 hpZ => by
      obtain ⟨hpair, hnot⟩ := CFSG.RankThree.PartOne.Mult.sporadic_residual_of_center
        (e.trans eX) hp hp3 hpZ
      simp only [CFSG.RankThree.PartOne.Mult.SporadicResidualPair, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpair
      rcases hpair with ⟨rfl, -⟩ | ⟨-, hs⟩ | hs
      · exact hnot CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_mcl_five
      · simp at hs
      · simp at hs
    exact hconf.card_center_eq_three
      (Census.CoverCenterThreeRest.card_center_dvd_three_of_McL hLq hZ3 e)

theorem item417InJ3_of
    (hR : Item417InJ3Rest) : Item417InJ3 := by
  intro G _ _ L A E c m hconf ⟨e⟩
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  have hXc : Nonempty (NativeSporadic.J3 ≃* NativeSporadic.Carrier .J3) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hXc
  have hZ3 := hconf.isPGroup_center fun p hp hp3 =>
    not_dvd_center_of_spor12 (s := .J3) (by simp [spor12]) (e.trans eX) hp hp3
  have hZ := hconf.card_center_eq_three
    (Census.CoverCenterThreeRest.card_center_dvd_three_of_J3 hLq hZ3 e)
  obtain ⟨hm, hext⟩ := hR G L A E c m hconf hZ ⟨e⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, Or.inr ⟨hZ, ⟨e⟩⟩,
    hext⟩))))))

theorem item417InON_of
    (hR : Item417InONRank) : Item417InON := by
  intro G _ _ L A E c m hconf ⟨e⟩
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  have hXc : Nonempty (NativeSporadic.ON ≃* NativeSporadic.Carrier .ONan) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hXc
  have hZ3 := hconf.isPGroup_center fun p hp hp3 hpZ => by
    obtain ⟨hpair, hnot⟩ := CFSG.RankThree.PartOne.Mult.sporadic_residual_of_center (e.trans eX)
      hp hp3 hpZ
    simp only [CFSG.RankThree.PartOne.Mult.SporadicResidualPair, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hpair
    rcases hpair with ⟨-, hs⟩ | ⟨rfl, -⟩ | hs
    · simp at hs
    · exact hnot CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_on_seven
    · simp at hs
  have hZ := hconf.card_center_eq_three
    (Census.CoverCenterThreeRest.card_center_dvd_three_of_ON hLq hZ3 e)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hR G L A E c m hconf hZ ⟨e⟩, hZ, ⟨e⟩⟩)))))))

end Certs

end CFSG.RankThree.PartTwo.Sec4
