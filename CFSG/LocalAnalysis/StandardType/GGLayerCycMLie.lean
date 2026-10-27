module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycMCyclic
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Models.Transport
import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Open.Defs
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.LayerCycM

open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders generic exceptional)
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess hopfMultiplierToKer
  hopfMultiplierToKer_surjective finite_hopfMultiplier)

@[expose] def LieTwoModel (X : Type) [Group X] : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), CFSG.Models.LieModel X t n 2 f) ∨
    CFSG.Models.LieModel X .PSL 2 3 2 ∨ CFSG.Models.LieModel X .PSU 3 3 1

theorem LieTwoModel.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : LieTwoModel X) : LieTwoModel Y := by
  rcases h with ⟨t, n, f, hm⟩ | hm | hm
  · exact Or.inl ⟨t, n, f, hm.of_mulEquiv e⟩
  · exact Or.inr (Or.inl (hm.of_mulEquiv e))
  · exact Or.inr (Or.inr (hm.of_mulEquiv e))

theorem genericOrders_snd_charTwo (t : StatedLieTag) (n f : ℕ) (hf : 1 ≤ f) :
    (genericOrders t n 2 f).2 = 1 := by
  have hq : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  cases t <;> simp [genericOrders, hq]

theorem exceptionalOrders_dvd_four (t : StatedLieTag) (n f : ℕ) :
    (exceptionalOrders t n 2 f).1 ∣ 4 ∧ (exceptionalOrders t n 2 f).2 ∣ 4 := by
  unfold exceptionalOrders
  split <;> simp_all

theorem not_dvd_of_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} (hd : d ∣ 4) :
    ¬ p ∣ d := by
  intro h
  have h4 : p ∣ 2 ^ 2 := by simpa using h.trans hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))

theorem psubCyclic_griessHopfMultiplier (hG : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] (hX : LieTwoModel X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PSubCyclic p (CFSG.Open.griessHopfMultiplier X) := by
  rcases hX with ⟨t, n, f, hm⟩ | hm | hm
  · obtain ⟨-, ⟨g⟩⟩ := hG X t n 2 f hm
    have hf : 1 ≤ f := hm.1.2.1
    refine PSubCyclic.of_mulEquiv g.symm ?_
    have h2 : ¬ p ∣ (genericOrders t n 2 f).2 := by
      rw [genericOrders_snd_charTwo t n f hf]
      exact hp.not_dvd_one
    obtain ⟨h3, h4⟩ := exceptionalOrders_dvd_four t n f
    exact psubCyclic_zmod_quad_fst hp _ h2 (not_dvd_of_dvd_four hp hp2 h3)
      (not_dvd_of_dvd_four hp hp2 h4)
  · obtain ⟨-, ⟨g⟩⟩ := hG X .PSL 2 3 2 hm
    refine PSubCyclic.of_mulEquiv g.symm ?_
    have hg : genericOrders .PSL 2 3 2 = (2, 1) := by simp [genericOrders]
    have he : exceptionalOrders .PSL 2 3 2 = (3, 1) := rfl
    refine psubCyclic_zmod_quad_thd hp _ ?_ ?_ ?_
    · rw [hg]
      exact not_dvd_of_dvd_four hp hp2 (by norm_num)
    · rw [hg]
      exact hp.not_dvd_one
    · rw [he]
      exact hp.not_dvd_one
  · obtain ⟨-, ⟨g⟩⟩ := hG X .PSU 3 3 1 hm
    refine PSubCyclic.of_mulEquiv g.symm ?_
    have hg : genericOrders .PSU 3 3 1 = (1, 1) := by simp [genericOrders]
    have he : exceptionalOrders .PSU 3 3 1 = (1, 1) := rfl
    refine psubCyclic_zmod_quad_fst hp _ ?_ ?_ ?_
    · rw [hg]
      exact hp.not_dvd_one
    · rw [he]
      exact hp.not_dvd_one
    · rw [he]
      exact hp.not_dvd_one

theorem isCyclic_of_le_center_of_lieTwoModel (hG : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : LieTwoModel (J ⧸ Subgroup.center J)) {S : Subgroup J}
    (hSZ : S ≤ Subgroup.center J) (hSp : IsPGroup p S) : IsCyclic S := by
  haveI : Group.IsPerfect J := ⟨hperf⟩
  let q : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hkerq : q.ker = Subgroup.center J := QuotientGroup.ker_mk' _
  have hker : q.ker ≤ Subgroup.center J := hkerq.le
  haveI : Group.IsPerfect (J ⧸ Subgroup.center J) := Group.IsPerfect.ofSurjective hq
  haveI : Finite (hopfMultiplier (J ⧸ Subgroup.center J)) :=
    finite_hopfMultiplier inferInstance
  have hc : PSubCyclic p (hopfMultiplier (J ⧸ Subgroup.center J)) :=
    PSubCyclic.of_mulEquiv (hopfMultiplierEquivGriess _)
      (psubCyclic_griessHopfMultiplier hG hX hp hp2)
  have hc' : PSubCyclic p q.ker :=
    PSubCyclic.of_surjective (hopfMultiplierToKer q hq hker)
      (hopfMultiplierToKer_surjective q hq hker) hp hc
  have hc'' : PSubCyclic p (Subgroup.center J) :=
    PSubCyclic.of_mulEquiv (MulEquiv.subgroupCongr hkerq) hc'
  have hS' : IsPGroup p (S.subgroupOf (Subgroup.center J)) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  haveI : IsCyclic (S.subgroupOf (Subgroup.center J)) := hc'' _ hS'
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSZ)
    (Subgroup.subgroupOfEquivOfLe hSZ).surjective

end CFSG.StandardType.LayerCycM

end
