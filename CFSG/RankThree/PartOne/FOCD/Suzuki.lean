module

public import CFSG.RankThree.PartOne.FOCD.Bridge
import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.LieType.Ree
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo innerAut fixSub fixSubEquiv)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem noCompOf_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NoCompOf p (suzukiGroup a K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  refine noCompOf_of_forall fun b hb1 hbp L => ?_
  have hb : orderOf b = p := orderOf_eq_prime hbp hb1
  obtain ⟨hodd, -⟩ := (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha
    hK).2 b hb1 (hb ▸ hp.odd_of_ne_two (by omega))
  have : Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set (suzukiGroup a K))) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact not_isComponent_of_isSolvable L

theorem isSolvable_suzuki_zero {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) : Group.IsSolvable (suzukiGroup 0 k) := by
  obtain ⟨hcard, P, hPn, hPc, -, -⟩ := suzuki_two_normal_five_complement_core_trivial hk
  have : P.Normal := hPn
  have hK : Nat.card k = 2 ^ (2 * 0 + 1) := by rw [hk]; norm_num
  have := finite_suzukiGroup hK
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  have : Group.IsSolvable ↥P := inferInstance
  have hq : Nat.card (suzukiGroup 0 k ⧸ P) = 4 := by
    have := Subgroup.card_mul_index P
    rw [hcard, hPc] at this
    rw [← Subgroup.index_eq_card]
    omega
  have hQ : IsPGroup 2 (suzukiGroup 0 k ⧸ P) := IsPGroup.of_card (n := 2) (by rw [hq]; norm_num)
  have : Group.IsNilpotent (suzukiGroup 0 k ⧸ P) := hQ.isNilpotent
  have : Group.IsSolvable (suzukiGroup 0 k ⧸ P) := inferInstance
  exact Group.isSolvable_of_ker_le_range P.subtype (QuotientGroup.mk' P) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem outerComp_suzuki (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OuterComp p (suzukiGroup a K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hfin : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  intro _ β hβp hβout _ y hβy hyp E hE
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ (innerAut _).one_mem)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨σ, h, b, k, _, _, hσ, hbp, hkcard, hconj, ⟨efix⟩⟩ :=
    KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 β hord hβout
  have hφ : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
      szFieldAut a K σ := by
    have : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
        MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
    rw [this, hconj]
  have eX : ↥(fixSub β) ≃* suzukiGroup b k :=
    ((fixSubEquiv (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β).trans
      (MulEquiv.subgroupCongr (by rw [hφ]; rfl))).trans efix
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    have hk2 : Nat.card k = 2 := by rw [hkcard]; norm_num
    have := isSolvable_suzuki_zero hk2
    have : Group.IsSolvable ↥(fixSub β) :=
      Group.isSolvable_of_isSolvable_injective (f := eX.toMonoidHom) eX.injective
    exact (false_of_isComponentOf (fun L => not_isComponent_of_isSolvable L) hE).elim
  · have hsimple : IsSimpleGroup (suzukiGroup b k) := (suzuki_simple hb1 hkcard).2.2
    have : IsSimpleGroup ↥(fixSub β) := eX.isSimpleGroup
    rw [eq_of_isComponentOf_simple hE]
    exact hβy

end CFSG.RankThree.PartOne.FOCD
