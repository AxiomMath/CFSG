module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.Asc83Table.Reduction
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialConstructor
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private theorem commutator_val_eq_scalar_hs {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {x y : slPi π 3 (p ^ f) K} {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0)
    (hx : (x : GL (Fin 3) K) = diagTau hτ) (hy : (y : GL (Fin 3) K) = cycThree) :
    ((⁅x, y⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by
  have h1 := cycThree_pow_conj_diagTau hτ hτ0 1
  rw [pow_one, mul_one] at h1
  have hu : (Units.mk0 τ hτ0 ^ 2)⁻¹ = Units.mk0 τ hτ0 := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← pow_succ]
    exact hτ
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, hy]
  calc diagTau hτ * cycThree * (diagTau hτ)⁻¹ * cycThree⁻¹ =
      (cycThree * diagTau hτ * cycThree⁻¹ * (diagTau hτ)⁻¹)⁻¹ := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ *
        (diagTau hτ)⁻¹)⁻¹ := by rw [h1]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2))⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by rw [← map_inv, hu]

private theorem extraspecial_closure_hs {L : Type} [Group L] [Finite L] {x y : L}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) :
    IsExtraspecialExpP 3 1 ↥(Subgroup.closure ({x, y} : Set L)) := by
  classical
  have hFact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup L := Subgroup.closure ({x, y} : Set L)
  have hcard : Nat.card E = 27 := CFSG.RankThree.Asc83Table.ex27_card hx hy hzx hzy hz1
  have hE_nontriv : Nontrivial E := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard]
    norm_num
  have hexp : Monoid.exponent E = 3 := by
    rw [@Monoid.exponent_eq_prime_iff E _ hE_nontriv 3 Nat.prime_three]
    intro g hg
    exact orderOf_eq_prime (p := 3) (hp := hFact)
      (Subtype.ext (CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx hzx hzy hy g.2)) hg
  have hnc : ¬ IsMulCommutative E := by
    intro hc
    apply hz1
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h := mul_comm' (⟨x, Subgroup.subset_closure (by simp)⟩ : E)
      ⟨y, Subgroup.subset_closure (by simp)⟩
    exact congrArg Subtype.val h
  have hcenter : Nat.card (center E) = 3 := by
    have hc : Nat.card E = 3 ^ 3 := by rw [hcard]; norm_num
    exact (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_center_of_nonabelian_card_p_cube
      hc hnc)
  exact isExtraspecialExpP_three_of_card_exponent_center hcard hexp hcenter

private theorem center_le_closure_of_commutator_hs {L : Type} [Group L] [Finite L]
    {x y : L} (hx : x ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x)
    (hz_center : ⁅x, y⁆ ∈ center L) (hz1 : ⁅x, y⁆ ≠ 1)
    (hcenter : Nat.card (center L) = 3) :
    center L ≤ Subgroup.closure ({x, y} : Set L) := by
  have hFact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup L := Subgroup.closure ({x, y} : Set L)
  have hxE : x ∈ E := Subgroup.subset_closure (by simp)
  have hyE : y ∈ E := Subgroup.subset_closure (by simp)
  have hzE : ⁅x, y⁆ ∈ E := by
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem hxE hyE) (E.inv_mem hxE)) (E.inv_mem hyE)
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := CFSG.RankThree.Asc83Table.commutator_pow_three hx hzx
  have hcard_zpow : Nat.card (Subgroup.zpowers ⁅x, y⁆) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 3) (hp := hFact) hz3 hz1
  have hle : Subgroup.zpowers ⁅x, y⁆ ≤ center L := Subgroup.zpowers_le.mpr hz_center
  have heq : Subgroup.zpowers ⁅x, y⁆ = center L :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_zpow, hcenter])
  rw [← heq]
  exact Subgroup.zpowers_le.mpr hzE

theorem exists_isExtraspecialExpP_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ E : Subgroup (slPi π 3 (p ^ f) K), center (slPi π 3 (p ^ f) K) ≤ E ∧
      IsExtraspecialExpP 3 1 ↥E := by
  classical
  let : Finite K := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  let x : slPi π 3 (p ^ f) K := ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩
  let y : slPi π 3 (p ^ f) K := ⟨cycThree, cycThree_mem_slPi hπ⟩
  have hxval : (x : GL (Fin 3) K) = diagTau hτ := rfl
  have hyval : (y : GL (Fin 3) K) = cycThree := rfl
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hxval]
    exact diagTau_pow_three hτ
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hyval]
    exact cycThree_pow_three
  have hcommval : ((⁅x, y⁆ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) :=
    commutator_val_eq_scalar_hs hτ hτ0 hxval hyval
  have hz_center : ⁅x, y⁆ ∈ center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcommval]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 τ hτ0)
      (g : GL (Fin 3) K)).eq
  have hzx : Commute ⁅x, y⁆ x := (Subgroup.mem_center_iff.mp hz_center x).symm
  have hzy : Commute ⁅x, y⁆ y := (Subgroup.mem_center_iff.mp hz_center y).symm
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h
    have hval : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) = 1 := by
      rw [← hcommval, h]
      rfl
    have h00 := congrArg (fun A : GL (Fin 3) K => ((A : Matrix (Fin 3) (Fin 3) K) 0 0)) hval
    simp at h00
    exact hτ1 h00
  let E : Subgroup (slPi π 3 (p ^ f) K) := Subgroup.closure ({x, y} : Set _)
  refine ⟨E, ?_, ?_⟩
  · exact center_le_closure_of_commutator_hs hx3 hzx hz_center hz1
      (CFSG.RankThree.PartTwo.KFacts.card_center_slPi hK hq)
  · exact extraspecial_closure_hs hx3 hy3 hzx hzy hz1

theorem exists_isExtraspecialExpP_of_isSLThreePiAt {Q : Type} [Group Q] [Finite Q] {q : ℕ}
    (hQ : CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt Q q) :
    ∃ E : Subgroup Q, center Q ≤ E ∧ IsExtraspecialExpP 3 1 ↥E := by
  obtain ⟨π, p, f, K, _, hK, hq, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec12.Item128StepsProof.exists_model hQ
  obtain ⟨E₀, hZ, hE₀⟩ := exists_isExtraspecialExpP_slPi hK hq
  refine ⟨E₀.comap (e : Q →* slPi π 3 (p ^ f) K), ?_, ?_⟩
  · intro g hg
    exact Subgroup.mem_comap.mpr
      (hZ (CFSG.RankThree.PartTwo.KFacts.mem_center_of_mulEquiv e hg))
  · have hmap : (E₀.comap (e : Q →* slPi π 3 (p ^ f) K)).map
        (e : Q →* slPi π 3 (p ^ f) K) = E₀ :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective E₀
    exact isExtraspecialExpP_of_mulEquiv
      ((e.subgroupMap (E₀.comap (e : Q →* slPi π 3 (p ^ f) K))).trans
        (MulEquiv.subgroupCongr hmap)) hE₀

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
