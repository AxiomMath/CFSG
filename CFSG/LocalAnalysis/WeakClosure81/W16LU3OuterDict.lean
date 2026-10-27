module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootBase
public import CFSG.GroupTheory.OddKernelImage
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup
open scoped commutatorElement

section Certified


theorem IsU3Shape.exists_lift_data {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3Shape X n)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hYc : Nat.card Y = 2 ^ n) :
    ∃ (Q : Sylow 2 (X ⧸ Subgroup.center X)) (Qh : Subgroup X),
      rootCenter (Q : Subgroup (X ⧸ Subgroup.center X)) =
        Y.map (QuotientGroup.mk' (Subgroup.center X)) ∧
      IsPGroup 2 Qh ∧
      Qh.map (QuotientGroup.mk' (Subgroup.center X)) = (Q : Subgroup (X ⧸ Subgroup.center X)) ∧
      Qh ≤ Subgroup.centralizer (Y : Set X) ∧
      Subgroup.centralizer (Y : Set X) ≤ Subgroup.normalizer (Qh : Set X) ∧
      (∀ g : X, (g : X ⧸ Subgroup.center X) ∈
        Subgroup.centralizer (rootCenter (Q : Subgroup (X ⧸ Subgroup.center X)) :
          Set (X ⧸ Subgroup.center X)) → g ∈ Subgroup.centralizer (Y : Set X)) ∧
      ∀ α : MulAut X, (∀ y ∈ Y, α y = y) → ∀ q ∈ Qh, α q ∈ Qh := by
  classical
  let Z := Subgroup.center X
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hZodd : Odd (Nat.card Z) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hX.2.2 with h | h <;> rw [h] <;> decide
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hodd : Odd (Nat.card π.ker) := by rw [hker]; exact hZodd
  have hcen : π.ker ≤ Subgroup.center X := le_of_eq hker
  have hY2 : IsPGroup 2 Y := hY.isPGroup
  have hinf : Y ⊓ Z = ⊥ := CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hY2 hZodd
  have hYbar : IsElemAbelian 2 (Y.map π) := hY.map π
  have hYcbar : Nat.card (Y.map π) = 2 ^ n := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot π (by rw [hker]; exact hinf), hYc]
  obtain ⟨Q, hQ⟩ :=
    IsPSUGp.exists_sylow_sylowCenter_eq (P := X ⧸ Z) hX.2.1 hYbar hYcbar
  have hQroot : rootCenter (Q : Subgroup (X ⧸ Z)) = Y.map π := hQ
  have hB : BenderType (X ⧸ Z) n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.benderType_of_lieModel_PSU3 hX.2.1
  have hQ2 : IsPGroup 2 (Q : Subgroup (X ⧸ Z)) := Q.isPGroup'
  have hQrange : (Q : Subgroup (X ⧸ Z)) ≤ π.range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]
    exact le_top
  obtain ⟨Qh, hQh2, hQhmap, -⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd (Φ := π) hodd hQrange hQ2
  have hYle : Y ≤ Qh := by
    refine CFSG.GroupTheory.le_of_map_le_map_of_odd (Φ := π) hcen hodd hY2 ?_
    rw [hQhmap, ← hQroot]
    exact rootCenter_le (Q : Subgroup (X ⧸ Z))
  have hQh_cent : Qh ≤ Subgroup.centralizer (Y : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQh : y ∈ Qh := hYle hy
    have hqQ : π q ∈ (Q : Subgroup (X ⧸ Z)) := by
      rw [← hQhmap]; exact Subgroup.mem_map_of_mem π hq
    have hyroot : π y ∈ rootCenter (Q : Subgroup (X ⧸ Z)) := by
      rw [hQroot]; exact Subgroup.mem_map_of_mem π hy
    have hcent := (Subgroup.mem_inf.mp hyroot).2
    have hcomm : π q * π y = π y * π q :=
      Subgroup.mem_centralizer_iff.mp hcent (π q) hqQ
    have hmem : y * q * (q * y)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hcomm, mul_inv_cancel]
    rw [hker] at hmem
    have hmemQh : y * q * (q * y)⁻¹ ∈ Qh :=
      Qh.mul_mem (Qh.mul_mem hyQh hq) (Qh.inv_mem (Qh.mul_mem hq hyQh))
    have hbot : y * q * (q * y)⁻¹ ∈ Qh ⊓ Z := Subgroup.mem_inf.mpr ⟨hmemQh, hmem⟩
    rw [CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hQh2 hZodd, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot
  have hCbar : ∀ g : X, (g : X ⧸ Z) ∈
      Subgroup.centralizer (rootCenter (Q : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) →
      g ∈ Subgroup.centralizer (Y : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    have hyroot : π y ∈ rootCenter (Q : Subgroup (X ⧸ Z)) := by
      rw [hQroot]; exact Subgroup.mem_map_of_mem π hy
    have hcomm : π y * π g = π g * π y := hg (π y) hyroot
    have hmem : ⁅y, g⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [hker] at hmem
    have hcy : Commute y ⁅y, g⁆ := Subgroup.mem_center_iff.mp hmem y
    have hsq : ⁅y, g⁆ ^ 2 = 1 := by
      rw [hcy.commutatorElement_pow_left 2, hY.2 y hy, commutatorElement_one_left]
    have hoddord : Odd (orderOf ⁅y, g⁆) :=
      Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hmem)
    have hone : ⁅y, g⁆ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · rw [h1] at hoddord
        exact absurd hoddord (by decide)
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  have hQh_norm : Subgroup.centralizer (Y : Set X) ≤ Subgroup.normalizer (Qh : Set X) := by
    intro g hg
    have hcent_bar : π g ∈
        Subgroup.centralizer (rootCenter (Q : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hQroot] at hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hgy : y * g = g * y := Subgroup.mem_centralizer_iff.mp hg y hy
      rw [← map_mul, ← map_mul, hgy]
    have hconj : ∀ z ∈ rootCenter (Q : Subgroup (X ⧸ Z)), MulAut.conj (π g) z = z := by
      intro z hz
      rw [MulAut.conj_apply]
      have hcomm := Subgroup.mem_centralizer_iff.mp hcent_bar z hz
      rw [← hcomm]
      group
    have hQnorm : ∀ s ∈ (Q : Subgroup (X ⧸ Z)),
        MulAut.conj (π g) s ∈ (Q : Subgroup (X ⧸ Z)) :=
      BenderType.mem_of_centralizes_rootCenter hB Q (MulAut.conj (π g)) hconj
    have hcomp : π.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (π g)).toMonoidHom.comp π := by
      ext x
      change π (MulAut.conj g x) = MulAut.conj (π g) (π x)
      rw [MulAut.conj_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv]
    have hmap_le : (Qh.map (MulAut.conj g).toMonoidHom).map π ≤ Qh.map π := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hQhmap]
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      exact hQnorm s hs
    have hconj_le : Qh.map (MulAut.conj g).toMonoidHom ≤ Qh :=
      CFSG.GroupTheory.le_of_map_le_map_of_odd (Φ := π) hcen hodd
        (hQh2.map (MulAut.conj g).toMonoidHom) hmap_le
    have hconj_eq : Qh.map (MulAut.conj g).toMonoidHom = Qh := by
      refine Subgroup.eq_of_le_of_card_ge hconj_le ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj_eq
  refine ⟨Q, Qh, hQroot, hQh2, hQhmap, hQh_cent, hQh_norm, hCbar, ?_⟩
  intro α hα q hq
  have hαbar : ∀ z ∈ rootCenter (Q : Subgroup (X ⧸ Z)),
      CFSG.RankThree.PartTwo.KFacts.centerDescend X α z = z := by
    intro z hz
    rw [hQroot] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have h1 : π y = (y : X ⧸ Subgroup.center X) := rfl
    rw [h1, CFSG.RankThree.PartTwo.KFacts.centerDescend_mk, hα y hy]
  have hQinv : ∀ s ∈ (Q : Subgroup (X ⧸ Z)),
      CFSG.RankThree.PartTwo.KFacts.centerDescend X α s ∈ (Q : Subgroup (X ⧸ Z)) :=
    BenderType.mem_of_centralizes_rootCenter hB Q
      (CFSG.RankThree.PartTwo.KFacts.centerDescend X α) hαbar
  have hcompα : π.comp α.toMonoidHom =
      (CFSG.RankThree.PartTwo.KFacts.centerDescend X α).toMonoidHom.comp π := by
    ext x
    change π (α x) = CFSG.RankThree.PartTwo.KFacts.centerDescend X α (π x)
    exact (CFSG.RankThree.PartTwo.KFacts.centerDescend_mk X α x).symm
  have hmap_leα : (Qh.map α.toMonoidHom).map π ≤ Qh.map π := by
    rw [Subgroup.map_map, hcompα, ← Subgroup.map_map, hQhmap]
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    exact hQinv s hs
  have hleα : Qh.map α.toMonoidHom ≤ Qh :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd (Φ := π) hcen hodd
      (hQh2.map α.toMonoidHom) hmap_leα
  exact hleα (Subgroup.mem_map_of_mem α.toMonoidHom hq)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
