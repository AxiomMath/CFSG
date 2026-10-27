module

public import CFSG.OddTranspositions.PartThree.EightEight.Star
public import CFSG.Timmesfeld.Bridge.Asc72Minimal

import CFSG.OddTranspositions.PartThree.EightEight.DeltaOrbit
import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.FibreCentre
import CFSG.OddTranspositions.PartThree.EightEight.ThirdCentralizer
import CFSG.OddTranspositions.PartThree.EightEight.Transport
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.HalphaCentralizer

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem notMem_conjOrbit_of_mem_alpha (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {u : G} (hu : u ∈ hC.alpha) :
    u ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
  intro huO
  set z : G := (x * y * w) ^ n with hzdef
  have hx' : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  have hy' : y ∈ D := DalphaStar_subset hC.isBlock_alpha hy
  obtain ⟨-, -, -, -, -, heD⟩ :=
    IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hxy : Commute x y := ht.2.2.2.2.1
  have hxe : Commute x (x * y * z) := (commute_mul_mul_pow_left hC.setup.oddT
    hC.setup.normal ht hn hord).symm
  have hye : Commute y (x * y * z) := (commute_mul_mul_pow_right hC.setup.oddT
    hC.setup.normal ht hn hord).symm
  have hz_eq : x * y * (x * y * z) = z := mul_mul_mul_mul_cancel_of_isTriangle hC.setup.oddT ht z
  have hyO : y ∈ conjOrbit (localGroup D (x * y * (x * y * z))) x := by
    rw [hz_eq]
    exact (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have heO : x * y * z ∈ conjOrbit (localGroup D (x * y * (x * y * z))) x := by
    rw [hz_eq]
    exact mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
  have huO' : u ∈ conjOrbit (localGroup D (x * y * (x * y * z))) x := by
    rw [hz_eq]
    exact huO
  have hux : Commute u x := commute_of_mem_of_mem_DalphaStar hu hx
  have huy : Commute u y := commute_of_mem_of_mem_DalphaStar hu hy
  have hdisj := disjoint_alpha_DalphaStar hC.isBlock_alpha
  rcases mem_or_mem_or_mem_of_mem_conjOrbit hC hne hx' hy' heD hxy hxe hye hyO heO huO'
    hux huy (mem_blockClass_self hC.alpha) hu with h | h | h
  · exact Set.disjoint_right.mp hdisj hx h
  · exact Set.disjoint_right.mp hdisj hy h
  · exact Set.disjoint_right.mp hdisj (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord) h

theorem conjOrbit_subset_DalphaStar (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    conjOrbit (localGroup D ((x * y * w) ^ n)) x ⊆ DalphaStar D hC.alpha := by
  intro v hv
  set z : G := (x * y * w) ^ n with hzdef
  have hx' : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  have hzk : Commute z x :=
    (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1
  have hxcent : x ∈ centSet D z := ⟨hx', hzk.symm⟩
  have hxywH : x * y * w ∈ Halpha D hC.alpha :=
    (Halpha D hC.alpha).mul_mem ((Halpha D hC.alpha).mul_mem (Subgroup.subset_closure hx)
      (Subgroup.subset_closure hy)) (Subgroup.subset_closure hw)
  have hzH : z ∈ Halpha D hC.alpha := Subgroup.pow_mem _ hxywH n
  have hdz : Commute z hC.d :=
    Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC hzH)
  have hdcent : hC.d ∈ centSet D z := ⟨hC.hd, hdz.symm⟩
  have hdO : hC.d ∉ conjOrbit (localGroup D z) x :=
    notMem_conjOrbit_of_mem_alpha hC hne ht hx hw hy hn hord hC.d_mem_alpha
  rcases conjOrbit_subset_or_subset_DalphaStar hC hxcent hdcent hdO
    (mem_blockClass_self hC.alpha) hC.d_mem_alpha with h | h
  · exfalso
    exact Set.disjoint_right.mp (disjoint_alpha_DalphaStar hC.isBlock_alpha) hx
      (h (self_mem_conjOrbit (localGroup D z) x))
  · exact h hv

end CFSG.OddTranspositions.PartThree.EightEight

end
