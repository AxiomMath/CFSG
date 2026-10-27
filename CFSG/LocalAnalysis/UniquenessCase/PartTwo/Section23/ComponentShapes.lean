module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.Adapters.LieModelOrders
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.LieTypeOrderBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

theorem not_isSp4_of_isL2Odd {X : Type} [Group X] {q n : ℕ} (hq : IsL2Odd X q) :
    ¬ IsSp4 X n := by
  intro hsp
  have hqadm := hq.admissible
  simp only [StatedLieAdmissible] at hqadm
  have hqprime : q.Prime := hqadm.1
  have hqne2 : q ≠ 2 := by
    intro h2
    exact hqadm.2.2.2.1 (by rw [h2]; simp)
  have hqne3 : q ≠ 3 := by
    intro h3
    exact hqadm.2.2.2.2 (by rw [h3]; simp)
  have hq3 : 3 < q := by
    have := hqprime.two_le
    omega
  have hspadm := hsp.admissible
  simp only [StatedLieAdmissible] at hspadm
  have hn1 : 1 ≤ n := hspadm.2.1
  have hLcard : Nat.card X = ordA 1 q := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hq.card_eq_lieOrd (by norm_num)
  have hScard : Nat.card X = ordBC 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hsp.card_eq_lieOrd (by norm_num)
  have hord : ordA 1 q = ordBC 2 (2 ^ n) := hLcard.symm.trans hScard
  obtain ⟨r, -, hr⟩ := CFSG.GroupTheory.two_part_ordBC_two hn1
  have hdvd : 2 ^ (n * 4) ∣ ordBC 2 (2 ^ n) := by
    rw [hr]
    exact dvd_mul_right _ _
  exact CFSG.GroupTheory.ordA_one_ne_of_two_pow hqprime hq3 hdvd
    (CFSG.GroupTheory.ordBC_two_small hn1) hord

theorem not_isU3_of_isL2Odd {X : Type} [Group X] {q n : ℕ} (hq : IsL2Odd X q) :
    ¬ IsU3 X n := by
  intro hsu
  have hqadm := hq.admissible
  simp only [StatedLieAdmissible] at hqadm
  have hqprime : q.Prime := hqadm.1
  have hqne2 : q ≠ 2 := by
    intro h2
    exact hqadm.2.2.2.1 (by rw [h2]; simp)
  have hqne3 : q ≠ 3 := by
    intro h3
    exact hqadm.2.2.2.2 (by rw [h3]; simp)
  have hq3 : 3 < q := by
    have := hqprime.two_le
    omega
  have hsuadm := hsu.admissible
  simp only [StatedLieAdmissible] at hsuadm
  have hn1 : 1 ≤ n := hsuadm.2.1
  have hne : 2 ^ n ≠ 2 := by
    intro h2
    exact hsuadm.2.2.2 (by rw [h2])
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1' : n = 1 := by omega
    exact hne (by rw [hn1']; norm_num)
  have hLcard : Nat.card X = ordA 1 q := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hq.card_eq_lieOrd (by norm_num)
  have hUcard : Nat.card X = ordTwistedA 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hsu.card_eq_lieOrd (by norm_num)
  have hord : ordA 1 q = ordTwistedA 2 (2 ^ n) := hLcard.symm.trans hUcard
  obtain ⟨r, -, hr⟩ := CFSG.GroupTheory.two_part_ordTwistedA_two hn1
  have hdvd : 2 ^ (n * 3) ∣ ordTwistedA 2 (2 ^ n) := by
    rw [hr]
    exact dvd_mul_right _ _
  exact CFSG.GroupTheory.ordA_one_ne_of_two_pow hqprime hq3 hdvd
    (CFSG.GroupTheory.ordTwistedA_two_small hn2) hord

theorem hyp2120_two_of_s23_8 (hJ : J1NotSp4SU3) (D : Data G) (Ch : Choice2011 G)
    (h8 : S23_8 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) := by
  intro L hL
  obtain ⟨hnorm, hlist⟩ := h8 h1930 c L hL
  refine ⟨hnorm, ?_⟩
  rintro ⟨n, -, hsp | hsu⟩
  · have hshape : (∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n) := by
      left
      haveI : IsSimpleGroup (Bar2 L) :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) hsp
      have hc : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
      obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hc
      exact ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hsp⟩
    obtain ⟨hnotL2, hnotSz, -⟩ := uc22p21k_shape_not_list hJ hL hshape
    rcases hlist with ⟨a, -, haL2 | haSz⟩ | ⟨hsecond, -⟩
    · exact hnotL2 a haL2
    · exact hnotSz a haSz
    · rcases hsecond with ⟨q, -, -, hqL2Odd⟩ | hj1 | ⟨a, haL2⟩
      · exact not_isSp4_of_isL2Odd hqL2Odd hsp
      · exact (hJ (Bar2 L) hj1).2.1 n hsp
      · exact hnotL2 (2 * a) haL2
  · have hshape : (∃ n : ℕ, IsSp4 (BarInf L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n) :=
      Or.inr ⟨n, hsu⟩
    obtain ⟨hnotL2, hnotSz, -⟩ := uc22p21k_shape_not_list hJ hL hshape
    rcases hlist with ⟨a, -, haL2 | haSz⟩ | ⟨hsecond, -⟩
    · exact hnotL2 a haL2
    · exact hnotSz a haSz
    · rcases hsecond with ⟨q, -, -, hqL2Odd⟩ | hj1 | ⟨a, haL2⟩
      · haveI : IsSimpleGroup (Bar2 L) :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide)
            hqL2Odd
        have hc : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hsu.1
        obtain ⟨e⟩ := uc22p21k_quotCenter_equiv hc
        have hU : IsU3 (Bar2 L) n := CFSG.Blueprint.LieModel.of_mulEquiv e hsu.2
        exact not_isU3_of_isL2Odd hqL2Odd hU
      · exact (hJ (Bar2 L) hj1).2.2 n hsu
      · exact hnotL2 (2 * a) haL2

end CFSG.LocalAnalysis.UniquenessCase.UC22
