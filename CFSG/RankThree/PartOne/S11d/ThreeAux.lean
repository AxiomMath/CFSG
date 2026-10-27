module

public import CFSG.RankThree.PartOne.S12.Sec12Two

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem false_of_rank_four_of_normalizes (hev : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup G} (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    {V : Subgroup G} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hAV : A ≤ normalizer (V : Set G))
    {e : G} (heA : e ∉ A) (hep : e ^ p = 1) (hec : ∀ x ∈ A, x * e = e * x)
    (heV : e ∈ normalizer (V : Set G)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have he1 : e ≠ 1 := fun h => heA (h ▸ A.one_mem)
  have hHloc : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hV1, hV2, rfl⟩
  have hPQ : A ⊓ zpowers e = ⊥ := Sec12Two.inf_zpowers_eq_bot hp hep heA
  have hP : IsElemAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hAe
  have hQ : IsElemAbelian p (zpowers e) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp
      (IsElementaryAbelian.zpowers_of_pow_eq_one hep)
  have hcomm : ∀ x ∈ A, ∀ y ∈ zpowers e, Commute x y := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact Commute.zpow_right (hec x hx) i
  have hQH : zpowers e ≤ normalizer (V : Set G) := (zpowers_le).mpr heV
  have hcard : Nat.card (zpowers e) = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hep he1, pow_one]
  have h4 := Sec12Two.le_pRank_of_commute_of_inf_eq_bot hp hP hQ hcomm hPQ
    (a := 3) (b := 1) hAcard hcard hAV hQH
  have h5 := Sec12Two.pRank_le_evenRank_of_isTwoLocal hp hp2 hHloc
  omega

omit [Finite G] in
theorem card_sup_dvd_of_le_normalizer' (N I : Subgroup G)
    (hI : I ≤ normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

end CFSG.RankThree.PartOne
