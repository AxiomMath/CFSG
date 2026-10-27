module

public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaCentralizerTransfer
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.AlphaTheory

open CFSG CFSG.RankThree.GroupTheory Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_zpowers_sup_zpowers (c b : G) :
    centralizer ((zpowers c ⊔ zpowers b : Subgroup G) : Set G) =
      centralizer ({c} : Set G) ⊓ centralizer ({b} : Set G) := by
  ext x
  rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, mem_centralizer_iff]
  constructor
  · intro hx
    exact ⟨(hx c (mem_sup_left (mem_zpowers c))).symm,
      (hx b (mem_sup_right (mem_zpowers b))).symm⟩
  · rintro ⟨hxc, hxb⟩ h hh
    have hle : zpowers c ⊔ zpowers b ≤ centralizer ({x} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxc.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxb.symm))
    exact mem_centralizer_singleton_iff.mp (hle hh)

theorem commutator_inf_centralizer_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) {c : G} (hc : c ∈ A)
    (hc1 : c ≠ 1)
    (H1 : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → c ∈ D →
      ⁅inSubgroup (pCore 2) (normalizer (zpowers c : Set G) ⊓ centralizer (D : Set G)), A⁆ ≤
        inSubgroup (pCore 2) (normalizer (zpowers c : Set G)))
    {E : Subgroup G} (hEA : E ≤ A) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) :
    ⁅inSubgroup (pCore 2) (normalizer (zpowers c : Set G) ⊓ centralizer ({b} : Set G)), E⁆ ≤
      inSubgroup (pCore 2) (normalizer (zpowers c : Set G)) := by
  have := hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hcord : orderOf c = p := SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hc hc1
  obtain ⟨hCN, hCnormal, hOeq, -⟩ :=
    SteinbergBY.alpha_normal_odd_cyclic_centralizer_transfer_normalizer hp hp2 hcord
  have hNC : normalizer (zpowers c : Set G) ≤ normalizer (centralizer ({c} : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hCN).mp hCnormal
  have hbA : b ∈ A := hEA hb
  have hEC : E ≤ centralizer ({c} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hcomm c hc x (hEA hx)).symm
  by_cases hbc : b ∈ zpowers c
  ·
    have hzb : zpowers b = zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hbc) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hcord,
        SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hbA hb1]
    have hCb : centralizer ({b} : Set G) = centralizer ({c} : Set G) := by
      rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
        SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hzb]
    rw [hCb, inf_eq_right.mpr hCN, hOeq]
    exact le_normalizer_iff_commutator_le_left.mp
      ((hEC.trans hCN).trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _))
  ·
    have hDA : zpowers c ⊔ zpowers b ≤ A := sup_le (zpowers_le.mpr hc) (zpowers_le.mpr hbA)
    have hDcard : Nat.card (zpowers c ⊔ zpowers b : Subgroup G) = p ^ 2 :=
      SteinbergBY.card_zpowers_sup_zpowers hp hAcard hc hc1 hbA hbc
    have hcD : c ∈ zpowers c ⊔ zpowers b := mem_sup_left (mem_zpowers c)
    set N := normalizer (zpowers c : Set G) with hN
    set L := N ⊓ centralizer ({b} : Set G) with hL
    have hcL : c ∈ L :=
      ⟨Subgroup.le_normalizer (mem_zpowers c),
        mem_centralizer_singleton_iff.mpr (hcomm b hbA c hc).symm⟩
    have hLN : L ≤ normalizer (zpowers c : Set G) := inf_le_left
    have hO : inSubgroup (pCore 2) L ≤ L ⊓ centralizer ({c} : Set G) :=
      le_inf (SteinbergBY.inSubgroup_pCore_le 2 L)
        (SteinbergBY.inSubgroup_pCore_two_le_centralizer hp hp2 hcord hcL hLN)
    have hLC : L ≤ normalizer ((L ⊓ centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      fun x hx => SteinbergBY.mem_normalizer_inf (Subgroup.le_normalizer hx)
        (hNC hx.1)
    have htrans := (SteinbergBY.twoCoreAlpha_transfer_of_le_normalizer inf_le_left hLC hO).1
    have hLD : L ⊓ centralizer ({c} : Set G) =
        N ⊓ centralizer ((zpowers c ⊔ zpowers b : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_sup_zpowers, hL, inf_assoc,
        inf_comm (centralizer ({b} : Set G)) (centralizer ({c} : Set G))]
    rw [← htrans, hLD]
    exact (Subgroup.commutator_mono le_rfl hEA).trans (H1 _ hDA hDcard hcD)

end CFSG.RankThree.PartOne.AlphaTheory
