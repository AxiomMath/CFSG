module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Thirteen
public import CFSG.RankThree.GF2n.Stroth78.Sec2Lbar

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem QaOf_deriv_eq_zpowers (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    ⁅QaOf a, QaOf a⁆ = Subgroup.zpowers a := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  exact commutator_QaOf_eq_zpowers S hg

theorem card_QaOf_eq_two_mul_card_inf_H_of_isConj (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (hza : z ∈ QaOf a) (hzaZ : z ∉ centerIn (QaOf a)) :
    Nat.card (QaOf a) = 2 * Nat.card (QaOf a ⊓ H z : Subgroup G) := by
  have hderiv : ⁅QaOf a, QaOf a⁆ = Subgroup.zpowers a := QaOf_deriv_eq_zpowers S hconj
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj
  have ha1 : a ≠ 1 := by
    intro ha
    have hz1 : z = 1 := isConj_one_left.mp (ha ▸ hconj)
    have hord := S.hyp.orderOf_z
    rw [hz1, orderOf_one] at hord
    norm_num at hord
  have haCent : a ∈ Subgroup.centralizer (QaOf a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp
      (fStar_le (Subgroup.centralizer ({a} : Set G)) hx) a (Set.mem_singleton a)).symm
  let f : ↥(QaOf a) →* G := {
    toFun := fun x => ⁅z, (x : G)⁆
    map_one' := by simp
    map_mul' := fun x y => by
      have hy : ⁅z, (y : G)⁆ ∈ Subgroup.zpowers a := by
        have hmem : ⁅z, (y : G)⁆ ∈ ⁅QaOf a, QaOf a⁆ :=
          Subgroup.commutator_mem_commutator hza y.2
        rwa [hderiv] at hmem
      have hx : (x : G) * ⁅z, (y : G)⁆ * (x : G)⁻¹ = ⁅z, (y : G)⁆ := by
        have hcomm : (x : G) * ⁅z, (y : G)⁆ = ⁅z, (y : G)⁆ * (x : G) :=
          Subgroup.mem_centralizer_iff.mp
            (Subgroup.zpowers_le.mpr haCent hy) (x : G) x.2
        rw [hcomm]
        group
      calc
        ⁅z, ((x : G) * (y : G))⁆ =
            ⁅z, (x : G)⁆ * (x : G) * ⁅z, (y : G)⁆ * (x : G)⁻¹ :=
          commutatorElement_mul_right_eq_mul_conj z (x : G) (y : G)
        _ = ⁅z, (x : G)⁆ * ((x : G) * ⁅z, (y : G)⁆ * (x : G)⁻¹) := by group
        _ = ⁅z, (x : G)⁆ * ⁅z, (y : G)⁆ := by rw [hx] }
  have hker : f.ker = (QaOf a ⊓ H z).subgroupOf (QaOf a) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show ⁅z, (x : G)⁆ = 1 ↔ (x : G) ∈ QaOf a ∧ (x : G) ∈ H z
    rw [H, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      exact commutatorElement_eq_one_iff_mul_comm.mp hx
    · rintro ⟨-, hxH⟩
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hxH z (Set.mem_singleton z))
  have hrange_le : f.range ≤ Subgroup.zpowers a := by
    rintro y ⟨x, rfl⟩
    have hmem : ⁅z, (x : G)⁆ ∈ ⁅QaOf a, QaOf a⁆ :=
      Subgroup.commutator_mem_commutator hza x.2
    rwa [hderiv] at hmem
  have hrange_ne_bot : f.range ≠ ⊥ := by
    intro hbot
    apply hzaZ
    refine Subgroup.mem_inf.mpr ⟨hza, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : f ⟨y, hy⟩ = 1 := by
      have hmem : f ⟨y, hy⟩ ∈ f.range := ⟨⟨y, hy⟩, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hy1).symm
  have hcard_a : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have hrange_card : Nat.card f.range = 2 := by
    have hle : Nat.card f.range ≤ Nat.card (Subgroup.zpowers a) :=
      Subgroup.card_le_of_le hrange_le
    rw [hcard_a] at hle
    have hgt : 1 < Nat.card f.range :=
      (Subgroup.one_lt_card_iff_ne_bot f.range).mpr hrange_ne_bot
    omega
  have hmain := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange_card] at hmain
  have hker_card : Nat.card ((QaOf a ⊓ H z).subgroupOf (QaOf a)) =
      Nat.card (QaOf a ⊓ H z : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : QaOf a ⊓ H z ≤ QaOf a)).toEquiv
  rw [hker_card, Nat.mul_comm] at hmain
  exact hmain.symm


theorem two_mul_card_Lbar_mul_card_inf_Q_eq_card_Qa (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (hza : z ∈ QaOf a) (hzaZ : z ∉ centerIn (QaOf a)) :
    2 * Nat.card (Lbar S a) * Nat.card (QaOf a ⊓ Q z : Subgroup G) =
      Nat.card (QaOf a) := by
  have hindex := card_QaOf_eq_two_mul_card_inf_H_of_isConj S hconj hza hzaZ
  have hcard := card_Lbar_mul S a
  change Nat.card (QaOf a) = 2 * Nat.card (L0 S a) at hindex
  rw [← hcard] at hindex
  rw [mul_assoc]
  exact hindex.symm

end CFSG.RankThree.GF2n.Stroth78
