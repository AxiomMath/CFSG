module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.Alternating.Multipliers.Small
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

open Subgroup
open scoped commutatorElement

section Central

variable {G : Type*} [Group G]

theorem central_comm {z : G} (hz : z ∈ Subgroup.center G) (c : G) : z * c = c * z :=
  (Subgroup.mem_center_iff.mp hz c).symm

theorem comm_central_left {z : G} (hz : z ∈ Subgroup.center G) (c : G) :
    ⁅z, c⁆ = 1 := by
  rw [commutatorElement_def, central_comm hz c, mul_inv_cancel_right, mul_inv_cancel]

theorem comm_central_right {z : G} (hz : z ∈ Subgroup.center G) (c : G) :
    ⁅c, z⁆ = 1 := by
  rw [commutatorElement_def, ← central_comm hz c, mul_inv_cancel_right, mul_inv_cancel]

theorem conj_central {z : G} (hz : z ∈ Subgroup.center G) (x : G) : z * x * z⁻¹ = x := by
  rw [central_comm hz x, mul_inv_cancel_right]

theorem comm_mul_central_left {z a c : G} (hz : z ∈ Subgroup.center G) :
    ⁅z * a, c⁆ = ⁅a, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, comm_central_left hz c, mul_one, conj_central hz]

theorem comm_mul_central_right {z c d : G} (hz : z ∈ Subgroup.center G) :
    ⁅d, z * c⁆ = ⁅d, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, comm_central_right hz d, one_mul, conj_central hz]

theorem card_sup_eq_mul {N E : Subgroup G} [N.Normal] (h : N ⊓ E = ⊥) :
    Nat.card (N ⊔ E : Subgroup G) = Nat.card N * Nat.card E := by
  have h1 : N.relIndex (N ⊔ E) * Nat.card (N ⊓ (N ⊔ E) : Subgroup G) =
      Nat.card (N ⊔ E : Subgroup G) :=
    relIndex_mul_card N (N ⊔ E)
  have h2 : N.relIndex (N ⊔ E) = N.relIndex E := by
    rw [sup_comm]
    exact relIndex_sup_right E N
  have h3 : N.relIndex E * Nat.card (N ⊓ E : Subgroup G) = Nat.card E :=
    relIndex_mul_card N E
  rw [inf_eq_left.mpr le_sup_left] at h1
  rw [h, card_bot, mul_one] at h3
  rw [← h1, h2, h3, Nat.mul_comm]

theorem inf_ne_bot_of_perfect [Finite G] [Group.IsPerfect G] {N E : Subgroup G}
    (hN : N ≤ Subgroup.center G) (hN3 : Nat.card N = 3) (m : ℕ) (hG : Nat.card G = 27 * m)
    (hm : Nat.Coprime m 3) (hE : Nat.card E = 9) : N ⊓ E ≠ ⊥ := by
  intro h
  have : N.Normal := Subgroup.normal_of_le_center hN
  have : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (central_comm (hN a.2) (b : G))⟩⟩
  have hcard := card_sup_eq_mul h
  rw [hN3, hE] at hcard
  have hidx : (N ⊔ E).index = m := by
    have h1 := card_mul_index (N ⊔ E)
    rw [hcard, hG] at h1
    omega
  have hcop : Nat.Coprime (N ⊔ E).index (Nat.card N) := by
    rw [hidx, hN3]
    exact hm
  obtain ⟨D, -, hND, hsup⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N (N ⊔ E) E hcop h rfl
  have hcomm : commutator G ≤ D := by
    show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ D
    rw [commutator_le]
    intro g _ g' _
    have hg : g ∈ N ⊔ D := by
      rw [hsup]
      exact Subgroup.mem_top g
    have hg' : g' ∈ N ⊔ D := by
      rw [hsup]
      exact Subgroup.mem_top g'
    obtain ⟨n, hn, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hg
    obtain ⟨n', hn', d', hd', rfl⟩ := mem_sup_of_normal_left.mp hg'
    rw [comm_mul_central_left (hN hn), comm_mul_central_right (hN hn')]
    simp only [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd hd') (D.inv_mem hd)) (D.inv_mem hd')
  rw [Group.IsPerfect.commutator_eq_top] at hcomm
  have hDtop : D = ⊤ := top_le_iff.mp hcomm
  rw [hDtop, inf_top_eq] at hND
  rw [hND, card_bot] at hN3
  omega

end Central

section A7

open CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
  (nat_card_alternatingGroup_fin 5).trans (by decide)

end A7

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

end
