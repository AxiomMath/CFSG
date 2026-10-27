module

public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkG
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem comm_eq_bot_of_block_of_perfect {G : Type} [Group G] [Finite G] {L Y : Subgroup G}
    (hL : IsShort2 L) (hperf : ⁅L, L⁆ = L) {d : ℕ}
    (hd : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ d) (hd' : d = 3 ∨ d = 4 ∨ d = 6)
    (hY5 : IsPGroup 5 Y) (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hYc : Y ≤ SBc17.cMod L) : ⁅L, Y⁆ = ⊥ := by
  refine le_bot_iff.mp (Subgroup.commutator_le.2 fun l hl y hy => ?_)
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hY5 ⟨y, hy⟩
  have hyk : y ^ 5 ^ k = 1 := congrArg Subtype.val hk
  have hyN' : y ∈ Subgroup.normalizer (L : Set G) := hYN hy
  have h := modData_of_block hL hyN' (hYc hy)
  have hcM : ∀ x ∈ L, ⁅x, y⁆ ∈ blockQ L := (SBc17.mem_cMod.mp (hYc hy)).2
  have hS3 : ∀ l ∈ L, ⁅l, y⁆ ∈ blockU L :=
    commutator_mem_of_perfect (N := blockQ L) (M := blockU L) hperf hyN' h.normU
      (fun n hn g hg => Subgroup.commutator_mem_commutator hn hg) hcM
  have hS4 : ∀ l ∈ L, ⁅l, y⁆ ∈ ⁅blockU L, L⁆ :=
    commutator_mem_of_perfect (N := blockU L) (M := ⁅blockU L, L⁆) hperf hyN'
      (fun g hg m hm => conj_mem_commutator (le_normalizer_of_forall h.normU hg)
        (Subgroup.le_normalizer hg) hm)
      (fun n hn g hg => Subgroup.commutator_mem_commutator hn hg) hS3
  have hS1 : ∀ u ∈ blockU L, ⁅y, u⁆ ∈ blockZ L := h.comm_mem_Z hperf hyk hd hd'
  have hS2 : ⁅blockU L, L⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    refine Subgroup.commutator_le.2 fun u hu l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    have := h.y_comm_commutator hS1 hu hl
    rw [mul_inv_eq_iff_eq_mul] at this
    rw [hg]
    exact this
  have hU0U : ⁅blockU L, L⁆ ≤ blockU L := by
    refine Subgroup.commutator_le.2 fun u hu l hl => ?_
    have := mul_mem hu (h.normU l hl u⁻¹ (inv_mem hu))
    simpa [commutatorElement_def, mul_assoc] using this
  have hc := inv_mem (hS4 l hl)
  have hcy : y * ⁅l, y⁆⁻¹ * y⁻¹ = ⁅l, y⁆⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp (hS2 hc) y rfl
  have hyl : y * l * y⁻¹ = ⁅l, y⁆⁻¹ * l := by
    simp only [commutatorElement_def]
    group
  have h1 := eq_one_of_conj_step hcy (h.exp _ (hU0U hc)) (Odd.pow (by decide)) hyk hyl
  exact inv_eq_one.mp h1

theorem comm_eq_bot_of_block {G : Type} [Group G] [Finite G] {L Y : Subgroup G}
    (hL : IsShort2 L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {d : ℕ}
    (hd : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ d) (hd' : d = 3 ∨ d = 4 ∨ d = 6)
    (hY5 : IsPGroup 5 Y) (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hYc : Y ≤ SBc17.cMod L) : ⁅L, Y⁆ = ⊥ :=
  comm_eq_bot_of_block_of_perfect hL
    (C1GN.isShort2_perfect_of_perfect_quotient hL (Group.isPerfect_def.mp hq.1)) hd hd' hY5 hYN
    hYc

end CFSG.Quasithin.H23P4
