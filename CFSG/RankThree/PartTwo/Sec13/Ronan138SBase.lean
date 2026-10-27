module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Frame138Base (A L E F : Subgroup G) (c x y t : G) : Prop where
  hH : Hyp138 A c L E
  hF : IsF138N L E F
  hxE : x ∈ E
  hyF : y ∈ F
  frame : HeisFrame (E ⊓ F) x y
  hd1 : ⁅x, y⁆ ≠ 1
  hdL : ⁅x, y⁆ ∈ L
  hcF : c ∈ F
  h81 : Nat.card (E ⊔ F : Subgroup G) = 81
  h9 : Nat.card (E ⊓ F : Subgroup G) = 9
  hEFL : E ⊓ F ⊓ L = Subgroup.zpowers ⁅x, y⁆
  htL : t ∈ L
  htE : t ∈ Subgroup.normalizer (E : Set G)
  htd : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆⁻¹
  htc : t * c = c * t
  hEt : ∀ a ∈ E, t * a * t⁻¹ * a⁻¹ ∈ Subgroup.zpowers ⁅x, y⁆

namespace Frame138Base

variable {A L E F : Subgroup G} {c x y t : G} (h : Frame138Base A L E F c x y t)
include h

theorem hE3 : ∀ a ∈ E, a ^ 3 = 1 := h.hH.2.2.2.1.2
theorem hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.hH.2.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
theorem hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.hF.1.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
theorem hE27 : Nat.card E = 27 := h.hH.2.2.2.2.1
theorem hF27 : Nat.card F = 27 := h.hF.1.2.2.1
theorem hFN : F ≤ Subgroup.normalizer (E : Set G) := h.hF.1.2.2.2.2
theorem hcE : c ∈ E := h.hH.2.2.1
theorem hc1 : c ≠ 1 := h.hH.1.ne_one
theorem hc3 : c ^ 3 = 1 := h.hE3 c h.hcE
theorem hd3 : ⁅x, y⁆ ^ 3 = 1 := h.frame.comm_pow_three
theorem hdZ : ⁅x, y⁆ ∈ E ⊓ F := h.frame.comm_mem
theorem hdE : ⁅x, y⁆ ∈ E := (Subgroup.mem_inf.mp h.hdZ).1
theorem hcZ : c ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨h.hcE, h.hcF⟩

theorem hcL : c ∉ L := by
  obtain ⟨hD, -, -, -, -, -, -, -, hC⟩ := h.hH
  obtain ⟨π, p, f, Kf, _, hKf, hq, φ, -⟩ := hC
  have hL := hD.mem_thetaComponentsAt
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hKf hq φ
  exact Sec13.not_mem_of_center_eq_bot hD
    (Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hKf hq hq2))

theorem hdc : ⁅x, y⁆ ∉ Subgroup.zpowers c := by
  intro hdc
  have heq := zpowers_eq_of_mem h.hd3 h.hd1 h.hc3 h.hc1 hdc
  apply h.hcL
  have hc : c ∈ Subgroup.zpowers ⁅x, y⁆ := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr h.hdL hc

theorem hZgen : ∀ z ∈ E ⊓ F, ∃ α β : ℕ, z = c ^ α * ⁅x, y⁆ ^ β := by
  intro z hz
  have hcd : Subgroup.zpowers c ⊓ Subgroup.zpowers ⁅x, y⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [← zpowers_inf_eq_bot h.hc3 h.hcL]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1,
      Subgroup.zpowers_le.mpr h.hdL (Subgroup.mem_inf.mp hw).2⟩
  exact exists_pow_mul_pow_of_card h.hcZ h.hdZ (h.hEab c h.hcE _ h.hdE) h.hc3 h.hc1 h.hd3 h.hd1
    hcd h.h9 hz

end Frame138Base

theorem Frame138.toBase {A L E F : Subgroup G} {c x y t : G} (h : Frame138 A L E F c x y t) :
    Frame138Base A L E F c x y t where
  hH := h.hH
  hF := h.hF
  hxE := h.hxE
  hyF := h.hyF
  frame := h.frame
  hd1 := h.hd1
  hdL := h.hdL
  hcF := h.hcF
  h81 := h.h81
  h9 := h.h9
  hEFL := by
    rw [inf_right_comm, h.hEL]
    exact inf_eq_left.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp h.hdZ).2)
  htL := h.htL
  htE := h.htE
  htd := h.htd
  htc := h.htc
  hEt := by
    intro a ha
    rw [← h.hEL]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp h.htE a).mp ha) (inv_mem ha)
    · have haN := h.hH.2.2.2.2.2.1 ha
      have h1 : a * t⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN _).mp (inv_mem h.htL)
      rw [show t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) by group]
      exact mul_mem h.htL h1

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
