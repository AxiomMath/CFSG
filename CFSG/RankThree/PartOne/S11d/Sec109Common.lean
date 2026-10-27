module

public import CFSG.RankThree.PartOne.S11b.Sec109
public import CFSG.RankThree.PartOne.S11d.Common

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

namespace Sec109

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G}
  {n : ℕ}

theorem Config.A_elem (h : Config p A c L B n) : IsElementaryAbelian p A :=
  h.setup.2.2.2.2.2.2.1

theorem Config.A_card (h : Config p A c L B n) : Nat.card A = p ^ 3 :=
  h.setup.2.2.2.2.2.2.2.1

theorem Config.prime (h : Config p A c L B n) : p.Prime :=
  sectionTenSetup_prime h.setup

theorem Config.A_comm (h : Config p A c L B n) : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u :=
  fun u hu v hv => congrArg Subtype.val (h.A_elem.is_comm.comm (⟨u, hu⟩ : A) ⟨v, hv⟩)

theorem Config.pow_p_eq_one (h : Config p A c L B n) {u : G} (hu : u ∈ A) : u ^ p = 1 := by
  have := h.A_elem
  exact elemPow_eq_one_of_isElementaryAbelian (A := A) u hu

theorem Config.B_le_A (h : Config p A c L B n) : B ≤ A := by
  rw [h.B_eq]
  exact inf_le_left

theorem Config.c_notMem_B (h : Config p A c L B n) : c ∉ B := by
  intro hc
  have hA : A = B := by
    rw [h.A_eq]
    exact sup_eq_left.mpr (zpowers_le.mpr hc)
  have h1 := h.A_card
  rw [hA, h.B_card, h.p_eq] at h1
  norm_num at h1

theorem Config.L_le_centralizer (h : Config p A c L B n) : L ≤ centralizer ({c} : Set G) :=
  (mem_thetaComponentsAt_iff.mp h.L_mem.2).1

theorem Config.exists_x (h : Config p A c L B n) :
    ∃ (x : G) (lam : ℤ), x ∈ L ∧ x ≠ 1 ∧ x ∈ normalizer (B : Set G) ∧ ¬ (7 : ℤ) ∣ lam - 1 ∧
      ∀ b ∈ B, x * b * x⁻¹ = b ^ lam := by
  obtain ⟨b₁, b₂, x₁, x₂, x, -, -, -, -, -, hx₁L, hx₂L, hx₁N, hx₂N, -, -, -, -, -, hxcl, hx1,
    ⟨lam, hlam, hx⟩, -⟩ := h.structure_B
  refine ⟨x, lam, ?_, hx1, ?_, hlam, hx⟩
  · have hle : Subgroup.closure ({x₁, x₂} : Set G) ≤ L := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact hx₁L
      · exact hx₂L
    exact hle hxcl
  · have hle : Subgroup.closure ({x₁, x₂} : Set G) ≤ normalizer (B : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact hx₁N
      · exact hx₂N
    exact hle hxcl

theorem Config.mem_L_comm_c (h : Config p A c L B n) {x : G} (hx : x ∈ L) : x * c = c * x :=
  mem_centralizer_singleton_iff.mp (h.L_le_centralizer hx)

theorem Config.mem_normalizer_A (h : Config p A c L B n) {x : G}
    (hxN : x ∈ normalizer (B : Set G)) (hxc : x * c = c * x) : x ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hxN ⊢
  have hC : (zpowers c).map (MulAut.conj x : G →* G) = zpowers c := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change x * c * x⁻¹ = c
    rw [hxc]
    group
  rw [h.A_eq, Subgroup.map_sup, hxN, hC]

theorem Config.exists_decomp (h : Config p A c L B n) {a : G} (ha : a ∈ A) :
    ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j := by
  have hcomm : ∀ β ∈ B, Commute β c := fun β hβ =>
    h.A_comm β (h.B_le_A hβ) c h.c_mem
  rw [h.A_eq] at ha
  exact (S11d.mem_sup_zpowers_iff hcomm).mp ha

end Sec109

end CFSG.RankThree.PartOne
