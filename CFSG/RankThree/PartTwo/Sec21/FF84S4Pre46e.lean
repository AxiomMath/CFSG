module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46d

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

theorem tau_comm_c : a8c * swap 6 7 = swap 6 7 * a8c := by
  unfold a8c
  decide +kernel

theorem tau_comm_d : a8d * swap 6 7 = swap 6 7 * a8d := by
  unfold a8d
  decide +kernel

theorem B_le_cenS (h : FF84Sec4 b L B K b₁ b₂) : B ≤ CenS B := fun x hx =>
  Subgroup.mem_centralizer_iff.2 fun y hy => (comm_of_mem h hy hx).eq

theorem cenS_of_gens (h : FF84Sec4 b L B K b₁ b₂) {g : G} (hb : g * b = b * g)
    (hb₁ : g * b₁ = b₁ * g) (hb₂ : g * b₂ = b₂ * g) : g ∈ CenS B := by
  have hle : B ≤ Cen g := B_le_of_mem' h (Subgroup.mem_centralizer_singleton_iff.2 hb.symm)
    (Subgroup.mem_centralizer_singleton_iff.2 hb₁.symm)
    (Subgroup.mem_centralizer_singleton_iff.2 hb₂.symm)
  exact Subgroup.mem_centralizer_iff.2 fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem no_theta_tau (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥) (hY : Opp 3 (Cen (b * b₁)) = ⊥)
    (h41 : FF84_4_1) (hθ : ThM L b₁ b₂ θ) {g : G} (hgN : g ∈ Nor L) (hgB : g ∈ CenS B)
    (hgτ : thG L θ g = swap 6 7) : False := by
  have hgb := cenB_cen_b h hgB
  have hgg : g * g ∈ Subgroup.zpowers b := by
    refine Qθ h hZ hX hθ (mul_mem hgN hgN) (mul_mem hgb hgb) ?_
    rw [thG_mul hgN hgN, hgτ, swap_mul_self]
  have h6 : g ^ 6 = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hgg
    have h3 : (g * g) ^ 3 = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        pow3_of_mem h (mem_b h), one_zpow]
    calc g ^ 6 = (g * g) ^ 3 := by rw [← pow_two, ← pow_mul]
      _ = 1 := h3
  refine no_inv_cenB hA h hZ hX hY h41 (Subgroup.pow_mem _ hgB 3)
    (by rw [← pow_add]; exact h6) ?_
  intro he
  have h1 := thG_pow (θ := θ) hgN 3
  rw [he, thG_one, hgτ] at h1
  have hcube : (swap (6 : Fin 8) 7) ^ 3 = swap 6 7 := by decide
  have h2 : swap (6 : Fin 8) 7 = 1 := by
    calc swap (6 : Fin 8) 7 = swap 6 7 ^ 3 := hcube.symm
      _ = 1 := h1.symm
  exact absurd h2 (by decide)

theorem cenSB_le (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥) (hY : Opp 3 (Cen (b * b₁)) = ⊥)
    (h41 : FF84_4_1) (hθ : ThM L b₁ b₂ θ) : CenS B ≤ B := by
  intro g hgB
  have hgb := cenB_cen_b h hgB
  have hgN : g ∈ Nor L := h.hyp.hLN hgb
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2
  have hc₁ : thG L θ g * a8c = a8c * thG L θ g := by
    rw [← hθ.c, ← thG_mul hgN hb₁N, ← thG_mul hb₁N hgN,
      (Subgroup.mem_centralizer_iff.1 hgB b₁ (mem_b₁ h)).symm]
  have hc₂ : thG L θ g * a8d = a8d * thG L θ g := by
    rw [← hθ.d, ← thG_mul hgN hb₂N, ← thG_mul hb₂N hgN,
      (Subgroup.mem_centralizer_iff.1 hgB b₂ (mem_b₂ h)).symm]
  obtain ⟨⟨i, -, j, -, e, he, hgt⟩, -⟩ := cen_two _ hc₁ hc₂
  have hβB : b₁ ^ i * b₂ ^ j ∈ B :=
    mul_mem (Subgroup.pow_mem _ (mem_b₁ h) i) (Subgroup.pow_mem _ (mem_b₂ h) j)
  have hβN : b₁ ^ i * b₂ ^ j ∈ Nor L :=
    mul_mem (pow_mem hb₁N i) (pow_mem hb₂N j)
  have hβθ : thG L θ (b₁ ^ i * b₂ ^ j) = a8c ^ i * a8d ^ j := by
    rw [thG_mul (pow_mem hb₁N i) (pow_mem hb₂N j), thG_pow hb₁N, thG_pow hb₂N, hθ.c, hθ.d]
  have hg'N : (b₁ ^ i * b₂ ^ j)⁻¹ * g ∈ Nor L := mul_mem (inv_mem hβN) hgN
  have hg'B : (b₁ ^ i * b₂ ^ j)⁻¹ * g ∈ CenS B :=
    mul_mem (inv_mem (B_le_cenS h hβB)) hgB
  have hg'θ : thG L θ ((b₁ ^ i * b₂ ^ j)⁻¹ * g) = swap 6 7 ^ e := by
    rw [thG_mul (inv_mem hβN) hgN, thG_inv hβN, hβθ, hgt]
    group
  have he' : e = 0 ∨ e = 1 := by
    have := Finset.mem_range.1 he
    omega
  rcases he' with rfl | rfl
  · have hmem := Qθ h hZ hX hθ hg'N (cenB_cen_b h hg'B) (by rw [hg'θ, pow_zero])
    have hg : g = (b₁ ^ i * b₂ ^ j) * ((b₁ ^ i * b₂ ^ j)⁻¹ * g) := by group
    rw [hg]
    exact mul_mem hβB (Subgroup.zpowers_le.2 (mem_b h) hmem)
  · exact (no_theta_tau hA h hZ hX hY h41 hθ hg'N hg'B (by rw [hg'θ, pow_one])).elim

theorem cen_b_le (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥) (hY : Opp 3 (Cen (b * b₁)) = ⊥)
    (h41 : FF84_4_1) (hθ : ThM L b₁ b₂ θ) : Cen b ≤ Subgroup.zpowers b ⊔ L := by
  intro g hgb
  have hgN : g ∈ Nor L := h.hyp.hLN hgb
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hτs : sign (swap (6 : Fin 8) 7) = -1 := Perm.sign_swap (by decide)
  have hAlt : thG L θ g ∈ alternatingGroup (Fin 8) := by
    by_contra hnot
    have hsg : sign (thG L θ g) = -1 := by
      rcases Int.units_eq_one_or (sign (thG L θ g)) with h1 | h1
      · exact absurd (mem_alternatingGroup.2 h1) hnot
      · exact h1
    have heven : thG L θ g * swap 6 7 ∈ alternatingGroup (Fin 8) := by
      rw [mem_alternatingGroup, Perm.sign_mul, hsg, hτs]
      decide
    obtain ⟨l, hlL, hlθ⟩ := hθ.surj _ heven
    have hlN : l ∈ Nor L := Subgroup.le_normalizer hlL
    have hg'N : l⁻¹ * g ∈ Nor L := mul_mem (inv_mem hlN) hgN
    have hg'b : l⁻¹ * g ∈ Cen b := mul_mem (inv_mem (h.hyp.hLC hlL)) hgb
    have hg'θ : thG L θ (l⁻¹ * g) = swap 6 7 := by
      rw [thG_mul (inv_mem hlN) hgN, thG_inv hlN, hlθ, mul_inv_rev, inv_mul_cancel_right,
        swap_inv]
    have hg'B : l⁻¹ * g ∈ CenS B := by
      refine cenS_of_gens h (Subgroup.mem_centralizer_singleton_iff.1 hg'b) ?_ ?_
      · exact (cen_thG h hZ hθ hb₁L hg'N (by rw [hθ.c, hg'θ]; exact tau_comm_c)).symm
      · exact (cen_thG h hZ hθ hb₂L hg'N (by rw [hθ.d, hg'θ]; exact tau_comm_d)).symm
    exact no_theta_tau hA h hZ hX hY h41 hθ hg'N hg'B hg'θ
  obtain ⟨l, hlL, hlθ⟩ := hθ.surj _ hAlt
  have hlN : l ∈ Nor L := Subgroup.le_normalizer hlL
  have hq : l⁻¹ * g ∈ Subgroup.zpowers b :=
    Qθ h hZ hX hθ (mul_mem (inv_mem hlN) hgN) (mul_mem (inv_mem (h.hyp.hLC hlL)) hgb)
      (by rw [thG_mul (inv_mem hlN) hgN, thG_inv hlN, hlθ, inv_mul_cancel])
  have hg : g = l * (l⁻¹ * g) := by group
  rw [hg]
  exact mul_mem (Subgroup.mem_sup_right hlL) (Subgroup.mem_sup_left hq)

theorem S46_main (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥) (hY : Opp 3 (Cen (b * b₁)) = ⊥)
    (h41 : FF84_4_1) :
    CenS B = B ∧ Subgroup.zpowers b ⊔ L = Cen b ∧ Subgroup.zpowers b ⊓ L = ⊥ := by
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  refine ⟨le_antisymm (cenSB_le hA h hZ hX hY h41 hθ) (B_le_cenS h), le_antisymm ?_
    (cen_b_le hA h hZ hX hY h41 hθ), ?_⟩
  · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
      h.hyp.hLC
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxb, hxL⟩ := hx
    have hxc : x ∈ CenS L := Subgroup.zpowers_le.2 (b_mem_cenS h) hxb
    rw [Subgroup.mem_bot]
    exact L_inf_cenS hZ x hxL hxc

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
