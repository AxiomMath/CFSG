module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Setup
public import CFSG.GroupTheory.PGroupCommutingConjugate

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

private theorem conjBy_zpowers (g b : H) :
    conjBy g (Subgroup.zpowers b) = Subgroup.zpowers (g * b * g⁻¹) :=
  MonoidHom.map_zpowers _ _

private theorem eq_or_eq_inv_of_mem_zpowers {b : H} (hb : orderOf b = 3) {x : H}
    (hx : x ∈ Subgroup.zpowers b) (hx1 : x ≠ 1) : x = b ∨ x = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hb] at hx1 ⊢
  have hk : (k % ((3 : ℕ) : ℤ)) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h0 | h0 | h0 <;> rw [h0] at hx1 ⊢
  · exact absurd (zpow_zero b) hx1
  · left; exact zpow_one b
  · right
    have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hb3])

theorem FS79Hyp.weaklyClosed_sylow (h : FS79Hyp b t b₁ b₂ J)
    {M : Subgroup H} (hbM : Subgroup.zpowers b ≤ M) (P : Sylow 3 M)
    (hbP : b ∈ (P : Subgroup M).map M.subtype) :
    ∀ D : Subgroup H, (∃ g : H, conjBy g (Subgroup.zpowers b) = D) →
      D ≤ (P : Subgroup M).map M.subtype → D = Subgroup.zpowers b := by
  classical
  have hordb : orderOf b = 3 := h.ord_b
  set P' : Subgroup H := (P : Subgroup M).map M.subtype with hP'def
  have hP'p : IsPGroup 3 P' := P.isPGroup'.map M.subtype
  have hbP' : b ∈ P' := hbP
  have hP'le : P' ≤ Cen b := by
    by_contra hle
    obtain ⟨p, hpP', hpC⟩ := Set.not_subset.mp hle
    let x : P' := ⟨b, hbP'⟩
    have hx_not_center : x ∉ Subgroup.center P' := by
      intro hx
      apply hpC
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) (⟨p, hpP'⟩ : P')))
    obtain ⟨g, hgne, hgcomm⟩ :=
      CFSG.exists_commuting_conjugate_of_noncentral (by norm_num : Nat.Prime 3) hP'p
        hx_not_center
    let gH : H := (g : P')
    let y : H := gH * b * gH⁻¹
    have hgneH : y ≠ b := by
      intro hy
      apply hgne
      apply Subtype.ext
      simpa [y, gH, x] using hy
    have hgcommH : y * b = b * y := by
      have hh := congrArg Subtype.val hgcomm
      simpa [y, gH, x] using hh
    have hyCen : y ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr hgcommH
    have hy_le : Subgroup.zpowers y ≤ Cen b := Subgroup.zpowers_le.mpr hyCen
    have hconj : conjBy gH (Subgroup.zpowers b) = Subgroup.zpowers y := conjBy_zpowers gH b
    have hleNor : conjBy gH (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) := by
      rw [hconj]
      exact hy_le.trans h.cen_le_nor
    have hweak_eq : Subgroup.zpowers y = Subgroup.zpowers b := by
      rw [← hconj]
      exact h.weak gH hleNor
    have hy_mem : y ∈ Subgroup.zpowers b := by
      rw [← hweak_eq]
      exact Subgroup.mem_zpowers y
    have hb_ne_one : b ≠ 1 := by
      intro hb1
      have hordb' : orderOf b = 3 := hordb
      rw [hb1, orderOf_one] at hordb'
      norm_num at hordb'
    have hy_ne_one : y ≠ 1 := by
      intro hy1
      apply hb_ne_one
      have hy1' : gH * b * gH⁻¹ = 1 := by simpa [y] using hy1
      calc b = gH⁻¹ * (gH * b * gH⁻¹) * gH := by group
        _ = gH⁻¹ * (1 : H) * gH := by rw [hy1']
        _ = 1 := by group
    rcases eq_or_eq_inv_of_mem_zpowers hordb hy_mem hy_ne_one with hyb | hybinv
    · exact hgneH hyb
    ·
      obtain ⟨k, hk⟩ := hP'p.exists_pow_pow_eq_one g
      have hgn : gH ^ (3 ^ k) = 1 := by
        have hval := congrArg Subtype.val hk
        simpa [gH] using hval
      have hodd : Odd (3 ^ k) := (show Odd (3 : ℕ) by norm_num).pow
      let φ : MulAut H := MulAut.conj gH
      have hφb : φ b = b⁻¹ := by simpa [φ] using hybinv
      have hφ2 : (φ ^ 2) b = b := by
        calc (φ ^ 2) b = φ (φ b) := by rw [pow_two, MulAut.mul_apply]
          _ = φ b⁻¹ := by rw [hφb]
          _ = (φ b)⁻¹ := by simp
          _ = (b⁻¹)⁻¹ := by rw [hφb]
          _ = b := inv_inv b
      have hφn : φ ^ (3 ^ k) = 1 := by
        have hmap : MulAut.conj (gH ^ (3 ^ k)) = (MulAut.conj gH) ^ (3 ^ k) :=
          map_pow (MulAut.conj : H →* MulAut H) gH (3 ^ k)
        rw [hgn, map_one] at hmap
        simpa [φ] using hmap.symm
      obtain ⟨q, hq⟩ := hodd
      rw [hq] at hφn
      have h2q : ∀ q : ℕ, ((φ ^ 2) ^ q) b = b := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
            rw [pow_succ, MulAut.mul_apply, hφ2, ih]
      have hb_eq : b = b⁻¹ := by
        have h1 : (φ ^ (2 * q + 1)) b = b := by
          rw [hφn]
          simp
        have h2 : (φ ^ (2 * q + 1)) b = b⁻¹ := by
          calc (φ ^ (2 * q + 1)) b = (φ ^ (2 * q)) (φ b) := by
                rw [pow_succ, MulAut.mul_apply]
            _ = (φ ^ (2 * q)) b⁻¹ := by rw [hφb]
            _ = ((φ ^ (2 * q)) b)⁻¹ := by simp
            _ = (((φ ^ 2) ^ q) b)⁻¹ := by rw [pow_mul]
            _ = b⁻¹ := by rw [h2q q]
        rw [h1] at h2
        exact h2
      have hb2 : b ^ 2 = 1 := by
        rw [pow_two]
        exact eq_inv_iff_mul_eq_one.mp hb_eq
      have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
      rw [hordb] at hdvd
      norm_num at hdvd
  intro D hD hDle
  obtain ⟨g, rfl⟩ := hD
  exact h.weak g (hDle.trans (hP'le.trans h.cen_le_nor))

end CFSG.RankThree.PartTwo.Sec21.FF81
