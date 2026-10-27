module

public import CFSG.RankThree.PartOne.F106.NoQD32NADeg

public section

namespace CFSG.RankThree.PartOne.F106.NAD

open Matrix Module Subgroup CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.Q1327T.R8
open scoped commutatorElement

section Inv

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (L : Type) [Field L]
  [Algebra K L] {q : ℕ} {Y : Subgroup (GL ι K)}

theorem eq_one_of_inv_eq {x : L} (hqo : Odd q) (hx : x ^ q = 1) (hxi : x⁻¹ = x) : x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hqo.pos.ne'] at hx
    exact zero_ne_one hx
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hxi]
    exact inv_mul_cancel₀ hx0
  obtain ⟨k, rfl⟩ := hqo
  calc x = x ^ (2 * k + 1) := by rw [pow_succ, pow_mul, hx2, one_pow, one_mul]
    _ = 1 := hx

theorem exists_inv_wts [IsAlgClosed L] (hpL : (q : L) ≠ 0) (h : ClassTwo q q Y) (J : Matrix ι ι K)
    (hJ : J.det ≠ 0)
    (hYJ : ∀ y ∈ Y, ((y : GL ι K) : Matrix ι ι K)ᵀ * J * ((y : GL ι K) : Matrix ι ι K) = J)
    (w : Wts L (Fz Y)) : ∃ w' : Wts L (Fz Y), ∀ g, wv w'.1 g = (wv w.1 g)⁻¹ :=
  ⟨⟨fun e => (w.1 e)⁻¹, joint_inv_ne_bot L (Fz Y) hpL h.hexpF hcommF J hJ
    (fun e => hYJ e (Fz_le Y e.2)) w.2⟩, fun g => wv_inv w.1 g⟩

end Inv

end CFSG.RankThree.PartOne.F106.NAD

namespace CFSG.RankThree.PartOne.F106

open Matrix Module CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.Q1327T.R8
  CFSG.RankThree.PartOne.F106.NAD
open scoped commutatorElement

theorem na_deg_form {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqK : (q : K) ≠ 0) (Y : Subgroup (GL ι K))
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hYJ : ∀ y ∈ Y, ((y : GL ι K) : Matrix ι ι K)ᵀ * J * ((y : GL ι K) : Matrix ι ι K) = J) :
    3 * q ≤ Fintype.card ι := by
  classical
  have hC : ClassTwo q q Y := ⟨hq, fun e he => hexp e (Fz_le Y he),
    fun _ ha _ hb => hexp _ (Fz_le Y (comm_mem_Fz hcl ha hb)), hcl⟩
  let L := AlgebraicClosure K
  have hpL : (q : L) ≠ 0 := by
    intro h0
    apply hqK
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨a, b, ha, hb, hab⟩ := hC.exists_noncomm h4
  obtain ⟨w₀, hw₀⟩ := hC.exists_sig hpL ha hb hab
  obtain ⟨w₀', hv₀'⟩ := exists_inv_wts L hpL hC J hJ hYJ w₀
  have hne₀ : w₀' ≠ w₀ := by
    intro he
    have h1 : wv w₀.1 ⁅a, b⁆ = (wv w₀.1 ⁅a, b⁆)⁻¹ := by rw [← hv₀', he]
    rw [wv_of_mem w₀.1 (comm_mem_Fz hcl ha hb)] at h1 hw₀
    exact hw₀ (eq_one_of_inv_eq L hodd (weight_pow_eq_one L (Fz Y) hC.hexpF w₀.2 _) h1.symm)
  have hd₀ : q ≤ finrank L ↥(joint L (Fz Y) w₀.1) :=
    q_le_finrank_joint L hq hC.commq hcl w₀.2 ha hb hw₀
  have hd₀' : q ≤ finrank L ↥(joint L (Fz Y) w₀'.1) :=
    q_le_finrank_joint L hq hC.commq hcl w₀'.2 ha hb (by rw [hv₀']; exact inv_ne_one.2 hw₀)
  by_cases hex : ∃ w₁ : Wts L (Fz Y), w₁ ≠ w₀ ∧ w₁ ≠ w₀' ∧
      ∃ a' ∈ Y, ∃ b' ∈ Y, wv w₁.1 ⁅a', b'⁆ ≠ 1
  · obtain ⟨w₁, hne1, hne1', a', ha', b', hb', h'⟩ := hex
    have hd₁ : q ≤ finrank L ↥(joint L (Fz Y) w₁.1) :=
      q_le_finrank_joint L hq hC.commq hcl w₁.2 ha' hb' h'
    have h3 := hC.mul_card_le hpL ({w₀, w₀', w₁} : Finset (Wts L (Fz Y))) (by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hd₀
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hd₀'
      · rw [Finset.mem_singleton.1 hw]
        exact hd₁)
    rw [Finset.card_eq_three.2 ⟨w₀, w₀', w₁, hne₀.symm, hne1.symm, hne1'.symm, rfl⟩] at h3
    omega
  · push Not at hex
    have hnd : ∀ y ∈ Y, (∀ y' ∈ Y, wv w₀.1 ⁅y, y'⁆ = 1) → y ∈ Fz Y := by
      intro y hy hy'
      refine mem_Fz.2 ⟨hy, fun g hg => ?_⟩
      have h1 : ⁅y, g⁆ = 1 := hC.comm_eq_one_of_forall hpL hy hg fun w => by
        by_cases hw : w = w₀
        · rw [hw]
          exact hy' g hg
        · by_cases hw' : w = w₀'
          · rw [hw', hv₀', hy' g hg, inv_one]
          · exact hex w hw hw' y hy g hg
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have h2 := hC.sq_le_finrank h4 ha hb hw₀ hnd
    have h3 := finrank_joint_le L w₀
    have h5 : 3 * q ≤ q ^ 2 := by nlinarith
    omega

end CFSG.RankThree.PartOne.F106
