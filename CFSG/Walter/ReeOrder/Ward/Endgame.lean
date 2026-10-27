module

public import CFSG.Walter.ReeOrder.Ward.Symm
public import CFSG.Walter.ReeOrder.Ward.Sylow8
public import CFSG.Walter.ReeOrder.Ward.Comb
public import CFSG.Walter.ReeOrder.Ward.ArithSeven
public import CFSG.Walter.ReeOrder.Ward.DefectTwo
public import CFSG.Walter.ReeOrder.Ward.PBlock

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

theorem sum_four {α M : Type*} [DecidableEq α] [AddCommMonoid M] {s : Finset α} {o a b c : α}
    (hs : s = {o, a, b, c}) (h₁ : o ≠ a) (h₂ : o ≠ b) (h₃ : o ≠ c) (h₄ : a ≠ b) (h₅ : a ≠ c)
    (h₆ : b ≠ c) (f : α → M) : ∑ x ∈ s, f x = f o + f a + f b + f c := by
  rw [hs, Finset.sum_insert (by simp [h₁, h₂, h₃]), Finset.sum_insert (by simp [h₄, h₅]),
    Finset.sum_pair h₆]
  abel

theorem isSign_of_sq {δ : ℤ} (h : δ * δ = 1) : IsSign δ := by
  have : -1 ≤ δ ∧ δ ≤ 1 := by constructor <;> nlinarith
  rcases (show δ = -1 ∨ δ = 0 ∨ δ = 1 by omega) with h' | h' | h'
  · exact Or.inr h'
  · rw [h'] at h; norm_num at h
  · exact Or.inl h'

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  (S : WardSetup G L q e)

theorem J_100 {χ : G → ℂ} (h : χ ∈ S.S1) (h2 : S.d2 χ = 0) (h3 : S.d3 χ = 0) :
    χ S.J = S.d1 χ := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inl h), h2, h3]
  simp

theorem J_111 {χ : G → ℂ} (h : χ ∈ S.S1) (h2 : S.d2 χ = S.d1 χ) (h3 : S.d3 χ = S.d1 χ) :
    χ S.J = -e * q * S.d1 χ := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inl h), h2, h3]
  linear_combination (-(S.d1 χ : ℂ)) * S.e_sq_c

theorem J_110 {χ : G → ℂ} (h : χ ∈ S.S1) (h2 : S.d2 χ = S.d1 χ) (h3 : S.d3 χ = 0) :
    χ S.J = -e * S.d1 χ * (((q : ℂ) - e) / 2) := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inl h), h2, h3]
  push_cast
  linear_combination (-(S.d1 χ : ℂ)) * S.e_sq_c

theorem J_101 {χ : G → ℂ} (h : χ ∈ S.S1) (h2 : S.d2 χ = 0) (h3 : S.d3 χ = S.d1 χ) :
    χ S.J = -e * S.d1 χ * (((q : ℂ) - e) / 2) := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inl h), h2, h3]
  push_cast
  linear_combination (-(S.d1 χ : ℂ)) * S.e_sq_c

theorem J_010 {χ : G → ℂ} (h : χ ∈ S.S2) (h1 : S.d1 χ = 0) (h3 : S.d3 χ = 0) :
    χ S.J = -e * S.d2 χ * (((q : ℂ) + e) / 2) := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inr (Or.inl h)), h1, h3]
  push_cast
  ring

theorem J_011 {χ : G → ℂ} (h : χ ∈ S.S2) (h1 : S.d1 χ = 0) (h3 : S.d3 χ = S.d2 χ) :
    χ S.J = -e * S.d2 χ * ((q : ℂ) + e) := by
  rw [S.J_val_P (mem_supp.mp h).1 (Or.inr (Or.inl h)), h1, h3]
  push_cast
  ring

theorem card_K_mul_C : (Nat.card (ConjClasses.mk S.J).carrier : ℂ) *
    Nat.card (Subgroup.centralizer ({S.J} : Set G)) = Nat.card G := by
  exact_mod_cast card_conjClass_mul_card_centralizer S.J

theorem card_K {a : ℤ} (hG : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 2 - 1) * a) :
    (Nat.card (ConjClasses.mk S.J).carrier : ℤ) = q ^ 2 * a := by
  have h := S.card_K_mul_C
  rw [S.card_C] at h
  have hq0 : (q : ℂ) * ((q : ℂ) ^ 2 - 1) ≠ 0 := mul_ne_zero S.q_ne_zero (by
    have : (q : ℤ) ^ 2 - 1 ≠ 0 := by have := S.q_ge; nlinarith
    exact_mod_cast this)
  have hG' : (Nat.card G : ℂ) = q ^ 3 * ((q : ℂ) ^ 2 - 1) * a := by exact_mod_cast hG
  have : ((Nat.card (ConjClasses.mk S.J).carrier : ℤ) : ℂ) = ((q ^ 2 * a : ℤ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ hq0
    rw [h, hG']
    ring
  exact_mod_cast this

theorem sq_cast {δ : ℤ} (h : δ * δ = 1) : (δ : ℂ) ^ 2 = 1 := by
  have : ((δ * δ : ℤ) : ℂ) = 1 := by rw [h]; simp
  push_cast at this
  rw [sq]
  exact this

namespace EtaData

variable {S} (D : S.EtaData)

theorem nu_one_of_real {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hreal : starRingEnd ℂ ∘ χ = χ)
    {t : ℤ} (ht : χ S.J = t) (hodd : Odd t) : nu χ = 1 := by
  obtain ⟨k, hk⟩ := S.deg_parity hχ ht
  exact nu_eq_one hχ hreal (by rw [hk]; obtain ⟨j, hj⟩ := hodd; exact ⟨j + k, by omega⟩)

include D in
theorem eight_case {a₀ : ℤ} (ha₀ : 0 < a₀)
    (hG : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀) {a b c x y : G → ℂ}
    (hS1 : S.S1 = {1, a, b, c}) (hS2 : S.S2 = {b, c, x, y})
    (n1a : (1 : G → ℂ) ≠ a) (n1b : (1 : G → ℂ) ≠ b) (n1c : (1 : G → ℂ) ≠ c) (nab : a ≠ b)
    (nac : a ≠ c) (nbc : b ≠ c) (nbx : b ≠ x) (nby : b ≠ y) (ncx : c ≠ x) (ncy : c ≠ y)
    (nxy : x ≠ y) (ha2 : a ∉ S.S2) (ha3 : a ∉ S.S3) (hb3 : b ∈ S.S3) (hc3 : c ∈ S.S3)
    (hx1 : x ∉ S.S1) (hx3 : x ∉ S.S3) (hy1 : y ∉ S.S1) (hy3 : y ∉ S.S3) :
    e = -1 ∧ (∃ k : ℕ, 1 ≤ k ∧ (q : ℤ) = 3 ^ (2 * k + 1)) ∧
      (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀ = (q : ℤ) ^ 3 * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) - 1) := by
  obtain ⟨p, m, hp, hqpm⟩ := S.q_pow
  have hqpm' : (q : ℤ) = (p : ℤ) ^ m := by rw [hqpm]; push_cast; ring
  have ha1 : a ∈ S.S1 := by rw [hS1]; simp
  have hb1 : b ∈ S.S1 := by rw [hS1]; simp
  have hc1 : c ∈ S.S1 := by rw [hS1]; simp
  have hb2 : b ∈ S.S2 := by rw [hS2]; simp
  have hc2 : c ∈ S.S2 := by rw [hS2]; simp
  have hx2 : x ∈ S.S2 := by rw [hS2]; simp
  have hy2 : y ∈ S.S2 := by rw [hS2]; simp
  have haI := (mem_supp.mp ha1).1
  have hbI := (mem_supp.mp hb1).1
  have hcI := (mem_supp.mp hc1).1
  have hxI := (mem_supp.mp hx2).1
  have hyI := (mem_supp.mp hy2).1
  have ra2 : S.d2 a = 0 := S.van2 haI ha2
  have ra3 : S.d3 a = 0 := S.van3 haI ha3
  have rb2 : S.d2 b = S.d1 b := (S.agree12 hb1 hb2).symm
  have rb3 : S.d3 b = S.d1 b := (S.agree13 hb1 hb3).symm
  have rc2 : S.d2 c = S.d1 c := (S.agree12 hc1 hc2).symm
  have rc3 : S.d3 c = S.d1 c := (S.agree13 hc1 hc3).symm
  have rx1 : S.d1 x = 0 := S.van1 hxI hx1
  have rx3 : S.d3 x = 0 := S.van3 hxI hx3
  have ry1 : S.d1 y = 0 := S.van1 hyI hy1
  have ry3 : S.d3 y = 0 := S.van3 hyI hy3
  have r1 := S.one_row
  have sa := S.sq1 ha1
  have sb := S.sq1 hb1
  have sc := S.sq1 hc1
  have sx := S.sq2 hx2
  have sy := S.sq2 hy2
  have za := D.z_S1 ha1
  have zb := D.z_S1 hb1
  have zc := D.z_S1 hc1
  have hee := S.W.e_sq
  have hee' := S.e_sq_c
  have Ja := S.J_100 ha1 ra2 ra3
  have Jb := S.J_111 hb1 rb2 rb3
  have Jc := S.J_111 hc1 rc2 rc3
  have Jx := S.J_010 hx2 rx1 rx3
  have Jy := S.J_010 hy2 ry1 ry3
  have Ja' : a S.J = ((S.d1 a : ℤ) : ℂ) := Ja
  have Jb' : b S.J = ((-e * q * S.d1 b : ℤ) : ℂ) := by rw [Jb]; push_cast; ring
  have Jc' : c S.J = ((-e * q * S.d1 c : ℤ) : ℂ) := by rw [Jc]; push_cast; ring
  have pa := deg_pos haI
  have pb := deg_pos hbI
  have pc := deg_pos hcI
  have pxd := deg_pos hxI
  have pyd := deg_pos hyI
  have hd1 : deg (1 : G → ℂ) = 1 := by
    have : ((deg (1 : G → ℂ) : ℤ) : ℂ) = 1 := by rw [deg_eq (one_mem_blocksIrr G)]; rfl
    exact_mod_cast this
  have hGc : (Nat.card G : ℂ) = ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) := by
    have : ((Nat.card G : ℤ) : ℂ) = ((q ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀ : ℤ) : ℂ) := by rw [hG]
    push_cast at this ⊢
    exact this
  have hK := S.card_K hG
  have hdη := D.dη_pos
  have R1 := D.R1
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, z_one (S := S)] at R1
  have O2 := D.O2
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.2.1, ra2, rb2, rc2] at O2
  have R3 := S.R3
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, hd1] at R3
  have R2 := D.R2
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, z_one (S := S), hd1] at R2
  have hreal1 : starRingEnd ℂ ∘ (1 : G → ℂ) = 1 := by funext g; simp
  have hcd1 : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → S.d1 (starRingEnd ℂ ∘ χ) = S.d1 χ :=
    fun h => S.conj_d1 h
  have hcd23 : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → (S.d2 χ = 0 ∧ S.d3 χ = 0) →
      (S.d2 (starRingEnd ℂ ∘ χ) = 0 ∧ S.d3 (starRingEnd ℂ ∘ χ) = 0) := by
    intro χ h ⟨h2, h3⟩
    rw [S.conj_d2 h, S.conj_d3 h]
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  have hcd2 : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → S.d2 χ = S.d1 χ → S.d3 χ = S.d1 χ →
      S.d2 (starRingEnd ℂ ∘ χ) = S.d1 χ := by
    intro χ h h2 h3
    rw [S.conj_d2 h]
    split_ifs <;> assumption
  have hreal_bc : starRingEnd ℂ ∘ b = b ∧ starRingEnd ℂ ∘ c = c := by
    have hmem : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → S.d1 χ ≠ 0 → S.d2 χ = S.d1 χ →
        S.d3 χ = S.d1 χ → starRingEnd ℂ ∘ χ = b ∨ starRingEnd ℂ ∘ χ = c := by
      intro χ h h0 h2 h3
      have hI := irr_conj h
      have h1' : starRingEnd ℂ ∘ χ ∈ S.S1 := mem_supp.mpr ⟨hI, by rw [hcd1 h]; exact h0⟩
      have h2' : starRingEnd ℂ ∘ χ ∈ S.S2 := mem_supp.mpr ⟨hI, by rw [hcd2 h h2 h3]; exact h0⟩
      rw [hS1] at h1'
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1'
      rcases h1' with h' | h' | h' | h'
      · exfalso; rw [h'] at h2'; exact S.one_not_S2 h2'
      · exfalso; rw [h'] at h2'; exact ha2 h2'
      · exact Or.inl h'
      · exact Or.inr h'
    have hb0 : S.d1 b ≠ 0 := (mem_supp.mp hb1).2
    have hc0 : S.d1 c ≠ 0 := (mem_supp.mp hc1).2
    have hzb := D.conj_z (D.S1_NE hb1)
    have hzc := D.conj_z (D.S1_NE hc1)
    constructor
    · rcases hmem hbI hb0 rb2 rb3 with h | h
      · exact h
      · exfalso
        have hd : S.d1 c = S.d1 b := by rw [← h, hcd1 hbI]
        have hz : z (S := S) c = z (S := S) b := by
          rw [← h]; exact hzb (by rw [h]; exact D.S1_NE hc1)
        rw [hd, hz] at O2
        have h0 : S.d1 b * z (S := S) b = 0 := by linarith
        have h1 : (S.d1 b * z (S := S) b) * (S.d1 b * z (S := S) b) = 1 := by
          rw [mul_mul_mul_comm, sb, zb, one_mul]
        rw [h0, mul_zero] at h1
        exact zero_ne_one h1
    · rcases hmem hcI hc0 rc2 rc3 with h | h
      · exfalso
        have hd : S.d1 b = S.d1 c := by rw [← h, hcd1 hcI]
        have hz : z (S := S) b = z (S := S) c := by
          rw [← h]; exact hzc (by rw [h]; exact D.S1_NE hb1)
        rw [hd, hz] at O2
        have h0 : S.d1 c * z (S := S) c = 0 := by linarith
        have h1 : (S.d1 c * z (S := S) c) * (S.d1 c * z (S := S) c) = 1 := by
          rw [mul_mul_mul_comm, sc, zc, one_mul]
        rw [h0, mul_zero] at h1
        exact zero_ne_one h1
      · exact h
  have hreal_a : starRingEnd ℂ ∘ a = a := by
    have hI := irr_conj haI
    have ha0 : S.d1 a ≠ 0 := (mem_supp.mp ha1).2
    have h1' : starRingEnd ℂ ∘ a ∈ S.S1 := mem_supp.mpr ⟨hI, by rw [hcd1 haI]; exact ha0⟩
    have h2' : starRingEnd ℂ ∘ a ∉ S.S2 := fun h => (mem_supp.mp h).2 (hcd23 haI ⟨ra2, ra3⟩).1
    rw [hS1] at h1'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1'
    rcases h1' with h' | h' | h' | h'
    · exfalso
      apply n1a
      have := congrArg (starRingEnd ℂ ∘ ·) h'
      simp only [conj_conj_fun] at this
      rw [this, hreal1]
    · exact h'
    · exact absurd (h' ▸ hb2) h2'
    · exact absurd (h' ▸ hc2) h2'
  have hodd_q : Odd (q : ℤ) := by
    obtain ⟨k, hk⟩ := S.W.q_odd
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hoddsign : ∀ {δ : ℤ}, δ * δ = 1 → Odd δ := by
    intro δ h
    rcases isSign_of_sq h with h' | h' <;> rw [h'] <;> decide
  have hoddb : Odd (-e * q * S.d1 b) := by
    have h1 : Odd (-e) := hoddsign (by linear_combination hee)
    exact (h1.mul hodd_q).mul (hoddsign sb)
  have hoddc : Odd (-e * q * S.d1 c) := by
    have h1 : Odd (-e) := hoddsign (by linear_combination hee)
    exact (h1.mul hodd_q).mul (hoddsign sc)
  have nu1 : nu (1 : G → ℂ) = 1 :=
    nu_eq_one (one_mem_blocksIrr G) hreal1 (by rw [hd1]; decide)
  have nua : nu a = 1 := nu_one_of_real (S := S) haI hreal_a Ja' (hoddsign sa)
  have nub : nu b = 1 := nu_one_of_real (S := S) hbI hreal_bc.1 Jb' hoddb
  have nuc : nu c = 1 := nu_one_of_real (S := S) hcI hreal_bc.2 Jc' hoddc
  have FS := S.FS1
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, nu1, nua, nub, nuc, r1.1] at FS
  have hdeg_eq : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → χ 1 = ((deg χ : ℤ) : ℂ) :=
    fun h => (deg_eq h).symm
  have h6c : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
      (1 + ((S.d1 a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
        ((S.d1 b : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg b : ℤ) : ℂ) +
        ((S.d1 c : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg c : ℤ) : ℂ)) =
      (q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) ^ 2 * ((q : ℂ) + e) := by
    rw [← hGc, ← S.formula_S1, sum_four hS1 n1a n1b n1c nab nac nbc, Ja, Jb, Jc,
      hdeg_eq haI, hdeg_eq hbI, hdeg_eq hcI, r1.1]
    have sa' := sq_cast sa
    have sb' := sq_cast sb
    have sc' := sq_cast sc
    congr 1
    simp only [Pi.one_apply, one_pow, Int.cast_one, div_one, mul_one]
    rw [show ((S.d1 a : ℤ) : ℂ) ^ 2 * (S.d1 a : ℂ) = S.d1 a by rw [sa', one_mul],
      show (-(e : ℂ) * q * (S.d1 b : ℂ)) ^ 2 * (S.d1 b : ℂ) = (S.d1 b : ℂ) * q ^ 2 by
        rw [mul_pow, mul_pow, sb', neg_sq, sq (e : ℂ), hee']; ring,
      show (-(e : ℂ) * q * (S.d1 c : ℂ)) ^ 2 * (S.d1 c : ℂ) = (S.d1 c : ℂ) * q ^ 2 by
        rw [mul_pow, mul_pow, sc', neg_sq, sq (e : ℂ), hee']; ring]
  have hε := D.ε_sq
  have hε' : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast hε
  have hdη0 : (D.dη : ℂ) ≠ 0 := by exact_mod_cast hdη.ne'
  have hε0 : (D.ε : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hε'; exact zero_ne_one hε'
  have h8c : ((q : ℂ) + e) * ((q : ℂ) * ((q : ℂ) ^ 2 - 1)) ^ 2 =
      ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
        (2 * ((q : ℂ) - e) ^ 2 * e / ((D.ε * D.dη : ℤ) : ℂ) + 1 +
          ((z (S := S) a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
          ((z (S := S) b : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg b : ℤ) : ℂ) +
          ((z (S := S) c : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg c : ℤ) : ℂ)) := by
    have h := D.F8
    rw [S.card_C, hGc, sum_four hS1 n1a n1b n1c nab nac nbc, Ja, Jb, Jc, z_one (S := S),
      hd1] at h
    rw [h]
    have sa' := sq_cast sa
    have sb' := sq_cast sb
    have sc' := sq_cast sc
    have hfrac : 2 * ((q : ℂ) - e) ^ 2 * D.ε * e / D.dη =
        2 * ((q : ℂ) - e) ^ 2 * e / ((D.ε * D.dη : ℤ) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hdη0 (mul_ne_zero hε0 hdη0)]
      linear_combination (2 * ((q : ℂ) - e) ^ 2 * e * D.dη) * hε'
    have hb2' : (-(e : ℂ) * q * (S.d1 b : ℂ)) ^ 2 = (q : ℂ) ^ 2 := by
      rw [mul_pow, mul_pow, sb', neg_sq, sq (e : ℂ), hee']; ring
    have hc2' : (-(e : ℂ) * q * (S.d1 c : ℂ)) ^ 2 = (q : ℂ) ^ 2 := by
      rw [mul_pow, mul_pow, sc', neg_sq, sq (e : ℂ), hee']; ring
    rw [hfrac, sa', hb2', hc2']
    simp only [Pi.one_apply, one_pow, Int.cast_one, div_one, one_mul]
    ring
  have hx0 : S.d2 x ≠ 0 := (mem_supp.mp hx2).2
  have hy0 : S.d2 y ≠ 0 := (mem_supp.mp hy2).2
  have hf5 : S.d2 x * deg x ≠ 0 := mul_ne_zero hx0 pxd.ne'
  have hf6 : S.d2 y * deg y ≠ 0 := mul_ne_zero hy0 pyd.ne'
  have h20c : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
      ((q : ℂ) ^ 2 * ((S.d1 b : ℤ) : ℂ) / ((deg b : ℤ) : ℂ) +
        (q : ℂ) ^ 2 * ((S.d1 c : ℤ) : ℂ) / ((deg c : ℤ) : ℂ) +
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 x * deg x : ℤ) : ℂ)) +
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 y * deg y : ℤ) : ℂ))) =
      -e * (q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) * ((q : ℂ) + e) * (3 * (q : ℂ) + e) := by
    rw [← hGc, ← S.formula_S2, sum_four hS2 nbc nbx nby ncx ncy nxy, Jb, Jc, Jx, Jy,
      hdeg_eq hbI, hdeg_eq hcI, hdeg_eq hxI, hdeg_eq hyI, rb2, rc2]
    have sb' := sq_cast sb
    have sc' := sq_cast sc
    have sx' := sq_cast sx
    have sy' := sq_cast sy
    have hpx : (deg x : ℂ) ≠ 0 := by exact_mod_cast pxd.ne'
    have hpy : (deg y : ℂ) ≠ 0 := by exact_mod_cast pyd.ne'
    have hx0' : (S.d2 x : ℂ) ≠ 0 := by exact_mod_cast hx0
    have hy0' : (S.d2 y : ℂ) ≠ 0 := by exact_mod_cast hy0
    congr 1
    push_cast
    have tb : (-(e : ℂ) * q * (S.d1 b : ℂ)) ^ 2 * (S.d1 b : ℂ) / (deg b : ℂ) =
        (q : ℂ) ^ 2 * (S.d1 b : ℂ) / (deg b : ℂ) := by
      rw [mul_pow, mul_pow, sb', neg_sq, sq (e : ℂ), hee']; ring
    have tc : (-(e : ℂ) * q * (S.d1 c : ℂ)) ^ 2 * (S.d1 c : ℂ) / (deg c : ℂ) =
        (q : ℂ) ^ 2 * (S.d1 c : ℂ) / (deg c : ℂ) := by
      rw [mul_pow, mul_pow, sc', neg_sq, sq (e : ℂ), hee']; ring
    have tx : (-(e : ℂ) * (S.d2 x : ℂ) * (((q : ℂ) + e) / 2)) ^ 2 * (S.d2 x : ℂ) / (deg x : ℂ) =
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 x : ℂ) * (deg x : ℂ))) := by
      rw [div_eq_div_iff hpx (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (mul_ne_zero hx0' hpx))]
      rw [mul_pow, mul_pow, neg_sq, sq (e : ℂ), hee', sq (S.d2 x : ℂ)]
      have : (S.d2 x : ℂ) * S.d2 x = 1 := by rw [← sq]; exact sx'
      linear_combination (((q : ℂ) + e) ^ 2 * (deg x : ℂ) * ((S.d2 x : ℂ) * S.d2 x + 1)) * this
    have ty : (-(e : ℂ) * (S.d2 y : ℂ) * (((q : ℂ) + e) / 2)) ^ 2 * (S.d2 y : ℂ) / (deg y : ℂ) =
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 y : ℂ) * (deg y : ℂ))) := by
      rw [div_eq_div_iff hpy (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (mul_ne_zero hy0' hpy))]
      rw [mul_pow, mul_pow, neg_sq, sq (e : ℂ), hee', sq (S.d2 y : ℂ)]
      have : (S.d2 y : ℂ) * S.d2 y = 1 := by rw [← sq]; exact sy'
      linear_combination (((q : ℂ) + e) ^ 2 * (deg y : ℂ) * ((S.d2 y : ℂ) * S.d2 y + 1)) * this
    rw [tb, tc, tx, ty]
  have hdeg2 := S.deg2_S2
  rw [sum_four hS2 nbc nbx nby ncx ncy nxy, rb2, rc2] at hdeg2
  have hint₃ : deg b ∣ (q : ℤ) ^ 2 * a₀ * (-e * q * S.d1 b) := by
    have := omega_dvd hbI S.J Jb'
    rwa [hK] at this
  have hint₄ : deg c ∣ (q : ℤ) ^ 2 * a₀ * (-e * q * S.d1 c) := by
    have := omega_dvd hcI S.J Jc'
    rwa [hK] at this
  have hεz : D.ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hε; exact zero_ne_one hε
  have hq27 : (27 : ℤ) ≤ q := by exact_mod_cast S.q_ge
  exact eight_arith (q := (q : ℤ)) (e := e) (a := a₀) (d₂ := deg a) (d₃ := deg b)
    (d₄ := deg c) (δ₂ := S.d1 a) (δ₃ := S.d1 b) (δ₄ := S.d1 c) (e₂ := z (S := S) a)
    (e₃ := z (S := S) b) (e₄ := z (S := S) c) (D := D.ε * D.dη) (f₅ := S.d2 x * deg x)
    (f₆ := S.d2 y * deg y) (R := Nat.card S.W.Ro) hp hqpm' hq27 S.W.e_eq S.W.q_mod ha₀
    (isSign_of_sq sa) (isSign_of_sq sb) (isSign_of_sq sc) (isSign_of_sq zb) pa pb pc
    (mul_ne_zero hεz hdη.ne') hf5 hf6
    (by apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h6c; linear_combination h6c)
    (by apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h8c; linear_combination h8c)
    (by linear_combination R1) (by linear_combination R2) (by linear_combination R3)
    (by linear_combination O2) (by linear_combination FS) S.W.Ro_card
    (D.restrict_Ro (D.S1_NE ha1)) (S.deg_parity haI Ja') (S.sylow8 haI Ja') hint₃ hint₄
    (by apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h20c
        linear_combination h20c)
    (by linear_combination hdeg2)

include D in
theorem seven_case {a₀ : ℤ} (ha₀ : 0 < a₀)
    (hG : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀) {a b c x w : G → ℂ}
    (hS1 : S.S1 = {1, a, b, c}) (hS2 : S.S2 = {a, c, x, w})
    (n1a : (1 : G → ℂ) ≠ a) (n1b : (1 : G → ℂ) ≠ b) (n1c : (1 : G → ℂ) ≠ c) (nab : a ≠ b)
    (nac : a ≠ c) (nbc : b ≠ c) (nax : a ≠ x) (naw : a ≠ w) (ncx : c ≠ x) (ncw : c ≠ w)
    (nxw : x ≠ w) (ha3 : a ∉ S.S3) (hb2 : b ∉ S.S2) (hb3 : b ∈ S.S3) (hc3 : c ∈ S.S3)
    (hx1 : x ∉ S.S1) (hx3 : x ∉ S.S3) (hw1 : w ∉ S.S1) (hw3 : w ∈ S.S3) : False := by
  obtain ⟨p, m, hp, hqpm⟩ := S.q_pow
  have hqpm' : (q : ℤ) = (p : ℤ) ^ m := by rw [hqpm]; push_cast; ring
  have ha1 : a ∈ S.S1 := by rw [hS1]; simp
  have hb1 : b ∈ S.S1 := by rw [hS1]; simp
  have hc1 : c ∈ S.S1 := by rw [hS1]; simp
  have ha2 : a ∈ S.S2 := by rw [hS2]; simp
  have hc2 : c ∈ S.S2 := by rw [hS2]; simp
  have hx2 : x ∈ S.S2 := by rw [hS2]; simp
  have hw2 : w ∈ S.S2 := by rw [hS2]; simp
  have haI := (mem_supp.mp ha1).1
  have hbI := (mem_supp.mp hb1).1
  have hcI := (mem_supp.mp hc1).1
  have hxI := (mem_supp.mp hx2).1
  have hwI := (mem_supp.mp hw2).1
  have ha0 : S.d1 a ≠ 0 := (mem_supp.mp ha1).2
  have hc0 : S.d1 c ≠ 0 := (mem_supp.mp hc1).2
  have ra2 : S.d2 a = S.d1 a := (S.agree12 ha1 ha2).symm
  have ra3 : S.d3 a = 0 := S.van3 haI ha3
  have rb2 : S.d2 b = 0 := S.van2 hbI hb2
  have rb3 : S.d3 b = S.d1 b := (S.agree13 hb1 hb3).symm
  have rc2 : S.d2 c = S.d1 c := (S.agree12 hc1 hc2).symm
  have rc3 : S.d3 c = S.d1 c := (S.agree13 hc1 hc3).symm
  have rx1 : S.d1 x = 0 := S.van1 hxI hx1
  have rx3 : S.d3 x = 0 := S.van3 hxI hx3
  have qw1 : S.d1 w = 0 := S.van1 hwI hw1
  have qw3 : S.d3 w = S.d2 w := (S.agree23 hw2 hw3).symm
  have r1 := S.one_row
  have hpa : S.pw a = b := by
    have hI := S.pw_mem haI
    have h1' : S.pw a ∈ S.S1 := mem_supp.mpr ⟨hI, by rw [S.pw_d1 haI]; exact ha0⟩
    have h2' : S.pw a ∉ S.S2 := fun h => (mem_supp.mp h).2 (by rw [S.pw_d2 haI, ra3])
    have h3' : S.pw a ∈ S.S3 := mem_supp.mpr ⟨hI, by rw [S.pw_d3 haI, ra2]; exact ha0⟩
    rw [hS1] at h1'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1'
    rcases h1' with h' | h' | h' | h'
    · exfalso; rw [h'] at h3'; exact S.one_not_S3 h3'
    · exfalso; rw [h'] at h3'; exact ha3 h3'
    · exact h'
    · exfalso; rw [h'] at h2'; exact h2' hc2
  have rdb : deg b = deg a := by rw [← hpa, S.pw_deg haI]
  have rd1b : S.d1 b = S.d1 a := by rw [← hpa, S.pw_d1 haI]
  have rzb : z (S := S) b = z (S := S) a := by
    rw [← hpa]; exact D.pw_z (D.S1_NE ha1) (by rw [hpa]; exact D.S1_NE hb1)
  have rnub : nu b = nu a := by rw [← hpa, S.pw_nu haI]
  have sa := S.sq1 ha1
  have sc := S.sq1 hc1
  have sx := S.sq2 hx2
  have sw := S.sq2 hw2
  have hee := S.W.e_sq
  have hee' := S.e_sq_c
  obtain ⟨h, hh⟩ : ∃ h : ℤ, 2 * h = q - e := ⟨((q : ℤ) - e) / 2, by have := S.W.q_mod; omega⟩
  have hhc : ((q : ℂ) - e) / 2 = (h : ℂ) := by
    have : ((2 * h : ℤ) : ℂ) = (((q : ℤ) - e : ℤ) : ℂ) := by rw [hh]
    push_cast at this
    linear_combination (-1 / 2 : ℂ) * this
  have Ja := S.J_110 ha1 ra2 ra3
  have Jb := S.J_101 hb1 rb2 rb3
  have Jc := S.J_111 hc1 rc2 rc3
  have Jx := S.J_010 hx2 rx1 rx3
  have Jw := S.J_011 hw2 qw1 qw3
  have Ja' : a S.J = ((-e * S.d1 a * h : ℤ) : ℂ) := by rw [Ja, hhc]; push_cast; ring
  have Jc' : c S.J = ((-e * q * S.d1 c : ℤ) : ℂ) := by rw [Jc]; push_cast; ring
  have pa := deg_pos haI
  have pc := deg_pos hcI
  have pxd := deg_pos hxI
  have pwd := deg_pos hwI
  have hd1 : deg (1 : G → ℂ) = 1 := by
    have : ((deg (1 : G → ℂ) : ℤ) : ℂ) = 1 := by rw [deg_eq (one_mem_blocksIrr G)]; rfl
    exact_mod_cast this
  have hGc : (Nat.card G : ℂ) = ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) := by
    have : ((Nat.card G : ℤ) : ℂ) = ((q ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀ : ℤ) : ℂ) := by rw [hG]
    push_cast at this ⊢
    exact this
  have hK := S.card_K hG
  have R1 := D.R1
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, z_one (S := S), rd1b, rzb] at R1
  have O2 := D.O2
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.2.1, ra2, rb2, rc2] at O2
  have R3 := S.R3
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, hd1, rd1b, rdb] at R3
  have hreal1 : starRingEnd ℂ ∘ (1 : G → ℂ) = 1 := by funext g; simp
  have hreal_c : starRingEnd ℂ ∘ c = c := by
    have hI := irr_conj hcI
    have h1' : starRingEnd ℂ ∘ c ∈ S.S1 := mem_supp.mpr ⟨hI, by rw [S.conj_d1 hcI]; exact hc0⟩
    have h2' : starRingEnd ℂ ∘ c ∈ S.S2 := mem_supp.mpr ⟨hI, by
      rw [S.conj_d2 hcI]; split_ifs <;> simpa only [rc2, rc3] using hc0⟩
    have h3' : starRingEnd ℂ ∘ c ∈ S.S3 := mem_supp.mpr ⟨hI, by
      rw [S.conj_d3 hcI]; split_ifs <;> simpa only [rc2, rc3] using hc0⟩
    rw [hS1] at h1'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1'
    rcases h1' with h' | h' | h' | h'
    · exfalso; rw [h'] at h2'; exact S.one_not_S2 h2'
    · exfalso; rw [h'] at h3'; exact ha3 h3'
    · exfalso; rw [h'] at h2'; exact hb2 h2'
    · exact h'
  have hodd_q : Odd (q : ℤ) := by
    obtain ⟨k, hk⟩ := S.W.q_odd
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hoddsign : ∀ {δ : ℤ}, δ * δ = 1 → Odd δ := by
    intro δ h
    rcases isSign_of_sq h with h' | h' <;> rw [h'] <;> decide
  have hoddc : Odd (-e * q * S.d1 c) := by
    have h1 : Odd (-e) := hoddsign (by linear_combination hee)
    exact (h1.mul hodd_q).mul (hoddsign sc)
  have nu1 : nu (1 : G → ℂ) = 1 :=
    nu_eq_one (one_mem_blocksIrr G) hreal1 (by rw [hd1]; decide)
  have nuc : nu c = 1 := nu_one_of_real (S := S) hcI hreal_c Jc' hoddc
  have FS := S.FS1
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, nu1, rnub, nuc, r1.1, rd1b] at FS
  have hνe : e = -1 → nu a = 0 := by
    intro he1
    rw [nu_eq_zero_iff haI]
    intro hreal
    have h2 := S.conj_d2 haI
    rw [hreal, ite_eq_left he1, ra2, ra3] at h2
    exact ha0 h2
  have hνe' : e = 1 → nu a ≠ 0 := by
    intro he1 h0
    rw [nu_eq_zero_iff haI] at h0
    apply h0
    have hne : e ≠ -1 := by rw [he1]; norm_num
    have hI := irr_conj haI
    have h1' : starRingEnd ℂ ∘ a ∈ S.S1 := mem_supp.mpr ⟨hI, by rw [S.conj_d1 haI]; exact ha0⟩
    have h2' : starRingEnd ℂ ∘ a ∈ S.S2 := mem_supp.mpr ⟨hI, by
      rw [S.conj_d2 haI, ite_eq_right hne, ra2]; exact ha0⟩
    have h3' : starRingEnd ℂ ∘ a ∉ S.S3 := fun h => (mem_supp.mp h).2 (by
      rw [S.conj_d3 haI, ite_eq_right hne, ra3])
    rw [hS1] at h1'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1'
    rcases h1' with h' | h' | h' | h'
    · exfalso; rw [h'] at h2'; exact S.one_not_S2 h2'
    · exact h'
    · exfalso; rw [h'] at h2'; exact hb2 h2'
    · exfalso; rw [h'] at h3'; exact h3' hc3
  have hdeg_eq : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → χ 1 = ((deg χ : ℤ) : ℂ) :=
    fun h => (deg_eq h).symm
  have sa' := sq_cast sa
  have sc' := sq_cast sc
  have ka : (-(e : ℂ) * (S.d1 a : ℂ) * (h : ℂ)) ^ 2 = (h : ℂ) ^ 2 := by
    rw [mul_pow, mul_pow, sa', neg_sq, sq (e : ℂ), hee']; ring
  have kc : (-(e : ℂ) * q * (S.d1 c : ℂ)) ^ 2 = (q : ℂ) ^ 2 := by
    rw [mul_pow, mul_pow, sc', neg_sq, sq (e : ℂ), hee']; ring
  have h6c : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
      (1 + (h : ℂ) ^ 2 * ((S.d1 a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
        (h : ℂ) ^ 2 * ((S.d1 a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
        (q : ℂ) ^ 2 * ((S.d1 c : ℤ) : ℂ) / ((deg c : ℤ) : ℂ)) =
      (q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) ^ 2 * ((q : ℂ) + e) := by
    rw [← hGc, ← S.formula_S1, sum_four hS1 n1a n1b n1c nab nac nbc, Ja, Jb, Jc,
      hdeg_eq haI, hdeg_eq hbI, hdeg_eq hcI, r1.1, rd1b, rdb, hhc]
    congr 1
    simp only [Pi.one_apply, one_pow, Int.cast_one, div_one, mul_one]
    rw [ka, kc]
  have hx0 : S.d2 x ≠ 0 := (mem_supp.mp hx2).2
  have hw0 : S.d2 w ≠ 0 := (mem_supp.mp hw2).2
  have hf5 : S.d2 x * deg x ≠ 0 := mul_ne_zero hx0 pxd.ne'
  have hf7 : S.d2 w * deg w ≠ 0 := mul_ne_zero hw0 pwd.ne'
  have h17c : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
      ((h : ℂ) ^ 2 * ((S.d1 a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
        (q : ℂ) ^ 2 * ((S.d1 c : ℤ) : ℂ) / ((deg c : ℤ) : ℂ) +
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 x * deg x : ℤ) : ℂ)) +
        ((q : ℂ) + e) ^ 2 / ((S.d2 w * deg w : ℤ) : ℂ)) =
      -e * (q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) * ((q : ℂ) + e) * (3 * (q : ℂ) + e) := by
    rw [← hGc, ← S.formula_S2, sum_four hS2 nac nax naw ncx ncw nxw, Ja, Jc, Jx, Jw,
      hdeg_eq haI, hdeg_eq hcI, hdeg_eq hxI, hdeg_eq hwI, ra2, rc2, hhc]
    have sx' := sq_cast sx
    have sw' := sq_cast sw
    have hpx : (deg x : ℂ) ≠ 0 := by exact_mod_cast pxd.ne'
    have hpw : (deg w : ℂ) ≠ 0 := by exact_mod_cast pwd.ne'
    have hx0' : (S.d2 x : ℂ) ≠ 0 := by exact_mod_cast hx0
    have hw0' : (S.d2 w : ℂ) ≠ 0 := by exact_mod_cast hw0
    congr 1
    push_cast
    have tx : (-(e : ℂ) * (S.d2 x : ℂ) * (((q : ℂ) + e) / 2)) ^ 2 * (S.d2 x : ℂ) / (deg x : ℂ) =
        ((q : ℂ) + e) ^ 2 / (4 * ((S.d2 x : ℂ) * (deg x : ℂ))) := by
      rw [div_eq_div_iff hpx (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (mul_ne_zero hx0' hpx))]
      rw [mul_pow, mul_pow, neg_sq, sq (e : ℂ), hee', sq (S.d2 x : ℂ)]
      have : (S.d2 x : ℂ) * S.d2 x = 1 := by rw [← sq]; exact sx'
      linear_combination (((q : ℂ) + e) ^ 2 * (deg x : ℂ) * ((S.d2 x : ℂ) * S.d2 x + 1)) * this
    have tw : (-(e : ℂ) * (S.d2 w : ℂ) * ((q : ℂ) + e)) ^ 2 * (S.d2 w : ℂ) / (deg w : ℂ) =
        ((q : ℂ) + e) ^ 2 / ((S.d2 w : ℂ) * (deg w : ℂ)) := by
      rw [div_eq_div_iff hpw (mul_ne_zero hw0' hpw)]
      rw [mul_pow, mul_pow, neg_sq, sq (e : ℂ), hee', sq (S.d2 w : ℂ)]
      have : (S.d2 w : ℂ) * S.d2 w = 1 := by rw [← sq]; exact sw'
      linear_combination (((q : ℂ) + e) ^ 2 * (deg w : ℂ) * ((S.d2 w : ℂ) * S.d2 w + 1)) * this
    rw [ka, kc, tx, tw]
  have hdeg2 := S.deg2_S2
  rw [sum_four hS2 nac nax naw ncx ncw nxw, ra2, rc2] at hdeg2
  have hint : deg a ∣ (q : ℤ) ^ 2 * a₀ * (-e * S.d1 a * h) := by
    have := omega_dvd haI S.J Ja'
    rwa [hK] at this
  have hq27 : (27 : ℤ) ≤ q := by exact_mod_cast S.q_ge
  exact seven_arith (q := (q : ℤ)) (e := e) (a := a₀) (d₂ := deg a) (d₄ := deg c)
    (δ₂ := S.d1 a) (δ₄ := S.d1 c) (e₂ := z (S := S) a) (e₄ := z (S := S) c) (ν₂ := nu a)
    (f₅ := S.d2 x * deg x) (f₇ := S.d2 w * deg w) (h := h) (R := Nat.card S.W.Ro)
    hp hqpm' hq27 S.W.e_eq S.W.q_mod ha₀ (isSign_of_sq sa) (isSign_of_sq sc) nu_cases hνe hνe'
    pa pc hf5 hf7 hh S.W.Ro_card (by linear_combination FS) (by linear_combination O2)
    (by linear_combination R1) (by linear_combination R3)
    (by apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h6c; linear_combination h6c)
    hint (D.restrict_Ro (D.S1_NE hc1))
    (by apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h17c
        linear_combination h17c)
    (by linear_combination hdeg2)

end EtaData

include S in
theorem order_of_setup : e = -1 ∧ (∃ k : ℕ, 1 ≤ k ∧ q = 3 ^ (2 * k + 1)) ∧
    Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  obtain ⟨D⟩ := S.exists_etaData
  obtain ⟨a₀, ha₀, hG⟩ := S.card_dvd
  rcases three_sets S.S1 S.S2 S.S3 1 S.card_S1 S.card_S2 S.card_S12 S.card_S13 S.card_S23
      S.one_S1 S.one_not_S2 S.one_not_S3 with
    ⟨a, b, c, x, y, hS1, hS2, n1a, n1b, n1c, nab, nac, nbc, nbx, nby, ncx, ncy, nxy, ha2, ha3,
      hb3, hc3, hx1, hx3, hy1, hy3⟩ |
    ⟨a, b, c, x, w, hS1, hS2, n1a, n1b, n1c, nab, nac, nbc, nax, naw, ncx, ncw, nxw, ha3, hb2,
      hb3, hc3, hx1, hx3, hw1, hw3⟩
  · obtain ⟨he, ⟨k, hk, hq⟩, hcard⟩ := D.eight_case ha₀ hG hS1 hS2 n1a n1b n1c nab nac nbc nbx
      nby ncx ncy nxy ha2 ha3 hb3 hc3 hx1 hx3 hy1 hy3
    refine ⟨he, ⟨k, hk, by exact_mod_cast hq⟩, ?_⟩
    have hq1 : 1 ≤ q := by have := S.q_ge; omega
    have : (Nat.card G : ℤ) = ((q ^ 3 * (q ^ 3 + 1) * (q - 1) : ℕ) : ℤ) := by
      rw [hG, hcard]
      push_cast [Nat.cast_sub hq1]
      ring
    exact_mod_cast this
  · exact (D.seven_case ha₀ hG hS1 hS2 n1a n1b n1c nab nac nbc nax naw ncx ncw nxw ha3 hb2 hb3
      hc3 hx1 hx3 hw1 hw3).elim

end WardSetup

end CFSG.Walter.Ward
