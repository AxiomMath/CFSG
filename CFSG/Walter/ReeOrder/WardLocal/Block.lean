module

public import CFSG.Walter.ReeOrder.WardLocal.Arith
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.ReeOrder.Ward.Endgame

public section

open scoped BigOperators Classical

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ}

structure Block (S : WardSetup G L q (-1)) (D : S.EtaData) (m : ℕ) : Type where
  ξ₂ : G → ℂ
  ξ₃ : G → ℂ
  ξ₄ : G → ℂ
  ξ₅ : G → ℂ
  ξ₆ : G → ℂ
  hS1 : S.S1 = {1, ξ₂, ξ₃, ξ₄}
  hS2 : S.S2 = {ξ₃, ξ₄, ξ₅, ξ₆}
  n12 : (1 : G → ℂ) ≠ ξ₂
  n13 : (1 : G → ℂ) ≠ ξ₃
  n14 : (1 : G → ℂ) ≠ ξ₄
  n23 : ξ₂ ≠ ξ₃
  n24 : ξ₂ ≠ ξ₄
  n34 : ξ₃ ≠ ξ₄
  n35 : ξ₃ ≠ ξ₅
  n36 : ξ₃ ≠ ξ₆
  n45 : ξ₄ ≠ ξ₅
  n46 : ξ₄ ≠ ξ₆
  n56 : ξ₅ ≠ ξ₆
  ξ₂_S2 : ξ₂ ∉ S.S2
  ξ₂_S3 : ξ₂ ∉ S.S3
  ξ₃_S3 : ξ₃ ∈ S.S3
  ξ₄_S3 : ξ₄ ∈ S.S3
  ξ₅_S1 : ξ₅ ∉ S.S1
  ξ₅_S3 : ξ₅ ∉ S.S3
  ξ₆_S1 : ξ₆ ∉ S.S1
  ξ₆_S3 : ξ₆ ∉ S.S3
  d1_2 : S.d1 ξ₂ = -1
  d1_3 : S.d1 ξ₃ = 1
  d1_4 : S.d1 ξ₄ = -1
  d2_5 : S.d2 ξ₅ = -1
  d2_6 : S.d2 ξ₆ = 1
  deg_2 : deg ξ₂ = (q : ℤ) ^ 2 - q + 1
  deg_3 : deg ξ₃ = (q : ℤ) ^ 3
  deg_4 : deg ξ₄ = (q : ℤ) * ((q : ℤ) ^ 2 - q + 1)
  deg_5 : 2 * deg ξ₅ = ((q : ℤ) - 1) * m * (q + 1 + 3 * m)
  deg_6 : 2 * deg ξ₆ = ((q : ℤ) - 1) * m * (q + 1 - 3 * m)
  real_2 : starRingEnd ℂ ∘ ξ₂ = ξ₂
  real_3 : starRingEnd ℂ ∘ ξ₃ = ξ₃
  real_4 : starRingEnd ℂ ∘ ξ₄ = ξ₄
  z_2 : WardSetup.EtaData.z (S := S) ξ₂ = 1
  z_3 : WardSetup.EtaData.z (S := S) ξ₃ = 1
  z_4 : WardSetup.EtaData.z (S := S) ξ₄ = 1
  ε_eq : D.ε = 1
  dη_eq : D.dη = (q : ℤ) ^ 3 + 1

namespace Block

variable {S : WardSetup G L q (-1)} (D : S.EtaData)

theorem eight_data {a₀ : ℤ} (ha₀ : 0 < a₀)
    (hG : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 2 - 1) * a₀) {a b c x y : G → ℂ}
    (hS1 : S.S1 = {1, a, b, c}) (hS2 : S.S2 = {b, c, x, y})
    (n1a : (1 : G → ℂ) ≠ a) (n1b : (1 : G → ℂ) ≠ b) (n1c : (1 : G → ℂ) ≠ c) (nab : a ≠ b)
    (nac : a ≠ c) (nbc : b ≠ c) (ha2 : a ∉ S.S2) (ha3 : a ∉ S.S3) (hb3 : b ∈ S.S3)
    (hc3 : c ∈ S.S3) :
    ∃ b' c' : G → ℂ, ((b' = b ∧ c' = c) ∨ (b' = c ∧ c' = b)) ∧
      S.d1 a = -1 ∧ S.d1 b' = 1 ∧ S.d1 c' = -1 ∧
      WardSetup.EtaData.z (S := S) a = 1 ∧ WardSetup.EtaData.z (S := S) b' = 1 ∧
      WardSetup.EtaData.z (S := S) c' = 1 ∧
      deg a = (q : ℤ) ^ 2 - q + 1 ∧ deg b' = (q : ℤ) ^ 3 ∧ deg c' = q * ((q : ℤ) ^ 2 - q + 1) ∧
      D.ε * D.dη = (q : ℤ) ^ 3 + 1 ∧ a₀ = (q : ℤ) ^ 2 - q + 1 ∧
      starRingEnd ℂ ∘ a = a ∧ starRingEnd ℂ ∘ b = b ∧ starRingEnd ℂ ∘ c = c := by
  obtain ⟨p, mm, hp, hqpm⟩ := S.q_pow
  have hqpm' : (q : ℤ) = (p : ℤ) ^ mm := by rw [hqpm]; push_cast; ring
  have ha1 : a ∈ S.S1 := by rw [hS1]; simp
  have hb1 : b ∈ S.S1 := by rw [hS1]; simp
  have hc1 : c ∈ S.S1 := by rw [hS1]; simp
  have hb2 : b ∈ S.S2 := by rw [hS2]; simp
  have hc2 : c ∈ S.S2 := by rw [hS2]; simp
  have haI := (mem_supp.mp ha1).1
  have hbI := (mem_supp.mp hb1).1
  have hcI := (mem_supp.mp hc1).1
  have ra2 : S.d2 a = 0 := S.van2 haI ha2
  have ra3 : S.d3 a = 0 := S.van3 haI ha3
  have rb2 : S.d2 b = S.d1 b := (S.agree12 hb1 hb2).symm
  have rb3 : S.d3 b = S.d1 b := (S.agree13 hb1 hb3).symm
  have rc2 : S.d2 c = S.d1 c := (S.agree12 hc1 hc2).symm
  have rc3 : S.d3 c = S.d1 c := (S.agree13 hc1 hc3).symm
  have r1 := S.one_row
  have sa := S.sq1 ha1
  have sb := S.sq1 hb1
  have sc := S.sq1 hc1
  have za := D.z_S1 ha1
  have zb := D.z_S1 hb1
  have zc := D.z_S1 hc1
  have hee := S.W.e_sq
  have hee' := S.e_sq_c
  have Ja := S.J_100 ha1 ra2 ra3
  have Jb := S.J_111 hb1 rb2 rb3
  have Jc := S.J_111 hc1 rc2 rc3
  have Ja' : a S.J = ((S.d1 a : ℤ) : ℂ) := Ja
  have Jb' : b S.J = ((-(-1) * q * S.d1 b : ℤ) : ℂ) := by rw [Jb]; push_cast; ring
  have Jc' : c S.J = ((-(-1) * q * S.d1 c : ℤ) : ℂ) := by rw [Jc]; push_cast; ring
  have pa := deg_pos haI
  have pb := deg_pos hbI
  have pc := deg_pos hcI
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
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, WardSetup.EtaData.z_one (S := S)] at R1
  have O2 := D.O2
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.2.1, ra2, rb2, rc2] at O2
  have R3 := S.R3
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, r1.1, hd1] at R3
  have R2 := D.R2
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, WardSetup.EtaData.z_one (S := S), hd1] at R2
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
        have hz : WardSetup.EtaData.z (S := S) c = WardSetup.EtaData.z (S := S) b := by
          rw [← h]; exact hzb (by rw [h]; exact D.S1_NE hc1)
        rw [hd, hz] at O2
        have h0 : S.d1 b * WardSetup.EtaData.z (S := S) b = 0 := by linarith
        have h1 : (S.d1 b * WardSetup.EtaData.z (S := S) b) *
            (S.d1 b * WardSetup.EtaData.z (S := S) b) = 1 := by
          rw [mul_mul_mul_comm, sb, zb, one_mul]
        rw [h0, mul_zero] at h1
        exact zero_ne_one h1
    · rcases hmem hcI hc0 rc2 rc3 with h | h
      · exfalso
        have hd : S.d1 b = S.d1 c := by rw [← h, hcd1 hcI]
        have hz : WardSetup.EtaData.z (S := S) b = WardSetup.EtaData.z (S := S) c := by
          rw [← h]; exact hzc (by rw [h]; exact D.S1_NE hb1)
        rw [hd, hz] at O2
        have h0 : S.d1 c * WardSetup.EtaData.z (S := S) c = 0 := by linarith
        have h1 : (S.d1 c * WardSetup.EtaData.z (S := S) c) *
            (S.d1 c * WardSetup.EtaData.z (S := S) c) = 1 := by
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
  have hoddb : Odd (-(-1) * q * S.d1 b) := by
    have h1 : Odd (-(-1 : ℤ)) := by decide
    exact (h1.mul hodd_q).mul (hoddsign sb)
  have hoddc : Odd (-(-1) * q * S.d1 c) := by
    have h1 : Odd (-(-1 : ℤ)) := by decide
    exact (h1.mul hodd_q).mul (hoddsign sc)
  have nu1 : nu (1 : G → ℂ) = 1 :=
    nu_eq_one (one_mem_blocksIrr G) hreal1 (by rw [hd1]; decide)
  have nua : nu a = 1 := WardSetup.EtaData.nu_one_of_real (S := S) haI hreal_a Ja' (hoddsign sa)
  have nub : nu b = 1 := WardSetup.EtaData.nu_one_of_real (S := S) hbI hreal_bc.1 Jb' hoddb
  have nuc : nu c = 1 := WardSetup.EtaData.nu_one_of_real (S := S) hcI hreal_bc.2 Jc' hoddc
  have FS := S.FS1
  rw [sum_four hS1 n1a n1b n1c nab nac nbc, nu1, nua, nub, nuc, r1.1] at FS
  have hdeg_eq : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → χ 1 = ((deg χ : ℤ) : ℂ) :=
    fun h => (deg_eq h).symm
  have h6c : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
      (1 + ((S.d1 a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
        ((S.d1 b : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg b : ℤ) : ℂ) +
        ((S.d1 c : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg c : ℤ) : ℂ)) =
      (q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) ^ 2 * ((q : ℂ) + (-1 : ℤ)) := by
    rw [← hGc, ← S.formula_S1, sum_four hS1 n1a n1b n1c nab nac nbc, Ja, Jb, Jc,
      hdeg_eq haI, hdeg_eq hbI, hdeg_eq hcI, r1.1]
    have sa' := WardSetup.sq_cast sa
    have sb' := WardSetup.sq_cast sb
    have sc' := WardSetup.sq_cast sc
    congr 1
    simp only [Pi.one_apply, one_pow, Int.cast_one, div_one, mul_one]
    rw [show ((S.d1 a : ℤ) : ℂ) ^ 2 * (S.d1 a : ℂ) = S.d1 a by rw [sa', one_mul],
      show (-((-1 : ℤ) : ℂ) * q * (S.d1 b : ℂ)) ^ 2 * (S.d1 b : ℂ) = (S.d1 b : ℂ) * q ^ 2 by
        rw [mul_pow, mul_pow, sb', neg_sq]; push_cast; ring,
      show (-((-1 : ℤ) : ℂ) * q * (S.d1 c : ℂ)) ^ 2 * (S.d1 c : ℂ) = (S.d1 c : ℂ) * q ^ 2 by
        rw [mul_pow, mul_pow, sc', neg_sq]; push_cast; ring]
  have hε := D.ε_sq
  have hε' : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast hε
  have hdη0 : (D.dη : ℂ) ≠ 0 := by exact_mod_cast hdη.ne'
  have hε0 : (D.ε : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hε'; exact zero_ne_one hε'
  have h8c : ((q : ℂ) + (-1 : ℤ)) * ((q : ℂ) * ((q : ℂ) ^ 2 - 1)) ^ 2 =
      ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℂ) *
        (2 * ((q : ℂ) - (-1 : ℤ)) ^ 2 * ((-1 : ℤ) : ℂ) / ((D.ε * D.dη : ℤ) : ℂ) + 1 +
          ((WardSetup.EtaData.z (S := S) a : ℤ) : ℂ) / ((deg a : ℤ) : ℂ) +
          ((WardSetup.EtaData.z (S := S) b : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg b : ℤ) : ℂ) +
          ((WardSetup.EtaData.z (S := S) c : ℤ) : ℂ) * (q : ℂ) ^ 2 / ((deg c : ℤ) : ℂ)) := by
    have h := D.F8
    rw [S.card_C, hGc, sum_four hS1 n1a n1b n1c nab nac nbc, Ja, Jb, Jc,
      WardSetup.EtaData.z_one (S := S), hd1] at h
    rw [h]
    have sa' := WardSetup.sq_cast sa
    have sb' := WardSetup.sq_cast sb
    have sc' := WardSetup.sq_cast sc
    have hfrac : 2 * ((q : ℂ) - ((-1 : ℤ) : ℂ)) ^ 2 * D.ε * ((-1 : ℤ) : ℂ) / D.dη =
        2 * ((q : ℂ) - (-1 : ℤ)) ^ 2 * ((-1 : ℤ) : ℂ) / ((D.ε * D.dη : ℤ) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hdη0 (mul_ne_zero hε0 hdη0)]
      linear_combination (-2 * ((q : ℂ) + 1) ^ 2 * D.dη) * hε'
    have hb2' : (-((-1 : ℤ) : ℂ) * q * (S.d1 b : ℂ)) ^ 2 = (q : ℂ) ^ 2 := by
      rw [mul_pow, mul_pow, sb', neg_sq]; push_cast; ring
    have hc2' : (-((-1 : ℤ) : ℂ) * q * (S.d1 c : ℂ)) ^ 2 = (q : ℂ) ^ 2 := by
      rw [mul_pow, mul_pow, sc', neg_sq]; push_cast; ring
    rw [hfrac, sa', hb2', hc2']
    simp only [Pi.one_apply, one_pow, Int.cast_one, div_one, one_mul]
    ring
  have hint₃ : deg b ∣ (q : ℤ) ^ 2 * a₀ * (-(-1) * q * S.d1 b) := by
    have := omega_dvd hbI S.J Jb'
    rwa [hK] at this
  have hint₄ : deg c ∣ (q : ℤ) ^ 2 * a₀ * (-(-1) * q * S.d1 c) := by
    have := omega_dvd hcI S.J Jc'
    rwa [hK] at this
  have hεz : D.ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hε; exact zero_ne_one hε
  have hq27 : (27 : ℤ) ≤ q := by exact_mod_cast S.q_ge
  have hD0 : D.ε * D.dη ≠ 0 := mul_ne_zero hεz hdη.ne'
  have h6q : ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℚ) *
      (1 + (S.d1 a : ℚ) / deg a + (S.d1 b : ℚ) * q ^ 2 / deg b + (S.d1 c : ℚ) * q ^ 2 / deg c) =
      q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + -1) := by
    apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h6c; linear_combination h6c
  have h8q : ((q : ℚ) + -1) * (q * (q ^ 2 - 1)) ^ 2 = ((q ^ 3 * (q ^ 2 - 1) * a₀ : ℤ) : ℚ) *
      (2 * (q - -1) ^ 2 * (-1) / ((D.ε * D.dη : ℤ) : ℚ) + 1 +
        (WardSetup.EtaData.z (S := S) a : ℚ) / deg a +
        (WardSetup.EtaData.z (S := S) b : ℚ) * q ^ 2 / deg b +
        (WardSetup.EtaData.z (S := S) c : ℚ) * q ^ 2 / deg c) := by
    apply Rat.cast_injective (α := ℂ); push_cast; push_cast at h8c; linear_combination h8c
  have hR := S.W.Ro_card
  have hRo := D.restrict_Ro (D.S1_NE ha1)
  have hpar := S.deg_parity haI Ja'
  have hsyl := S.sylow8 haI Ja'
  have hq8 := S.W.q_mod
  rcases (isSign_of_sq sb).mul (isSign_of_sq zb) with hσ | hσ
  · have hσ' : S.d1 b = WardSetup.EtaData.z (S := S) b := by
      linear_combination (-(S.d1 b)) * hσ + (WardSetup.EtaData.z (S := S) b) * sb
    obtain ⟨h₂, h₃, h₄, e₂, e₃, e₄, d₂, d₃, d₄, hD, ha⟩ := block_arith hp hqpm' hq27 hq8 ha₀
      (isSign_of_sq sa) (isSign_of_sq sb) (isSign_of_sq sc) pa pb pc hD0 h6q h8q
      (by linear_combination R1) (by linear_combination R2) (by linear_combination R3)
      (by linear_combination O2) (by linear_combination FS) hR hRo hpar hsyl hint₃ hσ'
    exact ⟨b, c, Or.inl ⟨rfl, rfl⟩, h₂, h₃, h₄, e₂, e₃, e₄, d₂, d₃, d₄, hD, ha, hreal_a,
      hreal_bc.1, hreal_bc.2⟩
  · have h44 := sc
    have hσ4 : S.d1 c * WardSetup.EtaData.z (S := S) c = 1 := by
      linarith
    have hσ' : S.d1 c = WardSetup.EtaData.z (S := S) c := by
      linear_combination (-(S.d1 c)) * hσ4 + (WardSetup.EtaData.z (S := S) c) * h44
    obtain ⟨h₂, h₃, h₄, e₂, e₃, e₄, d₂, d₃, d₄, hD, ha⟩ := block_arith (d₃ := deg c)
      (d₄ := deg b) (δ₃ := S.d1 c) (δ₄ := S.d1 b) (e₃ := WardSetup.EtaData.z (S := S) c)
      (e₄ := WardSetup.EtaData.z (S := S) b) hp hqpm' hq27 hq8 ha₀
      (isSign_of_sq sa) (isSign_of_sq sc) (isSign_of_sq sb) pa pc pb hD0
      (by linear_combination h6q) (by linear_combination h8q)
      (by linear_combination R1) (by linear_combination R2) (by linear_combination R3)
      (by linear_combination O2) (by linear_combination FS) hR hRo hpar hsyl hint₄ hσ'
    exact ⟨c, b, Or.inr ⟨rfl, rfl⟩, h₂, h₃, h₄, e₂, e₃, e₄, d₂, d₃, d₄, hD, ha, hreal_a,
      hreal_bc.1, hreal_bc.2⟩

theorem col2_data {m : ℕ} (hm : q = 3 * m ^ 2) {a b c x y : G → ℂ}
    (hS2 : S.S2 = {b, c, x, y}) (hS1 : S.S1 = {1, a, b, c}) (nbc : b ≠ c) (nbx : b ≠ x)
    (nby : b ≠ y) (ncx : c ≠ x) (ncy : c ≠ y) (nxy : x ≠ y) (hb3 : b ∈ S.S3) (hc3 : c ∈ S.S3)
    (hx1 : x ∉ S.S1) (hx3 : x ∉ S.S3) (hy1 : y ∉ S.S1) (hy3 : y ∉ S.S3)
    (hG : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 3 + 1) * (q - 1))
    (hb : S.d1 b = 1) (hdb : deg b = (q : ℤ) ^ 3) (hc : S.d1 c = -1)
    (hdc : deg c = q * ((q : ℤ) ^ 2 - q + 1)) :
    (S.d2 x = 1 ∧ 2 * deg x = ((q : ℤ) - 1) * m * (q + 1 - 3 * m) ∧ S.d2 y = -1 ∧
        2 * deg y = ((q : ℤ) - 1) * m * (q + 1 + 3 * m)) ∨
      (S.d2 y = 1 ∧ 2 * deg y = ((q : ℤ) - 1) * m * (q + 1 - 3 * m) ∧ S.d2 x = -1 ∧
        2 * deg x = ((q : ℤ) - 1) * m * (q + 1 + 3 * m)) := by
  have hx2 : x ∈ S.S2 := by rw [hS2]; simp
  have hy2 : y ∈ S.S2 := by rw [hS2]; simp
  have hb1 : b ∈ S.S1 := by rw [hS1]; simp
  have hc1 : c ∈ S.S1 := by rw [hS1]; simp
  have hb2 : b ∈ S.S2 := by rw [hS2]; simp
  have hc2 : c ∈ S.S2 := by rw [hS2]; simp
  have hbI := (mem_supp.mp hb1).1
  have hcI := (mem_supp.mp hc1).1
  have hxI := (mem_supp.mp hx2).1
  have hyI := (mem_supp.mp hy2).1
  have rb2 : S.d2 b = S.d1 b := (S.agree12 hb1 hb2).symm
  have rc2 : S.d2 c = S.d1 c := (S.agree12 hc1 hc2).symm
  have rb3 : S.d3 b = S.d1 b := (S.agree13 hb1 hb3).symm
  have rc3 : S.d3 c = S.d1 c := (S.agree13 hc1 hc3).symm
  have rx1 : S.d1 x = 0 := S.van1 hxI hx1
  have rx3 : S.d3 x = 0 := S.van3 hxI hx3
  have ry1 : S.d1 y = 0 := S.van1 hyI hy1
  have ry3 : S.d3 y = 0 := S.van3 hyI hy3
  have sx := S.sq2 hx2
  have sy := S.sq2 hy2
  have pxd := deg_pos hxI
  have pyd := deg_pos hyI
  have hx0 : S.d2 x ≠ 0 := (mem_supp.mp hx2).2
  have hy0 : S.d2 y ≠ 0 := (mem_supp.mp hy2).2
  have Jb := S.J_111 hb1 rb2 rb3
  have Jc := S.J_111 hc1 rc2 rc3
  have Jx := S.J_010 hx2 rx1 rx3
  have Jy := S.J_010 hy2 ry1 ry3
  have hdeg_eq : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → χ 1 = ((deg χ : ℤ) : ℂ) :=
    fun h => (deg_eq h).symm
  have hq27 := S.q_ge
  have hdeg2 := S.deg2_S2
  rw [sum_four hS2 nbc nbx nby ncx ncy nxy, rb2, rc2, hb, hc, hdb, hdc] at hdeg2
  have hsum : S.d2 x * deg x + S.d2 y * deg y = -(q : ℤ) * (q - 1) := by linarith
  have hGc : (Nat.card G : ℂ) = ((q : ℂ) ^ 3 * ((q : ℂ) ^ 3 + 1) * ((q : ℂ) - 1)) := by
    have : ((Nat.card G : ℤ) : ℂ) = (((q : ℤ) ^ 3 * ((q : ℤ) ^ 3 + 1) * (q - 1) : ℤ) : ℂ) := by
      rw [hG]
    push_cast at this ⊢
    exact this
  have hF := S.formula_S2
  rw [sum_four hS2 nbc nbx nby ncx ncy nxy, Jb, Jc, Jx, Jy, hdeg_eq hbI, hdeg_eq hcI,
    hdeg_eq hxI, hdeg_eq hyI, rb2, rc2, hGc, hb, hc, hdb, hdc] at hF
  have sx' := WardSetup.sq_cast sx
  have sy' := WardSetup.sq_cast sy
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (q : ℂ) ^ 2 - q + 1 ≠ 0 := by
    have : ((q : ℤ) ^ 2 - q + 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hqm1 : (q : ℂ) - 1 ≠ 0 := by
    have : ((q : ℤ) - 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hqp1 : (q : ℂ) + 1 ≠ 0 := by
    have : ((q : ℤ) + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hpx : (deg x : ℂ) ≠ 0 := by exact_mod_cast pxd.ne'
  have hpy : (deg y : ℂ) ≠ 0 := by exact_mod_cast pyd.ne'
  have hx0' : (S.d2 x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hy0' : (S.d2 y : ℂ) ≠ 0 := by exact_mod_cast hy0
  have hxx : (S.d2 x : ℂ) * S.d2 x = 1 := by rw [← sq]; exact sx'
  have hyy : (S.d2 y : ℂ) * S.d2 y = 1 := by rw [← sq]; exact sy'
  have hsumc : (S.d2 x : ℂ) * deg x + S.d2 y * deg y = -(q : ℂ) * (q - 1) := by
    exact_mod_cast hsum
  have hprodc : 12 * ((S.d2 x : ℂ) * deg x) * ((S.d2 y : ℂ) * deg y) =
      -(q : ℂ) * (q ^ 2 - q + 1) * (q - 1) ^ 2 := by
    push_cast at hF
    have tx : (- -1 * (S.d2 x : ℂ) * (((q : ℂ) + -1) / 2)) ^ 2 * (S.d2 x : ℂ) / (deg x : ℂ) =
        ((q : ℂ) - 1) ^ 2 / (4 * ((S.d2 x : ℂ) * (deg x : ℂ))) := by
      rw [div_eq_div_iff hpx (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (mul_ne_zero hx0' hpx))]
      linear_combination (((q : ℂ) - 1) ^ 2 * (deg x : ℂ) * ((S.d2 x : ℂ) * S.d2 x + 1)) * hxx
    have ty : (- -1 * (S.d2 y : ℂ) * (((q : ℂ) + -1) / 2)) ^ 2 * (S.d2 y : ℂ) / (deg y : ℂ) =
        ((q : ℂ) - 1) ^ 2 / (4 * ((S.d2 y : ℂ) * (deg y : ℂ))) := by
      rw [div_eq_div_iff hpy (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (mul_ne_zero hy0' hpy))]
      linear_combination (((q : ℂ) - 1) ^ 2 * (deg y : ℂ) * ((S.d2 y : ℂ) * S.d2 y + 1)) * hyy
    rw [tx, ty] at hF
    set f5 : ℂ := (S.d2 x : ℂ) * deg x with hf5
    set f6 : ℂ := (S.d2 y : ℂ) * deg y with hf6
    have hf50 : f5 ≠ 0 := mul_ne_zero hx0' hpx
    have hf60 : f6 ≠ 0 := mul_ne_zero hy0' hpy
    have huv : 1 / f5 + 1 / f6 = (f5 + f6) / (f5 * f6) := by field_simp; ring
    have hK1 : (q : ℂ) ^ 3 * ((q : ℂ) ^ 3 + 1) * ((q : ℂ) - 1) *
        ((- -1 * (q : ℂ) * 1) ^ 2 * 1 / (q : ℂ) ^ 3 +
          (- -1 * (q : ℂ) * -1) ^ 2 * -1 / ((q : ℂ) * ((q : ℂ) ^ 2 - q + 1))) =
        -(q : ℂ) ^ 2 * ((q : ℂ) ^ 2 - 1) * ((q : ℂ) - 1) := by
      rw [div_add_div _ _ (pow_ne_zero 3 hq0) (mul_ne_zero hq0 hq1), mul_div_assoc',
        div_eq_iff (mul_ne_zero (pow_ne_zero 3 hq0) (mul_ne_zero hq0 hq1))]
      ring
    have hK2 : ((q : ℂ) - 1) ^ 2 / (4 * f5) + ((q : ℂ) - 1) ^ 2 / (4 * f6) =
        ((q : ℂ) - 1) ^ 2 / 4 * ((f5 + f6) / (f5 * f6)) := by
      rw [← huv]; ring
    rw [mul_add, mul_add, add_assoc, ← mul_add, hK1, hK2, hsumc] at hF
    have hcancel : (q : ℂ) ^ 3 * ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hq0) hqm1)
        (by have : ((q : ℤ) ^ 2 - 1 : ℤ) ≠ 0 := by nlinarith
            exact_mod_cast this)
    field_simp at hF
    apply mul_left_cancel₀ hcancel
    simp only [hf5, hf6] at hF ⊢
    linear_combination (-(q : ℂ) ^ 2) * hF
  have hprod : 12 * (S.d2 x * deg x) * (S.d2 y * deg y) =
      -(q : ℤ) * (q ^ 2 - q + 1) * (q - 1) ^ 2 := by exact_mod_cast hprodc
  have hmq : (q : ℤ) = 3 * (m : ℤ) ^ 2 := by rw [hm]; push_cast; ring
  have hm3 : 3 ≤ (m : ℤ) := by nlinarith
  have hpos : 0 < ((q : ℤ) - 1) * m * (q + 1 - 3 * m) := by
    have : 0 < (q : ℤ) + 1 - 3 * m := by nlinarith
    have : 0 < (q : ℤ) - 1 := by omega
    positivity
  have hpos' : 0 < ((q : ℤ) - 1) * m * (q + 1 + 3 * m) := by
    have : 0 < (q : ℤ) - 1 := by omega
    positivity
  have hsx := isSign_of_sq sx
  have hsy := isSign_of_sq sy
  rcases two_roots hmq hsum hprod with ⟨h5, h6⟩ | ⟨h6, h5⟩
  · left
    rcases hsx with h | h <;> rcases hsy with h' | h' <;> rw [h] at h5 <;> rw [h'] at h6 <;>
      simp only [one_mul, neg_mul] at h5 h6
    · linarith
    · exact ⟨h, by linarith, h', by linarith⟩
    · linarith
    · linarith
  · right
    rcases hsx with h | h <;> rcases hsy with h' | h' <;> rw [h] at h5 <;> rw [h'] at h6 <;>
      simp only [one_mul, neg_mul] at h5 h6
    · linarith
    · linarith
    · exact ⟨h', by linarith, h, by linarith⟩
    · linarith

theorem of_data {m : ℕ} {a b c x y : G → ℂ} (hS1 : S.S1 = {1, a, b, c})
    (hS2 : S.S2 = {b, c, y, x}) (n1a : (1 : G → ℂ) ≠ a) (n1b : (1 : G → ℂ) ≠ b)
    (n1c : (1 : G → ℂ) ≠ c) (nab : a ≠ b) (nac : a ≠ c) (nbc : b ≠ c) (nby : b ≠ y)
    (nbx : b ≠ x) (ncy : c ≠ y) (ncx : c ≠ x) (nyx : y ≠ x) (ha2 : a ∉ S.S2) (ha3 : a ∉ S.S3)
    (hb3 : b ∈ S.S3) (hc3 : c ∈ S.S3) (hy1 : y ∉ S.S1) (hy3 : y ∉ S.S3) (hx1 : x ∉ S.S1)
    (hx3 : x ∉ S.S3) (d1a : S.d1 a = -1) (d1b : S.d1 b = 1) (d1c : S.d1 c = -1)
    (d2y : S.d2 y = -1) (d2x : S.d2 x = 1) (dega : deg a = (q : ℤ) ^ 2 - q + 1)
    (degb : deg b = (q : ℤ) ^ 3) (degc : deg c = (q : ℤ) * ((q : ℤ) ^ 2 - q + 1))
    (degy : 2 * deg y = ((q : ℤ) - 1) * m * (q + 1 + 3 * m))
    (degx : 2 * deg x = ((q : ℤ) - 1) * m * (q + 1 - 3 * m))
    (ra : starRingEnd ℂ ∘ a = a) (rb : starRingEnd ℂ ∘ b = b) (rc : starRingEnd ℂ ∘ c = c)
    (za : WardSetup.EtaData.z (S := S) a = 1) (zb : WardSetup.EtaData.z (S := S) b = 1)
    (zc : WardSetup.EtaData.z (S := S) c = 1) (hε : D.ε = 1) (hdη : D.dη = (q : ℤ) ^ 3 + 1) :
    Nonempty (Block S D m) :=
  ⟨⟨a, b, c, y, x, hS1, hS2, n1a, n1b, n1c, nab, nac, nbc, nby, nbx, ncy, ncx, nyx, ha2, ha3,
    hb3, hc3, hy1, hy3, hx1, hx3, d1a, d1b, d1c, d2y, d2x, dega, degb, degc, degy, degx, ra, rb,
    rc, za, zb, zc, hε, hdη⟩⟩

end Block

theorem exists_block (S : WardSetup G L q (-1)) (D : S.EtaData) {m : ℕ} (hm : q = 3 * m ^ 2)
    (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1)) : Nonempty (Block S D m) := by
  obtain ⟨a₀, ha₀, hG'⟩ := S.card_dvd
  have hq27 := S.q_ge
  have hGz : (Nat.card G : ℤ) = q ^ 3 * ((q : ℤ) ^ 3 + 1) * (q - 1) := by
    rw [hG]; push_cast [Nat.cast_sub (show 1 ≤ q by omega)]; ring
  rcases three_sets S.S1 S.S2 S.S3 1 S.card_S1 S.card_S2 S.card_S12 S.card_S13 S.card_S23
      S.one_S1 S.one_not_S2 S.one_not_S3 with
    ⟨a, b, c, x, y, hS1, hS2, n1a, n1b, n1c, nab, nac, nbc, nbx, nby, ncx, ncy, nxy, ha2, ha3,
      hb3, hc3, hx1, hx3, hy1, hy3⟩ |
    ⟨a, b, c, x, w, hS1, hS2, n1a, n1b, n1c, nab, nac, nbc, nax, naw, ncx, ncw, nxw, ha3, hb2,
      hb3, hc3, hx1, hx3, hw1, hw3⟩
  swap
  · exact (D.seven_case ha₀ hG' hS1 hS2 n1a n1b n1c nab nac nbc nax naw ncx ncw nxw ha3 hb2 hb3
      hc3 hx1 hx3 hw1 hw3).elim
  obtain ⟨b', c', hbc, d1a, d1b, d1c, za, zb, zc, dega, degb, degc, hεdη, -, ra, rb, rc⟩ :=
    Block.eight_data D ha₀ hG' hS1 hS2 n1a n1b n1c nab nac nbc ha2 ha3 hb3 hc3
  have hε : D.ε = 1 := by
    have hpos := D.dη_pos
    rcases D.ε_eq with h | h
    · exact h
    · exfalso; rw [h] at hεdη; nlinarith
  have hdη : D.dη = (q : ℤ) ^ 3 + 1 := by rw [hε, one_mul] at hεdη; exact hεdη
  have hS2' : S.S2 = {b, c, y, x} := by rw [hS2, Finset.pair_comm x y]
  rcases hbc with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · rcases Block.col2_data hm hS2 hS1 nbc nbx nby ncx ncy nxy hb3 hc3 hx1 hx3 hy1 hy3 hGz d1b
        degb d1c degc with ⟨d2x, degx, d2y, degy⟩ | ⟨d2y, degy, d2x, degx⟩
    · exact Block.of_data D hS1 hS2' n1a n1b n1c nab nac nbc nby nbx ncy ncx nxy.symm ha2 ha3
        hb3 hc3 hy1 hy3 hx1 hx3 d1a d1b d1c d2y d2x dega degb degc degy degx ra rb rc za zb zc
        hε hdη
    · exact Block.of_data D hS1 hS2 n1a n1b n1c nab nac nbc nbx nby ncx ncy nxy ha2 ha3
        hb3 hc3 hx1 hx3 hy1 hy3 d1a d1b d1c d2x d2y dega degb degc degx degy ra rb rc za zb zc
        hε hdη
  · subst h1 h2
    have hS1c : S.S1 = {1, a, b', c'} := by rw [hS1, Finset.pair_comm]
    have hS2c : S.S2 = {b', c', x, y} := by rw [hS2, Finset.insert_comm]
    have hS2c' : S.S2 = {b', c', y, x} := by rw [hS2c, Finset.pair_comm x y]
    rcases Block.col2_data hm hS2c hS1c nbc.symm ncx ncy nbx nby nxy hc3 hb3 hx1 hx3 hy1 hy3
        hGz d1b degb d1c degc with ⟨d2x, degx, d2y, degy⟩ | ⟨d2y, degy, d2x, degx⟩
    · exact Block.of_data D hS1c hS2c' n1a n1c n1b nac nab nbc.symm ncy ncx nby nbx nxy.symm ha2
        ha3 hc3 hb3 hy1 hy3 hx1 hx3 d1a d1b d1c d2y d2x dega degb degc degy degx ra rc rb za zb
        zc hε hdη
    · exact Block.of_data D hS1c hS2c n1a n1c n1b nac nab nbc.symm ncx ncy nbx nby nxy ha2
        ha3 hc3 hb3 hx1 hx3 hy1 hy3 d1a d1b d1c d2x d2y dega degb degc degx degy ra rc rb za zb
        zc hε hdη

end CFSG.Walter.WardLocal
