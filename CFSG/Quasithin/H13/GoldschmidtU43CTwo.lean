module

public import CFSG.Quasithin.H13.GoldschmidtU43CBr
public import CFSG.Quasithin.H13.GoldschmidtU43BA
public import CFSG.Quasithin.H13.GoldschmidtU43CTheta

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

set_option synthInstance.maxSize 1024

theorem bq_two_lines : ∀ τ α β : V4, LinePair τ α → LinePair τ β → α + β ≠ 0 → α + β ≠ τ →
    bq α β = 1 := by
  decide +kernel

structure Two (z t w a a' : G) : Prop where
  swap : Swap z t w
  ha : Good z t a
  ha' : Good z t a'
  haa : a * a' ∉ Vg z t

namespace Two

variable [Finite G] {z t w a a' : G} (e : Two z t w a a')
include e

omit [Finite G] in
theorem a_mem_B : a ∈ Bg z t := Swap.N1_le_B e.ha.mem

omit [Finite G] in
theorem a'_mem_B : a' ∈ Bg z t := Swap.N1_le_B e.ha'.mem

omit [Finite G] in
theorem m_mem_B : w⁻¹ * a * w ∈ Bg z t := e.swap.m_mem_B e.ha

omit [Finite G] in
theorem m'_mem_B : w⁻¹ * a' * w ∈ Bg z t := e.swap.m_mem_B e.ha'

theorem bq_eq_one : bq (e.swap.alphaV e.ha) (e.swap.alphaV e.ha') = 1 := by
  have h := e.swap.hyp
  have hL := e.swap.linePair_ta e.ha
  have hL' := e.swap.linePair_ta e.ha'
  have hmem : a * a' ∈ Uz z := mul_mem e.ha.mem.1 e.ha'.mem.1
  have hsum : h.tv ⟨a * a', hmem⟩ = e.swap.alphaV e.ha + e.swap.alphaV e.ha' :=
    h.tv_mul ⟨a, e.ha.mem.1⟩ ⟨a', e.ha'.mem.1⟩
  have hne : ∀ γ : V4, h.tv ⟨a * a', hmem⟩ = γ → (γ = 0 ∨ γ = e.swap.tauV) → False := by
    intro γ hγ hγ'
    apply e.haa
    rcases hγ' with rfl | rfl
    · rcases (h.tv_eq_zero_iff _).1 hγ with h1 | h1
      · rw [show a * a' = 1 from h1]
        exact one_mem _
      · rw [show a * a' = z from h1]
        exact z_mem_Vg z t
    · have hτ : h.tv ⟨t, e.swap.ht.1⟩ = e.swap.tauV := rfl
      rcases h.eq_of_tv_eq (u := ⟨a * a', hmem⟩) (v := ⟨t, e.swap.ht.1⟩)
        (hγ.trans hτ.symm) with h1 | h1
      · rw [show a * a' = t from h1]
        exact t_mem_Vg z t
      · rw [show a * a' = z * t from h1]
        exact Swap.zt_mem_Vg z t
  refine bq_two_lines _ _ _ hL hL' ?_ ?_
  · intro h0
    exact hne 0 (by rw [hsum, h0]) (Or.inl rfl)
  · intro h0
    exact hne e.swap.tauV (by rw [hsum, h0]) (Or.inr rfl)

theorem br_a_a' : br a a' = z := by
  have h := e.swap.hyp
  have := h.comm_tv ⟨a, e.ha.mem.1⟩ ⟨a', e.ha'.mem.1⟩
  have e1 : h.tv ⟨a, e.ha.mem.1⟩ = e.swap.alphaV e.ha := rfl
  have e2 : h.tv ⟨a', e.ha'.mem.1⟩ = e.swap.alphaV e.ha' := rfl
  rw [e1, e2, e.bq_eq_one, zp_one] at this
  exact this

theorem br_m_m' : br (w⁻¹ * a * w) (w⁻¹ * a' * w) = t := by
  rw [br_conj, e.br_a_a']
  exact e.swap.w1

theorem br_a_m : br a (w⁻¹ * a * w) = 1 :=
  br_eq_one_of_comm (e.swap.commute_conj e.ha.mem)

theorem br_a'_m' : br a' (w⁻¹ * a' * w) = 1 :=
  br_eq_one_of_comm (e.swap.commute_conj e.ha'.mem)

theorem zeta_mem_V : br a (w⁻¹ * a' * w) ∈ Vg z t :=
  e.swap.br_mem_V e.a_mem_B e.m'_mem_B

theorem zeta'_mem_V : br a' (w⁻¹ * a * w) ∈ Vg z t :=
  e.swap.br_mem_V e.a'_mem_B e.m_mem_B

theorem zeta_eq : br a (w⁻¹ * a' * w) = br a' (w⁻¹ * a * w) := by
  have hc := e.swap.commute_conj (n := a * a') (mul_mem e.ha.mem e.ha'.mem)
  have h1 : br (a * a') (w⁻¹ * (a * a') * w) = 1 := br_eq_one_of_comm hc
  have hw : w⁻¹ * (a * a') * w = (w⁻¹ * a * w) * (w⁻¹ * a' * w) := by group
  rw [hw, e.swap.br_mul_left e.a_mem_B e.a'_mem_B (mul_mem e.m_mem_B e.m'_mem_B),
    e.swap.br_mul_right e.a_mem_B e.m_mem_B e.m'_mem_B,
    e.swap.br_mul_right e.a'_mem_B e.m_mem_B e.m'_mem_B, e.br_a_m, e.br_a'_m', one_mul,
    mul_one] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact inv_eq_of_mul_eq_one_right (e.swap.V_sq e.zeta'_mem_V)

theorem zeta_cases : br a (w⁻¹ * a' * w) = 1 ∨ br a (w⁻¹ * a' * w) = z * t := by
  have hζV := e.zeta_mem_V
  have hb : w * w ∈ Bg z t := e.swap.w_sq_mem_B
  have hn : a' ∈ N1g z t := e.ha'.mem
  have hv₀ := e.swap.B_acts_triv ((Bg z t).inv_mem hb) hn
  set v₀ := a'⁻¹ * ((w * w)⁻¹ * a' * (w * w)⁻¹⁻¹) with hv₀def
  have hexp : w⁻¹ * (w⁻¹ * a' * w) * w = a' * v₀ := by
    rw [hv₀def, inv_inv]
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hv₀B : v₀ ∈ Bg z t := Swap.N1_le_B (e.swap.Vg_le_N1 hv₀)
  have hinv : w⁻¹ * br a (w⁻¹ * a' * w) * w = br a (w⁻¹ * a' * w) := by
    rw [← br_conj, hexp, e.swap.br_mul_right e.m_mem_B e.a'_mem_B hv₀B,
      e.swap.br_V_right e.m_mem_B hv₀, mul_one, br_swap a' (w⁻¹ * a * w), ← e.zeta_eq]
    exact inv_eq_of_mul_eq_one_right (e.swap.V_sq e.zeta_mem_V)
  rcases (e.swap.cm.mem_Vg_iff₄ _).1 hζV with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    rw [h1, e.swap.w1] at hinv
    exact e.swap.ht.2.2.2 hinv
  · exfalso
    rw [h1, e.swap.w2] at hinv
    exact e.swap.ht.2.2.2 hinv.symm
  · exact Or.inr h1

omit [Finite G] in
theorem V_mem_B {v : G} (hv : v ∈ Vg z t) : v ∈ Bg z t :=
  Swap.N1_le_B (e.swap.Vg_le_N1 hv)

theorem br_expand {v v' : G} (hv : v ∈ Vg z t) (hv' : v' ∈ Vg z t) (i i' : ZMod 2) :
    br (v * zp a i * (w⁻¹ * a * w)) (v' * zp a' i' * (w⁻¹ * a' * w)) =
      zp (zp z i') i * zp (br a (w⁻¹ * a' * w)) i *
        (zp (br (w⁻¹ * a * w) a') i' * t) := by
  have hvB := e.V_mem_B hv
  have hv'B := e.V_mem_B hv'
  have hai := Swap.zp_mem_B e.ha i
  have ha'i := Swap.zp_mem_B e.ha' i'
  have hP : v * zp a i ∈ Bg z t := mul_mem hvB hai
  have hQ : v' * zp a' i' ∈ Bg z t := mul_mem hv'B ha'i
  have hmB := e.m_mem_B
  have hnB := e.m'_mem_B
  have h1 : br (v * zp a i) (v' * zp a' i') = zp (zp z i') i := by
    rw [e.swap.br_mul_left hvB hai hQ, e.swap.br_V_left hv hQ, one_mul,
      e.swap.br_mul_right hai hv'B ha'i, e.swap.br_V_right hai hv', one_mul, br_zp_left,
      br_zp_right, e.br_a_a']
  have h2 : br (v * zp a i) (w⁻¹ * a' * w) = zp (br a (w⁻¹ * a' * w)) i := by
    rw [e.swap.br_mul_left hvB hai hnB, e.swap.br_V_left hv hnB, one_mul, br_zp_left]
  have h3 : br (w⁻¹ * a * w) (v' * zp a' i') = zp (br (w⁻¹ * a * w) a') i' := by
    rw [e.swap.br_mul_right hmB hv'B ha'i, e.swap.br_V_right hmB hv', one_mul, br_zp_right]
  rw [e.swap.br_mul_left hP hmB (mul_mem hQ hnB), e.swap.br_mul_right hP hQ hnB,
    e.swap.br_mul_right hmB hQ hnB, h1, h2, h3, e.br_m_m']

theorem zeta'_eq : br (w⁻¹ * a * w) a' = br a (w⁻¹ * a' * w) := by
  rw [br_swap a' (w⁻¹ * a * w), ← e.zeta_eq]
  exact inv_eq_of_mul_eq_one_right (e.swap.V_sq e.zeta_mem_V)

theorem br_ne_one {v v' : G} (hv : v ∈ Vg z t) (hv' : v' ∈ Vg z t) (i i' : ZMod 2) :
    br (v * zp a i * (w⁻¹ * a * w)) (v' * zp a' i' * (w⁻¹ * a' * w)) ≠ 1 := by
  rw [e.br_expand hv hv' i i', e.zeta'_eq]
  have ht1 : t ≠ 1 := e.swap.ht.2.2.1
  have htz : t ≠ z := e.swap.ht.2.2.2
  have hz1 : z ≠ 1 := e.swap.hyp.z_ne_one
  have ht2 : t * t = 1 := e.swap.ht.2.1
  have hz2 : z * z = 1 := e.swap.hyp.sq_z
  have hzt : z * t ≠ 1 := by
    intro h
    apply htz
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz2
  have hA : z * t * t = z := by rw [mul_assoc, ht2, mul_one]
  have hB : z * (z * t) = t := by rw [← mul_assoc, hz2, one_mul]
  rcases e.zeta_cases with hζ | hζ <;> rw [hζ] <;>
    rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases i' with rfl | rfl <;>
    simp only [zp_zero, zp_one, one_mul, mul_one]
  all_goals first
    | exact ht1
    | exact hzt
    | (rw [hA]; exact hz1)
    | (rw [hB, hA, ← e.swap.cm.comm]; exact hzt)

end Two

end CFSG.Quasithin.H13.U43
