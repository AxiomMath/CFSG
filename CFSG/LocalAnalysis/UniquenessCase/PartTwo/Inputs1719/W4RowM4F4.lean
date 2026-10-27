module

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Orb
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin Subgroup

variable {U : Type} [CommGroup U] [Finite U]

private def m4phi (u : MulAut U) : U →* U where
  toFun w := u w * w⁻¹
  map_one' := by simp
  map_mul' w x := by
    show u (w * x) * (w * x)⁻¹ = (u w * w⁻¹) * (u x * x⁻¹)
    rw [map_mul, mul_inv]
    ac_rfl

@[simp] private lemma m4phi_apply {u : MulAut U} {w : U} : m4phi u w = u w * w⁻¹ := rfl

private def m4V (u : MulAut U) : Subgroup U := (m4phi u).range

private def m4p (u : MulAut U) : U →* U where
  toFun v := u v * (u ^ 4) v
  map_one' := by simp
  map_mul' v w := by
    show u (v * w) * (u ^ 4) (v * w) = (u v * (u ^ 4) v) * (u w * (u ^ 4) w)
    rw [map_mul, map_mul]
    ac_rfl

@[simp] private lemma m4p_apply {u : MulAut U} {v : U} : m4p u v = u v * (u ^ 4) v := rfl

private def m4q (u : MulAut U) : U →* U where
  toFun v := (u ^ 2) v * (u ^ 3) v
  map_one' := by simp
  map_mul' v w := by
    show (u ^ 2) (v * w) * (u ^ 3) (v * w)
      = ((u ^ 2) v * (u ^ 3) v) * ((u ^ 2) w * (u ^ 3) w)
    rw [map_mul, map_mul]
    ac_rfl

@[simp] private lemma m4q_apply {u : MulAut U} {v : U} :
    m4q u v = (u ^ 2) v * (u ^ 3) v := rfl

private def m4Phi (u : MulAut U) : U →* U where
  toFun v := v * u v * (u ^ 2) v * (u ^ 3) v * (u ^ 4) v
  map_one' := by simp
  map_mul' v w := by
    show (v * w) * u (v * w) * (u ^ 2) (v * w) * (u ^ 3) (v * w) * (u ^ 4) (v * w)
      = (v * u v * (u ^ 2) v * (u ^ 3) v * (u ^ 4) v)
        * (w * u w * (u ^ 2) w * (u ^ 3) w * (u ^ 4) w)
    rw [map_mul, map_mul, map_mul, map_mul]
    ac_rfl

@[simp] private lemma m4Phi_apply {u : MulAut U} {v : U} :
    m4Phi u v = v * u v * (u ^ 2) v * (u ^ 3) v * (u ^ 4) v := rfl

private lemma m4u_apply_u {u : MulAut U} (v : U) : u (u v) = (u ^ 2) v := by
  rw [← MulAut.mul_apply, ← pow_two]

private lemma m4u_apply_pow {u : MulAut U} (j : ℕ) (v : U) :
    u ((u ^ j) v) = (u ^ (j + 1)) v := by
  rw [← MulAut.mul_apply, ← pow_succ']

private lemma m4pow_apply_u {u : MulAut U} (i : ℕ) (v : U) :
    (u ^ i) (u v) = (u ^ (i + 1)) v := by
  rw [← MulAut.mul_apply, ← pow_succ]

private lemma m4pow_apply_pow {u : MulAut U} (i j : ℕ) (v : U) :
    (u ^ i) ((u ^ j) v) = (u ^ (i + j)) v := by
  rw [← MulAut.mul_apply, ← pow_add]

private lemma m4pow_apply_self {u : MulAut U} {v : U} (h : u v = v) (n : ℕ) :
    (u ^ n) v = v := by
  induction n with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

private lemma m4pow5_apply {u : MulAut U} (hu5 : u ^ 5 = 1) {v : U} : (u ^ 5) v = v := by
  rw [hu5, MulAut.one_apply]

private lemma m4pow6_apply {u : MulAut U} (hu5 : u ^ 5 = 1) {v : U} : (u ^ 6) v = u v := by
  rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, hu5, one_mul, pow_one]

private lemma m4pow7_apply {u : MulAut U} (hu5 : u ^ 5 = 1) {v : U} :
    (u ^ 7) v = (u ^ 2) v := by
  rw [show (7 : ℕ) = 5 + 2 by norm_num, pow_add, hu5, one_mul]

private lemma m4pow8_apply {u : MulAut U} (hu5 : u ^ 5 = 1) {v : U} :
    (u ^ 8) v = (u ^ 3) v := by
  rw [show (8 : ℕ) = 5 + 3 by norm_num, pow_add, hu5, one_mul]

private lemma m4Phi_apply_u {u : MulAut U} (v : U) :
    m4Phi u (u v) = u v * (u ^ 2) v * (u ^ 3) v * (u ^ 4) v * (u ^ 5) v := by
  rw [m4Phi_apply, m4u_apply_u, m4pow_apply_u 2, m4pow_apply_u 3, m4pow_apply_u 4]

private lemma m4Phi_shift {u : MulAut U} (hu5 : u ^ 5 = 1) (v : U) :
    m4Phi u (u v) = m4Phi u v := by
  rw [m4Phi_apply_u, m4Phi_apply, m4pow5_apply hu5]
  ac_rfl

private lemma m4Phi_phi {u : MulAut U} (hu5 : u ^ 5 = 1) (w : U) :
    m4Phi u (m4phi u w) = 1 := by
  change m4Phi u (u w * w⁻¹) = 1
  rw [map_mul, map_inv, m4Phi_shift hu5]
  group

private lemma m4Phi_memV {u : MulAut U} (hu5 : u ^ 5 = 1) {v : U} (hv : v ∈ m4V u) :
    m4Phi u v = 1 := by
  obtain ⟨w, rfl⟩ := hv
  exact m4Phi_phi hu5 w

private lemma m4Phi_eq {u : MulAut U} (v : U) :
    m4Phi u v = v * (m4p u v * m4q u v) := by
  rw [m4Phi_apply, m4p_apply, m4q_apply]
  ac_rfl

private lemma m4pq_eq {u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1)
    {v : U} (hv : v ∈ m4V u) : m4p u v * m4q u v = v := by
  have h := m4Phi_memV hu5 hv
  rw [m4Phi_eq] at h
  calc m4p u v * m4q u v = v * (v * (m4p u v * m4q u v)) := by
        rw [← mul_assoc, hU v, one_mul]
    _ = v * 1 := by rw [h]
    _ = v := mul_one v

private lemma m4p_m4q_cross {u : MulAut U} (hu5 : u ^ 5 = 1) (v : U) :
    m4p u (m4q u v) = m4p u v * m4q u v := by
  simp only [m4p_apply, m4q_apply, map_mul, m4u_apply_pow, m4pow_apply_u,
    m4pow_apply_pow, Nat.reduceAdd]
  simp only [m4pow6_apply hu5, m4pow7_apply hu5]
  ac_rfl

private lemma m4p_m4q {u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1)
    {v : U} (hv : v ∈ m4V u) : m4p u (m4q u v) = v := by
  rw [m4p_m4q_cross hu5, m4pq_eq hU hu5 hv]

private lemma m4p_sq {u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1) (v : U) :
    m4p u (m4p u v) = m4q u v := by
  simp only [m4p_apply, m4q_apply, map_mul, m4u_apply_u, m4u_apply_pow,
    m4pow_apply_u, m4pow_apply_pow, Nat.reduceAdd]
  simp only [m4pow5_apply hu5]
  rw [show ((u ^ 4) ^ 2 : MulAut U) = u ^ 8 from by rw [← pow_mul],
      m4pow8_apply hu5, mul_assoc ((u ^ 2) v) v (v * (u ^ 3) v),
      ← mul_assoc v v ((u ^ 3) v), hU v, one_mul]

private lemma m4comm_apply {ω : MulAut U} {a : MulAut U} (ha : a * ω = ω * a) (v : U) :
    a (ω v) = ω (a v) := by
  rw [← MulAut.mul_apply, ha, MulAut.mul_apply]

private lemma m4omega_u_apply {ω u : MulAut U} (huω : u * ω = ω * u) (v : U) :
    ω (u v) = u (ω v) := by
  rw [← MulAut.mul_apply, ← huω, MulAut.mul_apply]

private lemma m4u_p_comm {u : MulAut U} (v : U) : u (m4p u v) = m4p u (u v) := by
  simp only [m4p_apply, map_mul, m4u_apply_u, m4u_apply_pow, m4pow_apply_u]

private lemma m4u_q_comm {u : MulAut U} (v : U) : u (m4q u v) = m4q u (u v) := by
  simp only [m4q_apply, map_mul, m4u_apply_u, m4u_apply_pow, m4pow_apply_u]

private lemma m4q_omega {ω u : MulAut U} (huω : u * ω = ω * u) (v : U) :
    m4q u (ω v) = ω (m4q u v) := by
  rw [m4q_apply, m4q_apply, map_mul,
      m4comm_apply ((show Commute u ω from huω).pow_left 2) v,
      m4comm_apply ((show Commute u ω from huω).pow_left 3) v]

private lemma m4step1 {ω : MulAut U} (hω3 : ω ^ 3 = 1)
    (hfix : ∀ w : U, ω w = w → w = 1) (w : U) : ω (ω w) * ω w * w = 1 := by
  apply hfix
  have h3 : ω * ω * ω = 1 := by simpa [pow_three'] using hω3
  have h3w : ω (ω (ω w)) = w := by
    have := congrArg (fun σ : MulAut U => σ w) h3
    simpa [MulAut.mul_apply, MulAut.one_apply] using this
  rw [map_mul, map_mul, h3w]
  ac_rfl

private lemma m4V_u_mem {u : MulAut U} {v : U} (hv : v ∈ m4V u) : u v ∈ m4V u := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨u w, ?_⟩
  rw [m4phi_apply, m4phi_apply, map_mul, map_inv]

private lemma m4V_u2_le {u : MulAut U} : m4V (u ^ 2) ≤ m4V u := by
  rintro x ⟨w, rfl⟩
  refine ⟨u w * w, ?_⟩
  rw [map_mul, m4phi_apply, m4phi_apply, m4phi_apply, m4u_apply_u]
  group

private lemma m4V_omega_mem {ω u : MulAut U} (huω : u * ω = ω * u) {v : U}
    (hv : v ∈ m4V u) : ω v ∈ m4V u := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨ω w, ?_⟩
  rw [m4phi_apply, m4phi_apply, map_mul, map_inv, ← MulAut.mul_apply, huω,
      MulAut.mul_apply]

private lemma m4V_q_mem {u : MulAut U} {v : U} (hv : v ∈ m4V u) : m4q u v ∈ m4V u := by
  rw [m4q_apply]
  exact mul_mem (m4V_u_mem (m4V_u_mem hv))
    (m4V_u_mem (m4V_u_mem (m4V_u_mem hv)))

private lemma m4V_g_mem {u g : MulAut U} (hg : g * u * g⁻¹ = u ^ 2) {v : U}
    (hv : v ∈ m4V u) : g v ∈ m4V u := by
  obtain ⟨w, rfl⟩ := hv
  have h1 : g (m4phi u w) = m4phi (u ^ 2) (g w) := by
    have hgu : g * u = u ^ 2 * g := by rw [← hg]; group
    rw [m4phi_apply, m4phi_apply, map_mul, map_inv, ← MulAut.mul_apply, hgu,
        MulAut.mul_apply]
  rw [h1]
  exact m4V_u2_le ⟨g w, rfl⟩

private lemma m4g_p {u g : MulAut U} (hu5 : u ^ 5 = 1) (hg : g * u * g⁻¹ = u ^ 2)
    (v : U) : g (m4p u v) = m4q u (g v) := by
  have hgu : g * u = u ^ 2 * g := by rw [← hg]; group
  have hgu4 : g * u ^ 4 = u ^ 3 * g := by
    have h4 : g * u ^ 4 * g⁻¹ = u ^ 3 := by
      have h := congrArg (fun a : MulAut U => a ^ 4) hg
      rw [conj_pow] at h
      rw [h, show (u ^ 2) ^ 4 = u ^ 8 from by group,
          show (u : MulAut U) ^ 8 = u ^ 3 from by
            rw [show (8 : ℕ) = 5 + 3 by norm_num, pow_add, hu5, one_mul]]
    rw [← h4]; group
  have h1 : g (u v) = (u ^ 2) (g v) := by
    rw [← MulAut.mul_apply, hgu, MulAut.mul_apply]
  have h2 : g ((u ^ 4) v) = (u ^ 3) (g v) := by
    rw [← MulAut.mul_apply, hgu4, MulAut.mul_apply]
  rw [m4p_apply, m4q_apply, map_mul, h1, h2]

private lemma m4g_q {u g : MulAut U} (hu5 : u ^ 5 = 1) (hg : g * u * g⁻¹ = u ^ 2)
    (v : U) : g (m4q u v) = m4p u (g v) := by
  have hgu2 : g * u ^ 2 = u ^ 4 * g := by
    have h2 : g * u ^ 2 * g⁻¹ = u ^ 4 := by
      have h := congrArg (fun a : MulAut U => a ^ 2) hg
      rw [conj_pow] at h
      rw [h, show (u ^ 2) ^ 2 = u ^ 4 from by group]
    rw [← h2]; group
  have hgu3 : g * u ^ 3 = u * g := by
    have h3 : g * u ^ 3 * g⁻¹ = u := by
      have h := congrArg (fun a : MulAut U => a ^ 3) hg
      rw [conj_pow] at h
      rw [h, show (u ^ 2) ^ 3 = u ^ 6 from by group,
          show (u : MulAut U) ^ 6 = u from by
            rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, hu5, one_mul, pow_one]]
    calc g * u ^ 3 = (g * u ^ 3 * g⁻¹) * g := by group
      _ = u * g := by rw [h3]
  have h1 : g ((u ^ 2) v) = (u ^ 4) (g v) := by
    rw [← MulAut.mul_apply, hgu2, MulAut.mul_apply]
  have h2 : g ((u ^ 3) v) = u (g v) := by
    rw [← MulAut.mul_apply, hgu3, MulAut.mul_apply]
  rw [m4q_apply, m4p_apply, map_mul, h1, h2]
  ac_rfl

private lemma m4V_ne_bot {u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu1 : u ≠ 1) :
    m4V u ≠ ⊥ := by
  intro h
  apply hu1
  ext v
  have hv : m4phi u v ∈ m4V u := ⟨v, rfl⟩
  rw [h] at hv
  have hm : u v * v⁻¹ = 1 := by
    have := Subgroup.mem_bot.mp hv
    simpa [m4phi] using this
  simpa using mul_inv_eq_one.mp hm

private lemma m4fix_of_memV {u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1)
    {v : U} (hv : v ∈ m4V u) (h : u v = v) : v = 1 := by
  have hPhi := m4Phi_memV hu5 hv
  rw [m4Phi_apply] at hPhi
  rw [h, m4pow_apply_self h 2, m4pow_apply_self h 3, m4pow_apply_self h 4] at hPhi
  have hv2 : v * v = 1 := hU v
  have hvv : v * v * v * v * v = v := by
    calc v * v * v * v * v = (v * v) * (v * v) * v := by group
      _ = 1 * 1 * v := by rw [hv2]
      _ = v := by rw [one_mul, one_mul]
  rw [hvv] at hPhi
  exact hPhi

private def m4V1 (ω u : MulAut U) : Subgroup U where
  carrier := {v | v ∈ m4V u ∧ ω v = m4p u v}
  one_mem' := ⟨(m4V u).one_mem, by simp⟩
  mul_mem' := fun {v w} hv hw => ⟨mul_mem hv.1 hw.1, by
    show ω (v * w) = m4p u (v * w)
    rw [map_mul, hv.2, hw.2, map_mul]⟩
  inv_mem' := fun {v} hv => ⟨inv_mem hv.1, by
    show ω v⁻¹ = m4p u v⁻¹
    rw [map_inv, hv.2, map_inv]⟩

private def m4V2 (ω u : MulAut U) : Subgroup U where
  carrier := {v | v ∈ m4V u ∧ ω v = m4q u v}
  one_mem' := ⟨(m4V u).one_mem, by simp⟩
  mul_mem' := fun {v w} hv hw => ⟨mul_mem hv.1 hw.1, by
    show ω (v * w) = m4q u (v * w)
    rw [map_mul, hv.2, hw.2, map_mul]⟩
  inv_mem' := fun {v} hv => ⟨inv_mem hv.1, by
    show ω v⁻¹ = m4q u v⁻¹
    rw [map_inv, hv.2, map_inv]⟩

private lemma mem_m4V1 {ω u : MulAut U} {v : U} :
    v ∈ m4V1 ω u ↔ v ∈ m4V u ∧ ω v = m4p u v := Iff.rfl

private lemma mem_m4V2 {ω u : MulAut U} {v : U} :
    v ∈ m4V2 ω u ↔ v ∈ m4V u ∧ ω v = m4q u v := Iff.rfl

private lemma m4V1_inf_m4V2 {ω u : MulAut U} (hU : ∀ w : U, w * w = 1)
    (hfix : ∀ w : U, ω w = w → w = 1) (hu5 : u ^ 5 = 1) :
    m4V1 ω u ⊓ m4V2 ω u = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  rw [Subgroup.mem_inf, mem_m4V1, mem_m4V2] at hv
  obtain ⟨⟨hvV, hpv⟩, -, hqv⟩ := hv
  have hpq : m4p u v = m4q u v := by rw [← hpv, hqv]
  have h1 : m4p u (m4q u v) = v := m4p_m4q hU hu5 hvV
  have h2 : m4p u (m4q u v) = m4q u v := by
    rw [← hpq, m4p_sq hU hu5, ← hpq]
  have hvq : v = m4q u v := h1.symm.trans h2
  exact hfix v (by rw [hqv, ← hvq])

private lemma m4eq_of_mul_eq_one (hU : ∀ w : U, w * w = 1) {a b : U} (h : a * b = 1) :
    a = b := by
  calc a = a * (b * b) := by rw [hU b, mul_one]
    _ = (a * b) * b := by group
    _ = b := by rw [h, one_mul]

private lemma m4V1_ne_bot_or_m4V2_ne_bot {ω u : MulAut U} (hU : ∀ w : U, w * w = 1)
    (hω3 : ω ^ 3 = 1) (hfix : ∀ w : U, ω w = w → w = 1) (hu5 : u ^ 5 = 1)
    (huω : u * ω = ω * u) (hu1 : u ≠ 1) :
    m4V1 ω u ≠ ⊥ ∨ m4V2 ω u ≠ ⊥ := by
  have hVne : m4V u ≠ ⊥ := m4V_ne_bot hU hu1
  obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hwV : (v : U) ∈ m4V u := v.2
  have hw1 : (v : U) ≠ 1 := fun h => hvne (Subtype.ext h)
  by_cases hy : ω (v : U) * m4q u (v : U) = 1
  · right
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨(v : U), ?_⟩, ?_⟩
    · rw [mem_m4V2]
      exact ⟨hwV, m4eq_of_mul_eq_one hU hy⟩
    · intro hcon
      exact hw1 (Subtype.ext_iff.mp hcon)
  · left
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨ω (v : U) * m4q u (v : U), ?_⟩, ?_⟩
    · rw [mem_m4V1]
      refine ⟨mul_mem (m4V_omega_mem huω hwV) (m4V_q_mem hwV), ?_⟩
      have hVω : ω (v : U) ∈ m4V u := m4V_omega_mem huω hwV
      have hy1 : ω (ω (v : U) * m4q u (v : U))
          = ω (ω (v : U)) * m4q u (ω (v : U)) := by
        rw [map_mul, ← m4q_omega huω]
      have hy2 : m4p u (ω (v : U) * m4q u (v : U))
          = m4p u (ω (v : U)) * (v : U) := by
        rw [map_mul, m4p_m4q hU hu5 hwV]
      have hyd : ω (ω (v : U) * m4q u (v : U))
          * m4p u (ω (v : U) * m4q u (v : U)) = 1 := by
        rw [hy1, hy2]
        calc (ω (ω (v : U)) * m4q u (ω (v : U)))
              * (m4p u (ω (v : U)) * (v : U))
            = ω (ω (v : U)) * (m4p u (ω (v : U)) * m4q u (ω (v : U)))
              * (v : U) := by ac_rfl
          _ = ω (ω (v : U)) * ω (v : U) * (v : U) := by rw [m4pq_eq hU hu5 hVω]
          _ = 1 := m4step1 hω3 hfix (v : U)
      exact m4eq_of_mul_eq_one hU hyd
    · intro hcon
      exact hy (Subtype.ext_iff.mp hcon)

private lemma m4V1_g_mem {ω u g : MulAut U} (hu5 : u ^ 5 = 1) (hgω : g * ω = ω * g)
    (hg : g * u * g⁻¹ = u ^ 2) {v : U} (hv : v ∈ m4V1 ω u) : g v ∈ m4V2 ω u := by
  rw [mem_m4V1] at hv
  rw [mem_m4V2]
  refine ⟨m4V_g_mem hg hv.1, ?_⟩
  have hgω' : g (ω v) = ω (g v) := by
    rw [← MulAut.mul_apply, hgω, MulAut.mul_apply]
  rw [← hgω', hv.2]
  exact m4g_p hu5 hg v

private lemma m4V2_g_mem {ω u g : MulAut U} (hu5 : u ^ 5 = 1) (hgω : g * ω = ω * g)
    (hg : g * u * g⁻¹ = u ^ 2) {v : U} (hv : v ∈ m4V2 ω u) : g v ∈ m4V1 ω u := by
  rw [mem_m4V2] at hv
  rw [mem_m4V1]
  refine ⟨m4V_g_mem hg hv.1, ?_⟩
  have hgω' : g (ω v) = ω (g v) := by
    rw [← MulAut.mul_apply, hgω, MulAut.mul_apply]
  rw [← hgω', hv.2]
  exact m4g_q hu5 hg v

private lemma m4V1_ne_bot_iff_m4V2_ne_bot {ω u g : MulAut U} (hu5 : u ^ 5 = 1)
    (hgω : g * ω = ω * g) (hg : g * u * g⁻¹ = u ^ 2) :
    m4V1 ω u ≠ ⊥ ↔ m4V2 ω u ≠ ⊥ := by
  constructor
  · intro h
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h ⊢
    obtain ⟨v, hv⟩ := h
    refine ⟨⟨g (v : U), m4V1_g_mem hu5 hgω hg v.2⟩, ?_⟩
    intro hcon
    apply hv
    apply Subtype.ext
    have := congrArg (fun x : U => g⁻¹ x) (Subtype.ext_iff.mp hcon)
    simpa using this
  · intro h
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h ⊢
    obtain ⟨v, hv⟩ := h
    refine ⟨⟨g (v : U), m4V2_g_mem hu5 hgω hg v.2⟩, ?_⟩
    intro hcon
    apply hv
    apply Subtype.ext
    have := congrArg (fun x : U => g⁻¹ x) (Subtype.ext_iff.mp hcon)
    simpa using this

private lemma m4V1_u_mem {ω u : MulAut U} (huω : u * ω = ω * u) {v : U}
    (hv : v ∈ m4V1 ω u) : u v ∈ m4V1 ω u := by
  rw [mem_m4V1] at hv ⊢
  refine ⟨m4V_u_mem hv.1, ?_⟩
  rw [m4omega_u_apply huω, hv.2]
  exact m4u_p_comm v

private lemma m4V2_u_mem {ω u : MulAut U} (huω : u * ω = ω * u) {v : U}
    (hv : v ∈ m4V2 ω u) : u v ∈ m4V2 ω u := by
  rw [mem_m4V2] at hv ⊢
  refine ⟨m4V_u_mem hv.1, ?_⟩
  rw [m4omega_u_apply huω, hv.2]
  exact m4u_q_comm v

private lemma m4V1_fixfree {ω u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1)
    {v : U} (hv : v ∈ m4V1 ω u) (h : u v = v) : v = 1 := by
  rw [mem_m4V1] at hv
  exact m4fix_of_memV hU hu5 hv.1 h

private lemma m4V2_fixfree {ω u : MulAut U} (hU : ∀ w : U, w * w = 1) (hu5 : u ^ 5 = 1)
    {v : U} (hv : v ∈ m4V2 ω u) (h : u v = v) : v = 1 := by
  rw [mem_m4V2] at hv
  exact m4fix_of_memV hU hu5 hv.1 h

private noncomputable def m4Restrict (σ : MulAut U) (H : Subgroup U)
    (hH : ∀ x ∈ H, σ x ∈ H) : MulAut H :=
  let f : H →* H :=
    { toFun := fun x => ⟨σ x, hH x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  MulEquiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact σ.injective (Subtype.ext_iff.mp hxy)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

private lemma m4Restrict_apply (σ : MulAut U) (H : Subgroup U)
    (hH : ∀ x ∈ H, σ x ∈ H) (x : H) : ((m4Restrict σ H hH x : H) : U) = σ x := rfl

private lemma m4Restrict_pow (σ : MulAut U) (H : Subgroup U)
    (hH : ∀ x ∈ H, σ x ∈ H) (n : ℕ) (x : H) :
    (((m4Restrict σ H hH) ^ n) x : U) = (σ ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, m4Restrict_apply, ← MulAut.mul_apply, ← pow_succ]

private lemma m4card_ge_sixteen {u : MulAut U} (hU : ∀ w : U, w * w = 1)
    (hu5 : u ^ 5 = 1) (H : Subgroup U) (hstab : ∀ x ∈ H, u x ∈ H) (hne : H ≠ ⊥)
    (hfixH : ∀ x ∈ H, u x = x → x = 1) : 16 ≤ Nat.card H := by
  refine CFSG.QuasithinUnique.B42A57.card_ge_sixteen_of_order_five
    (fun w => Subtype.ext (hU (w : U))) (m4Restrict u H hstab) ?_ ?_
  · ext x
    simp [m4Restrict_pow, hu5]
  · intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : u x = x := by
      have := congrArg (fun f : MulAut H => ((f ⟨x, hx⟩ : H) : U)) h
      simpa [m4Restrict_apply] using this
    exact hfixH x hx h1

private lemma m4V1_card_ge_sixteen {ω u : MulAut U} (hU : ∀ w : U, w * w = 1)
    (hu5 : u ^ 5 = 1) (huω : u * ω = ω * u) (hne : m4V1 ω u ≠ ⊥) :
    16 ≤ Nat.card (m4V1 ω u) :=
  m4card_ge_sixteen hU hu5 (m4V1 ω u) (fun _ hx => m4V1_u_mem huω hx) hne
    (fun _ hx h => m4V1_fixfree hU hu5 hx h)

private lemma m4V2_card_ge_sixteen {ω u : MulAut U} (hU : ∀ w : U, w * w = 1)
    (hu5 : u ^ 5 = 1) (huω : u * ω = ω * u) (hne : m4V2 ω u ≠ ⊥) :
    16 ≤ Nat.card (m4V2 ω u) :=
  m4card_ge_sixteen hU hu5 (m4V2 ω u) (fun _ hx => m4V2_u_mem huω hx) hne
    (fun _ hx h => m4V2_fixfree hU hu5 hx h)

theorem two_pow_eight_le_index_of_conj_sq {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ w : U, w * w = 1) {ω u g : MulAut U} (hω3 : ω ^ 3 = 1)
    (hfix : ∀ w : U, ω w = w → w = 1) (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1)
    (huω : u * ω = ω * u) (hgω : g * ω = ω * g) (hg : g * u * g⁻¹ = u ^ 2) :
    2 ^ 8 ≤ (fixV (zpowers u)).index := by
  have hker : (m4phi u).ker = fixV (zpowers u) := by
    ext v
    rw [MonoidHom.mem_ker, CFSG.Quasithin.mem_fixV_zpowers_iff_apply, m4phi_apply]
    constructor
    · intro h; exact mul_inv_eq_one.mp h
    · intro h; rw [h, mul_inv_cancel]
  have hcardV : Nat.card (m4V u) = (fixV (zpowers u)).index := by
    rw [m4V, ← hker]
    exact (Subgroup.index_ker (m4phi u)).symm
  have hinf : m4V1 ω u ⊓ m4V2 ω u = ⊥ := m4V1_inf_m4V2 hU hfix hu5
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (m4V1 ω u)
    (m4V2 ω u) (fun x _ y _ => mul_comm x y)).1
  rw [hinf, Subgroup.card_bot, mul_one] at hprod
  have hiff := m4V1_ne_bot_iff_m4V2_ne_bot (ω := ω) (u := u) (g := g) hu5 hgω hg
  have h1ne : m4V1 ω u ≠ ⊥ := by
    rcases m4V1_ne_bot_or_m4V2_ne_bot hU hω3 hfix hu5 huω hu1 with h | h
    · exact h
    · exact hiff.mpr h
  have h2ne : m4V2 ω u ≠ ⊥ := hiff.mp h1ne
  have h16a : 16 ≤ Nat.card (m4V1 ω u) := m4V1_card_ge_sixteen hU hu5 huω h1ne
  have h16b : 16 ≤ Nat.card (m4V2 ω u) := m4V2_card_ge_sixteen hU hu5 huω h2ne
  have hle : m4V1 ω u ⊔ m4V2 ω u ≤ m4V u :=
    sup_le (fun _ hv => (mem_m4V1.mp hv).1) (fun _ hv => (mem_m4V2.mp hv).1)
  calc 2 ^ 8 = 16 * 16 := by norm_num
    _ ≤ Nat.card (m4V1 ω u) * Nat.card (m4V2 ω u) := Nat.mul_le_mul h16a h16b
    _ = Nat.card ↥(m4V1 ω u ⊔ m4V2 ω u) := hprod.symm
    _ ≤ Nat.card (m4V u) := Subgroup.card_le_of_le hle
    _ = (fixV (zpowers u)).index := hcardV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
