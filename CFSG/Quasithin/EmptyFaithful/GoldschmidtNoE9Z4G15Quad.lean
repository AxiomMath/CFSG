module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenWt
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.NoE9Z4GenGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace PairCtx

variable {Q U Z Cq Hs : Subgroup G} {z : G} (P : PairCtx Q U Z Cq Hs z)
include P

theorem T_inv_mid {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    PairCtx.T x y⁻¹ q = PairCtx.T x y q := by
  have h1 := P.T_mul_mid hx hy (inv_mem hy) hq
  rw [mul_inv_cancel] at h1
  have h2 : PairCtx.T x (1 : G) q = 1 := by
    show ⁅⁅x, (1 : G)⁆, q⁆ = (1 : G)
    simp [commutatorElement_def]
  rw [h2] at h1
  have h3 := P.T_sq hx hy hq
  exact (eq_inv_of_mul_eq_one_right h1.symm).trans (eq_inv_of_mul_eq_one_left h3).symm

theorem T_inv_right {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    PairCtx.T x y q⁻¹ = PairCtx.T x y q := by
  have h1 := P.T_mul_right hx hy hq (inv_mem hq)
  rw [mul_inv_cancel] at h1
  have h2 : PairCtx.T x y (1 : G) = 1 := by
    show ⁅⁅x, y⁆, (1 : G)⁆ = (1 : G)
    simp [commutatorElement_def]
  rw [h2] at h1
  have h3 := P.T_sq hx hy hq
  exact (eq_inv_of_mul_eq_one_right h1.symm).trans (eq_inv_of_mul_eq_one_left h3).symm

theorem T_jacobi {x y q : G} (hx : x ∈ Q) (hy : y ∈ Q) (hq : q ∈ Q) :
    PairCtx.T x y q * PairCtx.T q x y * PairCtx.T y q x = 1 := by
  have hw : (x⁻¹ * ⁅⁅x, y⁻¹⁆, q⁻¹⁆ * x) * (q⁻¹ * ⁅⁅q, x⁻¹⁆, y⁻¹⁆ * q) *
      (y⁻¹ * ⁅⁅y, q⁻¹⁆, x⁻¹⁆ * y) = 1 := by
    simp only [commutatorElement_def]; group
  have conjZ : ∀ {g c : G}, g ∈ Q → c ∈ Z → g⁻¹ * c * g = c := by
    intro g c hg hc
    have := P.Z_central (inv_mem (P.Q_le_H hg)) hc
    rw [this]; group
  have c1 : ⁅⁅x, y⁻¹⁆, q⁻¹⁆ ∈ Z := P.T_mem_Z hx (inv_mem hy) (inv_mem hq)
  have c2 : ⁅⁅q, x⁻¹⁆, y⁻¹⁆ ∈ Z := P.T_mem_Z hq (inv_mem hx) (inv_mem hy)
  have c3 : ⁅⁅y, q⁻¹⁆, x⁻¹⁆ ∈ Z := P.T_mem_Z hy (inv_mem hq) (inv_mem hx)
  rw [conjZ hx c1, conjZ hq c2, conjZ hy c3] at hw
  have e1 : ⁅⁅x, y⁻¹⁆, q⁻¹⁆ = PairCtx.T x y q := by
    show PairCtx.T x y⁻¹ q⁻¹ = _
    rw [P.T_inv_right hx (inv_mem hy) hq, P.T_inv_mid hx hy hq]
  have e2 : ⁅⁅q, x⁻¹⁆, y⁻¹⁆ = PairCtx.T q x y := by
    show PairCtx.T q x⁻¹ y⁻¹ = _
    rw [P.T_inv_right hq (inv_mem hx) hy, P.T_inv_mid hq hx hy]
  have e3 : ⁅⁅y, q⁻¹⁆, x⁻¹⁆ = PairCtx.T y q x := by
    show PairCtx.T y q⁻¹ x⁻¹ = _
    rw [P.T_inv_right hy (inv_mem hq) hx, P.T_inv_mid hy hq hx]
  rw [e1, e2, e3] at hw
  exact hw

end PairCtx

structure Data15 {Q Qe U Z Cq Cqe Hs : Subgroup G} {z : G}
    (P : PairCtx Q U Z Cq Hs z) (Pe : PairCtx Qe U Z Cqe Hs z) {a b : G} {Ua Ub : Subgroup G}
    (_W : WtCtx Pe a b Ua Ub) (e t : G) : Prop where
  Qe_le : Qe ≤ Q
  e_mem : e ∈ Q
  e_fix : ∀ h ∈ Hs, e⁻¹ * (h * e * h⁻¹) ∈ U
  e_cent_a : ∀ u ∈ Ua, ⁅u, e⁆ = 1
  e_cent_b : ∀ u ∈ Ub, ⁅u, e⁆ = 1
  t_mem : t ∈ Hs
  tt_mem : t * t ∈ Q
  ta_mem : t * a * t⁻¹ * a ∈ Q
  tb_mem : t * b * t⁻¹ * b ∈ Q
  tUa : ∀ u ∈ Ua, t⁻¹ * u * t ∈ Ua
  tUb : ∀ u ∈ Ub, t⁻¹ * u * t ∈ Ub

namespace Data15

variable {Q Qe U Z Cq Cqe Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Cq Hs z}
  {Pe : PairCtx Qe U Z Cqe Hs z} {a b : G} {Ua Ub : Subgroup G} {W : WtCtx Pe a b Ua Ub}
  {e t : G}

theorem symm (D : Data15 P Pe W e t) : Data15 P Pe W.symm e t where
  Qe_le := D.Qe_le
  e_mem := D.e_mem
  e_fix := D.e_fix
  e_cent_a := D.e_cent_b
  e_cent_b := D.e_cent_a
  t_mem := D.t_mem
  tt_mem := D.tt_mem
  ta_mem := D.tb_mem
  tb_mem := D.ta_mem
  tUa := D.tUb
  tUb := D.tUa

theorem s_conj (D : Data15 P Pe W e t) {h : G} (hh : h ∈ Hs) {y q : G} (hy : y ∈ Q)
    (hq : q ∈ Q) : PairCtx.T (h * y * h⁻¹) e (h * q * h⁻¹) = PairCtx.T y e q := by
  have he' : h⁻¹ * e * h ∈ Q := by simpa using P.normQ h⁻¹ (inv_mem hh) e D.e_mem
  have h1 := P.T_conj hh hy he' hq
  have e1 : h * (h⁻¹ * e * h) * h⁻¹ = e := by group
  rw [e1] at h1
  rw [h1]
  have hfix : e⁻¹ * (h⁻¹ * e * h) ∈ U := by simpa using D.e_fix h⁻¹ (inv_mem hh)
  exact (P.T_congr_mid hy D.e_mem he' hq hfix).symm

theorem InC_conj_t (D : Data15 P Pe W e t) {x : G} (hx : InC Qe Ub x) :
    InC Qe Ub (t * x * t⁻¹) :=
  ⟨Pe.normQ t D.t_mem x hx.1, fun u hu => by
    rw [Pe.pair_conj_inv D.t_mem (W.Ub_le hu) hx.1]
    exact hx.2 _ (D.tUb u hu)⟩

end Data15

namespace WtCtx

variable {Q U Z Cq Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Cq Hs z} {a b : G}
  {Ua Ub : Subgroup G} (W : WtCtx P a b Ua Ub)
include W

theorem a3_cong {x : G} (hx : InC Q Ub x) :
    x⁻¹ * (a * a * a * x * (a * a * a)⁻¹) ∈ U := by
  have ha := W.a_mem
  obtain ⟨x₁, hx₁def⟩ : ∃ x₁, x₁ = a * x * a⁻¹ := ⟨_, rfl⟩
  have hx₁ : InC Q Ub x₁ := hx₁def ▸ W.InC_conj_a hx
  obtain ⟨x₂, hx₂def⟩ : ∃ x₂, x₂ = a * x₁ * a⁻¹ := ⟨_, rfl⟩
  have hx₂ : InC Q Ub x₂ := hx₂def ▸ W.InC_conj_a hx₁
  obtain ⟨x₃, hx₃def⟩ : ∃ x₃, x₃ = a * x₂ * a⁻¹ := ⟨_, rfl⟩
  have hx₃ : InC Q Ub x₃ := hx₃def ▸ W.InC_conj_a hx₂
  have hu₁ : x₂ * x₁ * x ∈ U := by
    have h1 := W.Ec_a_mem_U hx₂
    unfold Ec at h1
    have e1 : a⁻¹ * x₂ * a = x₁ := by rw [hx₂def]; group
    have e2 : a⁻¹ * a⁻¹ * x₂ * a * a = x := by rw [hx₂def, hx₁def]; group
    rwa [e1, e2] at h1
  have hu₂ : x₃ * x₂ * x₁ ∈ U := by
    have h1 := W.Ec_a_mem_U hx₃
    unfold Ec at h1
    have e1 : a⁻¹ * x₃ * a = x₂ := by rw [hx₃def]; group
    have e2 : a⁻¹ * a⁻¹ * x₃ * a * a = x₁ := by rw [hx₃def, hx₂def]; group
    rwa [e1, e2] at h1
  have hw : x₂ * x₁ ∈ Hs := P.Q_le_H (Q.mul_mem hx₂.1 hx₁.1)
  have key : x₃⁻¹ * x = ((x₂ * x₁) * (x₃ * x₂ * x₁)⁻¹ * (x₂ * x₁)⁻¹) * (x₂ * x₁ * x) := by
    group
  have hmem : x₃⁻¹ * x ∈ U := by
    rw [key]
    exact U.mul_mem (by simpa using P.normU _ hw _ (U.inv_mem hu₂)) hu₁
  have e3 : x⁻¹ * (a * a * a * x * (a * a * a)⁻¹) = (x₃⁻¹ * x)⁻¹ := by
    rw [hx₃def, hx₂def, hx₁def]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e3]
  exact U.inv_mem hmem

end WtCtx

namespace Data15

variable {Q Qe U Z Cq Cqe Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Cq Hs z}
  {Pe : PairCtx Qe U Z Cqe Hs z} {a b : G} {Ua Ub : Subgroup G} {W : WtCtx Pe a b Ua Ub}
  {e t : G}

theorem exists_tfix (D : Data15 P Pe W e t) {x : G} (hx : InC Qe Ub x) (hxU : x ∉ U) :
    ∃ p, InC Qe Ub p ∧ p ∉ U ∧ p⁻¹ * (t * p * t⁻¹) ∈ U := by
  have hx' : InC Qe Ub (t * x * t⁻¹) := D.InC_conj_t hx
  by_cases hc : x⁻¹ * (t * x * t⁻¹) ∈ U
  · exact ⟨x, hx, hxU, hc⟩
  · refine ⟨x * (t * x * t⁻¹), Pe.InC_mul W.Ub_le hx hx', fun hp => hc ?_, ?_⟩
    · have e : x⁻¹ * (t * x * t⁻¹) = (x * x)⁻¹ * (x * (t * x * t⁻¹)) := by group
      rw [e]
      exact U.mul_mem (U.inv_mem (Pe.sq_mem_U hx.1)) hp
    · have e : (x * (t * x * t⁻¹))⁻¹ * (t * (x * (t * x * t⁻¹)) * t⁻¹) =
          ⁅(t * x * t⁻¹)⁻¹, x⁻¹⁆ * ⁅x⁻¹, t * t⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact U.mul_mem (Pe.comm_mem_U (Qe.inv_mem hx'.1) (Qe.inv_mem hx.1))
        (P.comm_mem_U (Q.inv_mem (D.Qe_le hx.1)) D.tt_mem)

theorem quadA (D : Data15 P Pe W e t) {x : G} (hx : InC Qe Ub x) : PairCtx.T x e x = 1 := by
  have hQe := D.Qe_le
  have hxQ : x ∈ Q := hQe hx.1
  by_cases hxU : x ∈ U
  · exact P.T_of_mem_U_left hxU D.e_mem hxQ
  obtain ⟨p, hp, hpU, hpt⟩ := D.exists_tfix hx hxU
  have ha := W.a_mem
  have hpQ : p ∈ Q := hQe hp.1
  obtain ⟨f, hf_def⟩ : ∃ f, f = a * p * a⁻¹ := ⟨_, rfl⟩
  have hf : InC Qe Ub f := hf_def ▸ W.InC_conj_a hp
  have hfQ : f ∈ Q := hQe hf.1
  obtain ⟨g₂, hg₂_def⟩ : ∃ g₂, g₂ = a * f * a⁻¹ := ⟨_, rfl⟩
  have hg₂ : InC Qe Ub g₂ := hg₂_def ▸ W.InC_conj_a hf
  have hg₂Q : g₂ ∈ Q := hQe hg₂.1
  have hfU : f ∉ U := fun h => hpU (by
    have h1 := Pe.normU a⁻¹ (inv_mem ha) f h
    have e : a⁻¹ * f * a⁻¹⁻¹ = p := by rw [hf_def]; group
    rwa [e] at h1)
  have hpf : p⁻¹ * f ∉ U := hf_def ▸ W.not_cong hp hpU
  have hEU : g₂ * f * p ∈ U := by
    have hEc : Ec a g₂ = g₂ * f * p := by
      unfold Ec
      have e1 : a⁻¹ * g₂ * a = f := by rw [hg₂_def]; group
      have e2 : a⁻¹ * a⁻¹ * g₂ * a * a = p := by rw [hg₂_def, hf_def]; group
      rw [e1, e2]
    exact hEc ▸ W.Ec_a_mem_U hg₂
  have hC3 : g₂⁻¹ * (p * f) ∈ U := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = g₂ * f * p := ⟨_, rfl⟩
    have hu₀U : u₀ ∈ U := hu₀ ▸ hEU
    have hg : g₂ = u₀ * p⁻¹ * f⁻¹ := by rw [hu₀]; group
    have hfp : f * p ∈ Hs := P.Q_le_H (Q.mul_mem hfQ hpQ)
    have e : g₂⁻¹ * (p * f) =
        ((f * p) * u₀⁻¹ * (f * p)⁻¹) * (f * (p * p) * f⁻¹) * (f * f) := by
      rw [hg]; group
    rw [e]
    refine U.mul_mem (U.mul_mem ?_ ?_) (P.sq_mem_U hfQ)
    · simpa using P.normU _ hfp _ (U.inv_mem hu₀U)
    · exact P.normU f (P.Q_le_H hfQ) _ (P.sq_mem_U hpQ)
  have hC2 : (t * f * t⁻¹)⁻¹ * g₂ ∈ U := by
    have hq₀ := D.ta_mem
    have hX : a⁻¹ * (t * p * t⁻¹) * a ∈ Q := by
      simpa using P.normQ a⁻¹ (inv_mem ha) _ (P.normQ t D.t_mem p hpQ)
    have h1 : ⁅t * a * t⁻¹ * a, (a⁻¹ * (t * p * t⁻¹) * a)⁻¹⁆ ∈ U :=
      P.comm_mem_U hq₀ (Q.inv_mem hX)
    have h2 : a⁻¹ * ((t * p * t⁻¹)⁻¹ * p) * a⁻¹⁻¹ ∈ U :=
      P.normU a⁻¹ (inv_mem ha) _ (by simpa using U.inv_mem hpt)
    have h3 : a⁻¹ * (p⁻¹ * (a * a * a * p * (a * a * a)⁻¹)) * a⁻¹⁻¹ ∈ U :=
      P.normU a⁻¹ (inv_mem ha) _ (W.a3_cong hp)
    have e : (t * f * t⁻¹)⁻¹ * g₂ =
        ⁅t * a * t⁻¹ * a, (a⁻¹ * (t * p * t⁻¹) * a)⁻¹⁆ *
          (a⁻¹ * ((t * p * t⁻¹)⁻¹ * p) * a⁻¹⁻¹) *
          (a⁻¹ * (p⁻¹ * (a * a * a * p * (a * a * a)⁻¹)) * a⁻¹⁻¹) := by
      rw [hg₂_def, hf_def]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact U.mul_mem (U.mul_mem h1 h2) h3
  have hp' : t * p * t⁻¹ ∈ Q := P.normQ t D.t_mem p hpQ
  have hf' : t * f * t⁻¹ ∈ Q := P.normQ t D.t_mem f hfQ
  have hpQ' : (t * p * t⁻¹)⁻¹ * p ∈ U := by simpa using U.inv_mem hpt
  have hspp : PairCtx.T p e p = 1 := by
    have h1 := D.s_conj D.t_mem hpQ hfQ
    rw [P.T_congr_left hp' hpQ D.e_mem hf' hpQ',
      P.T_congr_right hpQ D.e_mem hf' hg₂Q hC2,
      P.T_congr_right hpQ D.e_mem hg₂Q (Q.mul_mem hpQ hfQ) hC3,
      P.T_mul_right hpQ D.e_mem hpQ hfQ] at h1
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  have hsff : PairCtx.T f e f = 1 := by
    have h1 := D.s_conj ha hpQ hpQ
    rw [← hf_def] at h1
    rw [h1]
    exact hspp
  have hsgg : PairCtx.T g₂ e g₂ = 1 := by
    have h1 := D.s_conj ha hfQ hfQ
    rw [← hg₂_def] at h1
    rw [h1]
    exact hsff
  rcases W.pigeon hp hf hx hpU hfU hpf with h | h | h | h
  · exact absurd (by simpa using h) hxU
  · rw [P.T_congr_left hxQ hpQ D.e_mem hxQ h, P.T_congr_right hpQ D.e_mem hxQ hpQ h]
    exact hspp
  · rw [P.T_congr_left hxQ hfQ D.e_mem hxQ h, P.T_congr_right hfQ D.e_mem hxQ hfQ h]
    exact hsff
  · have hxg : x⁻¹ * g₂ ∈ U := by
      have e : x⁻¹ * g₂ = (x⁻¹ * (p * f)) * (g₂⁻¹ * (p * f))⁻¹ := by group
      rw [e]
      exact U.mul_mem h (U.inv_mem hC3)
    rw [P.T_congr_left hxQ hg₂Q D.e_mem hxQ hxg, P.T_congr_right hg₂Q D.e_mem hxQ hg₂Q hxg]
    exact hsgg

theorem psiA (D : Data15 P Pe W e t) {x y : G} (hx : InC Qe Ub x) (hy : InC Qe Ub y) :
    PairCtx.T x y e = 1 := by
  have hxQ : x ∈ Q := D.Qe_le hx.1
  have hyQ : y ∈ Q := D.Qe_le hy.1
  have hxy : InC Qe Ub (x * y) := Pe.InC_mul W.Ub_le hx hy
  have h0 := D.quadA hxy
  rw [P.T_mul_left hxQ hyQ D.e_mem (Q.mul_mem hxQ hyQ),
    P.T_mul_right hxQ D.e_mem hxQ hyQ, P.T_mul_right hyQ D.e_mem hxQ hyQ,
    D.quadA hx, D.quadA hy, one_mul, mul_one] at h0
  have hj := P.T_jacobi hxQ hyQ D.e_mem
  rw [P.T_swap hxQ D.e_mem hyQ] at hj
  rw [mul_assoc, h0, mul_one] at hj
  exact hj

theorem mixed15 (D : Data15 P Pe W e t) {x y q : G} (hx : InC Qe Ub x) (hy : y ∈ Q)
    (hq : q ∈ Q) (fy1 : y⁻¹ * (a⁻¹ * y * a⁻¹⁻¹) ∈ U) (fq1 : q⁻¹ * (a⁻¹ * q * a⁻¹⁻¹) ∈ U) :
    PairCtx.T x y q = 1 ∧ PairCtx.T y x q = 1 ∧ PairCtx.T y q x = 1 := by
  have ha := W.a_mem
  have hai : a⁻¹ ∈ Hs := inv_mem ha
  have haai : a⁻¹ * a⁻¹ ∈ Hs := mul_mem hai hai
  have hxQ : x ∈ Q := D.Qe_le hx.1
  have hE : Ec a x ∈ U := W.Ec_a_mem_U hx
  have fy2 := P.fix_sq hai fy1
  have fq2 := P.fix_sq hai fq1
  have hx1 : a⁻¹ * x * a ∈ Q := by
    have := P.normQ a⁻¹ hai x hxQ
    simpa using this
  have hx2 : a⁻¹ * a⁻¹ * x * a * a ∈ Q := by
    have := P.normQ (a⁻¹ * a⁻¹) haai x hxQ
    simpa [mul_assoc] using this
  have e1 : a⁻¹ * x * a = a⁻¹ * x * a⁻¹⁻¹ := by rw [inv_inv]
  have e2 : a⁻¹ * a⁻¹ * x * a * a = (a⁻¹ * a⁻¹) * x * (a⁻¹ * a⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]; simp only [mul_assoc]
  have h1 : PairCtx.T x y q = 1 := by
    have h0 : PairCtx.T (Ec a x) y q = 1 := P.T_of_mem_U_left hE hy hq
    unfold Ec at h0
    rw [P.T_mul_left (Q.mul_mem hxQ hx1) hx2 hy hq, P.T_mul_left hxQ hx1 hy hq,
      e1, e2, P.T_shift_left hai hxQ hy hq fy1 fq1,
      P.T_shift_left haai hxQ hy hq fy2 fq2] at h0
    exact P.eq_one_of_mul_mul (P.T_mem_Z hxQ hy hq) h0
  refine ⟨h1, by rw [P.T_swap hxQ hy hq]; exact h1, ?_⟩
  have h0 : PairCtx.T y q (Ec a x) = 1 := P.T_of_mem_U_right hy hq hE
  unfold Ec at h0
  rw [P.T_mul_right hy hq (Q.mul_mem hxQ hx1) hx2, P.T_mul_right hy hq hxQ hx1,
    e1, e2, P.T_shift_right hai hy hq hxQ fy1 fq1,
    P.T_shift_right haai hy hq hxQ fy2 fq2] at h0
  exact P.eq_one_of_mul_mul (P.T_mem_Z hy hq hxQ) h0

theorem T_xye_xee (D : Data15 P Pe W e t) {x y : G} (hx : x ∈ Qe) (hy : y ∈ Qe) :
    PairCtx.T x y e = 1 ∧ PairCtx.T x e e = 1 := by
  have hQe := D.Qe_le
  have hxQ : x ∈ Q := hQe hx
  have hyQ : y ∈ Q := hQe hy
  have ha := W.a_mem
  have hb := W.b_mem
  have hxA := W.InC_Ec_b hx
  have hxB := W.InC_Ec_a hx
  have hyA := W.InC_Ec_b hy
  have hyB := W.InC_Ec_a hy
  have hxAQ : Ec b x ∈ Q := hQe hxA.1
  have hxBQ : Ec a x ∈ Q := hQe hxB.1
  have hyAQ : Ec b y ∈ Q := hQe hyA.1
  have hyBQ : Ec a y ∈ Q := hQe hyB.1
  have hxd := W.decomp_Q hx
  have hyd := W.decomp_Q hy
  have fe : e⁻¹ * (a⁻¹ * e * a⁻¹⁻¹) ∈ U := D.e_fix a⁻¹ (inv_mem ha)
  have feb : e⁻¹ * (b⁻¹ * e * b⁻¹⁻¹) ∈ U := D.e_fix b⁻¹ (inv_mem hb)
  have fxB : (Ec a x)⁻¹ * (a⁻¹ * Ec a x * a⁻¹⁻¹) ∈ U := by
    have := P.fix_inv ha (W.symm.conj_b_cong hxB)
    simpa using this
  have fyB : (Ec a y)⁻¹ * (a⁻¹ * Ec a y * a⁻¹⁻¹) ∈ U := by
    have := P.fix_inv ha (W.symm.conj_b_cong hyB)
    simpa using this
  have hxxQ : Ec b x * Ec a x ∈ Q := Q.mul_mem hxAQ hxBQ
  have hyyQ : Ec b y * Ec a y ∈ Q := Q.mul_mem hyAQ hyBQ
  refine ⟨?_, ?_⟩
  · rw [P.T_congr_left hxQ hxxQ hyQ D.e_mem hxd,
      P.T_congr_mid hxxQ hyQ hyyQ D.e_mem hyd,
      P.T_mul_left hxAQ hxBQ hyyQ D.e_mem, P.T_mul_mid hxAQ hyAQ hyBQ D.e_mem,
      P.T_mul_mid hxBQ hyAQ hyBQ D.e_mem]
    have hAA : PairCtx.T (Ec b x) (Ec b y) e = 1 := D.psiA hxA hyA
    have hAB : PairCtx.T (Ec b x) (Ec a y) e = 1 :=
      (D.mixed15 hxA hyBQ D.e_mem fyB fe).1
    have hBA : PairCtx.T (Ec a x) (Ec b y) e = 1 := by
      rw [← P.T_swap hxBQ hyAQ D.e_mem]
      exact (D.mixed15 hyA hxBQ D.e_mem fxB fe).1
    have hBB : PairCtx.T (Ec a x) (Ec a y) e = 1 := D.symm.psiA hxB hyB
    rw [hAA, hAB, hBA, hBB]
    simp
  · rw [P.T_congr_left hxQ hxxQ D.e_mem D.e_mem hxd, P.T_mul_left hxAQ hxBQ D.e_mem D.e_mem]
    have hA : PairCtx.T (Ec b x) e e = 1 := (D.mixed15 hxA D.e_mem D.e_mem fe fe).1
    have hB : PairCtx.T (Ec a x) e e = 1 :=
      (D.symm.mixed15 hxB D.e_mem D.e_mem feb feb).1
    rw [hA, hB]
    simp

end Data15

end CFSG.Quasithin.NoE9Z4GenGrp
