module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4B
public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4C
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourCenterFusion
public import CFSG.Quasithin.EmptyFaithful.SzN27Cfg

public section

namespace CFSG.Quasithin.SzN27.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one card_and_isSylowTwoOf_antiUnipotent
  mem_antiUnipotentCenter_iff_central)
open CFSG.LocalAnalysis.SymplecticFourFusion (centralizer_center_eq)
open CFSG.QuasithinUnique.Fin257.Sp4
open CFSG.QuasithinUnique CFSG.Quasithin.SzN27
open Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem dSp_conj_tau (s t : Kˣ) (a : K) :
    dSp s t * (uElt a 0 0 0)⁻¹ * (dSp s t)⁻¹ = uElt ((s : K) * ((t⁻¹ : Kˣ) : K) * a) 0 0 0 := by
  rw [uElt_inv, dSp_conj_uElt]
  simp

theorem dSp_conj_sigma (s t : Kˣ) (e : K) :
    dSp s t * (uElt 0 0 0 e)⁻¹ * (dSp s t)⁻¹ = uElt 0 0 0 ((t : K) ^ 2 * e) := by
  rw [uElt_inv, dSp_conj_uElt]
  simp

theorem shape_A2 (a₀ b₀ c₀ d₀ s' a : K) :
    ∃ B C : K, uElt a 0 0 0 * uElt a₀ b₀ c₀ d₀ * uElt s' 0 0 0 * (uElt a₀ b₀ c₀ d₀)⁻¹ =
      uElt (a + s') B C 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?b, ?c, ?h⟩
  case h =>
    rw [uElt_inv, uElt_mul, uElt_mul, uElt_mul]
    congr 1
    · linear_combination a₀ * h2
    · rfl
    · rfl
    · linear_combination d₀ * h2

theorem shape_A1 (a₀ b₀ c₀ d₀ e e' : K) :
    ∃ B C : K, uElt 0 0 0 e * uElt a₀ b₀ c₀ d₀ * uElt 0 0 0 e' * (uElt a₀ b₀ c₀ d₀)⁻¹ =
      uElt 0 B C (e + e') := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?b, ?c, ?h⟩
  case h =>
    rw [uElt_inv, uElt_mul, uElt_mul, uElt_mul]
    congr 1
    · linear_combination a₀ * h2
    · rfl
    · rfl
    · linear_combination d₀ * h2


omit [CharP K 2] in
theorem diag_cube {y : antiSp K} (hup : ∀ i j : Fin 4, j < i → glMat (y : GL (Fin 4) K) i j = 0)
    (hy3 : y ^ 3 = 1) : (glMat (y : GL (Fin 4) K) 1 1) ^ 3 = 1 := by
  have h1 := congrArg (fun m : antiSp K => glMat (m : GL (Fin 4) K) 1 1) hy3
  have e : glMat ((y ^ 3 : antiSp K) : GL (Fin 4) K) =
      glMat (y : GL (Fin 4) K) * glMat (y : GL (Fin 4) K) * glMat (y : GL (Fin 4) K) := by
    rw [pow_three']
    rfl
  have h10 := hup 1 0 (by decide)
  have h21 := hup 2 1 (by decide)
  have h31 := hup 3 1 (by decide)
  have h20 := hup 2 0 (by decide)
  have h30 := hup 3 0 (by decide)
  have h32 := hup 3 2 (by decide)
  simp only [e] at h1
  simp [Matrix.mul_apply, Fin.sum_univ_four, h10, h21, h31, h20, h30, h32] at h1
  linear_combination h1

theorem eq_one_of_sq_eq_one {s : K} (h : s ^ 2 = 1) : s = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (s - 1) ^ 2 = 0 := by linear_combination h + (1 - s) * h2
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  linear_combination this

theorem char_conditions {s t b₀ c₀ b c : K} (hx : b₀ ≠ 0 ∨ c₀ ≠ 0)
    (hxb : s * t * b₀ = b₀) (hxc : s ^ 2 * c₀ = c₀) (hv : s * t * b ≠ b ∨ s ^ 2 * c ≠ c) :
    t ≠ 1 ∧ s ≠ t := by
  rcases hx with hb₀ | hc₀
  · have hst : s * t = 1 := by
      have : (s * t - 1) * b₀ = 0 := by linear_combination hxb
      have := (mul_eq_zero.mp this).resolve_right hb₀
      linear_combination this
    have hs2 : s ^ 2 ≠ 1 := by
      intro h
      rcases hv with hv | hv
      · exact hv (by rw [hst, one_mul])
      · exact hv (by rw [h, one_mul])
    refine ⟨fun ht => hs2 ?_, fun hs => hs2 ?_⟩
    · rw [ht, mul_one] at hst
      rw [hst]
      norm_num
    · rw [← hs] at hst
      rw [sq]
      exact hst
  · have hs2 : s ^ 2 = 1 := by
      have : (s ^ 2 - 1) * c₀ = 0 := by linear_combination hxc
      have := (mul_eq_zero.mp this).resolve_right hc₀
      linear_combination this
    have hs1 : s = 1 := eq_one_of_sq_eq_one hs2
    have ht : t ≠ 1 := by
      intro ht
      rcases hv with hv | hv
      · exact hv (by rw [hs1, ht]; ring)
      · exact hv (by rw [hs2, one_mul])
    exact ⟨ht, by rw [hs1]; exact fun h => ht h.symm⟩

omit [CharP K 2] in
theorem torus_conj_mem [Finite K] [CharP K 2] {H : Subgroup (antiSp K)} (hUH : antiUnipotent K ≤ H)
    (hHB : H ≤ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) (a b : Kˣ) :
    ∀ h ∈ H, dSp a b * h * (dSp a b)⁻¹ ∈ H := by
  intro h hh
  obtain ⟨u, s, t, hu, rfl, -, -⟩ := exists_unip_dSp_of_mem_normalizer (hHB hh)
  have huH : u ∈ H := hUH hu
  have hdH : dSp s t ∈ H := by
    have := H.mul_mem (H.inv_mem huH) hh
    simpa using this
  have hc : dSp a b * dSp s t * (dSp a b)⁻¹ = dSp s t := by
    rw [dSp_inv, dSp_mul, dSp_mul]
    congr 1 <;> simp
  have e : dSp a b * (u * dSp s t) * (dSp a b)⁻¹ = (dSp a b * u * (dSp a b)⁻¹) * dSp s t := by
    calc dSp a b * (u * dSp s t) * (dSp a b)⁻¹
        = dSp a b * u * (dSp a b)⁻¹ * (dSp a b * dSp s t * (dSp a b)⁻¹) := by group
      _ = (dSp a b * u * (dSp a b)⁻¹) * dSp s t := by rw [hc]
  rw [e]
  exact H.mul_mem (hUH ((Subgroup.mem_normalizer_iff.mp (dSp_mem_normalizer a b) u).mp hu)) hdH

theorem coords_of_y {H : Subgroup (antiSp K)}
    (hUH : antiUnipotent K ≤ Subgroup.normalizer (H : Set (antiSp K)))
    {u₀ : antiSp K} (hu₀ : u₀ ∈ antiUnipotent K) {s t : Kˣ} (hy : u₀ * dSp s t ∈ H)
    (hst : (s : K) ≠ t) (ht : (t : K) ≠ 1) :
    (∀ α : K, ∃ B C : K, uElt α B C 0 ∈ H) ∧ (∀ δ : K, ∃ B C : K, uElt 0 B C δ ∈ H) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a₀, b₀, c₀, d₀, rfl⟩ := hu₀
  have hcomm : ∀ τ ∈ antiUnipotent K,
      τ * (uElt a₀ b₀ c₀ d₀ * dSp s t) * τ⁻¹ * (uElt a₀ b₀ c₀ d₀ * dSp s t)⁻¹ ∈ H := by
    intro τ hτ
    have h1 : τ * (uElt a₀ b₀ c₀ d₀ * dSp s t) * τ⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hUH hτ) _).mp hy
    exact H.mul_mem h1 (H.inv_mem hy)
  have htinv : ((t⁻¹ : Kˣ) : K) = ((t : K))⁻¹ := Units.val_inv_eq_inv_val t
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  constructor
  · intro α
    have hne : (1 : K) + (s : K) * ((t : K))⁻¹ ≠ 0 := by
      intro h
      apply hst
      have h3 : (s : K) + t = 0 := by
        calc (s : K) + t = t * (1 + s * (t : K)⁻¹) := by field_simp; ring
          _ = 0 := by rw [h, mul_zero]
      exact CharTwo.add_eq_zero.mp h3
    set a : K := α / (1 + (s : K) * (t : K)⁻¹) with hadef
    have := hcomm (uElt a 0 0 0) (uElt_mem_antiUnipotent _ _ _ _)
    have e : uElt a 0 0 0 * (uElt a₀ b₀ c₀ d₀ * dSp s t) * (uElt a 0 0 0)⁻¹ *
        (uElt a₀ b₀ c₀ d₀ * dSp s t)⁻¹ = uElt a 0 0 0 * uElt a₀ b₀ c₀ d₀ *
          (dSp s t * (uElt a 0 0 0)⁻¹ * (dSp s t)⁻¹) * (uElt a₀ b₀ c₀ d₀)⁻¹ := by group
    rw [e, dSp_conj_tau, htinv] at this
    obtain ⟨B, C, hBC⟩ := shape_A2 a₀ b₀ c₀ d₀ ((s : K) * ((t : K))⁻¹ * a) a
    rw [hBC] at this
    refine ⟨B, C, ?_⟩
    have hα : a + (s : K) * (t : K)⁻¹ * a = α := by
      have : a * (1 + (s : K) * (t : K)⁻¹) = α := div_mul_cancel₀ α hne
      linear_combination this
    rwa [hα] at this
  · intro δ
    have hne : (1 : K) + (t : K) ^ 2 ≠ 0 := by
      have h1 : (1 : K) + (t : K) ^ 2 = (1 + t) ^ 2 := by linear_combination (-(t : K)) * h2
      rw [h1]
      refine pow_ne_zero 2 fun h => ht ?_
      have h3 : (1 : K) + t = 0 := h
      exact (CharTwo.add_eq_zero.mp h3).symm
    set e₁ : K := δ / (1 + (t : K) ^ 2) with he₁def
    have := hcomm (uElt 0 0 0 e₁) (uElt_mem_antiUnipotent _ _ _ _)
    have e : uElt 0 0 0 e₁ * (uElt a₀ b₀ c₀ d₀ * dSp s t) * (uElt 0 0 0 e₁)⁻¹ *
        (uElt a₀ b₀ c₀ d₀ * dSp s t)⁻¹ = uElt 0 0 0 e₁ * uElt a₀ b₀ c₀ d₀ *
          (dSp s t * (uElt 0 0 0 e₁)⁻¹ * (dSp s t)⁻¹) * (uElt a₀ b₀ c₀ d₀)⁻¹ := by group
    rw [e, dSp_conj_sigma] at this
    obtain ⟨B, C, hBC⟩ := shape_A1 a₀ b₀ c₀ d₀ e₁ ((t : K) ^ 2 * e₁)
    rw [hBC] at this
    refine ⟨B, C, ?_⟩
    have hδ : e₁ + (t : K) ^ 2 * e₁ = δ := by
      have : e₁ * (1 + (t : K) ^ 2) = δ := div_mul_cancel₀ δ hne
      linear_combination this
    rwa [hδ] at this


omit [CharP K 2] in
theorem U_eq_of_le {U P : Subgroup (antiSp K)} [Finite K] (hU : IsSylowTwoOf U ⊤) (hUP : U ≤ P)
    (hP : IsPGroup 2 ↥P) : P = U :=
  IsSylowTwoOf.eq_of_le hU hUP le_top hP

theorem not_elDataPlus [Finite K] (hK : 4 ≤ Nat.card K)
    (hS : K1.SylowCentralizingAutInner (antiSp K)) {V H : Subgroup (antiSp K)}
    {ζ : MulAut (antiSp K)} (hd : ElDataPlus (antiUnipotent K) V H ζ) : False := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hSyl : IsSylowTwoOf (antiUnipotent K) ⊤ := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  obtain ⟨x, hx⟩ := hS (antiUnipotent K) hSyl ζ hd.fixT
  have hxU : x ∈ antiUnipotent K := by
    rw [← centralizer_center_eq (K := K), Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hx z
    rw [hd.fixT z (antiUnipotentCenter_le hz)] at h1
    have h3 : z * x = x * z := by
      calc z * x = x * (x⁻¹ * z * x) := by group
        _ = x * z := by rw [← h1]
    exact h3
  have hxZ : x ∈ antiUnipotentCenter K := by
    rw [mem_antiUnipotentCenter_iff_central]
    refine ⟨hxU, fun u hu => ?_⟩
    have h1 := hx u
    rw [hd.fixT u hu] at h1
    calc x * u = x * (x⁻¹ * u * x) := by rw [← h1]
      _ = u * x := by group
  have hx1 : x ≠ 1 := by
    intro h
    apply hd.ne
    ext y
    rw [hx y, h]
    simp
  have hxH : ∀ h ∈ H, x * h = h * x := by
    intro h hh
    have h1 := hx h
    rw [hd.fixH h hh] at h1
    calc x * h = x * (x⁻¹ * h * x) := by rw [← h1]
      _ = h * x := by group
  have hVz : V ≤ antiUnipotentCenter K := V_le_center hd.V4 hd.V2 hd.VT hd.TV hK
  obtain ⟨y, hyH, hy3, hynt⟩ := hd.y3
  obtain ⟨b₀, c₀, rfl⟩ := hxZ
  have hxy : y * uElt 0 b₀ c₀ 0 = uElt 0 b₀ c₀ 0 * y := (hxH y hyH).symm
  have hup := y_upper hVz (hd.HV hyH) hynt hx1 hxy
  have hcube := diag_cube hup hy3
  obtain ⟨u₀, s, t, hu₀, hy, hs, ht⟩ := exists_unip_dSp_of_upper hup
  have ht3 : (t : K) ^ 3 = 1 := by rw [ht]; exact hcube
  have hxcon : dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹ =
      uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 := by
    rw [dSp_conj_uElt]
    simp
  have hxx : dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹ = uElt 0 b₀ c₀ 0 := by
    have hcen : uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀ =
        u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 :=
      antiUnipotentCenter_comm ⟨_, _, rfl⟩ hu₀
    have h1 : y * uElt 0 b₀ c₀ 0 * y⁻¹ = uElt 0 b₀ c₀ 0 := by
      rw [hxy]
      group
    rw [hy] at h1
    have h3 : u₀ * (dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹) * u₀⁻¹ = uElt 0 b₀ c₀ 0 := by
      calc u₀ * (dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹) * u₀⁻¹
          = u₀ * dSp s t * uElt 0 b₀ c₀ 0 * (u₀ * dSp s t)⁻¹ := by group
        _ = uElt 0 b₀ c₀ 0 := h1
    rw [hxcon] at h3 ⊢
    refine (show uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 =
        u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀⁻¹ from ?_).trans h3
    calc uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0
        = uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀ * u₀⁻¹ := by group
      _ = u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀⁻¹ := by rw [hcen]
  obtain ⟨-, hxb, hxc, -⟩ := uElt_inj (hxcon.symm.trans hxx)
  have hx0 : b₀ ≠ 0 ∨ c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact hx1 uElt_zero_eq_one
  push Not at hynt
  obtain ⟨v, hvV, hne⟩ := hynt
  obtain ⟨b, c, rfl⟩ := hVz hvV
  have hvd : dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹ ≠ uElt 0 b c 0 := by
    intro h
    apply hne
    have hcen : u₀ * uElt 0 b c 0 = uElt 0 b c 0 * u₀ :=
      (antiUnipotentCenter_comm ⟨b, c, rfl⟩ hu₀).symm
    calc y * uElt 0 b c 0 = u₀ * (dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹) * dSp s t := by
          rw [hy]
          group
      _ = u₀ * uElt 0 b c 0 * dSp s t := by rw [h]
      _ = uElt 0 b c 0 * u₀ * dSp s t := by rw [hcen]
      _ = uElt 0 b c 0 * y := by
          rw [hy]
          group
  have hv : (s : K) * t * b ≠ b ∨ (s : K) ^ 2 * c ≠ c := by
    by_contra hcon
    push Not at hcon
    apply hvd
    rw [dSp_conj_uElt]
    simp only [mul_zero]
    rw [hcon.1, hcon.2]
  obtain ⟨ht1, hst⟩ := char_conditions hx0 hxb hxc hv
  have hyH' : u₀ * dSp s t ∈ H := by
    rw [← hy]
    exact hyH
  obtain ⟨hα, hδ⟩ := coords_of_y hd.TH hu₀ hyH' hst ht1
  have hUH : antiUnipotent K ≤ H := U_le_of_coords hK hα hδ
  obtain ⟨P, hPH, hHP, hP2, hP3⟩ := hd.quot3
  have hUP : antiUnipotent K ≤ P := by
    intro u hu
    obtain ⟨k, hk⟩ := hSyl.2.1 ⟨u, hu⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (orderOf u) := by
      have : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      exact Nat.Coprime.coprime_dvd_right this (Nat.Coprime.pow_right k (by norm_num))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact P.pow_mem (hP3 u (hUH hu)) m
  have hPU : P = antiUnipotent K := U_eq_of_le hSyl hUP hP2
  have hHB : H ≤ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := hPU ▸ hHP
  have key : ∀ a b : Kˣ, ∀ h, h ∈ H ↔ dSp a b * h * (dSp a b)⁻¹ ∈ H := by
    intro a b h
    refine ⟨torus_conj_mem hUH hHB a b h, fun h' => ?_⟩
    have := torus_conj_mem hUH hHB a⁻¹ b⁻¹ _ h'
    have e : dSp a⁻¹ b⁻¹ * (dSp a b * h * (dSp a b)⁻¹) * (dSp a⁻¹ b⁻¹)⁻¹ = h := by
      rw [← dSp_inv]
      group
    rwa [e] at this
  have hd2N : dSp t 1 ∈ Subgroup.normalizer (H : Set (antiSp K)) :=
    Subgroup.mem_normalizer_iff.mpr (key t 1)
  have ht3u : t ^ 3 = 1 := Units.ext (by simpa using ht3)
  have hd23 : (dSp t 1 : antiSp K) ^ 3 = 1 := by
    rw [dSp_pow, ht3u, one_pow, dSp_one]
  have hd2H : dSp t 1 ∈ H := hd.theta _ hd2N hd23
  have hc := hxH _ hd2H
  have h5 : dSp t 1 * uElt 0 b₀ c₀ 0 * (dSp t 1)⁻¹ = uElt 0 b₀ c₀ 0 := by
    rw [← hc]
    group
  rw [dSp_conj_uElt] at h5
  obtain ⟨-, h6b, h6c, -⟩ := uElt_inj h5
  simp only [Units.val_one, mul_one] at h6b h6c
  have hb₀ : b₀ = 0 := by
    have : ((t : K) - 1) * b₀ = 0 := by linear_combination h6b
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht1)
  have hc₀ : c₀ = 0 := by
    have ht2 : (t : K) ^ 2 ≠ 1 := fun h => ht1 (eq_one_of_sq_eq_one h)
    have : ((t : K) ^ 2 - 1) * c₀ = 0 := by linear_combination h6c
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht2)
  exact hx1 (by rw [hb₀, hc₀]; exact uElt_zero_eq_one)

end CFSG.Quasithin.SzN27.Sp4
