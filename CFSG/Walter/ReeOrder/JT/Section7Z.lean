module

public import CFSG.Walter.ReeOrder.JT.Section7Y
import CFSG.Walter.Transitivity.OddCore

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG CFSG.Walter.Transitivity

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_mem_zpowers_of_not_nine_dvd (h9 : ¬ 9 ∣ Nat.card X) {a b : X}
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ n : X, n * b * n⁻¹ ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card X := ha ▸ orderOf_dvd_natCard a
  have hfac : (Nat.card X).factorization 3 = 1 := by
    have h1 : 1 ≤ (Nat.card X).factorization 3 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
    have h2 : ¬ 2 ≤ (Nat.card X).factorization 3 := fun h2 => h9 (by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mpr h2
      simpa using this)
    omega
  let Sa : Sylow 3 X := Sylow.ofCard (Subgroup.zpowers a)
    (by rw [Nat.card_zpowers, ha, hfac, pow_one])
  let Sb : Sylow 3 X := Sylow.ofCard (Subgroup.zpowers b)
    (by rw [Nat.card_zpowers, hb, hfac, pow_one])
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq X Sb Sa
  refine ⟨n, ?_⟩
  have hSa : (Sa : Subgroup X) = Subgroup.zpowers a := Sylow.coe_ofCard _ _
  have hSb : (Sb : Subgroup X) = Subgroup.zpowers b := Sylow.coe_ofCard _ _
  rw [← hSa, ← hn, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hSb]
  exact ⟨b, Subgroup.mem_zpowers b, rfl⟩

theorem commute_of_orderOf_three_of_odd [DecidableEq X] {a x : X} (hx : orderOf x = 3)
    (ha : Odd (orderOf a)) (hax : a * x * a⁻¹ ∈ Subgroup.zpowers x) : a * x = x * a := by
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hax
  simp only [Finset.mem_image, Finset.mem_range] at hax
  obtain ⟨k, hk3, hk⟩ := hax
  have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hx
    norm_num at hx
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    apply hx1
    calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
      _ = 1 := by rw [← hk]; group
  · rw [pow_one] at hk
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [← hk]
  · exfalso
    have hinv : a * x * a⁻¹ = x⁻¹ := by
      rw [← hk, eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
    have ha2 : a ^ 2 * x * (a ^ 2)⁻¹ = x := by
      calc a ^ 2 * x * (a ^ 2)⁻¹ = a * (a * x * a⁻¹) * a⁻¹ := by rw [pow_two]; group
        _ = a * x⁻¹ * a⁻¹ := by rw [hinv]
        _ = (a * x * a⁻¹)⁻¹ := by group
        _ = x := by rw [hinv, inv_inv]
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 2) (x := a)
      (Nat.Coprime.symm (Nat.coprime_two_right.mpr ha))
    have hc : Commute (a ^ 2) x := by
      have : a ^ 2 * x = x * a ^ 2 := by
        calc a ^ 2 * x = a ^ 2 * x * (a ^ 2)⁻¹ * a ^ 2 := by group
          _ = x * a ^ 2 := by rw [ha2]
      exact this
    have hc' : Commute a x := by
      rw [← hm]
      exact hc.pow_left m
    apply hx1
    have h2 : x = x⁻¹ := by
      rw [← hinv, hc'.eq, mul_inv_cancel_right]
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      nth_rewrite 2 [h2]
      exact mul_inv_cancel x)
    rw [hx] at h3
    norm_num at h3

theorem mul_self_eq_one_of_inv_of_commute {V : Subgroup X} (hV : IsKleinFour V) {s : X}
    (hsN : s ∈ Subgroup.normalizer (V : Set X)) (hs3 : s ^ 3 = 1)
    (hsC : s ∉ Subgroup.centralizer (V : Set X)) {t : X} (htV : t ∈ V) (ht1 : t ≠ 1) {y : X}
    (hys : y * s = s * y) (hty : t * y * t⁻¹ = y⁻¹) : y * y = 1 := by
  have hconj : ∀ x ∈ V, s * x * s⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
  have hs3C : s ^ 3 ∈ Subgroup.centralizer (V : Set X) := by
    rw [hs3]
    exact Subgroup.one_mem _
  have ht'V : s * t * s⁻¹ ∈ V := hconj t htV
  have ht''V : s * (s * t * s⁻¹) * s⁻¹ ∈ V := hconj _ ht'V
  have hne1 : ∀ u : X, u ≠ 1 → s * u * s⁻¹ ≠ 1 := fun u hu h0 => hu (by
    calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
      _ = 1 := by rw [h0]; group)
  have ht'1 := hne1 t ht1
  have ht''1 := hne1 _ ht'1
  have htt' : t ≠ s * t * s⁻¹ := fun h0 =>
    ht1 (eq_one_of_conj_eq_of_pow_three_mem hV hsN hs3C hsC htV h0.symm)
  have ht''t' : s * (s * t * s⁻¹) * s⁻¹ ≠ s * t * s⁻¹ := fun h0 =>
    ht'1 (eq_one_of_conj_eq_of_pow_three_mem hV hsN hs3C hsC ht'V h0)
  have ht''t : s * (s * t * s⁻¹) * s⁻¹ ≠ t := by
    intro h0
    have hs2N : s ^ 2 ∈ Subgroup.normalizer (V : Set X) := Subgroup.pow_mem _ hsN 2
    have hs23 : (s ^ 2) ^ 3 ∈ Subgroup.centralizer (V : Set X) := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hs3, one_pow]
      exact Subgroup.one_mem _
    have hs2C : s ^ 2 ∉ Subgroup.centralizer (V : Set X) := fun hC => hsC (by
      have : s = (s ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hs3, one_mul, pow_one]
      rw [this]
      exact Subgroup.pow_mem _ hC 2)
    have h1 : s ^ 2 * t * (s ^ 2)⁻¹ = t := by
      calc s ^ 2 * t * (s ^ 2)⁻¹ = s * (s * t * s⁻¹) * s⁻¹ := by rw [pow_two]; group
        _ = t := h0
    exact ht1 (eq_one_of_conj_eq_of_pow_three_mem hV hs2N hs23 hs2C htV h1)
  have hprod : s * (s * t * s⁻¹) * s⁻¹ = t * (s * t * s⁻¹) :=
    eq_mul_of_mem_kleinFour hV htV ht'V ht''V ht1 ht'1 htt' ht''1 ht''t ht''t'
  have hys' : s⁻¹ * y * s = y := by
    calc s⁻¹ * y * s = s⁻¹ * (y * s) := by group
      _ = s⁻¹ * (s * y) := by rw [hys]
      _ = y := by group
  have hsy : s * y * s⁻¹ = y := by
    calc s * y * s⁻¹ = (s * y) * s⁻¹ := rfl
      _ = (y * s) * s⁻¹ := by rw [hys]
      _ = y := by group
  have hinv' : ∀ u : X, u * y * u⁻¹ = y⁻¹ → (s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ = y⁻¹ := by
    intro u hu
    calc (s * u * s⁻¹) * y * (s * u * s⁻¹)⁻¹ = s * (u * (s⁻¹ * y * s) * u⁻¹) * s⁻¹ := by group
      _ = s * y⁻¹ * s⁻¹ := by rw [hys', hu]
      _ = (s * y * s⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [hsy]
  have h1 := hinv' t hty
  have h2 := hinv' _ h1
  rw [hprod] at h2
  have h3 : (t * (s * t * s⁻¹)) * y * (t * (s * t * s⁻¹))⁻¹ = y := by
    calc (t * (s * t * s⁻¹)) * y * (t * (s * t * s⁻¹))⁻¹ =
        t * ((s * t * s⁻¹) * y * (s * t * s⁻¹)⁻¹) * t⁻¹ := by group
      _ = t * y⁻¹ * t⁻¹ := by rw [h1]
      _ = (t * y * t⁻¹)⁻¹ := by group
      _ = y := by rw [hty, inv_inv]
  have h4 : y = y⁻¹ := h3.symm.trans h2
  rw [mul_eq_one_iff_eq_inv]
  exact h4

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem card_le_of_le_omegaZ_of_commute
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G) (hnc : ¬ IsCyclic (P : Subgroup G)) {y : G}
    (hyN : y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hy3 : orderOf y = 3)
    {E : Subgroup G} (hEW : E ≤ omegaZ (P : Subgroup G) p) (hEy : ∀ x ∈ E, y * x = x * y) :
    Nat.card E ≤ p := by
  classical
  have hp7 := h.seven_le_of_pi hp3 hpq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, -, hT₀P₀⟩ := h.exists_sylow_invariant hp3 c hpq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hPmap : (P : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hPmem : ∀ z, z ∈ (P : Subgroup G) ↔ g⁻¹ * z * g ∈ (P₀ : Subgroup G) := by
    intro z
    rw [hPmap]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [this]
      exact hw
    · intro hz
      exact ⟨g⁻¹ * z * g, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hnc₀ : ¬ IsCyclic (P₀ : Subgroup G) := fun hc => hnc (by
    rw [hPmap]
    exact isCyclic_of_surjective ((P₀ : Subgroup G).equivMapOfInjective _
      (MulAut.conj g).injective).toMonoidHom (MulEquiv.surjective _))
  have hW₀ : ¬ IsCyclic (omegaZ (P₀ : Subgroup G) p) := fun hc =>
    h.false_of_isCyclic_omegaZ hp3 c hpq P₀ hT₀P₀ hnc₀ hc
  obtain ⟨s, hsP, hsT, hs3⟩ := h.exists_orderOf_three hp3 c hpq P₀ hT₀P₀ hW₀
  set W := omegaZ (P₀ : Subgroup G) p with hWdef
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => mul_comm_of_mem_omegaZ ha hb
  have hNW : ∀ n ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G), ∀ x ∈ W,
      n * x * n⁻¹ ∈ W := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_omegaZ hn) x).mp hx
  set y₁ := g⁻¹ * y * g with hy₁def
  have hy₁N : y₁ ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    have h1 : g * z * g⁻¹ ∈ (P : Subgroup G) := (hPmem _).mpr (by convert hz using 1; group)
    have h2 := (Subgroup.mem_normalizer_iff.mp hyN _).mp h1
    have h3 := (hPmem _).mp h2
    convert h3 using 1
    rw [hy₁def]
    group
  have hy₁3 : orderOf y₁ = 3 := by
    rw [hy₁def, show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hy3]
  set E₁ := E.map (MulAut.conj g⁻¹).toMonoidHom with hE₁def
  have hE₁card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hE₁W : E₁ ≤ W := by
    rintro _ ⟨e, he, rfl⟩
    have heW := hEW he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨(hPmem e).mp heW.1, fun z hz => ?_, ?_⟩
    · have h1 : g * z * g⁻¹ ∈ (P : Subgroup G) := (hPmem _).mpr (by convert hz using 1; group)
      have h2 := heW.2.1 _ h1
      calc g⁻¹ * e * g * z = g⁻¹ * (e * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * e) * g := by rw [h2]
        _ = z * (g⁻¹ * e * g) := by group
    · rw [show g⁻¹ * e * g = g⁻¹ * e * g⁻¹⁻¹ by rw [inv_inv], conj_pow, heW.2.2]
      group
  have hE₁y : ∀ x ∈ E₁, y₁ * x = x * y₁ := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hEy e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc y₁ * (g⁻¹ * e * g) = g⁻¹ * (y * e) * g := by rw [hy₁def]; group
      _ = g⁻¹ * (e * y) * g := by rw [h1]
      _ = g⁻¹ * e * g * y₁ := by rw [hy₁def]; group
  obtain ⟨-, -, h9, -, -⟩ := h.sylow_facts hp3 c hpq P₀
  set NP := Subgroup.normalizer ((P₀ : Subgroup G) : Set G) with hNPdef
  obtain ⟨n, hn⟩ := exists_conj_mem_zpowers_of_not_nine_dvd (X := NP) h9
    (a := ⟨s, hsP⟩) (b := ⟨y₁, hy₁N⟩) (by rw [Subgroup.orderOf_mk, hs3])
    (by rw [Subgroup.orderOf_mk, hy₁3])
  set y₂ := (n : G) * y₁ * (n : G)⁻¹ with hy₂def
  have hy₂s : y₂ ∈ Subgroup.zpowers s := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hy₂3 : orderOf y₂ = 3 := by
    rw [hy₂def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy₁3]
  have hsy₂ : s ∈ Subgroup.zpowers y₂ := by
    have hle : Subgroup.zpowers y₂ ≤ Subgroup.zpowers s := (Subgroup.zpowers_le).mpr hy₂s
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hs3, hy₂3])
    rw [heq]
    exact Subgroup.mem_zpowers s
  set E₂ := E₁.map (MulAut.conj (n : G)).toMonoidHom with hE₂def
  have hE₂card : Nat.card E₂ = Nat.card E₁ :=
    Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective
  have hE₂W : E₂ ≤ W := by
    rintro _ ⟨e, he, rfl⟩
    exact hNW n n.2 e (hE₁W he)
  have hE₂s : ∀ x ∈ E₂, x * s = s * x := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hE₁y e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : Commute y₂ ((n : G) * e * (n : G)⁻¹) := by
      change y₂ * ((n : G) * e * (n : G)⁻¹) = ((n : G) * e * (n : G)⁻¹) * y₂
      calc y₂ * ((n : G) * e * (n : G)⁻¹) = (n : G) * (y₁ * e) * (n : G)⁻¹ := by
            rw [hy₂def]; group
        _ = (n : G) * (e * y₁) * (n : G)⁻¹ := by rw [h1]
        _ = ((n : G) * e * (n : G)⁻¹) * y₂ := by rw [hy₂def]; group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsy₂
    rw [← hk]
    exact ((hc.zpow_left k).eq).symm
  have htN : h.t ∈ NP := hT₀P₀ c.t_mem_T₀
  have htt : h.t * h.t = 1 := h.t_mul_t
  have htinv : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right htt
  set B := W ⊓ Subgroup.centralizer ({h.t} : Set G) with hBdef
  have hBp : IsPGroup p B := P₀.isPGroup'.to_le (inf_le_left.trans omegaZ_le)
  have hBcard : Nat.card B ≤ p := h.card_le_of_le_centralizer hp3 hpq hBp
    (fun x hx => pow_eq_one_of_mem_omegaZ hx.1) h.orderOf_t inf_le_right
  have hmem : ∀ x ∈ E₂, x * (h.t * x * h.t⁻¹) ∈ B := by
    intro x hx
    have hxW := hE₂W hx
    have htxW := hNW _ htN x hxW
    refine ⟨W.mul_mem hxW htxW, ?_⟩
    show _ ∈ Subgroup.centralizer ({h.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : h.t * (x * (h.t * x * h.t⁻¹)) * h.t⁻¹ = x * (h.t * x * h.t⁻¹) := by
      calc h.t * (x * (h.t * x * h.t⁻¹)) * h.t⁻¹ =
          (h.t * x * h.t⁻¹) * ((h.t * h.t) * x * (h.t⁻¹ * h.t⁻¹)) := by group
        _ = (h.t * x * h.t⁻¹) * x := by rw [htt, htinv, htt]; group
        _ = x * (h.t * x * h.t⁻¹) := hWc _ htxW _ hxW
    calc x * (h.t * x * h.t⁻¹) * h.t = h.t * (x * (h.t * x * h.t⁻¹)) * h.t⁻¹ * h.t := by
          rw [h1]
      _ = h.t * (x * (h.t * x * h.t⁻¹)) := by group
  let f : E₂ → B := fun x => ⟨(x : G) * (h.t * x * h.t⁻¹), hmem x x.2⟩
  have hsC : s ∉ Subgroup.centralizer (c.T₀ : Set G) := fun hC =>
    h.three_not_dvd_card_centralizer hp3 c.isKleinFour_T₀
      (hs3 ▸ Subgroup.orderOf_dvd_natCard _ hC)
  have hs3' : s ^ 3 = 1 := by rw [← hs3, pow_orderOf_eq_one]
  have hf : Function.Injective f := by
    intro x₁ x₂ h12
    have h12' : (x₁ : G) * (h.t * x₁ * h.t⁻¹) = x₂ * (h.t * x₂ * h.t⁻¹) :=
      congrArg Subtype.val h12
    have hx₁W := hE₂W x₁.2
    have hx₂W := hE₂W x₂.2
    set z := (x₁ : G) * (x₂ : G)⁻¹ with hzdef
    have hz : z ∈ E₂ := E₂.mul_mem x₁.2 (E₂.inv_mem x₂.2)
    have hcomm : (x₁ : G)⁻¹ * x₂ = x₂ * (x₁ : G)⁻¹ :=
      hWc _ (W.inv_mem hx₁W) _ hx₂W
    have hzinv : h.t * z * h.t⁻¹ = z⁻¹ := by
      calc h.t * z * h.t⁻¹ = (h.t * x₁ * h.t⁻¹) * (h.t * x₂ * h.t⁻¹)⁻¹ := by
            rw [hzdef]; group
        _ = (x₁ : G)⁻¹ * ((x₁ : G) * (h.t * x₁ * h.t⁻¹)) * (h.t * x₂ * h.t⁻¹)⁻¹ := by group
        _ = (x₁ : G)⁻¹ * ((x₂ : G) * (h.t * x₂ * h.t⁻¹)) * (h.t * x₂ * h.t⁻¹)⁻¹ := by
            rw [h12']
        _ = (x₁ : G)⁻¹ * x₂ := by group
        _ = x₂ * (x₁ : G)⁻¹ := hcomm
        _ = z⁻¹ := by rw [hzdef]; group
    have hzz := mul_self_eq_one_of_inv_of_commute c.isKleinFour_T₀ hsT hs3' hsC c.t_mem_T₀
      h.t_ne_one (hE₂s z hz) hzinv
    have hz1 : z = 1 := by
      obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨z, (omegaZ_le (hE₂W hz))⟩
      have h1 : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
        simpa using congrArg Subtype.val hk)
      have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
      have hcop : Nat.Coprime (p ^ k) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hp.out Nat.prime_two).mpr (by omega))
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    apply Subtype.ext
    rw [hzdef, mul_inv_eq_one] at hz1
    exact hz1
  have := Nat.card_le_card_of_injective f hf
  omega

theorem lemma_7_14
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    {E : Subgroup G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEcard : Nat.card E = p ^ 2) {H : Subgroup G} (hH : IsPGroup 3 H)
    (hEH : E ≤ Subgroup.normalizer (H : Set G)) : H = ⊥ := by
  classical
  have hS := CFSG.Walter.suzukiFourGroupTheorem
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hH1
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hppow : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  have hEnc : ¬ IsCyclic E := fun hc => by
    have := card_le_of_isCyclic_of_pow_eq_one hp.out.pos
      (fun x : E => Subtype.ext (by simpa using hEexp x x.2))
    omega
  have hcopH : ∀ {K : Subgroup G}, IsPGroup 3 K → Nat.Coprime p (Nat.card K) := by
    intro K hK
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out Nat.prime_three).mpr hp3')
  obtain ⟨e, heE, he1, x₀, hx₀H, hx₀1, hx₀e⟩ :
      ∃ e ∈ E, e ≠ 1 ∧ ∃ x ∈ H, x ≠ 1 ∧ e * x = x * e := by
    let : CommGroup E :=
      { (inferInstance : Group E) with
        mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
    have : Fact (IsPGroup p E) := ⟨hEp⟩
    have : Subgroup.Normalizes E H := ⟨hEH⟩
    have hsup := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
      (G := H) (A := E) p (hcopH hH) hEnc
    by_contra! hall
    apply hH1
    have hbot : ∀ a : E, a ≠ 1 → fixedPointSubgroup (Subgroup.zpowers a) H = ⊥ := by
      intro a ha1
      refine eq_bot_iff.mpr fun x hx => ?_
      have hax : a • x = x :=
        (FixedPoints.mem_subgroup (Subgroup.zpowers a) H x).mp hx ⟨a, Subgroup.mem_zpowers a⟩
      have hcomm := mem_centralizer_of_smul_eq_conj hax
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hall a a.2 (fun h0 => ha1 (Subtype.ext h0)) x x.2
        (fun h0 => hx1 (Subtype.ext h0)) (Subgroup.mem_centralizer_singleton_iff.mp hcomm).symm
    have htop : (⊤ : Subgroup H) = ⊥ := by
      rw [← hsup]
      exact iSup₂_eq_bot.mpr hbot
    refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, hx⟩ : H) ∈ (⊥ : Subgroup H) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at this ⊢
    exact congrArg Subtype.val this
  set L := Subgroup.centralizer ({e} : Set G) with hLdef
  set H₀ := H ⊓ L with hH₀def
  have hH₀3 : IsPGroup 3 H₀ := hH.to_le inf_le_left
  have hx₀H₀ : x₀ ∈ H₀ := ⟨hx₀H, Subgroup.mem_centralizer_singleton_iff.mpr hx₀e.symm⟩
  have hH₀1 : H₀ ≠ ⊥ := fun h0 => hx₀1 (by rw [h0] at hx₀H₀; exact Subgroup.mem_bot.mp hx₀H₀)
  have heo : orderOf e = p := orderOf_eq_prime (hEexp e heE) he1
  have he2 : e ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [heo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hLs : Group.IsSolvable L := h.lemma_7_7_a hp3 hS he2
  have hEL : E ≤ L := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx e heE)
  have hEH₀ : E ≤ Subgroup.normalizer (H₀ : Set G) :=
    le_normalizer_inf hEH (hEL.trans Subgroup.le_normalizer)
  have hdisj : Disjoint E H₀ := Subgroup.disjoint_of_coprime_natCard (by
    rw [hEcard]
    exact Nat.Coprime.pow_left _ (hcopH hH₀3))
  have hEHcard : Nat.card (E ⊔ H₀ : Subgroup G) = Nat.card E * Nat.card H₀ :=
    card_sup_eq_mul_of_disjoint hEH₀ hdisj
  have hEHL : E ⊔ H₀ ≤ L := sup_le hEL inf_le_right
  set π : Set Nat.Primes := {⟨3, Nat.prime_three⟩, ⟨p, hp.out⟩} with hπdef
  have hπ : IsPiSubgroup π ((E ⊔ H₀).subgroupOf L) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEHL).toEquiv, hEHcard, hEcard] at hr
    obtain ⟨n, hn⟩ := hH₀3.exists_card_eq
    rw [hn] at hr
    rcases (Nat.Prime.dvd_mul r.2).mp hr with h1 | h1
    · right
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 hp.out).mp (r.2.dvd_of_dvd_pow h1))
    · left
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_three).mp
        (r.2.dvd_of_dvd_pow h1))
  obtain ⟨L₀', hL₀', hEHL₀'⟩ := SolvableHall.solvable_hall_containment hLs π _ hπ
  set L₀ := L₀'.map L.subtype with hL₀def
  have hL₀L : L₀ ≤ L := Subgroup.map_subtype_le _
  have hL₀card : Nat.card L₀ = Nat.card L₀' := Subgroup.card_map_of_injective L.subtype_injective
  have hEHL₀ : E ⊔ H₀ ≤ L₀ := fun y hy =>
    ⟨⟨y, hEHL hy⟩, hEHL₀' (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩
  have hEL₀ : E ≤ L₀ := le_sup_left.trans hEHL₀
  have hH₀L₀ : H₀ ≤ L₀ := le_sup_right.trans hEHL₀
  have hL₀π : ∀ r : ℕ, r.Prime → r ∣ Nat.card L₀ → r = 3 ∨ r = p := by
    intro r hr hrd
    rw [hL₀card] at hrd
    rcases hL₀'.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  obtain ⟨P', hEP'⟩ := hEp.exists_le_sylow
  have hP'nc : ¬ IsCyclic (P' : Subgroup G) := fun hc => hEnc (Subgroup.isCyclic_of_le hEP')
  obtain ⟨-, -, hΩP'⟩ := h.lemma_7_8 hp3 c hpq P' hP'nc
  have heZ : e ∈ omegaZ (P' : Subgroup G) p := hΩP' ▸ mem_omegaOne (hEP' heE) (hEexp e heE)
  have hP'L : (P' : Subgroup G) ≤ L := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (heZ.2.1 y hy).symm
  have hfacL₀ : (Nat.card L₀).factorization p = (Nat.card G).factorization p := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card _) p
    · have h1 : (Nat.card G).factorization p ≤ (Nat.card L).factorization p := by
        have := Subgroup.card_dvd_of_le hP'L
        rw [P'.card_eq_multiplicity] at this
        exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp this
      have h2 : (Nat.card L).factorization p = (Nat.card L₀').factorization p := by
        have hidx : ¬ p ∣ L₀'.index := fun hd =>
          hL₀'.p_in_pi_of_p_dvd_index ⟨p, hp.out⟩ hd (Or.inr rfl)
        rw [← L₀'.card_mul_index, Nat.factorization_mul Nat.card_pos.ne'
          Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
      rw [hL₀card]
      omega
  obtain ⟨L₁, hEL₁⟩ := (hEp.comap_subtype (K := L₀)).exists_le_sylow
  set L₁' := (L₁ : Subgroup L₀).map L₀.subtype with hL₁'def
  have hL₁'card : Nat.card L₁' = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective L₀.subtype_injective, L₁.card_eq_multiplicity, hfacL₀]
  let Sg : Sylow p G := Sylow.ofCard L₁' hL₁'card
  have hSg : (Sg : Subgroup G) = L₁' := Sylow.coe_ofCard _ _
  have hESg : E ≤ (Sg : Subgroup G) := by
    rw [hSg]
    intro y hy
    exact ⟨⟨y, hEL₀ hy⟩, hEL₁ (by rw [Subgroup.mem_comap]; exact hy), rfl⟩
  have hSgL₀ : (Sg : Subgroup G) ≤ L₀ := by
    rw [hSg]
    exact Subgroup.map_subtype_le _
  have hSgnc : ¬ IsCyclic (Sg : Subgroup G) := fun hc => hEnc (Subgroup.isCyclic_of_le hESg)
  obtain ⟨-, -, hΩSg⟩ := h.lemma_7_8 hp3 c hpq Sg hSgnc
  obtain ⟨-, -, h9Sg, -, -⟩ := h.sylow_facts hp3 c hpq Sg
  have hL₀s : Group.IsSolvable L₀ := isSolvable_of_le hL₀L hLs
  have hcore : pPrimeCore p L₀ = ⊥ := by
    set K₀ := (pPrimeCore p L₀).map L₀.subtype with hK₀def
    have hK₀3 : IsPGroup 3 K₀ := by
      refine IsPGroup.of_card (n := (Nat.card K₀).primeFactorsList.length)
        (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdK => ?_)
      have hdL₀ : d ∣ Nat.card L₀ :=
        hdK.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
      rcases hL₀π d hd hdL₀ with h1 | h1
      · exact h1
      · exfalso
        have := coprime_card_map_pPrimeCore (p := p) L₀
        rw [h1] at hdK
        exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp this hdK
    have hSgK₀ : (Sg : Subgroup G) ≤ Subgroup.normalizer (K₀ : Set G) :=
      hSgL₀.trans (le_normalizer_map_pPrimeCore L₀)
    have := h.lemma_7_13 hp3 c hpq Sg hSgnc hK₀3 hSgK₀
    exact (Subgroup.map_eq_bot_iff_of_injective _ L₀.subtype_injective).mp this
  have hL₁n := normal_sylow_of_pPrimeCore_eq_bot hp2 hL₀s hcore L₁ (fun x hx hxp y hy => by
    have hx' : (x : G) ∈ omegaZ (Sg : Subgroup G) p := by
      rw [← hΩSg]
      refine mem_omegaOne ?_ (by simpa using congrArg Subtype.val hxp)
      rw [hSg]
      exact ⟨x, hx, rfl⟩
    have hy' : (y : G) ∈ (Sg : Subgroup G) := by
      rw [hSg]
      exact ⟨y, hy, rfl⟩
    exact Subtype.ext (hx'.2.1 _ hy'))
  have hL₀N : L₀ ≤ Subgroup.normalizer ((Sg : Subgroup G) : Set G) := by
    intro g hg
    have hmem : (⟨g, hg⟩ : L₀) ∈ Subgroup.normalizer ((L₁ : Subgroup L₀) : Set L₀) := by
      have := hL₁n
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    rw [hSg]
    exact Subgroup.le_normalizer_map L₀.subtype ⟨⟨g, hg⟩, hmem, rfl⟩
  have hH₀N : H₀ ≤ Subgroup.normalizer ((Sg : Subgroup G) : Set G) := hH₀L₀.trans hL₀N
  have hH₀card : Nat.card H₀ = 3 := by
    obtain ⟨a, ha⟩ := hH₀3.exists_card_eq
    have hdvd : Nat.card H₀ ∣ Nat.card (Subgroup.normalizer ((Sg : Subgroup G) : Set G)) :=
      Subgroup.card_dvd_of_le hH₀N
    have ha1 : a ≤ 1 := by
      by_contra ha1
      exact h9Sg ((show (9 : ℕ) = 3 ^ 2 by norm_num) ▸
        (pow_dvd_pow 3 (by omega : 2 ≤ a)).trans (ha ▸ hdvd))
    interval_cases a
    · exfalso
      rw [pow_zero] at ha
      exact hH₀1 (Subgroup.card_eq_one.mp ha)
    · rw [ha, pow_one]
  have hx₀3 : orderOf x₀ = 3 := by
    have h1 : orderOf x₀ ∣ 3 := hH₀card ▸ Subgroup.orderOf_dvd_natCard H₀ hx₀H₀
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx₀1
    · exact h1
  have hH₀z : H₀ = Subgroup.zpowers x₀ := (Subgroup.eq_of_le_of_card_ge
    ((Subgroup.zpowers_le).mpr hx₀H₀) (by rw [Nat.card_zpowers, hx₀3, hH₀card])).symm
  have hEx₀ : ∀ a ∈ E, a * x₀ = x₀ * a := by
    intro a ha
    refine commute_of_orderOf_three_of_odd hx₀3 ?_ ?_
    · have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hEexp a ha)
      exact Odd.of_dvd_nat (hp.out.odd_of_ne_two hp2) h1
    · rw [← hH₀z]
      exact (Subgroup.mem_normalizer_iff.mp (hEH₀ ha) x₀).mp hx₀H₀
  have hEW : E ≤ omegaZ (Sg : Subgroup G) p := fun y hy =>
    hΩSg ▸ mem_omegaOne (hESg hy) (hEexp y hy)
  have hcard := h.card_le_of_le_omegaZ_of_commute hp3 c hpq Sg hSgnc (hH₀N hx₀H₀) hx₀3 hEW
    (fun y hy => (hEx₀ y hy).symm)
  rw [hEcard] at hcard
  omega

theorem eq_bot_of_le_normalizer_of_not_isCyclic
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {Sg : Subgroup G} (hSg : IsPGroup p Sg) (hnc : ¬ IsCyclic Sg)
    {H : Subgroup G} (hH : IsPGroup 3 H) (hSgH : Sg ≤ Subgroup.normalizer (H : Set G)) :
    H = ⊥ := by
  have hp7 := h.seven_le_of_pi hp3 hpq
  have : Fact (IsPGroup p Sg) := ⟨hSg⟩
  obtain ⟨S, -, hScard, hSe⟩ := lemma_4_5_a (R := Sg) (p := p) (by omega) hnc
  have := hSe
  refine h.lemma_7_14 hp3 c hpq (E := S.map Sg.subtype) ?_ ?_ ?_ hH
    ((Subgroup.map_subtype_le S).trans hSgH)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val
      (hSe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    have := @elemPow_eq_one_of_isElementaryAbelian p _ _ S hSe a ha
    simpa using congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective Sg.subtype_injective, hScard]

end JTHyp

end CFSG.Walter.JT
