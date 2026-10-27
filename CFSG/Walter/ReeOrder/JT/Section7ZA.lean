module

public import CFSG.Walter.ReeOrder.JT.Section7R

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG CFSG.Walter.Transitivity

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X]

theorem mem_of_pow_mem_of_coprime {H : Subgroup X} {x : X} {m n : ℕ}
    (hm : x ^ m ∈ H) (hn : x ^ n ∈ H) (hmn : Nat.Coprime m n) : x ∈ H := by
  have h1 := Nat.gcd_eq_gcd_ab m n
  rw [Nat.Coprime.gcd_eq_one hmn, Nat.cast_one] at h1
  have : x = (x ^ m) ^ (Nat.gcdA m n) * (x ^ n) ^ (Nat.gcdB m n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h1, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem hm _) (H.zpow_mem hn _)

theorem conj_ne_of_pow_three {V : Subgroup X} (hV : IsKleinFour V) {s : X}
    (hsN : s ∈ Subgroup.normalizer (V : Set X)) (hs3 : s ^ 3 = 1)
    (hsC : s ∉ Subgroup.centralizer (V : Set X)) {v : X} (hv : v ∈ V) (hv1 : v ≠ 1) :
    s * v * s⁻¹ ≠ v ∧ s * (s * v * s⁻¹) * s⁻¹ ≠ v := by
  have hs3C : s ^ 3 ∈ Subgroup.centralizer (V : Set X) := by
    rw [hs3]
    exact Subgroup.one_mem _
  refine ⟨fun h0 => hv1 (eq_one_of_conj_eq_of_pow_three_mem hV hsN hs3C hsC hv h0), ?_⟩
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
  have h1 : s ^ 2 * v * (s ^ 2)⁻¹ = v := by
    calc s ^ 2 * v * (s ^ 2)⁻¹ = s * (s * v * s⁻¹) * s⁻¹ := by rw [pow_two]; group
      _ = v := h0
  exact hv1 (eq_one_of_conj_eq_of_pow_three_mem hV hs2N hs23 hs2C hv h1)

variable [Finite X]

theorem isSolvable_of_prime_dvd {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hrp : r ≠ p)
    {H : Subgroup X} (hH : ∀ d : ℕ, d.Prime → d ∣ Nat.card H → d = r ∨ d = p) :
    Group.IsSolvable H := by
  classical
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := H)).ne' r
    hr.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcard
    exact Nat.card_pos.ne' hcard
  have hmp : m = p ^ m.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdm => by
      rcases hH d hd (hcard ▸ Dvd.dvd.mul_left hdm _) with h1 | h1
      · exact absurd (h1 ▸ hdm) hm
      · exact h1)
  have : Fintype H := Fintype.ofFinite H
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hr hp hrp
    (by rw [← Nat.card_eq_fintype_card, hcard, hmp])

theorem card_eq_of_isPiSubgroup_maximal {π : Set Nat.Primes} {Z : Subgroup X}
    (hmax : ∀ Z' : Subgroup X, IsPiSubgroup π Z' → Z ≤ Z' → Z' ≤ Z) (hZ : IsPiSubgroup π Z)
    {r : ℕ} [hr : Fact r.Prime] (hrπ : (⟨r, hr.out⟩ : Nat.Primes) ∈ π) {D : Subgroup X}
    (hZD : Z ≤ Subgroup.normalizer (D : Set X))
    (hDcard : Nat.card D = r ^ (Nat.card Z).factorization r)
    (hsolv : Group.IsSolvable (Subgroup.normalizer (D : Set X))) :
    Nat.card D = r ^ (Nat.card X).factorization r := by
  set N := Subgroup.normalizer (D : Set X) with hNdef
  have hZπ : IsPiSubgroup π (Z.subgroupOf N) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv] at hq
    exact hZ q hq
  obtain ⟨M', hM', hZM'⟩ := SolvableHall.solvable_hall_containment hsolv π _ hZπ
  set M := M'.map N.subtype with hMdef
  have hMcard : Nat.card M = Nat.card M' := Subgroup.card_map_of_injective N.subtype_injective
  have hMπ : IsPiSubgroup π M := fun q hq => hM'.p_in_pi_of_p_dvd_card q (hMcard ▸ hq)
  have hZM : Z ≤ M := fun z hz =>
    ⟨⟨z, hZD hz⟩, hZM' (by rw [Subgroup.mem_subgroupOf]; exact hz), rfl⟩
  have hMZ : M = Z := le_antisymm (hmax M hMπ hZM) hZM
  have hNr : (Nat.card N).factorization r = (Nat.card Z).factorization r := by
    have hidx : ¬ r ∣ M'.index := fun hd => hM'.p_in_pi_of_p_dvd_index ⟨r, hr.out⟩ hd hrπ
    rw [← M'.card_mul_index, Nat.factorization_mul Nat.card_pos.ne'
      Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero, ← hMcard, hMZ]
  set n := (Nat.card Z).factorization r with hndef
  by_contra hne
  have hdvd : r ^ n ∣ Nat.card X := hDcard ▸ Subgroup.card_subgroup_dvd_card D
  have hle : n ≤ (Nat.card X).factorization r :=
    (Nat.Prime.pow_dvd_iff_le_factorization hr.out Nat.card_pos.ne').mp hdvd
  have hlt : n < (Nat.card X).factorization r := by
    rcases hle.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (by rw [hDcard, h1]) hne
  have h2 : r ^ (n + 1) ∣ Nat.card X :=
    (Nat.Prime.pow_dvd_iff_le_factorization hr.out Nat.card_pos.ne').mpr hlt
  have h3 := Sylow.prime_pow_dvd_card_normalizer h2 hDcard
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization hr.out Nat.card_pos.ne').mp h3
  rw [hNr] at h4
  omega

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem nine_dvd_card_centralizer_of_commute
    {s u : G} (hs3 : orderOf s = 3)
    (hu : orderOf u = 2) (hsu : s * u = u * s) :
    9 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu
  have hs't : a * s * a⁻¹ ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← ha]
    calc a * s * a⁻¹ * (a * u * a⁻¹) = a * (s * u) * a⁻¹ := by group
      _ = a * (u * s) * a⁻¹ := by rw [hsu]
      _ = a * u * a⁻¹ * (a * s * a⁻¹) := by group
  have hs'3 : orderOf (a * s * a⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs3]
  have hs'F : a * s * a⁻¹ ∈ h.F := h.mem_F_of_odd hs't (by rw [hs'3]; decide)
  have hu' := h.unipotentFacts hp3
  have hz3 : IsPGroup h.p (Subgroup.zpowers (a * s * a⁻¹)) := by
    rw [hp3]
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hs'3, pow_one] :
      Nat.card (Subgroup.zpowers (a * s * a⁻¹)) = 3 ^ 1)
  obtain ⟨R, hsR, hRF, hRcard⟩ :=
    hu'.exists_le (Subgroup.zpowers (a * s * a⁻¹)) ((Subgroup.zpowers_le).mpr hs'F) hz3
  have hRab := hu'.abelian R hRF hRcard
  have hRC : R ≤ Subgroup.centralizer ({a * s * a⁻¹} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hRab.is_comm.comm ⟨x, hx⟩ ⟨_, hsR (Subgroup.mem_zpowers _)⟩))
  have hcard : Nat.card (Subgroup.centralizer ({a * s * a⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({s} : Set G)) := by
    rw [← MulAut.conj_apply, ← centralizer_singleton_map,
      Subgroup.card_map_of_injective (MulAut.conj a).injective]
  have hf2 : 2 ≤ h.f := by
    have := h.five_lt
    rw [hp3] at this
    by_contra hf
    interval_cases hf' : h.f <;> norm_num at this
  have h9 : 9 ∣ Nat.card R := by
    rw [hRcard, hp3, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 hf2
  rw [← hcard]
  exact h9.trans (Subgroup.card_dvd_of_le hRC)

theorem eq_one_of_commute_t_w
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {P₀ : Subgroup G} (hP₀ : IsPGroup p P₀) (hCpP₀ : c.Cp p ≤ P₀)
    {z : G} (hzP : z ∈ P₀) (hzt : z * h.t = h.t * z) (hzw : z * c.w = c.w * z) : z = 1 := by
  have hzCp : z ∈ c.Cp p := by
    rw [← h.inf_centralizer_t_eq hp3 c hpq hP₀ hCpP₀]
    exact ⟨hzP, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩
  have hzC : z ∈ c.C := c.Cp_le_C p hzCp
  have hinv := c.torus.inv z hzC
  rw [← hzw, mul_inv_cancel_right] at hinv
  have hCodd : Odd (Nat.card c.C) := by
    have := c.card_C
    have hq8 := h.q_mod_eight_of_eq_three hp3
    exact Nat.odd_iff.mpr (by omega)
  have hzodd : Odd (orderOf z) := Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard c.C hzC)
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel z)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hzodd
    exact absurd hzodd (by decide)

theorem exists_fixed_omegaZ
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P₀ : Sylow p G) (hCpP₀ : c.Cp p ≤ P₀)
    (hT₀P₀ : c.T₀ ≤ Subgroup.normalizer ((P₀ : Subgroup G) : Set G))
    (hnc₀ : ¬ IsCyclic (P₀ : Subgroup G)) :
    ∃ s : G, s ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G) ∧
      s ∈ Subgroup.normalizer (c.T₀ : Set G) ∧ orderOf s = 3 ∧
      ∃ w₀ ∈ omegaZ (P₀ : Subgroup G) p, w₀ ≠ 1 ∧ w₀ * s = s * w₀ := by
  classical
  have hp7 := h.seven_le_of_pi hp3 hpq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₀ : ¬ IsCyclic (omegaZ (P₀ : Subgroup G) p) := fun hc =>
    h.false_of_isCyclic_omegaZ hp3 c hpq P₀ hT₀P₀ hnc₀ hc
  obtain ⟨s, hsP, hsT, hs3⟩ := h.exists_orderOf_three hp3 c hpq P₀ hT₀P₀ hW₀
  obtain ⟨-, hΩ⟩ := h.omegaOne_eq_omegaZ hp3 c hpq P₀ hT₀P₀ hsP hsT hs3
  refine ⟨s, hsP, hsT, hs3, ?_⟩
  set W := omegaZ (P₀ : Subgroup G) p with hWdef
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => mul_comm_of_mem_omegaZ ha hb
  have hNW : ∀ n ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G), ∀ x ∈ W,
      n * x * n⁻¹ ∈ W := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_omegaZ hn) x).mp hx
  have hs3' : s ^ 3 = 1 := by rw [← hs3, pow_orderOf_eq_one]
  have hsC : s ∉ Subgroup.centralizer (c.T₀ : Set G) := fun hC =>
    h.three_not_dvd_card_centralizer hp3 c.isKleinFour_T₀
      (hs3 ▸ Subgroup.orderOf_dvd_natCard _ hC)
  have hconj : ∀ x ∈ c.T₀, s * x * s⁻¹ ∈ c.T₀ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsT x).mp hx
  have hpC : p ∣ Nat.card c.C := by
    have := c.card_C
    have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
    rwa [hq] at hpq
  have hCpp : IsPGroup p (c.Cp p) := c.isPGroup_Cp p
  obtain ⟨n, hn⟩ := hCpp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact c.Cp_ne_bot p hpC (Subgroup.card_eq_one.mp hn)
  obtain ⟨⟨w₁, hw₁Cp⟩, hw₁⟩ := exists_prime_orderOf_dvd_card' (G := c.Cp p) p
    (hn ▸ dvd_pow_self p hn0)
  have hw₁o : orderOf w₁ = p := by rw [← hw₁, Subgroup.orderOf_mk]
  have hw₁1 : w₁ ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hw₁o
    exact hp.out.one_lt.ne hw₁o
  have hw₁P : w₁ ∈ (P₀ : Subgroup G) := hCpP₀ hw₁Cp
  have hw₁W : w₁ ∈ W := hΩ ▸ mem_omegaOne hw₁P (by rw [← hw₁o, pow_orderOf_eq_one])
  have hw₁t : w₁ * h.t = h.t * w₁ :=
    h.commute_of_mem_F (c.torus.le (c.Cp_le_C p hw₁Cp))
  obtain ⟨ht'ne, ht''ne⟩ := conj_ne_of_pow_three c.isKleinFour_T₀ hsT hs3' hsC c.t_mem_T₀
    h.t_ne_one
  have hne1 : ∀ u : G, u ≠ 1 → s * u * s⁻¹ ≠ 1 := fun u hu h0 => hu (by
    calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
      _ = 1 := by rw [h0]; group)
  have htT : h.t ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G) := hT₀P₀ c.t_mem_T₀
  have htt : h.t * h.t = 1 := h.t_mul_t
  have htinv : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right htt
  have hinv : ∀ v ∈ c.T₀, v ≠ 1 → v ≠ h.t → ∀ z ∈ W, z * v = v * z →
      h.t * z * h.t⁻¹ = z⁻¹ := by
    intro v hvT hv1 hvt z hzW hzv
    have hvt' : v * h.t = h.t * v := by
      have hc := (c.isKleinFour_T₀.isMulCommutative).is_comm.comm ⟨v, hvT⟩ ⟨h.t, c.t_mem_T₀⟩
      exact congrArg Subtype.val hc
    have htzW := hNW _ htT z hzW
    set y := z * (h.t * z * h.t⁻¹) with hydef
    have hyP : y ∈ (P₀ : Subgroup G) := omegaZ_le (W.mul_mem hzW htzW)
    have hyt : y * h.t = h.t * y := by
      have h1 : h.t * y * h.t⁻¹ = y := by
        calc h.t * y * h.t⁻¹ = (h.t * z * h.t⁻¹) * ((h.t * h.t) * z * (h.t⁻¹ * h.t⁻¹)) := by
              rw [hydef]; group
          _ = (h.t * z * h.t⁻¹) * z := by rw [htt, htinv, htt]; group
          _ = y := by rw [hydef]; exact hWc _ htzW _ hzW
      calc y * h.t = h.t * y * h.t⁻¹ * h.t := by rw [h1]
        _ = h.t * y := by group
    have hyv : y * v = v * y := by
      have h1 : v * (h.t * z * h.t⁻¹) = (h.t * z * h.t⁻¹) * v := by
        calc v * (h.t * z * h.t⁻¹) = h.t * (v * z) * h.t⁻¹ := by
              rw [show v * (h.t * z * h.t⁻¹) = (v * h.t) * z * h.t⁻¹ by group, hvt']; group
          _ = h.t * (z * v) * h.t⁻¹ := by rw [hzv]
          _ = (h.t * z * h.t⁻¹) * v := by
              rw [show h.t * (z * v) * h.t⁻¹ = h.t * z * (v * h.t⁻¹) by group,
                show v * h.t⁻¹ = h.t⁻¹ * v by
                  rw [htinv]; exact hvt']
              group
      calc y * v = z * ((h.t * z * h.t⁻¹) * v) := by rw [hydef]; group
        _ = z * (v * (h.t * z * h.t⁻¹)) := by rw [h1]
        _ = (z * v) * (h.t * z * h.t⁻¹) := by group
        _ = (v * z) * (h.t * z * h.t⁻¹) := by rw [hzv]
        _ = v * y := by rw [hydef]; group
    have hyw : y * c.w = c.w * y := by
      rcases c.mem_T₀.mp hvT with hv | hv | hv | hv
      ·
        have hw : c.w = h.t⁻¹ * v := by rw [hv]; group
        rw [hw]
        calc y * (h.t⁻¹ * v) = (y * h.t⁻¹) * v := by group
          _ = (h.t⁻¹ * y) * v := by
              rw [show y * h.t⁻¹ = h.t⁻¹ * y by
                rw [htinv]; exact hyt]
          _ = h.t⁻¹ * (y * v) := by group
          _ = h.t⁻¹ * (v * y) := by rw [hyv]
          _ = h.t⁻¹ * v * y := by group
      · exact absurd hv hvt
      · rw [← hv]; exact hyv
      · exact absurd hv hv1
    have hy1 := h.eq_one_of_commute_t_w hp3 c hpq P₀.isPGroup' hCpP₀ hyP hyt hyw
    rw [hydef] at hy1
    calc h.t * z * h.t⁻¹ = z⁻¹ * (z * (h.t * z * h.t⁻¹)) := by group
      _ = z⁻¹ := by rw [hy1, mul_one]
  set a := s * w₁ * s⁻¹ with hadef
  set b := s * a * s⁻¹ with hbdef
  have haW : a ∈ W := hNW s hsP w₁ hw₁W
  have hbW : b ∈ W := hNW s hsP a haW
  have hcomm_conj : ∀ x y : G, x * y = y * x →
      (s * x * s⁻¹) * (s * y * s⁻¹) = (s * y * s⁻¹) * (s * x * s⁻¹) := by
    intro x y hxy
    calc (s * x * s⁻¹) * (s * y * s⁻¹) = s * (x * y) * s⁻¹ := by group
      _ = s * (y * x) * s⁻¹ := by rw [hxy]
      _ = (s * y * s⁻¹) * (s * x * s⁻¹) := by group
  have hat : a * (s * h.t * s⁻¹) = (s * h.t * s⁻¹) * a := hcomm_conj _ _ hw₁t
  have hbt : b * (s * (s * h.t * s⁻¹) * s⁻¹) = (s * (s * h.t * s⁻¹) * s⁻¹) * b :=
    hcomm_conj _ _ hat
  have hta : h.t * a * h.t⁻¹ = a⁻¹ :=
    hinv _ (hconj _ c.t_mem_T₀) (hne1 _ h.t_ne_one) ht'ne _ haW hat
  have htb : h.t * b * h.t⁻¹ = b⁻¹ :=
    hinv _ (hconj _ (hconj _ c.t_mem_T₀)) (hne1 _ (hne1 _ h.t_ne_one)) ht''ne _ hbW hbt
  refine ⟨w₁ * a * b, W.mul_mem (W.mul_mem hw₁W haW) hbW, ?_, ?_⟩
  · intro h0
    have h1 : h.t * (w₁ * a * b) * h.t⁻¹ = w₁ * a⁻¹ * b⁻¹ := by
      calc h.t * (w₁ * a * b) * h.t⁻¹ =
          (h.t * w₁ * h.t⁻¹) * (h.t * a * h.t⁻¹) * (h.t * b * h.t⁻¹) := by group
        _ = w₁ * a⁻¹ * b⁻¹ := by
            rw [hta, htb, show h.t * w₁ * h.t⁻¹ = w₁ by rw [← hw₁t]; group]
    rw [h0, show h.t * 1 * h.t⁻¹ = (1 : G) by group] at h1
    have h2 : w₁ * w₁ = 1 := by
      have hab : (w₁ * a * b) * (w₁ * a⁻¹ * b⁻¹) = w₁ * w₁ := by
        have e1 : a * b = b * a := hWc _ haW _ hbW
        have e2 : b * w₁ = w₁ * b := hWc _ hbW _ hw₁W
        have e3 : a * w₁ = w₁ * a := hWc _ haW _ hw₁W
        have e4 : b * a⁻¹ = a⁻¹ * b := hWc _ hbW _ (W.inv_mem haW)
        calc (w₁ * a * b) * (w₁ * a⁻¹ * b⁻¹) = w₁ * a * (b * w₁) * a⁻¹ * b⁻¹ := by group
          _ = w₁ * a * (w₁ * b) * a⁻¹ * b⁻¹ := by rw [e2]
          _ = w₁ * (a * w₁) * (b * a⁻¹) * b⁻¹ := by group
          _ = w₁ * (w₁ * a) * (a⁻¹ * b) * b⁻¹ := by rw [e3, e4]
          _ = w₁ * w₁ := by group
      rw [← hab, h0, ← h1, one_mul]
    have h3 : orderOf w₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hw₁o] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  ·
    have hsb : s * b * s⁻¹ = w₁ := by
      calc s * b * s⁻¹ = s ^ 3 * w₁ * (s ^ 3)⁻¹ := by rw [hbdef, hadef, pow_three]; group
        _ = w₁ := by rw [hs3']; group
    have h1 : s * (w₁ * a * b) * s⁻¹ = w₁ * a * b := by
      calc s * (w₁ * a * b) * s⁻¹ = (s * w₁ * s⁻¹) * (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a * b * w₁ := by rw [hsb]
        _ = w₁ * a * b := by
            rw [hWc _ (W.mul_mem haW hbW) _ hw₁W, ← mul_assoc]
    calc w₁ * a * b * s = s * (w₁ * a * b) * s⁻¹ * s := by rw [h1]
      _ = s * (w₁ * a * b) := by group

theorem commute_of_mem_normalizer_zpowers
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P₀ : Sylow p G) {s : G}
    (hsP : s ∈ Subgroup.normalizer ((P₀ : Subgroup G) : Set G)) (hs3 : orderOf s = 3)
    {w₀ : G} (hw₀ : w₀ ∈ omegaZ (P₀ : Subgroup G) p) (hw₀s : w₀ * s = s * w₀) {y : G}
    (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers w₀ : Set G)) : y * w₀ = w₀ * y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, h9, -, -⟩ := h.sylow_facts hp3 c hpq P₀
  set Cw := Subgroup.centralizer ({w₀} : Set G) with hCwdef
  set Nw := Subgroup.normalizer (Subgroup.zpowers w₀ : Set G) with hNwdef
  have hNC : ∀ m ∈ Nw, m ∈ Subgroup.normalizer (Cw : Set G) := by
    intro m hm
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have hm' : m⁻¹ * w₀ * m ∈ Subgroup.zpowers w₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Nw.inv_mem hm) w₀).mp (Subgroup.mem_zpowers w₀)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm'
    have hzk : z * (m⁻¹ * w₀ * m) = (m⁻¹ * w₀ * m) * z := by
      rw [← hk]
      exact ((Commute.zpow_right (hz : Commute z w₀) k)).eq
    calc m * z * m⁻¹ * w₀ = m * (z * (m⁻¹ * w₀ * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * w₀ * m) * z) * m⁻¹ := by rw [hzk]
      _ = w₀ * (m * z * m⁻¹) := by group
  have hCN : Cw ≤ Nw := fun z hz =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hz)
  have hP₀C : (P₀ : Subgroup G) ≤ Cw := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hw₀.2.1 z hz).symm
  obtain ⟨c₀, hc₀C, hc₀y⟩ := exists_mul_mem_normalizer_of_sylow (P₀.subtype hP₀C) (hNC y hyN)
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀C] at hc₀y
  set n := c₀ * y with hndef
  have hact : ∀ x ∈ Subgroup.zpowers w₀, n * x * n⁻¹ = y * x * y⁻¹ := by
    intro x hx
    have hyx : y * x * y⁻¹ ∈ Subgroup.zpowers w₀ := (Subgroup.mem_normalizer_iff.mp hyN x).mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
    have hc₀k : c₀ * (y * x * y⁻¹) = (y * x * y⁻¹) * c₀ := by
      rw [← hk]
      exact ((Commute.zpow_right
        (Subgroup.mem_centralizer_singleton_iff.mp hc₀C : Commute c₀ w₀) k)).eq
    calc n * x * n⁻¹ = c₀ * (y * x * y⁻¹) * c₀⁻¹ := by rw [hndef]; group
      _ = y * x * y⁻¹ := by rw [hc₀k, mul_inv_cancel_right]
  have hnN : n ∈ Nw := Nw.mul_mem (hCN hc₀C) hyN
  have hpow : ∀ i : ℕ, n ^ i * w₀ * (n ^ i)⁻¹ = y ^ i * w₀ * (y ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hmem : y ^ i * w₀ * (y ^ i)⁻¹ ∈ Subgroup.zpowers w₀ :=
        (Subgroup.mem_normalizer_iff.mp (Nw.pow_mem hyN i) w₀).mp (Subgroup.mem_zpowers w₀)
      calc n ^ (i + 1) * w₀ * (n ^ (i + 1))⁻¹ = n * (n ^ i * w₀ * (n ^ i)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = n * (y ^ i * w₀ * (y ^ i)⁻¹) * n⁻¹ := by rw [ih]
        _ = y * (y ^ i * w₀ * (y ^ i)⁻¹) * y⁻¹ := hact _ hmem
        _ = y ^ (i + 1) * w₀ * (y ^ (i + 1))⁻¹ := by rw [pow_succ']; group
  obtain ⟨j, hj⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hyj : y ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hn3 : n ^ 3 ^ j ∈ Cw := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hpow (3 ^ j)
    rw [hyj, one_mul, inv_one, mul_one] at this
    calc n ^ 3 ^ j * w₀ = n ^ 3 ^ j * w₀ * (n ^ 3 ^ j)⁻¹ * n ^ 3 ^ j := by group
      _ = w₀ * n ^ 3 ^ j := by rw [this]
  set N₁ := Subgroup.normalizer ((P₀ : Subgroup G) : Set G) ⊓ Nw with hN₁def
  set C₁ := Cw ⊓ N₁ with hC₁def
  have hC₁N₁ : C₁ ≤ N₁ := inf_le_right
  have hC₁n : (C₁.subgroupOf N₁).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, N₁.mul_mem (N₁.mul_mem g.2 x.2) (N₁.inv_mem g.2)⟩
    have := (Subgroup.mem_normalizer_iff.mp (hNC _ g.2.2) x).mp hx.1
    simpa using this
  have hsC₁ : s ∈ C₁ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hw₀s.symm, hsP,
    mem_normalizer_zpowers_of_commute hw₀s.symm⟩
  have hnN₁ : n ∈ N₁ := ⟨hc₀y, hnN⟩
  set m := (C₁.subgroupOf N₁).index with hmdef
  have hm3 : ¬ 3 ∣ m := by
    intro h3
    have h1 := (C₁.subgroupOf N₁).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₁N₁).toEquiv] at h1
    have h2 : 3 ∣ Nat.card C₁ := hs3 ▸ Subgroup.orderOf_dvd_natCard C₁ hsC₁
    have h3' : 9 ∣ Nat.card N₁ := by
      rw [← h1, show (9 : ℕ) = 3 * 3 by norm_num]
      exact Nat.mul_dvd_mul h2 h3
    exact h9 (h3'.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hnm : n ^ m ∈ Cw := by
    have := Subgroup.pow_index_mem (C₁.subgroupOf N₁) (⟨n, hnN₁⟩ : N₁)
    rw [Subgroup.mem_subgroupOf] at this
    exact (by simpa using this : n ^ m ∈ C₁).1
  have hnC : n ∈ Cw := mem_of_pow_mem_of_coprime hn3 hnm
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3))
  have h1 := hact w₀ (Subgroup.mem_zpowers w₀)
  rw [Subgroup.mem_centralizer_singleton_iff.mp hnC, mul_inv_cancel_right] at h1
  calc y * w₀ = y * w₀ * y⁻¹ * y := by group
    _ = w₀ * y := by rw [← h1]

end JTHyp

end CFSG.Walter.JT
