module

public import CFSG.Walter.W67.Section6.Core62J
public import CFSG.Walter.W67.Section6.Core62I

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

theorem coprime_card_range {r : ℕ} [Fact r.Prime] {S N : Subgroup G} {H : Type*} [Group H]
    (ρ : N →* H) (hSN : S ≤ N) (hScard : Nat.card S = r ^ (Nat.card G).factorization r)
    (hker : S.subgroupOf N ≤ ρ.ker) : Nat.Coprime r (Nat.card ρ.range) := by
  rw [← Subgroup.index_ker]
  apply (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
  intro hdvd
  have h1 := ρ.ker.card_mul_index
  have h2 : r ^ (Nat.card G).factorization r ∣ Nat.card ρ.ker := by
    rw [← hScard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact Subgroup.card_dvd_of_le hker
  have h3 : r ^ ((Nat.card G).factorization r + 1) ∣ Nat.card N := by
    rw [← h1, pow_succ]
    exact Nat.mul_dvd_mul h2 hdvd
  exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out
    (h3.trans (Subgroup.card_subgroup_dvd_card N))

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

section CaseCSmall

variable {S : Subgroup G} {w : G} (c : CaseC r J y₀ P₀ P₁ S w)
  (hδ : Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) ≤ r * Nat.card P₁)
include c hδ

theorem caseC_decomp {s : G} (hs : s ∈ S) :
    ∃ b ∈ P₁, ∃ k i : ℕ, s = b * w ^ k * x₀ ^ i := by
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hXN : Subgroup.zpowers x₀ ≤
      Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx₀S).trans (h.caseC_normal c)
  obtain ⟨q, hq, x, hx, rfl⟩ := (mem_sup_iff_of_le_normalizer hXN).mp (h.caseC_sup c hs)
  rw [h.caseC_eq_sup c hδ] at hq
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.caseC_w_comm c hb
  obtain ⟨b, hb, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hwN).mp hq
  obtain ⟨k, rfl⟩ := (isOfFinOrder_of_finite w).mem_powers_iff_mem_zpowers.mpr he
  obtain ⟨i, rfl⟩ := (isOfFinOrder_of_finite x₀).mem_powers_iff_mem_zpowers.mpr hx
  exact ⟨b, hb, k, i, rfl⟩

omit hδ in
theorem caseC_le_normalizer_P₁ : S ≤ Subgroup.normalizer (P₁ : Set G) := fun _ hs =>
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun _ hb => h.caseC_P₁_comm c hb hs)

omit hδ in
theorem caseC_normal_P₁ : (P₁.subgroupOf S).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right.trans c.hPS)).mpr
    (h.caseC_le_normalizer_P₁ c)

theorem caseC_card_Q :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) = Nat.card P₁ * r := by
  have hw1 : w ≠ 1 := fun h1 => c.hwY (h1 ▸ Subgroup.one_mem _)
  have hwo : orderOf w = r := orderOf_eq_prime c.hw.2.1 hw1
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.caseC_w_comm c hb
  rw [h.caseC_eq_sup c hδ, card_sup_of_inf_eq_bot hwN (h.caseC_inf_w c), Nat.card_zpowers, hwo]

theorem caseC_plane [(P₁.subgroupOf S).Normal] : Huppert.Plane r (S ⧸ P₁.subgroupOf S) := by
  have hcard : Nat.card (S ⧸ P₁.subgroupOf S) = r ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P₁.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right.trans c.hPS)).toEquiv,
      h.caseC_card c, h.caseC_card_Q c hδ] at h1
    have h2 : Nat.card (S ⧸ P₁.subgroupOf S) * Nat.card P₁ = r ^ 2 * Nat.card P₁ := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hcomm : ∀ a b : S ⧸ P₁.subgroupOf S, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := r) hcard).is_comm.comm a b
  refine ⟨hcomm, fun v => ?_, hcard⟩
  induction v using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨b, hb, k, i, hs⟩ := h.caseC_decomp c hδ s.2
    have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
    have hbS : b ∈ S := c.hPS (Subgroup.mem_sup_right hb)
    have e : s = ⟨b, hbS⟩ * ⟨w, c.hw.1⟩ ^ k * ⟨x₀, hx₀S⟩ ^ i := Subtype.ext (by simpa using hs)
    have hb1 : ((⟨b, hbS⟩ : S) : S ⧸ P₁.subgroupOf S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hb
    have hw1 : ((⟨w, c.hw.1⟩ : S) : S ⧸ P₁.subgroupOf S) ^ r = 1 := by
      rw [← QuotientGroup.mk_pow]
      convert QuotientGroup.mk_one (P₁.subgroupOf S) using 2
      exact Subtype.ext (by simpa using c.hw.2.1)
    have hx1 : ((⟨x₀, hx₀S⟩ : S) : S ⧸ P₁.subgroupOf S) ^ r = 1 := by
      rw [← QuotientGroup.mk_pow]
      convert QuotientGroup.mk_one (P₁.subgroupOf S) using 2
      exact Subtype.ext (by simpa using (show x₀ ^ r = 1 by
        rw [← h.orderOf_x₀, pow_orderOf_eq_one]))
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hb1, one_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, (Commute.mul_pow (hcomm _ _) r), ← pow_mul, ← pow_mul, mul_comm k,
      mul_comm i, pow_mul, pow_mul, hw1, hx1, one_pow, one_pow, one_mul]

theorem caseC_normalizer_le (hScard : Nat.card S = r ^ (Nat.card G).factorization r) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) := by
  have : (P₁.subgroupOf S).Normal := h.caseC_normal_P₁ c
  have hpl := h.caseC_plane c hδ
  have hcomm : ∀ a b : S ⧸ P₁.subgroupOf S, a * b = b * a := hpl.comm
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hP₁S : P₁ ≤ S := le_sup_right.trans c.hPS
  have hNP₁ := h.caseC_normalizer_P₁ c
  set ρ := quotAct (N := Subgroup.normalizer (S : Set G)) le_rfl hNP₁ with hρ
  obtain ⟨d', hd'S, -, hd'J, hd'x, ⟨m, hd'y, hm1⟩, hd'o⟩ :=
    h.exists_d' c.hS hScard c.hPS c.hJS c.hSP (h.caseC_isT_x₀ c hδ)
  set e : S ⧸ P₁.subgroupOf S := ((⟨x₀, hx₀S⟩ : S) : S ⧸ P₁.subgroupOf S) with he_def
  set f : S ⧸ P₁.subgroupOf S := ((⟨w, c.hw.1⟩ : S) : S ⧸ P₁.subgroupOf S) with hf_def
  have hmk : ∀ {a b : S}, (a : S ⧸ P₁.subgroupOf S) = b ↔ (a : G)⁻¹ * b ∈ P₁ := fun {a b} =>
    QuotientGroup.eq
  have he : e ≠ 1 := by
    intro h1
    have hx := (QuotientGroup.eq_one_iff _).mp h1
    have : x₀ ∈ P₀ ⊓ P₁ := Subgroup.mem_inf.mpr ⟨h.x₀_mem, hx⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at this
    exact h.x₀_ne_one this
  have hf : f ∉ Subgroup.zpowers e := by
    intro hfe
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfe
    rw [he_def, ← QuotientGroup.mk_zpow, hf_def, hmk] at hk
    simp only [SubgroupClass.coe_zpow] at hk
    have hQ : x₀ ^ k ∈ S ⊓ Subgroup.centralizer ({w} : Set G) := by
      have e1 : x₀ ^ k = w * ((x₀ ^ k)⁻¹ * w)⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (caseC_w_mem c) (Subgroup.inv_mem _ (h.caseC_P₁_le c hk))
    have hk1 : x₀ ^ k ∈ (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ P₀ :=
      Subgroup.mem_inf.mpr ⟨hQ, Subgroup.zpow_mem _ h.x₀_mem k⟩
    rw [h.caseC_inf_P₀ c, Subgroup.mem_bot] at hk1
    rw [hk1, inv_one, one_mul] at hk
    exact c.hwY (h.mem_Y_of_pow hk c.hw.2.1)
  have hd'wS : d' * w * d'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hd'S w).mp c.hw.1
  have hd'wJ : J * (d' * w * d'⁻¹) * J⁻¹ = (d' * w * d'⁻¹)⁻¹ := by
    have e1 : J * (d' * w * d'⁻¹) * J⁻¹ = d' * (J * w * J⁻¹) * d'⁻¹ := by
      calc J * (d' * w * d'⁻¹) * J⁻¹ = (J * d') * w * (J * d')⁻¹ := by group
        _ = (d' * J) * w * (d' * J)⁻¹ := by rw [hd'J]
        _ = d' * (J * w * J⁻¹) * d'⁻¹ := by group
    rw [e1, c.hwJ]
    group
  have hd'wQ := h.caseC_inv_mem c hd'wS hd'wJ
  rw [h.caseC_eq_sup c hδ] at hd'wQ
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.caseC_w_comm c hb
  obtain ⟨b, hb, e', he', hbe⟩ := (mem_sup_iff_of_le_normalizer hwN).mp hd'wQ
  obtain ⟨j, rfl⟩ := (isOfFinOrder_of_finite w).mem_powers_iff_mem_zpowers.mpr he'
  have hyC := h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP
  set c₁ := x₀ * w * x₀⁻¹ * w⁻¹ with hc₁
  have hc₁Y : c₁ ∈ Subgroup.zpowers y₀ := c.hw.2.2 x₀ hx₀S
  have hc₁1 : c₁ ≠ 1 := by
    intro h1
    apply h.caseC_x₀ c
    calc x₀ * w = c₁ * w * x₀ := by rw [hc₁]; group
      _ = w * x₀ := by rw [h1, one_mul]
  have hc₁o : orderOf c₁ = r := orderOf_eq_prime (IsT.pow_eq_one_of_mem_zpowers h.y₀_pow hc₁Y) hc₁1
  have hk : ((j : ℕ) : ZMod r) ≠ 1 := by
    intro hj1
    apply hm1
    have h1 : d' * c₁ * d'⁻¹ = c₁ ^ m := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc₁Y
      rw [← hi, ← conj_zpow, hd'y, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
        mul_comm]
    have hbx : b * x₀ = x₀ * b := Subgroup.mem_centralizer_singleton_iff.mp (h.M_le (h.P₁_le_M hb))
    have hbw : b * w = w * b := h.caseC_w_comm c hb
    have hcw : c₁ * w = w * c₁ := (IsT.comm_of_mem_zpowers hyC hc₁Y c.hw.1)
    have h2 : d' * c₁ * d'⁻¹ = c₁ ^ j := by
      have e1 : d' * c₁ * d'⁻¹ = x₀ * (d' * w * d'⁻¹) * x₀⁻¹ * (d' * w * d'⁻¹)⁻¹ := by
        rw [hc₁]
        calc d' * (x₀ * w * x₀⁻¹ * w⁻¹) * d'⁻¹ = (d' * x₀ * d'⁻¹) * (d' * w * d'⁻¹) *
            (d' * x₀ * d'⁻¹)⁻¹ * (d' * w * d'⁻¹)⁻¹ := by group
          _ = _ := by rw [hd'x]
      rw [e1, ← hbe]
      have hxb : x₀ * b * x₀⁻¹ = b := by rw [← hbx, mul_inv_cancel_right]
      have e3 : x₀ * w ^ j * x₀⁻¹ = c₁ ^ j * w ^ j := by
        rw [← conj_pow, show x₀ * w * x₀⁻¹ = c₁ * w by rw [hc₁]; group,
          (Commute.mul_pow (show Commute c₁ w from hcw) j)]
      have hcj : c₁ ^ j ∈ Subgroup.zpowers y₀ := Subgroup.pow_mem _ hc₁Y j
      have hbS : b ∈ S := c.hPS (Subgroup.mem_sup_right hb)
      calc x₀ * (b * w ^ j) * x₀⁻¹ * (b * w ^ j)⁻¹
          = (x₀ * b * x₀⁻¹) * (x₀ * w ^ j * x₀⁻¹) * (w ^ j)⁻¹ * b⁻¹ := by group
        _ = b * c₁ ^ j * b⁻¹ := by rw [hxb, e3]; group
        _ = c₁ ^ j := by rw [← IsT.comm_of_mem_zpowers hyC hcj hbS, mul_inv_cancel_right]
    have h3 : c₁ ^ m = c₁ ^ j := by rw [← h1, h2]
    rw [pow_eq_pow_iff_modEq, hc₁o] at h3
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h3]
    exact hj1
  have hSN : S ≤ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer
  have hker : S.subgroupOf (Subgroup.normalizer (S : Set G)) ≤ ρ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H t =>
      rw [hρ, quotAct_mk, MulAut.one_apply]
      change ((⟨s, hs⟩ * t * (⟨s, hs⟩ : S)⁻¹ : S) : S ⧸ P₁.subgroupOf S) = t
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hcomm _ (t : S ⧸ P₁.subgroupOf S),
        mul_assoc, QuotientGroup.mk_inv, mul_inv_cancel, mul_one]
  have hcop := coprime_card_range ρ hSN hScard hker
  have h2 : (Nat.card ρ.range).factorization 2 ≤ 1 :=
    ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_range_dvd ρ) 2).trans (h.factorization_two_le c.hS c.hPS le_rfl)
  have hJx : J * x₀ * J⁻¹ = x₀ := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le h.x₀_mem), mul_inv_cancel_right]
  have hte : ρ ⟨J, c.hJS⟩ e = e := by
    rw [hρ, he_def, quotAct_mk]
    exact congrArg _ (Subtype.ext hJx)
  have htf : ρ ⟨J, c.hJS⟩ f = f⁻¹ := by
    rw [hρ, hf_def, quotAct_mk, ← QuotientGroup.mk_inv]
    exact congrArg _ (Subtype.ext c.hwJ)
  have hδe : ρ ⟨d', hd'S⟩ e = e := by
    rw [hρ, he_def, quotAct_mk]
    exact congrArg _ (Subtype.ext hd'x)
  have hδf : ρ ⟨d', hd'S⟩ f = f ^ ((j : ℕ) : ZMod r).val := by
    rw [hpl.pow_val_natCast, hρ, hf_def, quotAct_mk, ← QuotientGroup.mk_pow]
    rw [hmk]
    change (d' * w * d'⁻¹)⁻¹ * w ^ j ∈ P₁
    have hbe' : (d' * w * d'⁻¹)⁻¹ * w ^ j = (w ^ j)⁻¹ * b⁻¹ * (w ^ j)⁻¹⁻¹ := by
      rw [← hbe]; group
    rw [hbe']
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hwN (Subgroup.pow_mem _
      (Subgroup.mem_zpowers w) j))) b⁻¹).mp (P₁.inv_mem hb)
  have hδo : Odd (orderOf (⟨d', hd'S⟩ : Subgroup.normalizer (S : Set G))) := by
    rw [Subgroup.orderOf_mk]
    exact hd'o
  have hcomm' := GL2.comm_of_plane hpl he hf h.r_ne_two ρ hcop h2 hte htf hδe hδf hk hδo
  intro n hn
  apply JT.mem_normalizer_of_conj_mem
  intro q hq
  have hqS : q ∈ S := (Subgroup.mem_inf.mp hq).1
  have hnqS : n * q * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn q).mp hqS
  set v : S ⧸ P₁.subgroupOf S := ((⟨n * q * n⁻¹, hnqS⟩ : S) : S ⧸ P₁.subgroupOf S) with hv
  have hvρ : v = ρ ⟨n, hn⟩ ((⟨q, hqS⟩ : S) : S ⧸ P₁.subgroupOf S) := rfl
  have htq : ρ ⟨J, c.hJS⟩ ((⟨q, hqS⟩ : S) : S ⧸ P₁.subgroupOf S) =
      ((⟨q, hqS⟩ : S) : S ⧸ P₁.subgroupOf S)⁻¹ := by
    rw [hρ, quotAct_mk, ← QuotientGroup.mk_inv]
    exact congrArg _ (Subtype.ext (h.caseC_J_inv c q hq))
  have hvJ : ρ ⟨J, c.hJS⟩ v = v⁻¹ := by
    rw [hvρ, ← MulAut.mul_apply, (hcomm' ⟨n, hn⟩).1.symm, MulAut.mul_apply, htq, map_inv]
  obtain ⟨a₀, b₀, hab⟩ := hpl.exists_coords he hf v
  have h1 : ρ ⟨J, c.hJS⟩ v = e ^ a₀.val * (f ^ b₀.val)⁻¹ := by
    rw [hab, map_mul, map_pow, map_pow, hte, htf, inv_pow]
  have h2' : v⁻¹ = (e ^ a₀.val)⁻¹ * (f ^ b₀.val)⁻¹ := by
    rw [hab, mul_inv_rev, hcomm]
  rw [h1, h2'] at hvJ
  have h3 : e ^ (a₀ + a₀).val * f ^ (0 : ZMod r).val =
      e ^ (0 : ZMod r).val * f ^ (0 : ZMod r).val := by
    rw [hpl.pow_val_add, ZMod.val_zero, pow_zero, pow_zero, mul_one, mul_one]
    have := mul_right_cancel hvJ
    calc e ^ a₀.val * e ^ a₀.val = (e ^ a₀.val)⁻¹ * e ^ a₀.val := by rw [← this]
      _ = 1 := inv_mul_cancel _
  have ha₀0 : a₀ = 0 := by
    have h4 := (GL2.coords_unique hpl he hf h3).1
    have h5 : (2 : ZMod r) * a₀ = 0 := by rw [two_mul]; exact h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 (GL2.two_ne_zero' h.r_ne_two)
    · exact h6
  rw [ha₀0, ZMod.val_zero, pow_zero, one_mul, hf_def, ← QuotientGroup.mk_pow, eq_comm, hmk] at hab
  simp only [SubgroupClass.coe_pow] at hab
  have e1 : n * q * n⁻¹ = w ^ b₀.val * ((w ^ b₀.val)⁻¹ * (n * q * n⁻¹)) := by group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (caseC_w_mem c) _) (h.caseC_P₁_le c hab)

theorem caseC_weaklyClosedIn' (hScard : Nat.card S = r ^ (Nat.card G).factorization r) :
    WeaklyClosedIn S (S ⊓ Subgroup.centralizer ({w} : Set G)) := by
  set Q := S ⊓ Subgroup.centralizer ({w} : Set G) with hQ
  refine ⟨inf_le_left, fun g hg => ?_⟩
  have hA : rightConjugate Q g = cj g⁻¹ Q := rfl
  rw [hA] at hg ⊢
  have hAS : S ≤ Subgroup.normalizer ((cj g⁻¹ Q : Subgroup G) : Set G) := by
    have hidx : (cj g⁻¹ Q).relIndex S = r :=
      relIndex_eq_of_card hg (by rw [card_cj, h.caseC_card c])
    have hSr : (Nat.card S).minFac = r := by
      rw [hScard]
      refine Nat.Prime.pow_minFac Fact.out ?_
      intro h0
      rw [h0, pow_zero] at hScard
      have := Subgroup.card_le_of_le (c.hPS.trans le_rfl)
      rw [hScard, h.card_P] at this
      have h1 : 1 < Nat.card P₀ := (Subgroup.one_lt_card_iff_ne_bot _).mpr h.P₀_ne_bot
      have h2 : 0 < Nat.card P₁ := Nat.card_pos
      nlinarith
    have hn : ((cj g⁻¹ Q).subgroupOf S).Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hSr]; exact hidx)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hg).mp hn
  have hgS : cj g⁻¹ S ≤ Subgroup.normalizer ((cj g⁻¹ Q : Subgroup G) : Set G) := by
    rw [← cj_normalizer]
    exact cj_mono (h.caseC_normal c)
  have hSc := card_eq_of_le_of_card_eq hAS hScard
  have hgSc : Nat.card (cj g⁻¹ S) =
      r ^ (Nat.card (Subgroup.normalizer ((cj g⁻¹ Q : Subgroup G) : Set G))).factorization r := by
    rw [card_cj, hSc]
  obtain ⟨ℓ, hℓ, hℓS⟩ := exists_conj_of_sylowIn hAS hgS hSc hgSc
  have hh₀ : g * ℓ ∈ Subgroup.normalizer (S : Set G) :=
    mem_normalizer_of_cj_eq (by rw [cj_mul, ← hℓS, ← cj_mul, mul_inv_cancel, cj_one])
  have hQN := h.caseC_normalizer_le c hδ hScard hh₀
  calc cj g⁻¹ Q = cj ℓ⁻¹ (cj g⁻¹ Q) := (cj_eq_self_of_mem_normalizer (Subgroup.inv_mem _ hℓ)).symm
    _ = cj (g * ℓ)⁻¹ Q := by rw [← cj_mul, mul_inv_rev]
    _ = Q := cj_eq_self_of_mem_normalizer (Subgroup.inv_mem _ hQN)

theorem false_of_caseC_small (hScard : Nat.card S = r ^ (Nat.card G).factorization r) : False :=
  h.false_of_caseC_weak c hScard (h.caseC_weaklyClosedIn' c hδ hScard)

end CaseCSmall

end Hyp62

end CFSG.Walter.W67.Sec6
