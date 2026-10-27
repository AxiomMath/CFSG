module

public import CFSG.Sporadic.Co2Smith.RigidSetup

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert

universe u

theorem frS_y1_pow :
    frS 0 ^ 3 = 1 := by
  have h := frS_y_pow (i := 0) (by norm_num)
  rwa [mul_zero] at h

theorem frS_s1_sq :
    frS 1 * frS 1 = 1 := frS_s_sq (i := 0) (by norm_num)

theorem frS_s1_y1 :

    frS 1 * frS 0 * frS 1 = frS 0 * frS 0 := frS_s_y (i := 0) (by norm_num)

namespace LocalConfig

variable (c : LocalConfig.{u})

section Sec

variable (N : Subgroup c.E) [N.Characteristic] (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N)

theorem sA_y3 (q : c.E ⧸ N) :
    c.sA N hab (frS 0) (c.sA N hab (frS 0) (c.sA N hab (frS 0) q)) = q := by
  rw [← sA_mul, ← sA_mul, ← pow_three', frS_y1_pow, sA_one]

theorem sA_s2
    (q : c.E ⧸ N) : c.sA N hab (frS 1) (c.sA N hab (frS 1) q) = q := by
  rw [← sA_mul, frS_s1_sq, sA_one]

theorem sA_sy (q : c.E ⧸ N) :
    c.sA N hab (frS 1) (c.sA N hab (frS 0) (c.sA N hab (frS 1) q)) =
      c.sA N hab (frS 0) (c.sA N hab (frS 0) q) := by
  rw [← sA_mul, ← sA_mul, ← sA_mul, frS_s1_y1]

theorem sA_xy (q : c.E ⧸ N) :
    c.sA N hab (frS 8) (c.sA N hab (frS 0) q) = c.sA N hab (frS 0) (c.sA N hab (frS 8) q) := by
  rw [← sA_mul, ← sA_mul, frS_x_y1]

theorem sA_xs (q : c.E ⧸ N) :
    c.sA N hab (frS 8) (c.sA N hab (frS 1) q) = c.sA N hab (frS 1) (c.sA N hab (frS 8) q) := by
  rw [← sA_mul, ← sA_mul, frS_x_s1]

end Sec

theorem quot_comm (N : Subgroup c.E) [N.Normal] (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N)
    (q r : c.E ⧸ N) : q * r = r * q := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    induction r using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h := hab b⁻¹ a⁻¹
      have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
      rw [e]
      exact h

theorem card_quot_mul
    (N : Subgroup c.E) [N.Normal] :
    Nat.card (c.E ⧸ N) * Nat.card N = 2 ^ 9 := by
  rw [← c.card_E, Subgroup.card_eq_card_quotient_mul_card_subgroup N]

theorem sec_large
    (N : Subgroup c.E) [N.Characteristic] (hZ : Subgroup.center c.E ≤ N)
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (hne : N ≠ ⊤) :
    256 ≤ Nat.card (c.E ⧸ N) ∧ (Nat.card (c.E ⧸ N) ≤ 256 →
      (∀ q : c.E ⧸ N, q * q = 1) ∧ ∀ q : c.E ⧸ N, c.sA N hab (frS 0) q = q → q = 1) := by
  have hc := c.quot_comm N hab
  let Ω : Subgroup (c.E ⧸ N) :=
    { carrier := {q | q * q = 1}
      mul_mem' := fun {q r} hq hr => by
        simp only [Set.mem_ofPred_eq] at *
        rw [comm4 hc, hq, hr, one_mul]
      one_mem' := by simp
      inv_mem' := fun {q} hq => by
        simp only [Set.mem_ofPred_eq] at *
        rw [← mul_inv_rev, hq, inv_one] }
  have hΩ : ∀ g : S0, ∀ a ∈ Ω, c.sA N hab g a ∈ Ω := by
    intro g a ha
    show c.sA N hab g a * c.sA N hab g a = 1
    rw [← map_mul, show a * a = 1 from ha, map_one]
  have hN5 : ∀ e : c.E, c.xh * e = e * c.xh → e ∈ N :=
    fun e he => hZ (c.mem_center_of_comm_xh e he)
  have hcardA : Nat.card (c.E ⧸ N) ∣ 2 ^ 9 := ⟨_, (c.card_quot_mul N).symm⟩
  have hntriv : 1 < Nat.card (c.E ⧸ N) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    obtain ⟨e, he⟩ : ∃ e : c.E, e ∉ N := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.mpr fun e _ => h e)
    exact ⟨⟨(e : c.E ⧸ N), 1, fun h => he ((QuotientGroup.eq_one_iff e).mp h)⟩⟩
  obtain ⟨q0, hq0⟩ : ∃ q : c.E ⧸ N, orderOf q = 2 := by
    have h2 : 2 ∣ Nat.card (c.E ⧸ N) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcardA
      rw [hj] at hntriv ⊢
      rcases j with _ | j
      · simp at hntriv
      · exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact exists_prime_orderOf_dvd_card' 2 h2
  have hq0Ω : q0 ∈ Ω := by
    show q0 * q0 = 1
    rw [← sq, ← hq0, pow_orderOf_eq_one]
  have hq01 : q0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hq0
    exact absurd hq0 (by norm_num)
  have hres := trivial_or_large hc (c.sA N hab (frS 0)) (c.sA N hab (frS 1))
    (c.sA N hab (frS 8)) Ω (fun a ha => ha) (hΩ _) (hΩ _) (hΩ _) (c.sA_y3 N hab)
    (c.sA_s2 N hab) (c.sA_sy N hab) (c.sA_xy N hab) (c.sA_xs N hab)
    (fun U _ hU => c.sec_card_mod5' N hab hN5 U hU)
    ((Subgroup.card_subgroup_dvd_card Ω).trans hcardA)
  rcases hres with htriv | ⟨hlarge, hfpf⟩
  · exfalso
    have hall := c.sec_trivial_of_y1 N hab Ω (fun g a ha => hΩ g a ha) htriv
    have hx : c.sA N hab (frS 8) q0 = q0 := hall (frS 8) q0 hq0Ω
    have h5 := c.sec_card_mod5' N hab hN5 (Subgroup.zpowers q0) (by
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      show c.sA N hab (frS 8) (q0 ^ k) ∈ Subgroup.zpowers q0
      rw [map_zpow, hx]
      exact Subgroup.zpow_mem_zpowers q0 k)
    rw [Nat.card_zpowers, hq0] at h5
    norm_num at h5
  · have hΩA : Nat.card Ω ≤ Nat.card (c.E ⧸ N) := Subgroup.card_le_card_group Ω
    refine ⟨hlarge.trans hΩA, fun hA => ?_⟩
    have hΩtop : Ω = ⊤ := Subgroup.eq_top_of_card_eq Ω (le_antisymm hΩA (hA.trans hlarge))
    have hmem : ∀ q : c.E ⧸ N, q ∈ Ω := fun q => hΩtop ▸ Subgroup.mem_top q
    exact ⟨fun q => hmem q, fun q hq => hfpf (hΩA.trans hA) q (hmem q) hq⟩

theorem ucs_eq_top_of_succ_eq {G : Type*} [Group G] [Group.IsNilpotent G] {k : ℕ}
    (h : Subgroup.upperCentralSeries G (k + 1) = Subgroup.upperCentralSeries G k) :
    Subgroup.upperCentralSeries G k = ⊤ := by
  have hstab : ∀ m, Subgroup.upperCentralSeries G (k + m) = Subgroup.upperCentralSeries G k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← h]
      ext x
      rw [show k + (m + 1) = (k + m) + 1 by omega, Subgroup.mem_upperCentralSeries_succ_iff,
        Subgroup.mem_upperCentralSeries_succ_iff, ih]
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent G
  rw [← hstab n]
  exact eq_top_iff.mpr (hn ▸ Subgroup.upperCentralSeries_mono G (by omega : n ≤ k + n))

theorem isNilpotent_E : Group.IsNilpotent c.E :=
  IsPGroup.isNilpotent CFSG.pCore_isPGroup

theorem card_ucs_dvd
    (k : ℕ) : Nat.card (Subgroup.upperCentralSeries c.E k) ∣ 2 ^ 9 :=
  c.card_E ▸ Subgroup.card_subgroup_dvd_card _

theorem center_le_ucs
    {k : ℕ} (hk : 1 ≤ k) :
    Subgroup.center c.E ≤ Subgroup.upperCentralSeries c.E k := by
  rw [← Subgroup.upperCentralSeries_one]
  exact Subgroup.upperCentralSeries_mono c.E hk

theorem card_ucs_modEq
    {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (Subgroup.upperCentralSeries c.E k) ≡
      Nat.card {e : c.E // c.xh * e = e * c.xh} [MOD 5] :=
  c.card_modEq_CEx _ (fun _ ht => char_mem _ _ ht)
    fun e he => c.center_le_ucs hk (c.mem_center_of_comm_xh e he)

theorem card_top_modEq :
    Nat.card c.E ≡ Nat.card {e : c.E // c.xh * e = e * c.xh} [MOD 5] := by
  have h := c.card_modEq_CEx ⊤ (fun _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _)
  rwa [Subgroup.card_top] at h

theorem ucs_step
    {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (Subgroup.upperCentralSeries c.E (k + 1)) =
        Nat.card (Subgroup.upperCentralSeries c.E k) ∨
      Nat.card (Subgroup.upperCentralSeries c.E (k + 1)) =
        16 * Nat.card (Subgroup.upperCentralSeries c.E k) ∨
      Nat.card (Subgroup.upperCentralSeries c.E (k + 1)) =
        256 * Nat.card (Subgroup.upperCentralSeries c.E k) :=
  ratio_of_modEq_five (Subgroup.card_dvd_of_le (Subgroup.upperCentralSeries_mono c.E (by omega)))
    (c.card_ucs_dvd _) ((c.card_ucs_modEq (by omega)).trans (c.card_ucs_modEq hk).symm)

theorem ucs_eq_of_card {k : ℕ}
    (h : Nat.card (Subgroup.upperCentralSeries c.E (k + 1)) =
      Nat.card (Subgroup.upperCentralSeries c.E k)) :
    Subgroup.upperCentralSeries c.E (k + 1) = Subgroup.upperCentralSeries c.E k :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.upperCentralSeries_mono c.E (Nat.le_succ k)) h.le).symm

theorem ucs_top_of_card
    {k : ℕ} (h : Nat.card (Subgroup.upperCentralSeries c.E k) = 2 ^ 9) :
    Subgroup.upperCentralSeries c.E k = ⊤ :=
  Subgroup.eq_top_of_card_eq _ (by rw [h, c.card_E])

theorem comm_mem_of_succ_top
    {k : ℕ} (h : Subgroup.upperCentralSeries c.E (k + 1) = ⊤) (a b : c.E) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.upperCentralSeries c.E k := by
  have ha : a ∈ Subgroup.upperCentralSeries c.E (k + 1) := h ▸ Subgroup.mem_top a
  rw [Subgroup.mem_upperCentralSeries_succ_iff] at ha
  have := ha b
  rwa [commutatorElement_def] at this

theorem center_ne_top : Subgroup.center c.E ≠ ⊤ := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := c.loc.pCore_noncomm
  have hx' : (⟨x, hx⟩ : c.E) ∈ Subgroup.center c.E := h ▸ Subgroup.mem_top _
  rw [Subgroup.mem_center_iff] at hx'
  exact hxy (congrArg Subtype.val (hx' ⟨y, hy⟩)).symm

theorem center_structure :
    Nat.card (Subgroup.center c.E) = 2 ∧
      (∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center c.E) ∧
      (∀ q : c.E ⧸ Subgroup.center c.E, q * q = 1) ∧
      ∀ hab : (∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center c.E),
        ∀ q : c.E ⧸ Subgroup.center c.E, c.sA _ hab (frS 0) q = q → q = 1 := by
  have := c.isNilpotent_E
  have h1 : Nat.card (Subgroup.upperCentralSeries c.E 1) = Nat.card (Subgroup.center c.E) := by
    rw [Subgroup.upperCentralSeries_one]
  have hcne : Nat.card (Subgroup.center c.E) ≠ 2 ^ 9 := fun h =>
    c.center_ne_top (Subgroup.eq_top_of_card_eq _ (by rw [h, c.card_E]))
  have hZ1 : Nat.card (Subgroup.center c.E) = 2 ∨ Nat.card (Subgroup.center c.E) = 32 := by
    have h := ratio_of_modEq_five (Subgroup.card_subgroup_dvd_card (Subgroup.center c.E))
      (by rw [c.card_E]) (c.card_top_modEq.trans (h1 ▸ c.card_ucs_modEq le_rfl).symm)
    rw [c.card_E] at h
    omega
  have hcomm2 : Subgroup.upperCentralSeries c.E 2 = ⊤ →
      ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center c.E := fun h a b => by
    have := c.comm_mem_of_succ_top (k := 1) h a b
    rwa [Subgroup.upperCentralSeries_one] at this
  have hstep1 := c.ucs_step (k := 1) le_rfl
  have hstep2 := c.ucs_step (k := 2) (by norm_num)
  rw [show (1 : ℕ) + 1 = 2 from rfl] at hstep1
  rw [show (2 : ℕ) + 1 = 3 from rfl] at hstep2
  have hd2 := c.card_ucs_dvd 2
  have hd3 := c.card_ucs_dvd 3
  rw [h1] at hstep1
  have hZ2ne : Nat.card (Subgroup.upperCentralSeries c.E 2) ≠ Nat.card (Subgroup.center c.E) := by
    intro h
    rw [← h1] at h
    have := ucs_eq_top_of_succ_eq (c.ucs_eq_of_card h)
    rw [Subgroup.upperCentralSeries_one] at this
    exact c.center_ne_top this
  have hsecZ1 := fun h2 : Subgroup.upperCentralSeries c.E 2 = ⊤ =>
    c.sec_large (Subgroup.center c.E) le_rfl (hcomm2 h2) c.center_ne_top
  have hqZ1 := c.card_quot_mul (Subgroup.center c.E)
  rcases hZ1 with hZ1 | hZ1
  ·
    rw [hZ1] at hstep1 hqZ1
    rcases hstep1 with h | h | h
    · exact absurd (h.trans hZ1.symm) hZ2ne
    ·
      exfalso
      rw [h] at hstep2
      have h3 : Nat.card (Subgroup.upperCentralSeries c.E 3) = 2 ^ 9 := by
        rcases hstep2 with h' | h' | h'
        · exfalso
          have := ucs_eq_top_of_succ_eq (c.ucs_eq_of_card (k := 2) (h'.trans h.symm))
          have hc2 := congrArg (fun K : Subgroup c.E => Nat.card K) this
          simp only [Subgroup.card_top] at hc2
          rw [h, c.card_E] at hc2
          norm_num at hc2
        · rw [h']; norm_num
        · rw [h'] at hd3
          norm_num at hd3
      have htop3 := c.ucs_top_of_card h3
      have hne2 : Subgroup.upperCentralSeries c.E 2 ≠ ⊤ := fun ht => by
        have hc2 := congrArg (fun K : Subgroup c.E => Nat.card K) ht
        simp only [Subgroup.card_top] at hc2
        rw [h, c.card_E] at hc2
        norm_num at hc2
      have hsec := c.sec_large (Subgroup.upperCentralSeries c.E 2) (c.center_le_ucs (by norm_num))
        (c.comm_mem_of_succ_top htop3) hne2
      have hq := c.card_quot_mul (Subgroup.upperCentralSeries c.E 2)
      rw [h] at hq
      omega
    ·
      have htop2 := c.ucs_top_of_card (by rw [h]; norm_num)
      obtain ⟨-, hsec⟩ := hsecZ1 htop2
      obtain ⟨hsq, hfpf⟩ := hsec (by omega)
      exact ⟨hZ1, hcomm2 htop2, hsq, fun _ => hfpf⟩
  ·
    exfalso
    rw [hZ1] at hstep1 hqZ1
    have h2 : Nat.card (Subgroup.upperCentralSeries c.E 2) = 2 ^ 9 := by
      rcases hstep1 with h | h | h
      · exact absurd (h.trans hZ1.symm) hZ2ne
      · rw [h]; norm_num
      · rw [h] at hd2
        norm_num at hd2
    obtain ⟨hl, -⟩ := hsecZ1 (c.ucs_top_of_card h2)
    omega

end LocalConfig

end CFSG.Sporadic.Co2Smith
