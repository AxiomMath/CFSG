module

public import CFSG.Walter.W67.Section6.Core62G
public import CFSG.Walter.W67.Section6.Core62F

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

theorem exists_le_cj_of_sylowIn {r : ℕ} [Fact r.Prime] {L S R : Subgroup G} (hSL : S ≤ L)
    (hSc : Nat.card S = r ^ (Nat.card L).factorization r) (hRL : R ≤ L) (hR : IsPGroup r R) :
    ∃ c ∈ L, R ≤ cj c S := by
  obtain ⟨T, hT⟩ := (hR.comap_subtype (K := L)).exists_le_sylow
  set T' := (T : Subgroup L).map L.subtype with hT'
  have hT'L : T' ≤ L := Subgroup.map_subtype_le _
  have hT'c : Nat.card T' = r ^ (Nat.card L).factorization r := by
    rw [hT', Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity]
  obtain ⟨c, hcL, hc⟩ := exists_conj_of_sylowIn hSL hT'L hSc hT'c
  refine ⟨c, hcL, fun x hx => ?_⟩
  rw [← hc]
  exact ⟨⟨x, hRL hx⟩, hT hx, rfl⟩

theorem card_eq_of_le_of_card_eq {r : ℕ} [Fact r.Prime] {S L : Subgroup G} (hSL : S ≤ L)
    (hSc : Nat.card S = r ^ (Nat.card G).factorization r) :
    Nat.card S = r ^ (Nat.card L).factorization r := by
  have h1 : (Nat.card L).factorization r ≤ (Nat.card G).factorization r :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card L) r
  have h2 : (Nat.card G).factorization r ≤ (Nat.card L).factorization r := by
    have := Subgroup.card_dvd_of_le hSL
    rw [hSc] at this
    exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp this
  rw [hSc, le_antisymm h1 h2]

namespace IsT

variable {S : Subgroup G} {y₀ w : G} {r : ℕ}

omit [Finite G] in
theorem conj_mul (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) (hw : IsT S y₀ r w) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) :
    (a * b) * w * (a * b)⁻¹ * w⁻¹ = (a * w * a⁻¹ * w⁻¹) * (b * w * b⁻¹ * w⁻¹) := by
  have hcb := hw.2.2 b hb
  have hca := hw.2.2 a ha
  have e : (a * b) * w * (a * b)⁻¹ * w⁻¹ = a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) :=
    by group
  rw [e, ← comm_of_mem_zpowers hyC hcb ha, mul_inv_cancel_right]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcb
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hca
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

end IsT

structure CaseC (r : ℕ) (J y₀ : G) (P₀ P₁ S : Subgroup G) (w : G) : Prop where
  hS : IsPGroup r S
  hPS : P₀ ⊔ P₁ ≤ S
  hJS : J ∈ Subgroup.normalizer (S : Set G)
  hSP : ¬ S ≤ P₀ ⊔ P₁
  hw : IsT S y₀ r w
  hwY : w ∉ Subgroup.zpowers y₀
  hwJ : J * w * J⁻¹ = w⁻¹

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

omit [Finite G] in
theorem mem_P₁_of_inv {p : G} (hp : p ∈ P₀ ⊔ P₁) (hpJ : J * p * J⁻¹ = p⁻¹) : p ∈ P₁ := by
  obtain ⟨b, hb, a, ha, rfl⟩ := h.mem_P.mp hp
  have haJ : J * a * J⁻¹ = a := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le ha), mul_inv_cancel_right]
  have e : J * (b * a) * J⁻¹ = (J * b * J⁻¹) * (J * a * J⁻¹) := by group
  rw [e, h.P₁_inv b hb, haJ, mul_inv_rev] at hpJ
  have h0 : a * b⁻¹ * a = b⁻¹ := by
    calc a * b⁻¹ * a = a * (b⁻¹ * a) := by group
      _ = a * (a⁻¹ * b⁻¹) := by rw [hpJ]
      _ = b⁻¹ := by group
  have h1 : a * a = (a * b * a⁻¹) * b⁻¹ := by
    calc a * a = (a * b * a⁻¹) * (a * b⁻¹ * a) := by group
      _ = (a * b * a⁻¹) * b⁻¹ := by rw [h0]
  have h2 : a * a ∈ P₀ ⊓ P₁ := by
    refine ⟨P₀.mul_mem ha ha, ?_⟩
    rw [h1]
    exact P₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.P₀_le_N ha) b).mp hb) (P₁.inv_mem hb)
  rw [h.inf_eq_bot, Subgroup.mem_bot] at h2
  rw [h.eq_one_of_sq h.P₀_r ha h2, mul_one]
  exact hb

section CaseC

variable {S : Subgroup G} {w : G} (c : CaseC r J y₀ P₀ P₁ S w)
include c

theorem caseC_x₀ : x₀ * w ≠ w * x₀ := by
  intro hxw
  have hwP : w ∈ P₀ ⊔ P₁ := by
    rw [← h.inf_centralizer_eq c.hS c.hPS]
    exact Subgroup.mem_inf.mpr ⟨c.hw.1, Subgroup.mem_centralizer_singleton_iff.mpr hxw.symm⟩
  exact c.hwY (h.mem_Y_of_pow (h.mem_P₁_of_inv hwP c.hwJ) c.hw.2.1)

theorem caseC_inv_mem {s : G} (hs : s ∈ S) (hsJ : J * s * J⁻¹ = s⁻¹) :
    s ∈ S ⊓ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr (IsT.comm_of_inv
    (h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP) h.y₀_pow h.r_odd h.J_y₀ c.hw c.hwJ hs hsJ)⟩

theorem caseC_inf_P₀ : (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ P₀ = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨ha1, haP₀⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨-, haw⟩ := Subgroup.mem_inf.mp ha1
  rw [Subgroup.mem_bot]
  by_contra ha1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.P₀_r) ⟨a, haP₀⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact ha1 hk
  have hdvd : r ∣ orderOf a := by rw [hk]; exact dvd_pow_self r hk0
  have ho := orderOf_pow_orderOf_div (orderOf_pos a).ne' hdvd
  have hz := zpowers_eq_of_cyclic h.P₀_cyc (P₀.pow_mem haP₀ _) h.x₀_mem (by rw [ho, h.orderOf_x₀])
  have hx : x₀ ∈ Subgroup.zpowers (a ^ (orderOf a / r)) := hz ▸ Subgroup.mem_zpowers x₀
  have hxC : x₀ ∈ Subgroup.centralizer ({w} : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ haw _)) hx
  exact h.caseC_x₀ c (Subgroup.mem_centralizer_singleton_iff.mp hxC)

theorem caseC_P₀ : P₀ = Subgroup.zpowers x₀ := by
  refine le_antisymm (fun a ha => ?_) (Subgroup.zpowers_le.mpr h.x₀_mem)
  have hyC := h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP
  have haS : a ∈ S := c.hPS (Subgroup.mem_sup_left ha)
  have h1 := c.hw.conj_pow hyC haS r
  rw [IsT.pow_eq_one_of_mem_zpowers h.y₀_pow (c.hw.2.2 a haS)] at h1
  have har : a ^ r ∈ (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ P₀ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨S.pow_mem haS r,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, P₀.pow_mem ha r⟩
    calc a ^ r * w = a ^ r * w * (a ^ r)⁻¹ * w⁻¹ * w * a ^ r := by group
      _ = w * a ^ r := by rw [h1, one_mul]
  rw [h.caseC_inf_P₀ c, Subgroup.mem_bot] at har
  exact h.mem_X_of_pow ha har

theorem caseC_normal :
    S ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) := by
  have hyC := h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP
  intro s hs
  apply JT.mem_normalizer_of_conj_mem
  intro q hq
  obtain ⟨hqS, hqw⟩ := Subgroup.mem_inf.mp hq
  refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs hqS) (S.inv_mem hs), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hqw ⊢
  have hc := c.hw.2.2 _ (S.inv_mem hs)
  rw [inv_inv] at hc
  have e : s⁻¹ * w * s = (s⁻¹ * w * s * w⁻¹) * w := by group
  have hq1 : q * (s⁻¹ * w * s) = (s⁻¹ * w * s) * q := by
    rw [e, ← mul_assoc, ← IsT.comm_of_mem_zpowers hyC hc hqS, mul_assoc, hqw, ← mul_assoc]
  calc s * q * s⁻¹ * w = s * (q * (s⁻¹ * w * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * w * s) * q) * s⁻¹ := by rw [hq1]
    _ = w * (s * q * s⁻¹) := by group

theorem caseC_J_inv :
    ∀ q ∈ S ⊓ Subgroup.centralizer ({w} : Set G), J * q * J⁻¹ = q⁻¹ := by
  apply inv_of_fixedPointFree h.J_mul_J
  · apply JT.mem_normalizer_of_conj_mem
    intro q hq
    obtain ⟨hqS, hqw⟩ := Subgroup.mem_inf.mp hq
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp c.hJS q).mp hqS, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hqw ⊢
    have hw' : J⁻¹ * w * J = w⁻¹ := by
      have := c.hwJ
      rw [h.J_inv] at this ⊢
      exact this
    have hqw' : q * w⁻¹ = w⁻¹ * q := by
      calc q * w⁻¹ = w⁻¹ * (w * q) * w⁻¹ := by group
        _ = w⁻¹ * (q * w) * w⁻¹ := by rw [hqw]
        _ = w⁻¹ * q := by group
    calc J * q * J⁻¹ * w = J * (q * (J⁻¹ * w * J)) * J⁻¹ := by group
      _ = J * (q * w⁻¹) * J⁻¹ := by rw [hw']
      _ = J * (w⁻¹ * q) * J⁻¹ := by rw [hqw']
      _ = (J * w⁻¹ * J⁻¹) * (J * q * J⁻¹) := by group
      _ = w * (J * q * J⁻¹) := by
          rw [show J * w⁻¹ * J⁻¹ = (J * w * J⁻¹)⁻¹ by group, c.hwJ, inv_inv]
  · rintro q hq hqJ
    have hqP₀ : q ∈ P₀ := by
      rw [← h.inf_centralizer_J c.hS c.hPS]
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hq).1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc q * J = J * q * J⁻¹ * J := by rw [hqJ]
        _ = J * q := by group
    have : q ∈ (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ P₀ := Subgroup.mem_inf.mpr ⟨hq, hqP₀⟩
    rw [h.caseC_inf_P₀ c, Subgroup.mem_bot] at this
    exact this

theorem caseC_P₁_le : P₁ ≤ S ⊓ Subgroup.centralizer ({w} : Set G) := fun b hb =>
  h.caseC_inv_mem c (c.hPS (Subgroup.mem_sup_right hb)) (h.P₁_inv b hb)

theorem caseC_inf_centralizer {q : G} (hq : q ∈ S ⊓ Subgroup.centralizer ({w} : Set G))
    (hqx : q * x₀ = x₀ * q) : q ∈ P₁ := by
  have hqP : q ∈ P₀ ⊔ P₁ := by
    rw [← h.inf_centralizer_eq c.hS c.hPS]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hq).1,
      Subgroup.mem_centralizer_singleton_iff.mpr hqx⟩
  exact h.mem_P₁_of_inv hqP (h.caseC_J_inv c q hq)

omit h [Finite G] [Fact (Nat.Prime r)] in
theorem caseC_w_mem : w ∈ S ⊓ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_inf.mpr ⟨c.hw.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem caseC_sup : S ≤ (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊔ Subgroup.zpowers x₀ := by
  have hyC := h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  set c₀ := x₀ * w * x₀⁻¹ * w⁻¹ with hc₀
  have hc₀Y : c₀ ∈ Subgroup.zpowers y₀ := c.hw.2.2 x₀ hx₀S
  have hc₀1 : c₀ ≠ 1 := by
    intro h1
    apply h.caseC_x₀ c
    calc x₀ * w = c₀ * w * x₀ := by rw [hc₀]; group
      _ = w * x₀ := by rw [h1, one_mul]
  have hc₀r : c₀ ^ r = 1 := IsT.pow_eq_one_of_mem_zpowers h.y₀_pow hc₀Y
  have hc₀o : orderOf c₀ = r := orderOf_eq_prime hc₀r hc₀1
  have hz := zpowers_eq_of_cyclic h.P₁_cyc ((Subgroup.zpowers_le.mpr h.y₀_mem) hc₀Y) h.y₀_mem
    (by rw [hc₀o, h.orderOf_y₀])
  intro s hs
  have hcs : s * w * s⁻¹ * w⁻¹ ∈ Subgroup.zpowers c₀ := hz ▸ c.hw.2.2 s hs
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite c₀).mem_powers_iff_mem_zpowers.mpr hcs
  have h1 : x₀ ^ j * w * (x₀ ^ j)⁻¹ * w⁻¹ = s * w * s⁻¹ * w⁻¹ := by
    rw [c.hw.conj_pow hyC hx₀S j]
    exact hj
  have hxjS : (x₀ ^ j)⁻¹ ∈ S := S.inv_mem (S.pow_mem hx₀S j)
  have h2 := IsT.conj_mul hyC c.hw (S.pow_mem hx₀S j) hxjS
  have h2' : (x₀ ^ j * w * (x₀ ^ j)⁻¹ * w⁻¹) * ((x₀ ^ j)⁻¹ * w * ((x₀ ^ j)⁻¹)⁻¹ * w⁻¹) = 1 := by
    rw [← h2]
    group
  have hc2 := eq_inv_of_mul_eq_one_right h2'
  have h3 := IsT.conj_mul hyC c.hw hxjS hs
  rw [hc2, h1, inv_mul_cancel] at h3
  have ht : (x₀ ^ j)⁻¹ * s ∈ S ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem hxjS hs, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (x₀ ^ j)⁻¹ * s * w
        = ((x₀ ^ j)⁻¹ * s) * w * ((x₀ ^ j)⁻¹ * s)⁻¹ * w⁻¹ * w * ((x₀ ^ j)⁻¹ * s) := by group
      _ = w * ((x₀ ^ j)⁻¹ * s) := by rw [h3, one_mul]
  have e : s = x₀ ^ j * ((x₀ ^ j)⁻¹ * s) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₀) j))
    (Subgroup.mem_sup_left ht)

theorem caseC_card : Nat.card S = Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) * r := by
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hXS : Subgroup.zpowers x₀ ≤ S := Subgroup.zpowers_le.mpr hx₀S
  have hXN := hXS.trans (h.caseC_normal c)
  have hinf : (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ Subgroup.zpowers x₀ = ⊥ := by
    have := h.caseC_inf_P₀ c
    rw [h.caseC_P₀ c] at this
    exact this
  have heq : S = (S ⊓ Subgroup.centralizer ({w} : Set G)) ⊔ Subgroup.zpowers x₀ :=
    le_antisymm (h.caseC_sup c) (sup_le inf_le_left hXS)
  calc Nat.card S
      = Nat.card ↥((S ⊓ Subgroup.centralizer ({w} : Set G)) ⊔ Subgroup.zpowers x₀) :=
        congrArg (fun H : Subgroup G => Nat.card H) heq
    _ = Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) * Nat.card (Subgroup.zpowers x₀) :=
        card_sup_of_inf_eq_bot hXN hinf
    _ = _ := by rw [Nat.card_zpowers, h.orderOf_x₀]

theorem false_of_caseC_cyclic (hScard : Nat.card S = r ^ (Nat.card G).factorization r)
    (hQc : IsCyclic ↥(S ⊓ Subgroup.centralizer ({w} : Set G))) : False := by
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  exact false_of_metacyclic h.perfect h.r_ne_two hScard inf_le_left (h.caseC_normal c) hQc hx₀S
    (h.caseC_sup c) (fun hab => h.caseC_x₀ c (hab x₀ hx₀S w c.hw.1))

theorem caseC_weaklyClosedIn (hlt : r * Nat.card P₁ < Nat.card ↥(S ⊓ Subgroup.centralizer
    ({w} : Set G))) : WeaklyClosedIn S (S ⊓ Subgroup.centralizer ({w} : Set G)) := by
  set Q := S ⊓ Subgroup.centralizer ({w} : Set G) with hQ
  refine ⟨inf_le_left, fun g hg => ?_⟩
  have hAc : Nat.card (rightConjugate Q g) = Nat.card Q := card_cj g⁻¹ Q
  by_contra hne
  have hnle : ¬ rightConjugate Q g ≤ Q := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle hAc.ge)
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hnle
  have hQab := comm_of_inv (h.caseC_J_inv c)
  have hAab : ∀ x ∈ rightConjugate Q g, ∀ y ∈ rightConjugate Q g, x * y = y * x :=
    comm_cj (g := g⁻¹) hQab
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hXN : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.mpr hx₀S).trans (h.caseC_normal c)
  obtain ⟨q₀, hq₀, x, hx, rfl⟩ := (mem_sup_iff_of_le_normalizer hXN).mp (h.caseC_sup c (hg haA))
  have hx1 : x ≠ 1 := fun h1 => haQ (by rw [h1, mul_one]; exact hq₀)
  have hxP₀ : x ∈ P₀ := (Subgroup.zpowers_le.mpr h.x₀_mem) hx
  have hAQ : Q ⊓ rightConjugate Q g ≤ P₁ := by
    intro y hy
    obtain ⟨hyQ, hyA⟩ := Subgroup.mem_inf.mp hy
    have h1 : y * (q₀ * x) = (q₀ * x) * y := hAab y hyA _ haA
    have h2 : y * q₀ = q₀ * y := hQab y hyQ q₀ hq₀
    have hyx : y * x = x * y := by
      have : q₀ * (y * x) = q₀ * (x * y) := by
        calc q₀ * (y * x) = (y * q₀) * x := by rw [h2]; group
          _ = (q₀ * x) * y := by rw [mul_assoc, h1]
          _ = q₀ * (x * y) := by group
      exact mul_left_cancel this
    have hxr : x ^ r = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_x₀,
        pow_orderOf_eq_one, one_zpow]
    have hxo : orderOf x = r := orderOf_eq_prime hxr hx1
    have hz := zpowers_eq_of_cyclic h.P₀_cyc hxP₀ h.x₀_mem (by rw [hxo, h.orderOf_x₀])
    have hx₀ : x₀ ∈ Subgroup.zpowers x := hz ▸ Subgroup.mem_zpowers x₀
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx₀
    have hyx₀ : y * x₀ = x₀ * y := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute y x from hyx) k)).eq
    exact h.caseC_inf_centralizer c hyQ hyx₀
  have hAN : rightConjugate Q g ≤ Subgroup.normalizer (Q : Set G) := hg.trans (h.caseC_normal c)
  have hcount := Sec52.card_sup_mul_card_inf hAN
  have hle1 : Nat.card ↥(rightConjugate Q g ⊔ Q) ≤ Nat.card S :=
    Subgroup.card_le_of_le (sup_le hg inf_le_left)
  have hle2 : Nat.card ↥(Q ⊓ rightConjugate Q g) ≤ Nat.card P₁ := Subgroup.card_le_of_le hAQ
  rw [hAc] at hcount
  have key : Nat.card Q * Nat.card Q ≤ Nat.card Q * (r * Nat.card P₁) := by
    calc Nat.card Q * Nat.card Q
        = Nat.card ↥(rightConjugate Q g ⊔ Q) * Nat.card ↥(Q ⊓ rightConjugate Q g) := hcount.symm
      _ ≤ Nat.card S * Nat.card P₁ := Nat.mul_le_mul hle1 hle2
      _ = Nat.card Q * (r * Nat.card P₁) := by rw [h.caseC_card c, mul_assoc]
  have := Nat.le_of_mul_le_mul_left key Nat.card_pos
  omega

theorem false_of_caseC_weak (hScard : Nat.card S = r ^ (Nat.card G).factorization r)
    (hweak : WeaklyClosedIn S (S ⊓ Subgroup.centralizer ({w} : Set G))) : False := by
  set Q := S ⊓ Subgroup.centralizer ({w} : Set G) with hQ
  set T : Sylow r G := Sylow.ofCard S hScard with hT
  have hTS : (T : Subgroup G) = S := Sylow.coe_ofCard _ _
  have hSN := h.caseC_normal c
  have hQ1 : Q ≠ ⊥ := by
    intro h1
    have := caseC_w_mem c
    rw [← hQ, h1, Subgroup.mem_bot] at this
    exact c.hwY (this ▸ Subgroup.one_mem _)
  refine h.false_of_inv T (c.hS.to_le inf_le_left) hQ1 (h.caseC_J_inv c)
    (by rw [hTS]; exact hweak) ((le_sup_left.trans c.hPS).trans hSN) ?_
  intro g hg hgo
  have hSc' := card_eq_of_le_of_card_eq hSN hScard
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hg)
  have hgr : IsPGroup r (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  obtain ⟨c', hc'N, hle⟩ := exists_le_cj_of_sylowIn hSN hSc' hgN hgr
  have hg' : c'⁻¹ * g * c' ∈ S := mem_cj.mp (hle (Subgroup.mem_zpowers g))
  have hwQ := caseC_w_mem c
  have hcw : c' * w * c'⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hc'N w).mp hwQ
  have hgw := Subgroup.mem_centralizer_iff.mp hg _ hcw
  have hg'Q : c'⁻¹ * g * c' ∈ Q := by
    refine Subgroup.mem_inf.mpr ⟨hg', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc c'⁻¹ * g * c' * w = c'⁻¹ * (g * (c' * w * c'⁻¹)) * c' := by group
      _ = c'⁻¹ * ((c' * w * c'⁻¹) * g) * c' := by rw [hgw]
      _ = w * (c'⁻¹ * g * c') := by group
  have := (Subgroup.mem_normalizer_iff.mp hc'N _).mp hg'Q
  simpa [mul_assoc] using this

theorem false_of_caseC_large (hScard : Nat.card S = r ^ (Nat.card G).factorization r)
    (hlt : r * Nat.card P₁ < Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G))) : False :=
  h.false_of_caseC_weak c hScard (h.caseC_weaklyClosedIn c hlt)

end CaseC

end Hyp62

end CFSG.Walter.W67.Sec6
