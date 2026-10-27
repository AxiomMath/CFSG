module

public import CFSG.RankThree.PartOne.D4RC.Lines

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section LinesSylow

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]}
  {E : Subgroup 𝒞[K, σ]}

theorem rcePerm_mul (Ln : RceLines F S c E) {n n' : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]))
    (hn' : n' ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) :
    rcePerm Ln (Subgroup.mul_mem _ hn hn') = rcePerm Ln hn * rcePerm Ln hn' :=
  Equiv.ext fun j => rceIdx_mul Ln hn hn' j

theorem rcePerm_eq_one (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]))
    (h : ∀ j, n * Ln.x j = Ln.x j * n) : rcePerm Ln hn = 1 :=
  Equiv.ext fun j => rceIdx_of_commute Ln hn (h j)

theorem rcePerm_inv (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) :
    rcePerm Ln (Subgroup.inv_mem _ hn) = (rcePerm Ln hn)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rcePerm_mul]
  exact rcePerm_eq_one Ln _ (fun j => by rw [inv_mul_cancel, one_mul, mul_one])

theorem rcePerm_pow (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (k : ℕ) :
    rcePerm Ln (Subgroup.pow_mem _ hn k) = rcePerm Ln hn ^ k :=
  Equiv.ext fun j => (rcePerm_pow_apply Ln hn k j).symm

theorem rce_E_split (Ln : RceLines F S c E) [Fact p.Prime] (k : Fin 4) :
    ∀ y ∈ E, ∃ a ∈ E ⊓ rclPx (Ln.sp k), ∃ b ∈ E ⊓ Subgroup.centralizer
      (rclPx (Ln.sp k) : Set 𝒞[K, σ]), y = a * b := by
  intro y hy
  have hxS : Ln.x k ∈ (S : Subgroup 𝒞[K, σ]) := Ln.hES (Ln.hx k).1
  obtain ⟨-, -, -, hAZ, -, hsplit⟩ := rcy_sylow_split F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS
  obtain ⟨-, -, -, -, κ, hκ, -⟩ := rcy_coord F Ln.hc
  obtain ⟨a, ha, b, hb, rfl⟩ := hsplit y (Ln.hES hy)
  have hab : Commute a b := Subgroup.mem_centralizer_iff.1 hb.2 a ha.2
  have h1 : a ^ p * b ^ p = 1 := by rw [← hab.mul_pow]; exact Ln.hEp _ hy
  have h2 : a ^ p = 1 := by
    have hmem : a ^ p ∈ (S : Subgroup 𝒞[K, σ]) ⊓ rclPx (Ln.sp k) ⊓
        Subgroup.centralizer (rclPx (Ln.sp k) : Set 𝒞[K, σ]) := by
      refine ⟨⟨Subgroup.pow_mem _ ha.1 p, Subgroup.pow_mem _ ha.2 p⟩, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb.2 p)
    rw [hAZ, Subgroup.mem_bot] at hmem
    exact hmem
  have h3 : b ^ p = 1 := by rw [h2, one_mul] at h1; exact h1
  exact ⟨a, ⟨rcy_mem_of_pow_eq_one F.hp κ hκ Ln.hES Ln.hEp Ln.hEc ha.1 h2, ha.2⟩, b,
    ⟨rcy_mem_of_pow_eq_one F.hp κ hκ Ln.hES Ln.hEp Ln.hEc hb.1 h3, hb.2⟩, rfl⟩

theorem rce_card_line (Ln : RceLines F S c E) [Fact p.Prime] (k : Fin 4) :
    Nat.card ↥(E ⊓ rclPx (Ln.sp k)) = p := by
  classical
  have hp : p.Prime := Fact.out
  have hxS : Ln.x k ∈ (S : Subgroup 𝒞[K, σ]) := Ln.hES (Ln.hx k).1
  obtain ⟨-, hA1, -, hAZ, hxZ, -⟩ := rcy_sylow_split F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS
  obtain ⟨-, -, -, -, κ, hκ, -⟩ := rcy_coord F Ln.hc
  have hdvd : Nat.card ↥(E ⊓ rclPx (Ln.sp k)) ∣ p ^ 2 :=
    Ln.hEc ▸ Subgroup.card_dvd_of_le inf_le_left
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [Ln.hEc]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨e, he, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases e
  · exfalso
    have hSP : IsPGroup p ↥((S : Subgroup 𝒞[K, σ]) ⊓ rclPx (Ln.sp k)) :=
      S.isPGroup'.to_inf_left
    obtain ⟨z, hz, hzo⟩ := rcn_exists_orderOf_eq hSP hA1
    have hzE : z ∈ E := rcy_mem_of_pow_eq_one hp κ hκ Ln.hES Ln.hEp Ln.hEc hz.1
      (by rw [← hzo]; exact pow_orderOf_eq_one z)
    have h1 : z ∈ E ⊓ rclPx (Ln.sp k) := ⟨hzE, hz.2⟩
    rw [pow_zero] at hcard
    rw [Subgroup.card_eq_one.1 hcard, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  · rw [hcard, pow_one]
  · exfalso
    have hEP : E ≤ rclPx (Ln.sp k) := by
      have h1 : E ⊓ rclPx (Ln.sp k) = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, Ln.hEc])
      intro y hy
      have : y ∈ E ⊓ rclPx (Ln.sp k) := by rw [h1]; exact hy
      exact this.2
    have h2 : Ln.x k ∈ (S : Subgroup 𝒞[K, σ]) ⊓ rclPx (Ln.sp k) ⊓
        Subgroup.centralizer (rclPx (Ln.sp k) : Set 𝒞[K, σ]) := ⟨⟨hxS, hEP (Ln.hx k).1⟩, hxZ.2⟩
    rw [hAZ, Subgroup.mem_bot] at h2
    exact (Ln.hx k).2 h2

theorem rce_comm_mem (Ln : RceLines F S c E) [Fact p.Prime] (k : Fin 4) {g : 𝒞[K, σ]}
    (hgP : g ∈ rclPx (Ln.sp k))
    (hgN : g ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) {y : 𝒞[K, σ]}
    (hy : y ∈ E) : g * y * g⁻¹ * y⁻¹ ∈ E ⊓ rclPx (Ln.sp k) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := rce_E_split Ln k y hy
  have hgb : g * b = b * g := Subgroup.mem_centralizer_iff.1 hb.2 g hgP
  have hga : g * a * g⁻¹ ∈ E ⊓ rclPx (Ln.sp k) :=
    ⟨rce_conj_mem Ln hgN ha.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgP ha.2)
      (Subgroup.inv_mem _ hgP)⟩
  have hgb' : g * b * g⁻¹ = b := by rw [hgb, mul_inv_cancel_right]
  have h1 : g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹) * a⁻¹ := by
    calc g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = (g * a * g⁻¹) * a⁻¹ := by rw [hgb']; group
  rw [h1]
  exact Subgroup.mul_mem _ hga (Subgroup.inv_mem _ ha)

theorem rce_exists_line_ne (Ln : RceLines F S c E) [Fact p.Prime] :
    ∃ j, E ⊓ rclPx (Ln.sp j) ≠ E ⊓ rclPx (Ln.sp 0) := by
  classical
  have hp : p.Prime := Fact.out
  by_contra hall
  push Not at hall
  set m := E ⊓ rclPx (Ln.sp 0) with hm
  obtain ⟨g₀, hg₀P, hg₀N, h0k, h0mv, h03⟩ := rce_exists_rotation Ln 0
  obtain ⟨g₁, hg₁P, hg₁N, h1k, h1mv, h13⟩ := rce_exists_rotation Ln 1
  let Q : 𝒞[K, σ] → Prop := fun h => ∀ y ∈ E, h * y * h⁻¹ * y⁻¹ ∈ m
  have hQ0 : Q g₀ := fun y hy => rce_comm_mem Ln 0 hg₀P hg₀N hy
  have hQ0' : Q g₀⁻¹ := fun y hy =>
    rce_comm_mem Ln 0 (Subgroup.inv_mem _ hg₀P) (Subgroup.inv_mem _ hg₀N) hy
  have hQ1 : Q g₁ := fun y hy => by
    rw [← hall 1]
    exact rce_comm_mem Ln 1 hg₁P hg₁N hy
  have hQ1' : Q g₁⁻¹ := fun y hy => by
    rw [← hall 1]
    exact rce_comm_mem Ln 1 (Subgroup.inv_mem _ hg₁P) (Subgroup.inv_mem _ hg₁N) hy
  have hnorm : ∀ h, Q h → ∀ a ∈ m, h * a * h⁻¹ ∈ m := fun h hQ a ha => by
    have h1 := hQ a ha.1
    have h2 : h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a := by group
    rw [h2]
    exact Subgroup.mul_mem _ h1 ha
  have hprod : ∀ h h', Q h → Q h' → Q (h * h') := fun h h' hQ hQ' y hy => by
    have h1 : h * h' * y * (h * h')⁻¹ * y⁻¹ =
        (h * (h' * y * h'⁻¹ * y⁻¹) * h⁻¹) * (h * y * h⁻¹ * y⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (hnorm h hQ _ (hQ' y hy)) (hQ y hy)
  set u := g₀ * g₁ * g₀⁻¹ * g₁⁻¹ with hu
  have hQu : Q u := by
    have : u = g₀ * (g₁ * (g₀⁻¹ * g₁⁻¹)) := by rw [hu]; group
    rw [this]
    exact hprod _ _ hQ0 (hprod _ _ hQ1 (hprod _ _ hQ0' hQ1'))
  have hmcard : Nat.card ↥m = p := rce_card_line Ln 0
  have hfinm : Finite ↥m := Nat.finite_of_card_ne_zero (by rw [hmcard]; exact hp.ne_zero)
  have hgen : ∀ b ∈ m, b ≠ 1 → Subgroup.zpowers b = m := fun b hb hb1 => by
    have hle : Subgroup.zpowers b ≤ m := Subgroup.zpowers_le.2 hb
    have hdvd : Nat.card (Subgroup.zpowers b) ∣ p := hmcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exfalso
      apply hb1
      have hbz : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hbz
      exact hbz
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmcard, h1])
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ m, a ≠ 1 := by
    have hne : m ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hmcard
      exact hp.one_lt.ne hmcard
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have hma : m = Subgroup.zpowers a := (hgen a ha ha1).symm
  obtain ⟨s₀, hs₀⟩ := Subgroup.mem_zpowers_iff.1 (hma ▸ hnorm g₀ hQ0 a ha)
  obtain ⟨s₁, hs₁⟩ := Subgroup.mem_zpowers_iff.1 (hma ▸ hnorm g₁ hQ1 a ha)
  have hX : (g₀ * g₁) * a * (g₀ * g₁)⁻¹ = a ^ (s₁ * s₀) := by
    calc (g₀ * g₁) * a * (g₀ * g₁)⁻¹ = g₀ * (g₁ * a * g₁⁻¹) * g₀⁻¹ := by group
      _ = g₀ * a ^ s₁ * g₀⁻¹ := by rw [hs₁]
      _ = (g₀ * a * g₀⁻¹) ^ s₁ := by rw [conj_zpow]
      _ = a ^ (s₁ * s₀) := by rw [← hs₀, ← zpow_mul, mul_comm]
  have hY : (g₁ * g₀) * a * (g₁ * g₀)⁻¹ = a ^ (s₁ * s₀) := by
    calc (g₁ * g₀) * a * (g₁ * g₀)⁻¹ = g₁ * (g₀ * a * g₀⁻¹) * g₁⁻¹ := by group
      _ = g₁ * a ^ s₀ * g₁⁻¹ := by rw [hs₀]
      _ = (g₁ * a * g₁⁻¹) ^ s₀ := by rw [conj_zpow]
      _ = a ^ (s₁ * s₀) := by rw [← hs₁, ← zpow_mul]
  set b := (g₁ * g₀) * a * (g₁ * g₀)⁻¹ with hb
  have hub : u * b * u⁻¹ = b := by
    calc u * b * u⁻¹ = (g₀ * g₁) * a * (g₀ * g₁)⁻¹ := by rw [hu, hb]; group
      _ = b := by rw [hX, hY]
  have hbm : b ∈ m := by
    rw [hY, hma]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hb1 : b ≠ 1 := fun h => ha1 (by
    have : a = (g₁ * g₀)⁻¹ * b * (g₁ * g₀) := by rw [hb]; group
    rw [this, h]
    group)
  have hum : ∀ z ∈ m, u * z * u⁻¹ = z := fun z hz => by
    rw [← hgen b hbm hb1] at hz
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← conj_zpow, hub]
  have hupow : ∀ y ∈ E, ∀ n : ℕ, u ^ n * y * (u ^ n)⁻¹ = (u * y * u⁻¹ * y⁻¹) ^ n * y := by
    intro y hy n
    obtain ⟨z, hzdef⟩ : ∃ z, u * y * u⁻¹ * y⁻¹ = z := ⟨_, rfl⟩
    rw [hzdef]
    have hz : z ∈ m := hzdef ▸ hQu y hy
    have huy : u * y * u⁻¹ = z * y := by rw [← hzdef]; group
    have huz : ∀ k : ℕ, u * z ^ k * u⁻¹ = z ^ k := fun k => hum _ (Subgroup.pow_mem _ hz k)
    induction n with
    | zero => simp only [pow_zero, one_mul, inv_one, mul_one]
    | succ n ih =>
      calc u ^ (n + 1) * y * (u ^ (n + 1))⁻¹ = u * (u ^ n * y * (u ^ n)⁻¹) * u⁻¹ := by
            rw [pow_succ']
            simp only [mul_inv_rev, mul_assoc]
        _ = u * (z ^ n * y) * u⁻¹ := by rw [ih]
        _ = (u * z ^ n * u⁻¹) * (u * y * u⁻¹) := by group
        _ = z ^ n * (z * y) := by rw [huz, huy]
        _ = z ^ (n + 1) * y := by rw [pow_succ, mul_assoc]
  have hup : ∀ j, u ^ p * Ln.x j = Ln.x j * u ^ p := fun j => by
    have h1 := hupow _ (Ln.hx j).1 p
    have hz : (u * Ln.x j * u⁻¹ * (Ln.x j)⁻¹) ^ p = 1 := Ln.hEp _ (hQu _ (Ln.hx j).1).1
    rw [hz, one_mul] at h1
    calc u ^ p * Ln.x j = u ^ p * Ln.x j * (u ^ p)⁻¹ * u ^ p := by group
      _ = Ln.x j * u ^ p := by rw [h1]
  have huN : u ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₀N hg₁N)
      (Subgroup.inv_mem _ hg₀N)) (Subgroup.inv_mem _ hg₁N)
  have hτu : rcePerm Ln huN = rcePerm Ln hg₀N * rcePerm Ln hg₁N * (rcePerm Ln hg₀N)⁻¹ *
      (rcePerm Ln hg₁N)⁻¹ := by
    rw [← rcePerm_inv Ln hg₀N, ← rcePerm_inv Ln hg₁N, ← rcePerm_mul, ← rcePerm_mul,
      ← rcePerm_mul]
  have hτp : rcePerm Ln huN ^ p = 1 := by
    rw [← rcePerm_pow Ln huN p]
    exact rcePerm_eq_one Ln _ hup
  obtain ⟨hc2, hc1⟩ := (show ∀ a b : Equiv.Perm (Fin 4), (a 0 = 0 ∧ b 1 = 1 ∧
      (∀ v, v ≠ 0 → a v ≠ v) ∧ (∀ v, v ≠ 1 → b v ≠ v) ∧ a ^ 3 = 1 ∧ b ^ 3 = 1) →
      (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 by decide +kernel)
    (rcePerm Ln hg₀N) (rcePerm Ln hg₁N) ⟨h0k, h1k, h0mv, h1mv, h03, h13⟩
  set cc := rcePerm Ln hg₀N * rcePerm Ln hg₁N * (rcePerm Ln hg₀N)⁻¹ * (rcePerm Ln hg₁N)⁻¹
    with hcc
  have hτp' : cc ^ p = 1 := by rw [← hτu]; exact hτp
  obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have := F.hp3
      omega
    · exact h
  have hcp : cc ^ p = cc := by
    calc cc ^ p = cc ^ (2 * t + 1) := by rw [ht]
      _ = (cc ^ 2) ^ t * cc := by rw [pow_succ, pow_mul]
      _ = cc := by rw [hc2, one_pow, one_mul]
  exact hc1 (hcp.symm.trans hτp')

theorem rce_card_sylow_inf (Ln : RceLines F S c E) [Fact p.Prime] (k : Fin 4) :
    Nat.card ↥((S : Subgroup 𝒞[K, σ]) ⊓ rclPx (Ln.sp k)) = ordProj[p] (d4T36d ε (ℓ ^ f)) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
  have hxS : Ln.x k ∈ (S : Subgroup 𝒞[K, σ]) := Ln.hES (Ln.hx k).1
  obtain ⟨-, -, hidx, -, -, -⟩ := rcy_sylow_split F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS
  have hTp : IsPGroup p ↥(S : Subgroup 𝒞[K, σ]) := S.isPGroup'
  have hrel := Subgroup.relIndex_mul_card (S : Subgroup 𝒞[K, σ]) (rclPx (Ln.sp k))
  rw [← Subgroup.inf_relIndex_right] at hrel
  obtain ⟨m, hm⟩ := (hTp.to_inf_left (K := rclPx (Ln.sp k))).exists_card_eq
  have hPp : ordProj[p] (Nat.card ↥(rclPx (Ln.sp k))) = ordProj[p] (d4T36d ε (ℓ ^ f)) := by
    rw [card_rclPx]
    exact rcy_ordProj_card F.hε hp F.hp3 hq2 F.hpd (rcl_card_rclQ F k)
  have hr0 : ((S : Subgroup 𝒞[K, σ]) ⊓ rclPx (Ln.sp k)).relIndex (rclPx (Ln.sp k)) ≠ 0 :=
    fun h0 => hidx (h0 ▸ dvd_zero p)
  rw [← hrel, hm, Nat.factorization_mul hr0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hidx, hp.factorization_pow, Finsupp.single_eq_same,
    zero_add] at hPp
  rw [hm, hPp]

theorem rce_sylow_le_sup (Ln : RceLines F S c E) [Fact p.Prime] :
    ∃ j, (S : Subgroup 𝒞[K, σ]) ≤ rclPx (Ln.sp 0) ⊔ rclPx (Ln.sp j) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨j, hj⟩ := rce_exists_line_ne Ln
  have hmemE : ∀ w ∈ (S : Subgroup 𝒞[K, σ]), w ^ p = 1 → w ∈ E := by
    obtain ⟨-, -, -, -, κ, hκ, -⟩ := rcy_coord F Ln.hc
    exact fun w hw hwp => rcy_mem_of_pow_eq_one hp κ hκ Ln.hES Ln.hEp Ln.hEc hw hwp
  set T : Subgroup 𝒞[K, σ] := (S : Subgroup 𝒞[K, σ]) with hT
  set A₀ := T ⊓ rclPx (Ln.sp 0) with hA₀
  set A₁ := T ⊓ rclPx (Ln.sp j) with hA₁
  have hc₀ := rce_card_sylow_inf Ln 0
  have hc₁ := rce_card_sylow_inf Ln j
  have hTc := rcy_card_sylow F S
  have hline : ∀ z, z ∈ E ⊓ rclPx (Ln.sp 0) → z ∈ E ⊓ rclPx (Ln.sp j) → z = 1 := by
    intro z h0 h1
    by_contra hz1
    have hgen : ∀ k, z ∈ E ⊓ rclPx (Ln.sp k) → Subgroup.zpowers z = E ⊓ rclPx (Ln.sp k) := by
      intro k hk
      have hle : Subgroup.zpowers z ≤ E ⊓ rclPx (Ln.sp k) := Subgroup.zpowers_le.2 hk
      have hcard := rce_card_line Ln k
      have : Finite ↥(E ⊓ rclPx (Ln.sp k)) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
      have hdvd : Nat.card (Subgroup.zpowers z) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hp).1 hdvd with h2 | h2
      · exfalso
        apply hz1
        have hzz : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
        rw [Subgroup.card_eq_one.1 h2, Subgroup.mem_bot] at hzz
        exact hzz
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h2])
    exact hj ((hgen j h1).symm.trans (hgen 0 h0))
  have hA01 : ∀ z, z ∈ A₀ → z ∈ A₁ → z = 1 := by
    intro z h0 h1
    by_contra hz1
    have hpz : IsPGroup p ↥(A₀ ⊓ A₁) := S.isPGroup'.to_inf_left.to_le inf_le_left
    have hne : A₀ ⊓ A₁ ≠ ⊥ := fun h => hz1 (by
      have : z ∈ A₀ ⊓ A₁ := ⟨h0, h1⟩
      rw [h, Subgroup.mem_bot] at this
      exact this)
    obtain ⟨w, hw, hwo⟩ := rcn_exists_orderOf_eq hpz hne
    have hwp : w ^ p = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
    have hwE : w ∈ E := hmemE w hw.1.1 hwp
    have hw1 := hline w ⟨hwE, hw.1.2⟩ ⟨hwE, hw.2.2⟩
    rw [hw1, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  let μ : ↥A₀ × ↥A₁ → ↥T := fun ab => ⟨ab.1 * ab.2, T.mul_mem ab.1.2.1 ab.2.2.1⟩
  have hμ : Function.Injective μ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : 𝒞[K, σ]) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : 𝒞[K, σ])⁻¹ * a = b' * (b : 𝒞[K, σ])⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_assoc, mul_inv_cancel, mul_one]
    have h3 : (a' : 𝒞[K, σ])⁻¹ * a = 1 := hA01 _ (A₀.mul_mem (A₀.inv_mem a'.2) a.2)
      (h2 ▸ A₁.mul_mem b'.2 (A₁.inv_mem b.2))
    rw [inv_mul_eq_one] at h3
    have h4 : (b : 𝒞[K, σ]) = b' := by
      rw [← h3] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
  have hcard : Nat.card ↥T ≤ Nat.card (↥A₀ × ↥A₁) := by
    rw [Nat.card_prod, hc₀, hc₁, hT, hTc]
  have hbij := hμ.bijective_of_nat_card_le hcard
  refine ⟨j, fun s hs => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨s, hs⟩
  have hs' : s = (a : 𝒞[K, σ]) * b := (congrArg Subtype.val hab).symm
  rw [hs']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2.2) (Subgroup.mem_sup_right b.2.2)

end LinesSylow

end CFSG.RankThree.PartOne.D4RC
