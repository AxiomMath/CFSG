module

public import CFSG.Walter.W67.Section5.P56AbTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_2

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

@[expose] noncomputable def delta {a : G} (ha : a ∈ d.NV) : d.V →* d.V where
  toFun m := m⁻¹ * d.φ ⟨a, ha⟩ m
  map_one' := by simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    have c1 : ((y : G))⁻¹ * ((x : G))⁻¹ = ((x : G))⁻¹ * ((y : G))⁻¹ :=
      d.V_comm (d.V.inv_mem y.2) (d.V.inv_mem x.2)
    have c2 : ((y : G))⁻¹ * ((d.φ ⟨a, ha⟩ x : d.V) : G) =
        ((d.φ ⟨a, ha⟩ x : d.V) : G) * ((y : G))⁻¹ :=
      d.V_comm (d.V.inv_mem y.2) (d.φ ⟨a, ha⟩ x).2
    calc ((y : G))⁻¹ * ((x : G))⁻¹ * (((d.φ ⟨a, ha⟩ x : d.V) : G) *
          ((d.φ ⟨a, ha⟩ y : d.V) : G)) =
          ((x : G))⁻¹ * (((y : G))⁻¹ * ((d.φ ⟨a, ha⟩ x : d.V) : G)) *
            ((d.φ ⟨a, ha⟩ y : d.V) : G) := by rw [c1]; group
      _ = ((x : G))⁻¹ * (((d.φ ⟨a, ha⟩ x : d.V) : G) * ((y : G))⁻¹) *
            ((d.φ ⟨a, ha⟩ y : d.V) : G) := by rw [c2]
      _ = _ := by group

theorem delta_apply_coe {a : G} (ha : a ∈ d.NV) (m : d.V) :
    ((d.delta ha m : d.V) : G) = (m : G)⁻¹ * (a * m * a⁻¹) := rfl

theorem card_centralizer_le {a : G} (ha : a ∈ d.NV) {k : ℕ} (hak : a ^ (3 ^ k) = 1)
    {m : G} (hm : m ∈ d.V)
    (hq : a * (m⁻¹ * (a * m * a⁻¹)) * a⁻¹ ≠ m⁻¹ * (a * m * a⁻¹)) :
    Nat.card (d.V ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤ 3 ^ (2 * d.n - 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set δ := d.delta ha
  have hker :
      Nat.card δ.ker = Nat.card (d.V ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨((x : d.V) : G), ?_⟩) ⟨?_, ?_⟩)
    · refine Subgroup.mem_inf.mpr ⟨(x : d.V).2, ?_⟩
      have hx : δ x = 1 := x.2
      have hx' : ((x : d.V) : G)⁻¹ * (a * x * a⁻¹) = 1 := congrArg Subtype.val hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [inv_mul_eq_one] at hx'
      calc ((x : d.V) : G) * a = a * x * a⁻¹ * a := by rw [← hx']
        _ = a * x := by group
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨z, hz⟩
      obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
      refine ⟨⟨⟨z, hzV⟩, ?_⟩, rfl⟩
      apply Subtype.ext
      rw [delta_apply_coe]
      have : a * z * a⁻¹ = z := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hzC, mul_inv_cancel_right]
      rw [this, inv_mul_cancel]
      rfl
  have hcard := Subgroup.card_ker_mul_card_range δ
  rw [hker, d.card_V] at hcard
  set w : d.V := δ ⟨m, hm⟩ with hw
  have hδw : δ w ≠ 1 := by
    intro h
    apply hq
    have h' : ((w : G))⁻¹ * (a * w * a⁻¹) = 1 := congrArg Subtype.val h
    rw [inv_mul_eq_one] at h'
    have hwc : (w : G) = m⁻¹ * (a * m * a⁻¹) := rfl
    rw [← hwc]
    exact h'.symm
  have hw1 : w ≠ 1 := by
    intro h
    apply hδw
    rw [h, map_one]
  have hrange : 9 ≤ Nat.card δ.range := by
    have hp : IsPGroup 3 δ.range :=
      IsPGroup.of_surjective d.V_isPGroup δ.rangeRestrict δ.rangeRestrict_surjective
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp
    by_contra hlt
    push Not at hlt
    have hj1 : j ≤ 1 := by
      by_contra h2
      push Not at h2
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h2
      omega
    have hwr : w ∈ δ.range := ⟨_, rfl⟩
    have hw3 : w ^ 3 = 1 := Subtype.ext (by simpa using d.V_pow w.2)
    have how : orderOf w = 3 := by
      have := orderOf_dvd_of_pow_eq_one hw3
      have h1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
      rcases (Nat.dvd_prime Nat.prime_three).mp this with h | h
      · exact absurd h h1
      · exact h
    have hzw : Subgroup.zpowers w = δ.range := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwr)
      rw [hj, Nat.card_zpowers, how]
      calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
        _ = 3 := by norm_num
    set α := d.φ ⟨a, ha⟩ with hα
    have hαw : α w = w * δ w := by
      apply Subtype.ext
      show a * ((m : G)⁻¹ * (a * m * a⁻¹)) * a⁻¹ =
        ((m : G)⁻¹ * (a * m * a⁻¹)) * (((m : G)⁻¹ * (a * m * a⁻¹))⁻¹ *
          (a * ((m : G)⁻¹ * (a * m * a⁻¹)) * a⁻¹))
      group
    have hαwr : α w ∈ Subgroup.zpowers w := by
      rw [hzw]
      have hαm : α w = δ (α ⟨m, hm⟩) := by
        apply Subtype.ext
        show a * ((m : G)⁻¹ * (a * m * a⁻¹)) * a⁻¹ =
          (a * m * a⁻¹)⁻¹ * (a * (a * m * a⁻¹) * a⁻¹)
        group
      rw [hαm]
      exact ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := hαwr
    replace hi : w ^ i = α w := hi
    have hinv : α w = w⁻¹ := by
      rw [← hi, ← zpow_mod_orderOf, how]
      have hcases : (i % ((3 : ℕ) : ℤ)) = 0 ∨ (i % ((3 : ℕ) : ℤ)) = 1 ∨
          (i % ((3 : ℕ) : ℤ)) = 2 := by omega
      rcases hcases with h | h | h <;> rw [h]
      · exfalso
        have : α w = 1 := by rw [← hi, ← zpow_mod_orderOf, how, h, zpow_zero]
        rw [map_eq_one_iff _ α.injective] at this
        exact hw1 this
      · exfalso
        have : α w = w := by rw [← hi, ← zpow_mod_orderOf, how, h, zpow_one]
        rw [hαw, mul_eq_left] at this
        exact hδw this
      · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]
        exact hw3
    have h2 : (α * α) w = w := by rw [MulAut.mul_apply, hinv, map_inv, hinv, inv_inv]
    have hodd : ∀ j : ℕ, (α ^ (2 * j + 1)) w = w⁻¹ := by
      intro j
      induction j with
      | zero => simpa using hinv
      | succ j ih =>
        rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add, MulAut.mul_apply, ih,
          map_inv, sq, h2]
    obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have h1 : (α ^ (3 ^ k)) w = w := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : d.NV) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hak)
      rw [this, map_one, MulAut.one_apply]
    rw [ht, hodd t] at h1
    apply hw1
    have : w * w = 1 := by
      nth_rw 1 [← h1]
      exact inv_mul_cancel w
    calc w = w ^ 3 * (w * w)⁻¹ := by group
      _ = 1 := by rw [hw3, this, inv_one, one_mul]
  have h9 : Nat.card (d.V ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * 9 ≤ 3 ^ (2 * d.n) :=
    hcard ▸ Nat.mul_le_mul_left _ hrange
  have h2n : 3 ^ (2 * d.n) = 3 ^ (2 * d.n - 2) * 9 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
    congr 1
    have := d.three_le_n
    omega
  rw [h2n] at h9
  exact Nat.le_of_mul_le_mul_right h9 (by norm_num)

theorem factorization_three_CV : (Nat.card d.CV).factorization 3 = 2 * d.n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 d.CV))
    have hT := d.sylow_centralizer ((T : Subgroup d.CV).map d.CV.subtype) (T.isPGroup'.map _)
      (Subgroup.map_subtype_le _)
    rw [Subgroup.card_map_of_injective d.CV.subtype_injective, Sylow.card_eq_multiplicity] at hT
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hT
  · have hdvd : 3 ^ (2 * d.n) ∣ Nat.card d.CV := d.card_V ▸ Subgroup.card_dvd_of_le d.V_le_CV
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd

theorem inf_CV_eq {X : Subgroup G} (hX : IsPGroup 3 X) (hVX : d.V ≤ X) : X ⊓ d.CV = d.V := by
  have h := d.sylow_centralizer (X ⊓ d.CV) (hX.to_le inf_le_left) inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hVX d.V_le_CV) (by rw [d.card_V]; exact h)).symm

theorem card_eq_mul_bar {X : Subgroup G} (hXN : X ≤ d.NV) :
    Nat.card X = Nat.card (X ⊓ d.CV : Subgroup G) * Nat.card (d.bar X) := by
  set ψ : X →* MulAut d.V := d.φ.comp (Subgroup.inclusion hXN)
  have hker : Nat.card ψ.ker = Nat.card (X ⊓ d.CV : Subgroup G) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨((x : X) : G), ?_⟩) ⟨?_, ?_⟩)
    · have hx : ψ x = 1 := x.2
      exact Subgroup.mem_inf.mpr ⟨(x : X).2, (d.φ_eq_one_iff _).mp hx⟩
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨z, hz⟩
      obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.mp hz
      exact ⟨⟨⟨z, hzX⟩, (d.φ_eq_one_iff ⟨z, hXN hzX⟩).mpr hzC⟩, rfl⟩
  have hrange : ψ.range = d.bar X := by
    ext α
    rw [MonoidHom.mem_range, mem_bar]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXN x.2⟩, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range ψ, hker, hrange]

theorem exists_Q {Qbar : Subgroup (MulAut d.V)} (hQbar : Qbar ≤ d.Nbar)
    (hQcard : (Nat.card Qbar).factorization 3 = (Nat.card d.Nbar).factorization 3) :
    ∃ Q : Subgroup G, Q ≤ d.NV ∧ d.V ≤ Q ∧ IsPGroup 3 Q ∧
      (Nat.card Q).factorization 3 = (Nat.card d.NV).factorization 3 ∧ d.bar Q ≤ Qbar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Qpre : Subgroup G := (Qbar.comap d.φ).map d.NV.subtype with hQpre
  have hQpreN : Qpre ≤ d.NV := Subgroup.map_subtype_le _
  have hmem : ∀ x (hx : x ∈ d.NV), x ∈ Qpre ↔ d.φ ⟨x, hx⟩ ∈ Qbar := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hCQ : d.CV ≤ Qpre := fun x hx => (hmem x (d.CV_le_NV hx)).mpr (by
    rw [(d.φ_eq_one_iff ⟨x, d.CV_le_NV hx⟩).mpr hx]; exact Qbar.one_mem)
  have hVQ : d.V ≤ Qpre := d.V_le_CV.trans hCQ
  have hbar : d.bar Qpre = Qbar := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx⟩, hxQ, rfl⟩
      exact (hmem x hx).mp (Subgroup.mem_subgroupOf.mp hxQ)
    · intro α hα
      obtain ⟨x, hx⟩ := hQbar hα
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ((hmem x x.2).mpr (hx ▸ hα)), hx⟩
  have hcard : Nat.card Qpre = Nat.card d.CV * Nat.card Qbar := by
    rw [d.card_eq_mul_bar hQpreN, inf_eq_right.mpr hCQ, hbar]
  have hVp : IsPGroup 3 (d.V.subgroupOf Qpre) :=
    d.V_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hVQ).symm
  obtain ⟨T, hT⟩ := hVp.exists_le_sylow
  refine ⟨(T : Subgroup Qpre).map Qpre.subtype, (Subgroup.map_subtype_le _).trans hQpreN,
    fun x hx => ⟨⟨x, hVQ hx⟩, hT hx, rfl⟩, T.isPGroup'.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Qpre.subtype_injective, Sylow.card_eq_multiplicity,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, hcard,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hQcard,
      ← d.card_ker_mul_card_Nbar, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.CV_le_NV).toEquiv]
  · rintro _ ⟨⟨x, hxN⟩, hxQ, rfl⟩
    obtain ⟨y, -, hy⟩ := hxQ
    have hy' : (y : G) = x := hy
    have hxQpre : x ∈ Qpre := hy' ▸ y.2
    exact (hmem x hxN).mp hxQpre

section weak

variable {Qbar Q : Subgroup (MulAut d.V)}

theorem weaklyClosed
    {Qbar : Subgroup (MulAut d.V)}
    (hQcomm : ∀ a ∈ Qbar, ∀ b ∈ Qbar, a * b = b * a)
    (hQsmall : ∀ E : Subgroup (MulAut d.V), E ≤ Qbar → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 ^ 2)
    (hPQ : d.bar d.P₀ ≤ Qbar) {Q : Subgroup G} (hQN : Q ≤ d.NV) (hVQ : d.V ≤ Q)
    (hQp : IsPGroup 3 Q) (hQbar : d.bar Q ≤ Qbar) {c : G}
    (hc : d.V.map (MulAut.conj c).toMonoidHom ≤ Q) :
    d.V.map (MulAut.conj c).toMonoidHom = d.V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := d.V.map (MulAut.conj c).toMonoidHom with hA
  have hAcard : Nat.card A = 3 ^ (2 * d.n) := by
    rw [hA, Subgroup.card_map_of_injective (MulAut.conj c).injective, d.card_V]
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, d.V_comm hx hy]
  have hApow : ∀ x ∈ A, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, d.V_pow hx, map_one]
  have hAN : A ≤ d.NV := hc.trans hQN
  have hQC := d.inf_CV_eq hQp hVQ
  have hACV : A ⊓ d.CV ≤ d.V := by
    rw [← hQC]
    exact inf_le_inf_right _ hc
  have hAbar : Nat.card (d.bar A) ≤ 3 ^ 2 := by
    refine hQsmall _ ((d.bar_mono hc).trans hQbar) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hApow _ hx)
    rw [this, map_one]
  have hcardA := d.card_eq_mul_bar hAN
  rw [hAcard] at hcardA
  by_contra hAV
  obtain ⟨a₀, ha₀A, ha₀V⟩ : ∃ a₀ ∈ A, a₀ ∉ d.V := by
    by_contra h
    push Not at h
    exact hAV (Subgroup.eq_of_le_of_card_ge h (by rw [hAcard, d.card_V]))
  have ha₀N := hAN ha₀A
  have ha₀C : a₀ ∉ d.CV := fun h => ha₀V (hACV (Subgroup.mem_inf.mpr ⟨ha₀A, h⟩))
  obtain ⟨m, hm, hq⟩ : ∃ m ∈ d.V,
      a₀ * (m⁻¹ * (a₀ * m * a₀⁻¹)) * a₀⁻¹ ≠ m⁻¹ * (a₀ * m * a₀⁻¹) := by
    by_contra h
    push Not at h
    exact ha₀C (d.mem_CV_of_quadratic ha₀N h)
  obtain ⟨k, hk⟩ := hQp ⟨a₀, hc ha₀A⟩
  have hk' : a₀ ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have hCa₀ := d.card_centralizer_le ha₀N hk' hm hq
  have hAC_le : A ⊓ d.CV ≤ d.V ⊓ Subgroup.centralizer ({a₀} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hACV hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm x (Subgroup.mem_inf.mp hx).1 a₀ ha₀A
  have h9 : 3 ^ 2 ≤ Nat.card (d.bar A) := by
    have h1 := Subgroup.card_le_of_le hAC_le
    have h2 : 3 ^ (2 * d.n) ≤ 3 ^ (2 * d.n - 2) * Nat.card (d.bar A) :=
      hcardA ▸ Nat.mul_le_mul_right _ (h1.trans hCa₀)
    have h3 : 3 ^ (2 * d.n) = 3 ^ (2 * d.n - 2) * 3 ^ 2 := by
      rw [← pow_add]
      congr 1
      have := d.three_le_n
      omega
    rw [h3] at h2
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  let Ω : Subgroup (MulAut d.V) :=
    { carrier := {x | x ∈ Qbar ∧ x ^ 3 = 1}
      one_mem' := ⟨Qbar.one_mem, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨Qbar.mul_mem ha hb, by
          rw [(Commute.mul_pow (hQcomm a ha b hb) 3), ha', hb', one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨Qbar.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hAΩ : d.bar A ≤ Ω := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hQbar (d.bar_mono hc ⟨x, hx, rfl⟩), ?_⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hApow _ hx)
    rw [this, map_one]
  have hΩ : d.bar A = Ω := Subgroup.eq_of_le_of_card_ge hAΩ
    ((hQsmall Ω (fun _ hx => hx.1) (fun _ hx => hx.2)).trans h9)
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' (G := d.P₀) 3 (by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp d.P₀_isPGroup
    rw [hj]
    rcases j with _ | j
    · exfalso
      rw [pow_zero] at hj
      exact d.P₀_ne_bot (Subgroup.eq_bot_of_card_eq _ hj)
    · exact dvd_pow_self 3 (Nat.succ_ne_zero j))
  have hyN := d.P₀_le_NV y.2
  have hy3 : (y : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hyo] at this
    exact congrArg Subtype.val this
  have hyΩ : d.φ ⟨y, hyN⟩ ∈ Ω := ⟨hPQ (d.φ_mem_bar y.2), by
    rw [← map_pow]
    have : (⟨(y : G), hyN⟩ : d.NV) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]⟩
  rw [← hΩ] at hyΩ
  obtain ⟨a, haA, hay⟩ := d.mem_bar.mp hyΩ
  have hAC_le' : A ⊓ d.CV ≤ d.V ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    intro x hx
    have hxV := hACV hx
    refine Subgroup.mem_inf.mpr ⟨hxV, ?_⟩
    have hxa : x * a = a * x := hAcomm x (Subgroup.mem_inf.mp hx).1 a haA
    have h1 := congrArg (fun α : MulAut d.V => ((α ⟨x, hxV⟩ : d.V) : G)) hay
    simp only [φ_apply_coe] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (a : G) * x * (a : G)⁻¹ = x := by rw [← hxa, mul_inv_cancel_right]
    rw [h2] at h1
    calc x * y = (y : G) * x * (y : G)⁻¹ * y := by rw [← h1]
      _ = y * x := by group
  have hfree := d.free y y.2 (by rw [← Subgroup.orderOf_coe] at hyo; exact hyo)
  rw [d.card_V] at hfree
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
    (d.V_isPGroup.to_le (inf_le_left : (d.V ⊓ Subgroup.centralizer ({(y : G)} : Set G)) ≤ d.V))
  rw [hj, ← pow_mul] at hfree
  have hj3 : j * 3 = 2 * d.n := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hfree
  have hlow : 3 ^ (2 * d.n - 2) ≤ Nat.card (A ⊓ d.CV : Subgroup G) := by
    have h3 : 3 ^ (2 * d.n) = 3 ^ (2 * d.n - 2) * 3 ^ 2 := by
      rw [← pow_add]
      congr 1
      have := d.three_le_n
      omega
    have : 3 ^ (2 * d.n - 2) * 3 ^ 2 ≤ Nat.card (A ⊓ d.CV : Subgroup G) * 3 ^ 2 := by
      rw [← h3, hcardA]
      exact Nat.mul_le_mul_left _ hAbar
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have hup := (Subgroup.card_le_of_le hAC_le').trans_eq hj
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlow.trans hup)
  have := d.three_le_n
  omega

end weak

theorem eq_of_le_of_weak {Q : Subgroup G} (hQN : Q ≤ d.NV) (hVQ : d.V ≤ Q) (hQp : IsPGroup 3 Q)
    (hQcard : (Nat.card Q).factorization 3 = (Nat.card d.NV).factorization 3)
    (hweak : ∀ c : G, d.V.map (MulAut.conj c).toMonoidHom ≤ Q →
      d.V.map (MulAut.conj c).toMonoidHom = d.V)
    {S : Subgroup G} (hS : IsPGroup 3 S) (hQS : Q ≤ S) : S = Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hlt : Q.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm _ hQS
    intro y hy
    have : (⟨y, hy⟩ : S) ∈ Q.subgroupOf S := by rw [h]; exact Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨⟨g, hgS⟩, hgN, hgQ⟩ := IsConcreteLE.exists_of_lt hnc
  have hgNQ : g ∈ Subgroup.normalizer (Q : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    exact (Subgroup.mem_normalizer_iff.mp hgN ⟨y, hQS hy⟩).mp hy
  have hVg : d.V.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgNQ y).mp (hVQ hy)
  have hgV : g ∈ d.NV := by
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    rw [← hweak g hVg]
    exact ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := hS ⟨g, hgS⟩
  have hgk : g ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  exact hgQ (mem_of_isPGroup_of_le_normalizer hQN hQp hQcard hgV hgNQ ⟨k, hgk⟩)

end P56AbData

theorem prop_5_6_abelian :
    ∀ (G : Type) [Group G] [Finite G], P56AbData G → False := by
  intro G _ _ d
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hvp, hvn⟩ := d.exists_zsigmondy
  have : Fact v.Prime := ⟨hvp⟩
  obtain ⟨Qbar, hQK, -, hQcard, -, hPQ, hQcomm, hQsmall⟩ := d.exists_Qbar hvn
  obtain ⟨Q, hQN, hVQ, hQp, hQcardN, hQbar⟩ := d.exists_Q (hQK.trans d.Kbar_le_Nbar) hQcard
  have hweak : ∀ c : G, d.V.map (MulAut.conj c).toMonoidHom ≤ Q →
      d.V.map (MulAut.conj c).toMonoidHom = d.V :=
    fun c hc => d.weaklyClosed hQcomm hQsmall hPQ hQN hVQ hQp hQbar hc
  let P : Sylow 3 G :=
    { toSubgroup := Q
      isPGroup' := hQp
      is_maximal' := fun hS hQS => d.eq_of_le_of_weak hQN hVQ hQp hQcardN hweak hS hQS }
  have hW : BenderSuzuki.External.WeaklyClosedIn (P : Subgroup G) d.V :=
    ⟨hVQ, fun g hg => hweak g⁻¹ hg⟩
  have hengel : ∀ u z : G, u ∈ d.V → z ∈ d.V →
      BenderSuzuki.External.engelSymbol (3 - 1) u z = 1 :=
    fun u z hu hz => Sec52.iterated_eq_one (d.V_comm hu hz) 0
  have hHW := BenderSuzuki.External.hallWielandt_residual_intersection 3 P d.V d.NV rfl hW
    (Or.inr (Or.inl hengel))
  have h1 := hHW.1
  rw [Sec52.hallPResidual_eq_top d.perfect, inf_top_eq] at h1
  have hres : BenderSuzuki.External.hallPResidual 3 d.NV = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : (x : G) ∈ (BenderSuzuki.External.hallPResidual 3 d.NV).map d.NV.subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  exact d.false_of_hallPResidual_eq_top hres

end CFSG.Walter.W67
