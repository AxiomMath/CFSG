module

public import CFSG.Quasithin.Recognition.RuTypeJ210a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem factorization_29120_seven : (29120 : ℕ).factorization 7 = 1 := by
  rw [show (29120 : ℕ) = 7 * 4160 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 4160 by norm_num),
    Nat.Prime.factorization_self (show Nat.Prime 7 by norm_num)]

theorem factorization_29120_thirteen : (29120 : ℕ).factorization 13 = 1 := by
  rw [show (29120 : ℕ) = 13 * 2240 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 13 ∣ 2240 by norm_num),
    Nat.Prime.factorization_self (show Nat.Prime 13 by norm_num)]

theorem conj_pow_eq {Y : Subgroup G} {w n : G} (hw : ∀ y ∈ Y, w * y = y * w)
    (hn : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (k : ℕ) {y : G} (hy : y ∈ Y) :
    (w * n) ^ k * y * ((w * n) ^ k)⁻¹ = n ^ k * y * (n ^ k)⁻¹ := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hny : n * y * n⁻¹ ∈ Y := hn y hy
    have h1 := ih hny
    rw [pow_succ, pow_succ]
    calc (w * n) ^ k * (w * n) * y * ((w * n) ^ k * (w * n))⁻¹ =
        (w * n) ^ k * (w * (n * y * n⁻¹) * w⁻¹) * ((w * n) ^ k)⁻¹ := by group
      _ = (w * n) ^ k * (n * y * n⁻¹) * ((w * n) ^ k)⁻¹ := by
        rw [hw _ hny, mul_inv_cancel_right]
      _ = n ^ k * (n * y * n⁻¹) * (n ^ k)⁻¹ := h1
      _ = n ^ k * n * y * (n ^ k * n)⁻¹ := by group

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem card_sylowLs
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    Nat.card (Y.subgroupOf (Ls s)) = p ^ (Nat.card (Ls s)).factorization p := by
  rw [card_subgroupOf_of_le hYL, hY, M.card_Ls hs hs1]
  rcases hp with rfl | rfl
  · rw [factorization_29120_seven, pow_one]
  · rw [factorization_29120_thirteen, pow_one]

theorem sylowLs_props
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    (∀ x ∈ Ls s, (∀ y ∈ Y, x * y = y * x) → x ∈ Y) ∧
    (∀ x ∈ Ls s, (∀ y ∈ Y, x * y * x⁻¹ ∈ Y) → ∀ y ∈ Y,
      x ^ ((p - 1) / 3) * y = y * x ^ ((p - 1) / 3)) ∧
    (∀ x ∈ Ls s, (∀ y ∈ Y, x * y * x⁻¹ ∈ Y) → ∀ k : ℕ, x ^ p ^ k = 1 → x ∈ Y) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  set X := Ls s
  let P : Sylow p X := Sylow.ofCard (Y.subgroupOf X) (M.card_sylowLs hs hs1 hp hYL hY)
  have hPc : (P : Subgroup X) = Y.subgroupOf X := rfl
  have hdata : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) = p * ((p - 1) / 3) ∧
      Subgroup.centralizer ((P : Subgroup X) : Set X) = P := by
    rcases hp with rfl | rfl
    · exact M.normalizer_Ls_seven hs hs1 P
    · exact M.normalizer_Ls_thirteen hs hs1 P
  obtain ⟨hN, hC⟩ := hdata
  have hmemP : ∀ x : X, x ∈ (P : Subgroup X) ↔ (x : G) ∈ Y := fun x => by
    rw [hPc, Subgroup.mem_subgroupOf]
  have hnorm : ∀ x : X, (∀ y ∈ Y, (x : G) * y * (x : G)⁻¹ ∈ Y) →
      x ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [hmemP] at hy ⊢
    exact hx _ hy
  set N := Subgroup.normalizer ((P : Subgroup X) : Set X)
  have hPN : ((P : Subgroup X).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hQcard : Nat.card (N ⧸ (P : Subgroup X).subgroupOf N) = (p - 1) / 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((P : Subgroup X).subgroupOf N)
    rw [hN, card_subgroupOf_of_le Subgroup.le_normalizer, P.card_eq_multiplicity,
      ← (M.card_sylowLs hs hs1 hp hYL hY), card_subgroupOf_of_le hYL, hY] at h
    have hp0 : 0 < p := hpp.pos
    rw [mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right hp0 h).symm
  refine ⟨fun x hx hc => ?_, fun x hx hn y hy => ?_, fun x hx hn k hk => ?_⟩
  · have hxC : (⟨x, hx⟩ : X) ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hc _ ((hmemP y).mp hy)).symm
    rw [hC, hmemP] at hxC
    exact hxC
  · have hxN := hnorm ⟨x, hx⟩ hn
    have hq : (QuotientGroup.mk (⟨⟨x, hx⟩, hxN⟩ : N) : N ⧸ (P : Subgroup X).subgroupOf N) ^
        ((p - 1) / 3) = 1 := by
      rw [← hQcard]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    have hxC : ((⟨⟨x, hx⟩, hxN⟩ : N) ^ ((p - 1) / 3) : N).1 ∈
        Subgroup.centralizer ((P : Subgroup X) : Set X) := by
      rw [hC]
      exact hq
    have h := Subgroup.mem_centralizer_iff.mp hxC ⟨y, hYL hy⟩ ((hmemP _).mpr hy)
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at h'
    exact h'.symm
  · have hxN := hnorm ⟨x, hx⟩ hn
    have hq1 : (QuotientGroup.mk (⟨⟨x, hx⟩, hxN⟩ : N) : N ⧸ (P : Subgroup X).subgroupOf N) ^
        ((p - 1) / 3) = 1 := by
      rw [← hQcard]
      exact pow_card_eq_one'
    have hq2 : (QuotientGroup.mk (⟨⟨x, hx⟩, hxN⟩ : N) : N ⧸ (P : Subgroup X).subgroupOf N) ^
        (p ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨⟨x, hx⟩, hxN⟩ : N) ^ p ^ k = 1 := Subtype.ext (Subtype.ext (by simpa using hk))
      rw [this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime ((p - 1) / 3) (p ^ k) := by
      refine Nat.Coprime.pow_right _ ?_
      rcases hp with rfl | rfl <;> norm_num
    have hq := pow_gcd_eq_one.2 ⟨hq1, hq2⟩
    rw [hcop, pow_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    exact (hmemP _).mp hq

theorem not_dvd_card_GB
    {p : ℕ} (hp : p = 7 ∨ p = 13) : ¬ p ∣ Nat.card M.GB := by
  rw [M.card_GB]
  rcases hp with rfl | rfl <;> norm_num

theorem exists_conj_three
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    ∃ l ∈ Ls s, (∀ y ∈ Y, (l * M.bel * l⁻¹) * y * (l * M.bel * l⁻¹)⁻¹ ∈ Y) ∧
      ¬ ∀ y ∈ Y, (l * M.bel * l⁻¹) * y = y * (l * M.bel * l⁻¹) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  set X := Ls s
  obtain ⟨P0, hP0⟩ : ∃ P0 : Sylow p X, ∀ y ∈ (P0 : Subgroup X),
      M.conjLs hs hs1 y ∈ (P0 : Subgroup X) := by
    rcases hp with rfl | rfl
    · have hB7L : M.B7 ≤ Ls s := by
        rw [Subgroup.zpowers_le]
        exact M.cel_mem_Ls hs
      let P0 : Sylow 7 X := Sylow.ofCard (M.B7.subgroupOf X) (by
        rw [card_subgroupOf_of_le hB7L, M.card_B7, M.card_Ls hs hs1, factorization_29120_seven,
          pow_one])
      refine ⟨P0, fun y hy => ?_⟩
      have hy' : (y : G) ∈ M.B7 := Subgroup.mem_subgroupOf.mp hy
      show (M.conjLs hs hs1 y : X) ∈ M.B7.subgroupOf X
      rw [Subgroup.mem_subgroupOf, conjLs_apply]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
      rw [← hk]
      exact M.bel_conj_cel k
    · exact M.exists_bel_sylow_thirteen hs hs1
  let P : Sylow p X := Sylow.ofCard (Y.subgroupOf X) (M.card_sylowLs hs hs1 hp hYL hY)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X P0 P
  have hmemY : ∀ y : G, y ∈ Y ↔ ∃ y0 ∈ (P0 : Subgroup X), y = (c : G) * y0 * (c : G)⁻¹ := by
    intro y
    constructor
    · intro hy
      have hyP : (⟨y, hYL hy⟩ : X) ∈ (P : Subgroup X) := Subgroup.mem_subgroupOf.mpr hy
      rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP
      refine ⟨_, hyP, ?_⟩
      simp
      group
    · rintro ⟨y0, hy0, rfl⟩
      have h : c * y0 * c⁻¹ ∈ (P : Subgroup X) := by
        rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        exact ⟨y0, hy0, by simp [MulAut.conj_apply]⟩
      have := Subgroup.mem_subgroupOf.mp h
      simpa using this
  refine ⟨c, c.2, fun y hy => ?_, fun h => ?_⟩
  · obtain ⟨y0, hy0, rfl⟩ := (hmemY y).mp hy
    rw [hmemY]
    refine ⟨M.conjLs hs hs1 y0, hP0 y0 hy0, ?_⟩
    rw [conjLs_apply]
    group
  ·
    obtain ⟨y0, hy0o⟩ := exists_prime_orderOf_dvd_card' (G := (P0 : Subgroup X)) p (by
      rw [P0.card_eq_multiplicity, M.card_Ls hs hs1]
      rcases hp with rfl | rfl
      · rw [factorization_29120_seven, pow_one]
      · rw [factorization_29120_thirteen, pow_one])
    have hyY : (c : G) * ((y0 : X) : G) * (c : G)⁻¹ ∈ Y := (hmemY _).mpr ⟨y0, y0.2, rfl⟩
    have hcomm := h _ hyY
    have hbel : (M.bel : G) * ((y0 : X) : G) = ((y0 : X) : G) * M.bel := by
      calc (M.bel : G) * ((y0 : X) : G) = (c : G)⁻¹ * (((c : G) * M.bel * (c : G)⁻¹) *
          ((c : G) * ((y0 : X) : G) * (c : G)⁻¹)) * c := by group
        _ = (c : G)⁻¹ * (((c : G) * ((y0 : X) : G) * (c : G)⁻¹) *
          ((c : G) * M.bel * (c : G)⁻¹)) * c := by rw [hcomm]
        _ = ((y0 : X) : G) * M.bel := by group
    have hGB : ((y0 : X) : G) ∈ M.GB := M.mem_GB.mpr hbel
    apply M.not_dvd_card_GB hp
    have h1 := Subgroup.orderOf_dvd_natCard M.GB hGB
    rw [show orderOf ((y0 : X) : G) = p by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy0o]]
      at h1
    exact h1

theorem bel_conj_Cen
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hx : x ∈ Cen s) :
    (M.bel : G) * x * (M.bel : G)⁻¹ ∈ Cen s := by
  set s' := (M.bel : G)⁻¹ * s * M.bel with hs'
  have hs'S : s' ∈ M.S0 := by
    have h := M.bel_pow_conj_S0 2 hs
    have e : (M.bel : G)⁻¹ = (M.bel : G) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', M.bel_pow_three]
    rw [hs', e]
    have e2 : (M.bel : G) = ((M.bel : G) ^ 2)⁻¹ := by rw [← e, inv_inv]
    nth_rewrite 2 [e2]
    exact h
  have hs'1 : s' ≠ 1 := fun h => hs1 (by
    have : s = (M.bel : G) * s' * (M.bel : G)⁻¹ := by rw [hs']; group
    rw [this, h]; group)
  rw [M.Cen_eq hs hs1 hs'S hs'1] at hx
  rw [mem_Cen] at hx ⊢
  calc (M.bel : G) * x * (M.bel : G)⁻¹ * s = (M.bel : G) * (x * s') * (M.bel : G)⁻¹ := by
        rw [hs']; group
    _ = (M.bel : G) * (s' * x) * (M.bel : G)⁻¹ := by rw [hx]
    _ = s * ((M.bel : G) * x * (M.bel : G)⁻¹) := by rw [hs']; group

theorem mem_Cen_of_centralizes
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) {x : G}
    (hxY : ∀ y ∈ Y, x * y = y * x) (hxS : ∀ a ∈ M.S0, x * a * x⁻¹ ∈ M.S0) : x ∈ Cen s := by
  obtain ⟨c, hc, k, rfl⟩ := M.mem_normalizer_S0 hs hs1 hxS
  obtain ⟨l', hl', hl'Y, hl'c⟩ := M.exists_conj_three hs hs1 hp hYL hY
  obtain ⟨-, hNm, -⟩ := M.sylowLs_props hs hs1 hp hYL hY
  have h3 := M.bel_pow_three
  have key : ∀ c' ∈ Cen s, ¬ ∀ y ∈ Y, (c' * M.bel) * y = y * (c' * M.bel) := by
    intro c' hc' hcY
    obtain ⟨a, ha, l, hl, rfl⟩ := M.exists_S0_mul_Ls hs hs1 hc'
    have hw : ∀ y ∈ Y, (l * M.bel) * y = y * (l * M.bel) := by
      intro y hy
      have h1 := hcY y hy
      have ha' : a * y = y * a := M.comm_S0_Ls hs hs1 ha (hYL hy)
      calc l * M.bel * y = a⁻¹ * (a * l * M.bel * y) := by group
        _ = a⁻¹ * (y * (a * l * M.bel)) := by rw [h1]
        _ = a⁻¹ * (y * a) * (l * M.bel) := by group
        _ = a⁻¹ * (a * y) * (l * M.bel) := by rw [ha']
        _ = y * (l * M.bel) := by group
    set g := l' * M.bel * l'⁻¹ with hg
    set n := (l * M.bel)⁻¹ * g with hn
    have hnLs : n ∈ Ls s := by
      have h1 : (M.bel : G)⁻¹ * (l⁻¹ * l') * M.bel ∈ Ls s := by
        have := (M.lemma_J29 hs hs1).2.1.2.1 _ (inv_mem (Subgroup.mem_zpowers _)) _
          (mul_mem (inv_mem hl) hl')
        simpa using this
      have e : n = ((M.bel : G)⁻¹ * (l⁻¹ * l') * M.bel) * l'⁻¹ := by rw [hn, hg]; group
      rw [e]
      exact mul_mem h1 (inv_mem hl')
    have hnY : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
      intro y hy
      have h1 := hl'Y y hy
      have h2 := hw _ h1
      have e : n * y * n⁻¹ = g * y * g⁻¹ := by
        rw [hn]
        calc (l * M.bel)⁻¹ * g * y * ((l * M.bel)⁻¹ * g)⁻¹ =
            (l * M.bel)⁻¹ * ((g * y * g⁻¹) * (l * M.bel)) := by group
          _ = (l * M.bel)⁻¹ * ((l * M.bel) * (g * y * g⁻¹)) := by rw [h2]
          _ = g * y * g⁻¹ := by group
      rw [e]
      exact h1
    have hgwn : g = (l * M.bel) * n := by rw [hn]; group
    have hgm : ∀ y ∈ Y, g ^ ((p - 1) / 3) * y * (g ^ ((p - 1) / 3))⁻¹ = y := by
      intro y hy
      rw [hgwn, conj_pow_eq hw hnY _ hy, hNm n hnLs hnY y hy, mul_inv_cancel_right]
    have hg3 : ∀ y ∈ Y, g ^ 3 * y * (g ^ 3)⁻¹ = y := by
      intro y hy
      have : g ^ 3 = 1 := by
        rw [hg, conj_pow, h3]
        group
      rw [this]
      group
    apply hl'c
    intro y hy
    have hm : (p - 1) / 3 = 2 ∨ (p - 1) / 3 = 4 := by
      rcases hp with rfl | rfl
      · left; rfl
      · right; rfl
    have hg1 : g * y * g⁻¹ = y := by
      rcases hm with hm | hm
      · rw [hm] at hgm
        have e : g = g ^ 3 * (g ^ 2)⁻¹ := by group
        rw [e, show (g ^ 3 * (g ^ 2)⁻¹) * y * (g ^ 3 * (g ^ 2)⁻¹)⁻¹ =
          g ^ 3 * ((g ^ 2)⁻¹ * y * g ^ 2) * (g ^ 3)⁻¹ by group]
        have hy2 : (g ^ 2)⁻¹ * y * g ^ 2 = y := by
          have := hgm y hy
          calc (g ^ 2)⁻¹ * y * g ^ 2 = (g ^ 2)⁻¹ * (g ^ 2 * y * (g ^ 2)⁻¹) * g ^ 2 := by
                rw [this]
            _ = y := by group
        rw [hy2, hg3 y hy]
      · rw [hm] at hgm
        have e : g = g ^ 4 * (g ^ 3)⁻¹ := by group
        rw [e, show (g ^ 4 * (g ^ 3)⁻¹) * y * (g ^ 4 * (g ^ 3)⁻¹)⁻¹ =
          g ^ 4 * ((g ^ 3)⁻¹ * y * g ^ 3) * (g ^ 4)⁻¹ by group]
        have hy3 : (g ^ 3)⁻¹ * y * g ^ 3 = y := by
          have := hg3 y hy
          calc (g ^ 3)⁻¹ * y * g ^ 3 = (g ^ 3)⁻¹ * (g ^ 3 * y * (g ^ 3)⁻¹) * g ^ 3 := by
                rw [this]
            _ = y := by group
        rw [hy3, hgm y hy]
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [hg1]
  have hk : (M.bel : G) ^ k = (M.bel : G) ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk] at hxY ⊢
  rcases hcases with h0 | h1 | h2
  · rw [h0, pow_zero, mul_one]
    exact hc
  · exfalso
    rw [h1, pow_one] at hxY
    exact key c hc hxY
  · exfalso
    rw [h2] at hxY
    have hc2 : c * ((M.bel : G) ^ 2 * c * ((M.bel : G) ^ 2)⁻¹) ∈ Cen s := by
      refine mul_mem hc ?_
      have h1 := M.bel_conj_Cen hs hs1 (M.bel_conj_Cen hs hs1 hc)
      simpa [pow_two, mul_assoc] using h1
    apply key _ hc2
    intro y hy
    have e : c * ((M.bel : G) ^ 2 * c * ((M.bel : G) ^ 2)⁻¹) * M.bel =
        (c * (M.bel : G) ^ 2) * (c * (M.bel : G) ^ 2) := by
      have hb4 : (M.bel : G) ^ 2 * (M.bel : G) ^ 2 = M.bel := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, h3, one_mul, pow_one]
      calc c * ((M.bel : G) ^ 2 * c * ((M.bel : G) ^ 2)⁻¹) * M.bel =
          c * ((M.bel : G) ^ 2 * c * ((M.bel : G) ^ 2)⁻¹) *
            ((M.bel : G) ^ 2 * (M.bel : G) ^ 2) := by rw [hb4]
        _ = (c * (M.bel : G) ^ 2) * (c * (M.bel : G) ^ 2) := by group
    rw [e, mul_assoc, hxY y hy, ← mul_assoc, hxY y hy, mul_assoc]

theorem exists_S0_mul_Y
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) {x : G} (hx : x ∈ Cen s)
    (hxY : ∀ y ∈ Y, x * y = y * x) : ∃ a ∈ M.S0, ∃ y ∈ Y, x = a * y := by
  obtain ⟨a, ha, l, hl, rfl⟩ := M.exists_S0_mul_Ls hs hs1 hx
  obtain ⟨hC, -, -⟩ := M.sylowLs_props hs hs1 hp hYL hY
  refine ⟨a, ha, l, hC l hl fun y hy => ?_, rfl⟩
  have h1 := hxY y hy
  have ha' : a * y = y * a := M.comm_S0_Ls hs hs1 ha (hYL hy)
  calc l * y = a⁻¹ * (a * l * y) := by group
    _ = a⁻¹ * (y * (a * l)) := by rw [h1]
    _ = a⁻¹ * (y * a) * l := by group
    _ = a⁻¹ * (a * y) * l := by rw [ha']
    _ = y * l := by group

end RuDataM

end CFSG.Quasithin.RuType
