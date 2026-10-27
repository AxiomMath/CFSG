module

public import Mathlib
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.Coprime.ThompsonElementaryComplement

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def squares (U : Subgroup G) : Subgroup G := closure {g | ∃ u ∈ U, u ^ 2 = g}

theorem sq_mem_squares {U : Subgroup G} {u : G} (hu : u ∈ U) : u ^ 2 ∈ squares U :=
  subset_closure ⟨u, hu, rfl⟩

theorem squares_le (U : Subgroup G) : squares U ≤ U := by
  rw [squares, closure_le]
  rintro _ ⟨u, hu, rfl⟩
  exact U.pow_mem hu 2

theorem conj_mem_squares {U : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G)) {f : G}
    (hf : f ∈ squares U) : g * f * g⁻¹ ∈ squares U := by
  induction hf using closure_induction with
  | mem f hf =>
    obtain ⟨u, hu, rfl⟩ := hf
    rw [← conj_pow]
    exact sq_mem_squares ((mem_normalizer_iff.mp hg u).mp hu)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem mem_normalizer_of_forall_conj_mem [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h k hk, fun hk => ?_⟩
  let f : K → K := fun a => ⟨g * a * g⁻¹, h a a.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * k * g⁻¹, hk⟩
  have h1 : g * (a : G) * g⁻¹ = g * k * g⁻¹ := congrArg Subtype.val ha
  rw [← mul_left_cancel (mul_right_cancel h1)]
  exact a.2

theorem le_normalizer_squares [Finite G] {U V : Subgroup G} (hV : V ≤ normalizer (U : Set G)) :
    V ≤ normalizer (squares U : Set G) := fun _ hg =>
  mem_normalizer_of_forall_conj_mem fun _ hf => conj_mem_squares (hV hg) hf

theorem commutator_le_squares (U : Subgroup G) : ⁅U, U⁆ ≤ squares U := by
  rw [commutator_le]
  intro u hu v hv
  rw [show ⁅u, v⁆ = u ^ 2 * (u⁻¹ * v) ^ 2 * (v⁻¹) ^ 2 by
    simp only [commutatorElement_def, pow_two]; group]
  exact mul_mem (mul_mem (sq_mem_squares hu) (sq_mem_squares (mul_mem (inv_mem hu) hv)))
    (sq_mem_squares (inv_mem hv))

theorem squares_ne [Finite G] {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) :
    squares U ≠ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hn
    exact hU1 hn
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := n - 1)
    (hn ▸ pow_dvd_pow 2 (Nat.sub_le n 1))
  have hindex : M.index = 2 := by
    have h := M.card_mul_index
    rw [hM, hn] at h
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hsq : squares U ≤ M.map U.subtype := by
    rw [squares, closure_le]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩ * ⟨u, hu⟩, M.mul_self_mem_of_index_two hindex _, by
      simp [pow_two]⟩
  intro h
  have hle : U ≤ M.map U.subtype := fun a ha => hsq (by rw [h]; exact ha)
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨b, hb, hba⟩ := mem_map.mp (hle a.2)
    rwa [show b = a from Subtype.ext hba] at hb
  rw [htop, index_top] at hindex
  omega

section Minimal

variable [Finite G] {q : ℕ} {X U : Subgroup G}

theorem commutator_eq_bot_of_ne (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) {R : Subgroup G}
    (hRU : R ≤ U) (hRX : X ≤ normalizer (R : Set G)) (hRne : R ≠ U) : ⁅R, X⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ⁅R, X⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hRX
  have hcop : ¬ q ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := (hU.to_le hRU).exists_card_eq
    rw [hk]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    exact hq2 h2
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent q hq X R
    hX hcop hRX
  by_contra hbot
  have hU' := hmin _ (hle.trans hRU) hidem hbot
  exact hRne (le_antisymm hRU (hU' ▸ hle))

theorem commutator_squares_eq_bot (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) : ⁅squares U, X⁆ = ⊥ :=
  commutator_eq_bot_of_ne hq hq2 hX hU hmin (squares_le U) (le_normalizer_squares hXU)
    (squares_ne hU hU1)

theorem conj_eq_of_mem_squares (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) {y : G} (hy : y ∈ X) {f : G}
    (hf : f ∈ squares U) : y * f * y⁻¹ = f := by
  have h := commutator_squares_eq_bot hq hq2 hX hU hXU hU1 hmin
  have hc : ⁅f, y⁆ = 1 := by
    have : ⁅f, y⁆ ∈ ⁅squares U, X⁆ := commutator_mem_commutator hf hy
    rwa [h, mem_bot] at this
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  rw [← hc, mul_inv_cancel_right]

omit [Finite G] in
theorem commutator_subgroupOf {A B H : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ = (⁅A, B⁆).subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left hA, inf_of_le_left hB, inf_of_le_left]
  exact (commutator_mono hA hB).trans (le_normalizer_iff_commutator_le_left.mp le_normalizer)

theorem mem_squares_of_conj_mul_inv_mem (hq : q.Prime) (hq2 : q ≠ 2) {x : G}
    (hXx : X = zpowers x) (hXq : Nat.card X = q) (hU : IsPGroup 2 U)
    (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) {u : G} (hu : u ∈ U)
    (hux : x * u * x⁻¹ * u⁻¹ ∈ squares U) : u ∈ squares U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := U ⊔ X with hH
  set F := squares U with hF
  have hUH : U ≤ H := le_sup_left
  have hXH : X ≤ H := le_sup_right
  have hFH : F ≤ H := (squares_le U).trans hUH
  have hHF : H ≤ normalizer (F : Set G) :=
    sup_le (le_normalizer_squares (fun _ hg => mem_normalizer_of_forall_conj_mem fun _ hk =>
      mul_mem (mul_mem hg hk) (inv_mem hg))) (le_normalizer_squares hXU)
  have hN : (F.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hFH).mpr hHF
  let π := QuotientGroup.mk' (F.subgroupOf H)
  have hπ : ∀ a b : H, π a = π b ↔ (a : G)⁻¹ * b ∈ F := fun a b => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf,
      coe_mul, coe_inv]
  set K := (U.subgroupOf H).map π with hK
  set B := (X.subgroupOf H).map π with hB
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ]
    have ha' : (a : G) ∈ U := ha
    have hb' : (b : G) ∈ U := hb
    have : ((a * b : H) : G)⁻¹ * ((b * a : H) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [coe_mul, commutatorElement_def]
      group
    rw [this]
    exact commutator_le_squares U (commutator_mem_commutator (inv_mem hb') (inv_mem ha'))
  have hBK : B ≤ normalizer (K : Set (H ⧸ F.subgroupOf H)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro k
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨y * a * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have ha' : (a : G) ∈ U := ha
      have hy' : (y : G) ∈ X := hy
      change ((y * a * y⁻¹ : H) : G) ∈ U
      simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp (hXU hy') _).mp ha'
    · intro hk
      obtain ⟨a, ha, hak⟩ := hk
      refine ⟨y⁻¹ * a * y, ?_, ?_⟩
      · have ha' : (a : G) ∈ U := ha
        have hy' : (y : G) ∈ X := hy
        change ((y⁻¹ * a * y : H) : G) ∈ U
        simp only [coe_mul, coe_inv]
        have := (mem_normalizer_iff.mp (hXU (inv_mem hy')) _).mp ha'
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hak]
        group
  have hcop : Nat.Coprime (Nat.card B) (Nat.card K) := by
    have h1 : Nat.card B ∣ q := by
      rw [← hXq]
      refine (card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv]
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    have h2 : Nat.card K ∣ 2 ^ k := by
      rw [← hk]
      refine (card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv]
    have hq2' : Nat.Coprime q (2 ^ k) := Nat.Coprime.pow_right k
      ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    exact (hq2'.coprime_dvd_left h1).coprime_dvd_right h2
  have hinf := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hKc hBK hcop
  have hKB : ⁅K, B⁆ = K := by
    rw [hK, hB, ← map_commutator, commutator_subgroupOf hUH hXH, hUX]
  set ū := π ⟨u, hUH hu⟩ with hū
  have hūK : ū ∈ K := ⟨⟨u, hUH hu⟩, hu, rfl⟩
  have hūC : ū ∈ centralizer (B : Set (H ⧸ F.subgroupOf H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ zpowers x := hXx ▸ hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy'
    have hxH : x ∈ H := hXH (hXx ▸ mem_zpowers x)
    have hxu : π ⟨x, hxH⟩ * ū = ū * π ⟨x, hxH⟩ := by
      rw [hū, ← map_mul, ← map_mul, hπ]
      have : ((⟨x, hxH⟩ * ⟨u, hUH hu⟩ : H) : G)⁻¹ * ((⟨u, hUH hu⟩ * ⟨x, hxH⟩ : H) : G) =
          (u⁻¹ * x⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ * (u⁻¹ * x⁻¹)⁻¹ := by
        simp only [coe_mul]
        group
      rw [this]
      have hxN : u⁻¹ * x⁻¹ ∈ normalizer (F : Set G) :=
        hHF (mul_mem (inv_mem (hUH hu)) (inv_mem hxH))
      exact (mem_normalizer_iff.mp hxN _).mp (inv_mem hux)
    have hy' : y = ⟨x, hxH⟩ ^ k := Subtype.ext (by simp [← hk])
    rw [hy', map_zpow]
    exact ((Commute.zpow_left hxu k)).eq
  have hmem : ū ∈ ⁅B, K⁆ ⊓ centralizer (B : Set (H ⧸ F.subgroupOf H)) := by
    refine ⟨?_, hūC⟩
    rw [commutator_comm, hKB]
    exact hūK
  rw [hinf, mem_bot, hū, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    at hmem
  exact hmem

omit [Finite G] in
theorem sq_mem_of_commutator_le {N : Subgroup G} (hN : ⁅U, U⁆ ≤ N)
    (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U)
    (hcen : ∀ f ∈ squares U, ∀ v ∈ U, f * v = v * f)
    (hXF : ∀ y ∈ X, ∀ f ∈ squares U, y * f * y⁻¹ = f) {u : G} (hu : u ∈ U) : u ^ 2 ∈ N := by
  have hsqmul : ∀ a ∈ U, ∀ b ∈ U, (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := fun a _ b _ => by
    simp only [commutatorElement_def, pow_two]
    group
  let T : Subgroup G :=
    { carrier := {g | g ∈ U ∧ g ^ 2 ∈ N}
      one_mem' := ⟨U.one_mem, by rw [one_pow]; exact N.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨U.mul_mem ha hb, ?_⟩
        rw [hsqmul a ha b hb]
        exact N.mul_mem (N.mul_mem ha2 (hN (commutator_mem_commutator (inv_mem ha) hb))) hb2
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨U.inv_mem ha, by rw [inv_pow]; exact N.inv_mem ha2⟩ }
  have hle : ⁅U, X⁆ ≤ T := by
    rw [commutator_le]
    intro w hw y hy
    have hw' : y * w⁻¹ * y⁻¹ ∈ U := (mem_normalizer_iff.mp (hXU hy) _).mp (inv_mem hw)
    have heq : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    have h1 : (y * w⁻¹ * y⁻¹) ^ 2 = (w ^ 2)⁻¹ := by
      rw [show (y * w⁻¹ * y⁻¹) ^ 2 = (y * w ^ 2 * y⁻¹)⁻¹ by simp only [pow_two]; group,
        hXF y hy _ (sq_mem_squares hw)]
    have hcU : ⁅w⁻¹, y * w⁻¹ * y⁻¹⁆ ∈ U :=
      le_normalizer_iff_commutator_le_left.mp le_normalizer
        (commutator_mem_commutator (inv_mem hw) hw')
    have hc : ⁅w⁻¹, y * w⁻¹ * y⁻¹⁆ ∈ N := hN (commutator_mem_commutator (inv_mem hw) hw')
    refine ⟨by rw [heq]; exact mul_mem hw hw', ?_⟩
    rw [heq, hsqmul w hw _ hw', h1, hcen _ (sq_mem_squares hw) _ hcU, mul_inv_cancel_right]
    exact hc
  have hUT : U ≤ T := by rw [← hUX]; exact hle
  exact (hUT hu).2

theorem sq_eq_one_of_commute (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    {u : G} (hu : u ∈ U) : u ^ 2 = 1 := by
  have hUU : ⁅U, U⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  have h := sq_mem_of_commutator_le hUU hXU hUX
    (fun f hf v hv => hc f (squares_le U hf) v hv)
    (fun y hy f hf => conj_eq_of_mem_squares hq hq2 hX hU hXU hU1 hmin hy hf) hu
  rwa [mem_bot] at h

omit [Finite G] in
theorem conj_mem_commutator {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) {c : G} (hc : c ∈ ⁅A, B⁆) : g * c * g⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hc ⊢
  induction hc using closure_induction with
  | mem c hc =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    refine subset_closure ⟨g * a * g⁻¹, (mem_normalizer_iff.mp hA a).mp ha, g * b * g⁻¹,
      (mem_normalizer_iff.mp hB b).mp hb, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem squares_commute (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) {f : G} (hf : f ∈ squares U) {v : G}
    (hv : v ∈ U) : f * v = v * f := by
  have hXF := commutator_squares_eq_bot hq hq2 hX hU hXU hU1 hmin
  have hUleN : U ≤ normalizer (U : Set G) := le_normalizer
  have h1 : ⁅⁅X, squares U⁆, U⁆ = ⊥ := by
    rw [show ⁅X, squares U⁆ = ⊥ by rw [commutator_comm]; exact hXF, commutator_bot_left]
  have hFU : ⁅squares U, U⁆ ≤ U :=
    (commutator_mono (squares_le U) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp le_normalizer)
  have hFUne : ⁅squares U, U⁆ ≠ U := fun h => squares_ne hU hU1 (le_antisymm (squares_le U)
    (h.symm.le.trans ((commutator_mono (squares_le U) le_rfl).trans (commutator_le_squares U))))
  have hXFU : X ≤ normalizer ((⁅squares U, U⁆ : Subgroup G) : Set G) := fun _ hy =>
    mem_normalizer_of_forall_conj_mem fun _ hc =>
      conj_mem_commutator (le_normalizer_squares hXU hy) (hXU hy) hc
  have h2 : ⁅⁅squares U, U⁆, X⁆ = ⊥ :=
    commutator_eq_bot_of_ne hq hq2 hX hU hmin hFU hXFU hFUne
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hUX, commutator_eq_bot_iff_le_centralizer] at h3
  exact mem_centralizer_iff.mp (h3 hv) f hf

theorem mem_squares_of_forall_commute (hq : q.Prime) (hq2 : q ≠ 2) {x : G}
    (hXx : X = zpowers x) (hXq : Nat.card X = q) (hX : IsPGroup q X) (hU : IsPGroup 2 U)
    (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) (hnc : ¬ ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    {z : G} (hz : z ∈ U) (hzc : ∀ v ∈ U, z * v = v * z) : z ∈ squares U := by
  set Z := U ⊓ centralizer (U : Set G) with hZ
  have hZU : Z ≤ U := inf_le_left
  have hZne : Z ≠ U := fun h => hnc fun a ha b hb => by
    have ha' : a ∈ Z := h ▸ ha
    exact (mem_centralizer_iff.mp ha'.2 b hb).symm
  have hXZ : X ≤ normalizer (Z : Set G) := by
    intro y hy
    apply mem_normalizer_of_forall_conj_mem
    rintro c ⟨hcU, hcC⟩
    refine ⟨(mem_normalizer_iff.mp (hXU hy) c).mp hcU, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : y⁻¹ * v * y ∈ U := by
      have := (mem_normalizer_iff.mp (hXU (inv_mem hy)) v).mp hv
      rwa [inv_inv] at this
    have h := mem_centralizer_iff.mp hcC _ hv'
    calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [h]
      _ = y * c * y⁻¹ * v := by group
  have hU1 : U ≠ ⊥ := fun h => hZne (le_antisymm hZU (by rw [h]; exact bot_le))
  have h := commutator_eq_bot_of_ne hq hq2 hX hU hmin hZU hXZ hZne
  have hxX : x ∈ X := hXx ▸ mem_zpowers x
  have hzZ : z ∈ Z := ⟨hz, mem_centralizer_iff.mpr fun v hv => (hzc v hv).symm⟩
  have hc : ⁅z, x⁆ = 1 := by
    have : ⁅z, x⁆ ∈ ⁅Z, X⁆ := commutator_mem_commutator hzZ hxX
    rwa [h, mem_bot] at this
  apply mem_squares_of_conj_mul_inv_mem hq hq2 hXx hXq hU hXU hUX hz
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem commutator_eq_squares (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) : ⁅U, U⁆ = squares U := by
  refine le_antisymm (commutator_le_squares U) ?_
  rw [squares, closure_le]
  rintro _ ⟨u, hu, rfl⟩
  exact sq_mem_of_commutator_le le_rfl hXU hUX
    (fun f hf v hv => squares_commute hq hq2 hX hU hXU hUX hU1 hmin hf hv)
    (fun y hy f hf => conj_eq_of_mem_squares hq hq2 hX hU hXU hU1 hmin hy hf) hu

theorem sq_eq_one_of_mem_squares (hq : q.Prime) (hq2 : q ≠ 2) (hX : IsPGroup q X)
    (hU : IsPGroup 2 U) (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) {f : G} (hf : f ∈ squares U) : f ^ 2 = 1 := by
  have hcen : ∀ g ∈ squares U, ∀ v ∈ U, g * v = v * g := fun g hg v hv =>
    squares_commute hq hq2 hX hU hXU hUX hU1 hmin hg hv
  let T : Subgroup G :=
    { carrier := {g | g ∈ squares U ∧ g ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hab : a * b = b * a := hcen a ha b (squares_le U hb)
        rw [(Commute.mul_pow hab 2), ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hle : ⁅U, U⁆ ≤ T := by
    rw [commutator_le]
    intro u hu v hv
    have hc : ⁅u, v⁆ ∈ squares U := commutator_le_squares U (commutator_mem_commutator hu hv)
    refine ⟨hc, ?_⟩
    have hcu : ⁅u, v⁆ * u = u * ⁅u, v⁆ := hcen _ hc u hu
    have h1 : ⁅u, v⁆ ^ 2 = ⁅u ^ 2, v⁆ := by
      have : ⁅u ^ 2, v⁆ = (u * ⁅u, v⁆ * u⁻¹) * ⁅u, v⁆ := by
        simp only [commutatorElement_def, pow_two]
        group
      rw [this, ← hcu, mul_inv_cancel_right, pow_two]
    have h2 : ⁅u ^ 2, v⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcen _ (sq_mem_squares hu) v hv
    rw [h1, h2]
  rw [← commutator_eq_squares hq hq2 hX hU hXU hUX hU1 hmin] at hf
  exact (hle hf).2

theorem mem_squares_of_commutator_mem (hq : q.Prime) (hq2 : q ≠ 2) {x : G}
    (hXx : X = zpowers x) (hXq : Nat.card X = q) (hX : IsPGroup q X) (hU : IsPGroup 2 U)
    (hXU : X ≤ normalizer (U : Set G)) (hUX : ⁅U, X⁆ = U) (hU1 : U ≠ ⊥)
    (hmin : ∀ V ≤ U, ⁅V, X⁆ = V → V ≠ ⊥ → V = U) {Z₀ : Subgroup G} (hZ₀ : Z₀ ≤ squares U)
    (hZ₀ne : Z₀ ≠ squares U) {u : G} (hu : u ∈ U) (huc : ∀ v ∈ U, ⁅u, v⁆ ∈ Z₀) :
    u ∈ squares U := by
  have hcen : ∀ g ∈ Z₀, ∀ v ∈ U, g * v = v * g := fun g hg v hv =>
    squares_commute hq hq2 hX hU hXU hUX hU1 hmin (hZ₀ hg) hv
  have hXZ₀ : ∀ y ∈ X, ∀ g ∈ Z₀, y * g * y⁻¹ = g := fun y hy g hg =>
    conj_eq_of_mem_squares hq hq2 hX hU hXU hU1 hmin hy (hZ₀ hg)
  let R : Subgroup G :=
    { carrier := {g | g ∈ U ∧ ∀ v ∈ U, ⁅g, v⁆ ∈ Z₀}
      one_mem' := ⟨one_mem _, fun v _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun v hv => ?_⟩
        have hbv := hb' v hv
        have : ⁅a * b, v⁆ = (a * ⁅b, v⁆ * a⁻¹) * ⁅a, v⁆ := by
          simp only [commutatorElement_def]
          group
        rw [this, ← hcen _ hbv a ha, mul_inv_cancel_right]
        exact mul_mem hbv (ha' v hv)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun v hv => ?_⟩
        have hav := ha' v hv
        have : ⁅a⁻¹, v⁆ = a⁻¹ * ⁅a, v⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [this, show a⁻¹ * ⁅a, v⁆⁻¹ * a = ⁅a, v⁆⁻¹ by
          rw [mul_assoc, hcen _ (inv_mem hav) a ha, inv_mul_cancel_left]]
        exact inv_mem hav }
  have hRU : R ≤ U := fun g hg => hg.1
  have hRne : R ≠ U := by
    intro h
    apply hZ₀ne
    refine le_antisymm hZ₀ ?_
    have hUU : ⁅U, U⁆ ≤ Z₀ := by
      rw [commutator_le]
      intro a ha b hb
      have ha' : a ∈ R := h ▸ ha
      exact ha'.2 b hb
    rw [squares, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact sq_mem_of_commutator_le hUU hXU hUX
      (fun f hf v hv => squares_commute hq hq2 hX hU hXU hUX hU1 hmin hf hv)
      (fun y hy f hf => conj_eq_of_mem_squares hq hq2 hX hU hXU hU1 hmin hy hf) hw
  have hXR : X ≤ normalizer (R : Set G) := by
    intro y hy
    apply mem_normalizer_of_forall_conj_mem
    rintro g ⟨hg, hg'⟩
    refine ⟨(mem_normalizer_iff.mp (hXU hy) g).mp hg, fun v hv => ?_⟩
    have hv' : y⁻¹ * v * y ∈ U := by
      have := (mem_normalizer_iff.mp (hXU (inv_mem hy)) v).mp hv
      rwa [inv_inv] at this
    have h := hg' _ hv'
    have : ⁅y * g * y⁻¹, v⁆ = y * ⁅g, y⁻¹ * v * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this, hXZ₀ y hy _ h]
    exact h
  have h := commutator_eq_bot_of_ne hq hq2 hX hU hmin hRU hXR hRne
  have hxX : x ∈ X := hXx ▸ mem_zpowers x
  have huR : u ∈ R := ⟨hu, huc⟩
  have hc : ⁅u, x⁆ = 1 := by
    have : ⁅u, x⁆ ∈ ⁅R, X⁆ := commutator_mem_commutator huR hxX
    rwa [h, mem_bot] at this
  apply mem_squares_of_conj_mul_inv_mem hq hq2 hXx hXq hU hXU hUX hu
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

end Minimal

end CFSG.RankThree.PartTwo.Sec3
