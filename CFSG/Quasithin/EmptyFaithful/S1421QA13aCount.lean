module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.QA13a

open Subgroup
open scoped commutatorElement

theorem comm_map_eq_iff {Γ : Type*} [Group Γ] (n p c : Γ) :
    n * p * n⁻¹ * p⁻¹ = n * (p * c) * n⁻¹ * (p * c)⁻¹ ↔ c * n = n * c := by
  have e1 : n * (p * c) * n⁻¹ * (p * c)⁻¹ = (n * p) * (c * n⁻¹ * c⁻¹) * p⁻¹ := by group
  have e2 : n * p * n⁻¹ * p⁻¹ = (n * p) * n⁻¹ * p⁻¹ := by group
  rw [e1, e2, mul_left_inj, mul_right_inj, eq_mul_inv_iff_mul_eq]
  have key : Commute n⁻¹ c ↔ Commute n c := Commute.inv_left_iff
  rw [commute_iff_eq, commute_iff_eq] at key
  exact key.trans eq_comm

theorem count_lemma {Γ : Type*} [Group Γ] [Finite Γ] {S' T' N' : Subgroup Γ}
    (hT : T' ≤ Subgroup.normalizer (S' : Set Γ)) (hNT : N' ≤ T')
    (hNn : ∀ t ∈ T', ∀ a ∈ N', t * a * t⁻¹ ∈ N') {n : Γ} (hn : n ∈ N') :
    Nat.card ↥(T' ⊓ S') ≤
      Nat.card ↥(T' ⊓ S' ⊓ Subgroup.centralizer ({n} : Set Γ)) * Nat.card ↥(N' ⊓ S') := by
  set P₀ : Subgroup Γ := T' ⊓ S' with hP₀
  set C : Subgroup Γ := P₀ ⊓ Subgroup.centralizer ({n} : Set Γ) with hC
  set E : Subgroup Γ := N' ⊓ S' with hE
  have hmem : ∀ p ∈ P₀, n * p * n⁻¹ * p⁻¹ ∈ E := by
    intro p hp
    refine ⟨?_, ?_⟩
    · have h1 : p * n⁻¹ * p⁻¹ ∈ N' := hNn p hp.1 n⁻¹ (N'.inv_mem hn)
      have e : n * p * n⁻¹ * p⁻¹ = n * (p * n⁻¹ * p⁻¹) := by group
      rw [e]
      exact N'.mul_mem hn h1
    · have h1 : n * p * n⁻¹ ∈ S' :=
        (Subgroup.mem_normalizer_iff.mp (hT (hNT hn)) p).mp hp.2
      exact S'.mul_mem h1 (S'.inv_mem hp.2)
  let f : ↥P₀ → ↥E := fun p => ⟨n * p * n⁻¹ * (p : Γ)⁻¹, hmem p p.2⟩
  have hf : ∀ p q : ↥P₀, f p = f q ↔ p⁻¹ * q ∈ C.subgroupOf P₀ := by
    intro p q
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have hq : (q : Γ) = (p : Γ) * ((p : Γ)⁻¹ * q) := by group
    constructor
    · intro h
      have h' : n * (p : Γ) * n⁻¹ * (p : Γ)⁻¹ = n * (q : Γ) * n⁻¹ * (q : Γ)⁻¹ :=
        congrArg Subtype.val h
      rw [hq] at h'
      exact ⟨P₀.mul_mem (P₀.inv_mem p.2) q.2, (comm_map_eq_iff n p _).mp h'⟩
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show n * (p : Γ) * n⁻¹ * (p : Γ)⁻¹ = n * (q : Γ) * n⁻¹ * (q : Γ)⁻¹
      rw [hq]
      exact (comm_map_eq_iff n p _).mpr h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf P₀)
  have hC' : Nat.card ↥(C.subgroupOf P₀) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ P₀)).toEquiv
  let g : ↥P₀ ⧸ C.subgroupOf P₀ → ↥E := Quotient.lift f (fun a b hab => by
    rw [hf]
    exact (QuotientGroup.leftRel_apply).mp hab)
  have hg : Function.Injective g := by
    intro a b
    induction a using Quotient.inductionOn' with | _ a =>
    induction b using Quotient.inductionOn' with | _ b =>
    intro hab
    exact Quotient.sound' ((QuotientGroup.leftRel_apply).mpr ((hf a b).mp hab))
  have hle : Nat.card (↥P₀ ⧸ C.subgroupOf P₀) ≤ Nat.card ↥E := Nat.card_le_card_of_injective g hg
  calc Nat.card ↥P₀ = Nat.card (↥P₀ ⧸ C.subgroupOf P₀) * Nat.card ↥(C.subgroupOf P₀) := hcard
    _ ≤ Nat.card ↥E * Nat.card ↥C := by rw [hC']; exact Nat.mul_le_mul_right _ hle
    _ = Nat.card ↥C * Nat.card ↥E := mul_comm _ _

theorem no_abelian_eight_of_derived {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 72)
    (h1 : Nat.card (derivedSeries D 1) = 18) (h2 : Nat.card (derivedSeries D 2) = 9)
    (E : Subgroup D) (hE : Nat.card E = 8) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : False := by
  set N : Subgroup D := derivedSeries D 2 with hN
  have : N.Normal := derivedSeries_normal D 2
  let π : D →* D ⧸ N := QuotientGroup.mk' N
  let φ : E →* D ⧸ N := π.comp E.subtype
  have hEN : E ⊓ N = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h3 : Nat.card ↥(E ⊓ N) ∣ 8 := hE ▸ Subgroup.card_dvd_of_le inf_le_left
    have h4 : Nat.card ↥(E ⊓ N) ∣ 9 := h2 ▸ Subgroup.card_dvd_of_le inf_le_right
    have := Nat.dvd_gcd h3 h4
    simpa using this
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : D) ∈ N := (QuotientGroup.eq_one_iff (x : D)).mp hx
    have : (x : D) ∈ E ⊓ N := ⟨x.2, hxN⟩
    rw [hEN, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hQ : Nat.card (D ⧸ N) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hD, h2] at h
    omega
  have hbij : Function.Bijective φ := by
    refine ⟨hφinj, ?_⟩
    have := hφinj.bijective_of_nat_card_le (by rw [hQ, hE])
    exact this.2
  have hcomm : ∀ u v : D ⧸ N, u * v = v * u := by
    intro u v
    obtain ⟨a, rfl⟩ := hbij.2 u
    obtain ⟨b, rfl⟩ := hbij.2 v
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hab a a.2 b b.2)
  have hle : derivedSeries D 1 ≤ N := by
    rw [derivedSeries_succ, derivedSeries_zero]
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hπ : π ⁅g₁, g₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (QuotientGroup.eq_one_iff _).mp hπ
  have := Subgroup.card_dvd_of_le hle
  rw [h1, h2] at this
  omega

theorem no_index_three_of_simple168 {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hcard : Nat.card D = 168) (S : Subgroup D) (hS : S.index = 3) : False := by
  have hfin : S.FiniteIndex := ⟨by omega⟩
  have hnorm : S.normalCore.Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.normalCore with h | h
  · have hdvd := S.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, hcard, hS] at hdvd
    norm_num [Nat.factorial] at hdvd
  · have : S = ⊤ := by
      rw [eq_top_iff, ← h]
      exact S.normalCore_le
    rw [this, Subgroup.index_top] at hS
    omega

theorem eq_one_of_central_168 {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hD : Nat.card D = 168) {x : D} (hx : ∀ y : D, y * x = x * y) : x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
  · have hxc : x ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      exact hx
    rw [h, Subgroup.mem_bot] at hxc
    exact hxc
  · exfalso
    have : IsMulCommutative D := Subgroup.center_eq_top_iff.mp h
    have hp := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup D)
    rw [hD] at hp
    have h2 := hp.eq_one_or_self_of_dvd 2 ⟨84, by norm_num⟩
    omega

theorem exists_fixed_of_order_three {D : Type*} [Group D] [Finite D] {E : Subgroup D}
    (hE : Nat.card E = 8) {g : D} (hg : g ∈ Subgroup.normalizer (E : Set D)) (hg3 : g ^ 3 = 1) :
    ∃ e ∈ E, e ≠ 1 ∧ g * e * g⁻¹ = e := by
  classical
  have : Fintype D := Fintype.ofFinite D
  have hgi : g⁻¹ ∈ Subgroup.normalizer (E : Set D) := Subgroup.inv_mem _ hg
  let f : {x : ↥E // x ≠ 1} → {x : ↥E // x ≠ 1} := fun x =>
    ⟨⟨g * (x.1 : D) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x.1).mp x.1.2⟩, by
      intro h
      apply x.2
      apply Subtype.ext
      have h' : g * (x.1 : D) * g⁻¹ = 1 := congrArg Subtype.val h
      have : (x.1 : D) = 1 := by
        calc (x.1 : D) = g⁻¹ * (g * (x.1 : D) * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group
      exact this⟩
  let f' : {x : ↥E // x ≠ 1} → {x : ↥E // x ≠ 1} := fun x =>
    ⟨⟨g⁻¹ * (x.1 : D) * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hgi x.1).mp x.1.2⟩, by
      intro h
      apply x.2
      apply Subtype.ext
      have h' : g⁻¹ * (x.1 : D) * g⁻¹⁻¹ = 1 := congrArg Subtype.val h
      have : (x.1 : D) = 1 := by
        calc (x.1 : D) = g * (g⁻¹ * (x.1 : D) * g⁻¹⁻¹) * g⁻¹ := by group
          _ = 1 := by rw [h']; group
      exact this⟩
  let σ : Equiv.Perm {x : ↥E // x ≠ 1} :=
    ⟨f, f', fun x => by
      apply Subtype.ext
      apply Subtype.ext
      show g⁻¹ * (g * (x.1 : D) * g⁻¹) * g⁻¹⁻¹ = (x.1 : D)
      group, fun x => by
      apply Subtype.ext
      apply Subtype.ext
      show g * (g⁻¹ * (x.1 : D) * g⁻¹⁻¹) * g⁻¹ = (x.1 : D)
      group⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext x
    rw [pow_one, pow_succ, pow_succ, pow_one]
    change ((f (f (f x))).1 : D) = ((1 : Equiv.Perm {x : ↥E // x ≠ 1}) x).1
    show g * (g * (g * (x.1 : D) * g⁻¹) * g⁻¹) * g⁻¹ = (x.1 : D)
    have hg3' : g * (g * g) = 1 := by rw [← pow_three]; exact hg3
    have e : g * (g * (g * (x.1 : D) * g⁻¹) * g⁻¹) * g⁻¹ =
        (g * (g * g)) * (x.1 : D) * (g * (g * g))⁻¹ := by
      group
    rw [e, hg3']
    group
  have hcard : Fintype.card {x : ↥E // x ≠ 1} = 7 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : Fintype.card ↥E = 8 := by rw [← Nat.card_eq_fintype_card, hE]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rw [hcard]; norm_num) hσ
  refine ⟨(a.1 : D), a.1.2, fun h => a.2 (Subtype.ext h), ?_⟩
  have := congrArg (fun y => (y.1 : D)) ha
  simpa [σ, f] using this

theorem no_abelian_eight_simple168 {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hD : Nat.card D = 168)
    (hcl : ∀ x : D, (Subgroup.centralizer ({x} : Set D)).index = 1 ∨
      (Subgroup.centralizer ({x} : Set D)).index = 21 ∨
      (Subgroup.centralizer ({x} : Set D)).index = 42 ∨
      (Subgroup.centralizer ({x} : Set D)).index = 56 ∨
      (Subgroup.centralizer ({x} : Set D)).index = 24)
    (E : Subgroup D) (hE : Nat.card E = 8) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : False := by
  have hcent : ∀ x ∈ E, x ≠ 1 → E = Subgroup.centralizer ({x} : Set D) := by
    intro x hxE hx1
    set C := Subgroup.centralizer ({x} : Set D) with hC
    have hEC : E ≤ C := by
      intro e he
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact hab e he x hxE
    have hmul : Nat.card C * C.index = 168 := by rw [Subgroup.card_mul_index, hD]
    have h8 : 8 ∣ Nat.card C := hE ▸ Subgroup.card_dvd_of_le hEC
    have hidx : C.index = 21 := by
      rcases hcl x with h | h | h | h | h
      · exfalso
        have hCtop : C = ⊤ := Subgroup.index_eq_one.mp h
        apply hx1
        refine eq_one_of_central_168 hD (fun y => ?_)
        have : y ∈ C := by rw [hCtop]; trivial
        rw [hC, Subgroup.mem_centralizer_singleton_iff] at this
        exact this
      · exact h
      · exfalso; rw [h] at hmul; omega
      · exfalso; rw [h] at hmul; omega
      · exfalso; rw [h] at hmul; omega
    have hCcard : Nat.card C = 8 := by rw [hidx] at hmul; omega
    exact Subgroup.eq_of_le_of_card_ge hEC (by rw [hCcard, hE])
  have hEne : ¬ (E = ⊥ ∨ E = ⊤) := by
    rintro (h | h)
    · rw [h, Subgroup.card_bot] at hE; omega
    · rw [h, Subgroup.card_top, hD] at hE; omega
  have hnorm : Subgroup.normalizer (E : Set D) = E := by
    refine le_antisymm ?_ Subgroup.le_normalizer
    by_contra hnle
    set Nn := Subgroup.normalizer (E : Set D) with hNn
    have hEN : E ≤ Nn := Subgroup.le_normalizer
    have h8 : 8 ∣ Nat.card Nn := hE ▸ Subgroup.card_dvd_of_le hEN
    have hdvd : Nat.card Nn ∣ 168 := hD ▸ Subgroup.card_subgroup_dvd_card Nn
    have hne8 : Nat.card Nn ≠ 8 := by
      intro h
      apply hnle
      have := Subgroup.eq_of_le_of_card_ge hEN (by rw [h, hE])
      rw [← this]
    obtain ⟨m, hm⟩ := h8
    have hm21 : m ∣ 21 := by
      have : 8 * m ∣ 8 * 21 := by rw [← hm]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hm1 : m ≠ 1 := by rintro rfl; apply hne8; omega
    have hm21' : m = 3 ∨ m = 7 ∨ m = 21 := by
      have hle : m ≤ 21 := Nat.le_of_dvd (by norm_num) hm21
      interval_cases m <;> simp_all
    rcases hm21' with rfl | rfl | rfl
    · have h3 : 3 ∣ Nat.card Nn := ⟨8, by omega⟩
      obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Nn) 3 h3
      have hgN : (g : D) ∈ Subgroup.normalizer (E : Set D) := g.2
      have hgpow : (g : D) ^ 3 = 1 := by
        have := pow_orderOf_eq_one g
        rw [hg3] at this
        exact congrArg Subtype.val this
      obtain ⟨e, heE, he1, hfix⟩ := exists_fixed_of_order_three hE hgN hgpow
      have hgC : (g : D) ∈ Subgroup.centralizer ({e} : Set D) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g : D) * e = ((g : D) * e * (g : D)⁻¹) * g := by group
          _ = e * g := by rw [hfix]
      rw [← hcent e heE he1] at hgC
      have hord : orderOf (⟨(g : D), hgC⟩ : ↥E) ∣ 8 := hE ▸ orderOf_dvd_natCard _
      have : orderOf (⟨(g : D), hgC⟩ : ↥E) = 3 := by
        rw [Subgroup.orderOf_mk]
        have := Subgroup.orderOf_coe g
        rw [this, hg3]
      rw [this] at hord
      omega
    · have hidx : Nn.index = 3 := by
        have := Subgroup.card_mul_index Nn
        rw [hD, hm] at this
        omega
      exact no_index_three_of_simple168 hD Nn hidx
    · have htop : Nn = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top]
        omega
      have : E.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      exact hEne (IsSimpleGroup.eq_bot_or_eq_top_of_normal E)
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE]; norm_num)
  have hidxE : ¬ 2 ∣ E.index := by
    have := Subgroup.card_mul_index E
    rw [hE, hD] at this
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 D := hE2.toSylow hidxE
  have hP : Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) := by
    show Subgroup.normalizer (E : Set D) ≤ Subgroup.centralizer (E : Set D)
    rw [hnorm]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hab b hb a ha
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hcard := hcompl.card_mul_card
  have hPcard : Nat.card (P : Subgroup D) = 8 := hE
  rw [hPcard, hD] at hcard
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hP).ker with h | h
  · rw [h, Subgroup.card_bot] at hcard
    omega
  · rw [h, Subgroup.card_top, hD] at hcard
    omega

end CFSG.Quasithin.QA13a
