module

public import CFSG.Quasithin.Background.HDefs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13.L32A.TJ1

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_or_eq_of_relIndex_prime {O F Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hOY : O.relIndex Y = p) (hOF : O ≤ F) (hFY : F ≤ Y) : F = O ∨ F = Y := by
  have h := Subgroup.relIndex_mul_relIndex O F Y hOF hFY
  rw [hOY] at h
  rw [← h] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr (le_antisymm hFY (Subgroup.relIndex_eq_one.mp h1))
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hOF)

omit [Finite G] in
theorem pow_mem_of_relIndex {O Y : Subgroup G} [hn : (O.subgroupOf Y).Normal] {p : ℕ}
    (hOY : O.relIndex Y = p) {y : G} (hy : y ∈ Y) : y ^ p ∈ O := by
  have h : (QuotientGroup.mk' (O.subgroupOf Y) ⟨y, hy⟩) ^ p = 1 := by
    rw [← hOY]
    exact pow_card_eq_one'
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  simpa using h

omit [Finite G] in
theorem pow_not_mem_of_coprime {O Y : Subgroup G} [(O.subgroupOf Y).Normal] {p : ℕ}
    (hOY : O.relIndex Y = p) {y : G} (hy : y ∈ Y) (hyO : y ∉ O) {k : ℕ}
    (hk : Nat.Coprime k p) : y ^ k ∉ O := by
  intro hyk
  apply hyO
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hk
  have hyp := pow_mem_of_relIndex hOY hy
  have e : y = (y ^ k) ^ u * (y ^ p) ^ v := by
    calc y = y ^ (u * (k : ℤ) + v * (p : ℤ)) := by rw [huv, zpow_one]
      _ = (y ^ k) ^ u * (y ^ p) ^ v := by
        rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [e]
  exact O.mul_mem (O.zpow_mem hyk u) (O.zpow_mem hyp v)

omit [Finite G] in
theorem comm_mem_of_relIndex_prime {O Y : Subgroup G} [(O.subgroupOf Y).Normal] {p : ℕ}
    (hp : p.Prime) (hOY : O.relIndex Y = p) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) :
    a * b * a⁻¹ * b⁻¹ ∈ O := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (↥Y ⧸ O.subgroupOf Y) = p := hOY
  have := isCyclic_of_prime_card hcard
  have hc : QuotientGroup.mk' (O.subgroupOf Y) ⟨a, ha⟩ *
      QuotientGroup.mk' (O.subgroupOf Y) ⟨b, hb⟩ =
      QuotientGroup.mk' (O.subgroupOf Y) ⟨b, hb⟩ * QuotientGroup.mk' (O.subgroupOf Y) ⟨a, ha⟩ :=
    (IsCyclic.commGroup).mul_comm _ _
  have h1 : QuotientGroup.mk' (O.subgroupOf Y)
      (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥Y)⁻¹ * (⟨b, hb⟩ : ↥Y)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

omit [Finite G] in
theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
theorem isElemAbelian_of_forall' {E : Subgroup G} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h2⟩

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have h1 := h a ha _ hb
    have e : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rw [e]
    exact hb

omit [Finite G] in
theorem isElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian 2 (A ⊔ B) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem mem_of_card_eq_two_pow_pRank {R B : Subgroup G} (hBR : B ≤ R) (hB : IsElemAbelian 2 B)
    (hcard : Nat.card B = 2 ^ CFSG.Open.pRank 2 R) {c : G} (hcR : c ∈ R) (hc2 : c ^ 2 = 1)
    (hcB : ∀ b ∈ B, c * b = b * c) : c ∈ B := by
  have hZ : IsElemAbelian 2 (Subgroup.zpowers c) := by
    refine isElemAbelian_of_forall' (fun x hx y hy => ?_) fun x hx => ?_
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc2, one_zpow]
  have hsup := isElemAbelian_sup hB hZ fun b hb z hz => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute c b from hcB b hb) i)).symm.eq
  have hle : B ⊔ Subgroup.zpowers c ≤ R := sup_le hBR (Subgroup.zpowers_le.mpr hcR)
  have h1 := H.card_le_two_pow_pRank hle hsup
  have h2 : Nat.card B ≤ Nat.card ↥(B ⊔ Subgroup.zpowers c) :=
    Subgroup.card_le_of_le le_sup_left
  have heq : B = B ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

omit [Finite G] in
theorem commute_of_stab {W₀ : Subgroup G} (hW₀ : IsPGroup 2 W₀) {x : G} {n : ℕ} (hn : Odd n)
    (hxn : x ^ n = 1) (hx₀ : ∀ c ∈ W₀, x * c * x⁻¹ = c) {w : G}
    (hw : x * w * x⁻¹ * w⁻¹ ∈ W₀) : x * w * x⁻¹ = w := by
  set c := x * w * x⁻¹ * w⁻¹ with hc
  have hxw : x * w * x⁻¹ = c * w := by rw [hc]; group
  have hk : ∀ k : ℕ, x ^ k * w * (x ^ k)⁻¹ = c ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * w * (x ^ (k + 1))⁻¹ = x * (x ^ k * w * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * (c ^ k * w) * x⁻¹ := by rw [ih]
        _ = (x * c ^ k * x⁻¹) * (x * w * x⁻¹) := by group
        _ = c ^ k * (c * w) := by
          rw [hxw, show x * c ^ k * x⁻¹ = (x * c * x⁻¹) ^ k by rw [conj_pow], hx₀ c hw]
        _ = c ^ (k + 1) * w := by rw [pow_succ]; group
  have hcn : c ^ n = 1 := by
    have := hk n
    rw [hxn, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨j, hj⟩ := hW₀ ⟨c, hw⟩
  have hcj : c ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd1 := orderOf_dvd_of_pow_eq_one hcn
  have hd2 := orderOf_dvd_of_pow_eq_one hcj
  have hcop : Nat.Coprime n (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hn)
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  rw [hxw, orderOf_eq_one_iff.mp h1, one_mul]

theorem commute_pow_of_transvections {Ω : Subgroup G} (hΩ : IsElemAbelian 2 Ω) {a b α β : G}
    (hα : α ∈ Ω) (hβ : β ∈ Ω) (hbN : b ∈ Subgroup.normalizer (Ω : Set G))
    (ha : ∀ ω ∈ Ω, a * ω * a⁻¹ * ω⁻¹ = 1 ∨ a * ω * a⁻¹ * ω⁻¹ = α)
    (hb : ∀ ω ∈ Ω, b * ω * b⁻¹ * ω⁻¹ = 1 ∨ b * ω * b⁻¹ * ω⁻¹ = β) {ω : G} (hω : ω ∈ Ω) :
    (a * b) ^ 48 * ω * ((a * b) ^ 48)⁻¹ = ω := by
  set g := a * b with hg
  set U := Subgroup.zpowers α ⊔ Subgroup.zpowers β with hU
  have hUΩ : U ≤ Ω := sup_le (Subgroup.zpowers_le.mpr hα) (Subgroup.zpowers_le.mpr hβ)
  have hUe : IsElemAbelian 2 U := isElemAbelian_of_le hUΩ hΩ
  have hαU : α ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers α)
  have hβU : β ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers β)
  have haU : ∀ x ∈ Ω, a * x * a⁻¹ * x⁻¹ ∈ U := fun x hx => by
    rcases ha x hx with h | h <;> rw [h]
    · exact U.one_mem
    · exact hαU
  have hbU : ∀ x ∈ Ω, b * x * b⁻¹ * x⁻¹ ∈ U := fun x hx => by
    rcases hb x hx with h | h <;> rw [h]
    · exact U.one_mem
    · exact hβU
  have hconjΩ : ∀ y ∈ Subgroup.normalizer (Ω : Set G), ∀ x ∈ Ω, y * x * y⁻¹ ∈ Ω :=
    fun y hy x hx => (Subgroup.mem_normalizer_iff.mp hy x).mp hx
  have hgU : ∀ x ∈ Ω, g * x * g⁻¹ * x⁻¹ ∈ U := by
    intro x hx
    have hbx : b * x * b⁻¹ * x⁻¹ ∈ Ω := Ω.mul_mem (hconjΩ b hbN x hx) (Ω.inv_mem hx)
    have e : g * x * g⁻¹ * x⁻¹ = (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (b * x * b⁻¹ * x⁻¹)⁻¹) *
        (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) := by rw [hg]; group
    rw [e]
    exact U.mul_mem (U.mul_mem (haU _ hbx) (hbU x hx)) (haU x hx)
  have hgUU : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu => by
    rw [show g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u by group]
    exact U.mul_mem (hgU u (hUΩ hu)) hu
  let f : ↥U → ↥U := fun u => ⟨g * u * g⁻¹, hgUU u u.2⟩
  have hf : Function.Injective f := fun u v h => by
    have h1 : g * (u : G) * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  let σ : Equiv.Perm ↥U := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : ∀ (n : ℕ) (u : ↥U), (((σ ^ n) u : ↥U) : G) = g ^ n * u * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', Equiv.Perm.mul_apply]
      change g * (((σ ^ n) u : ↥U) : G) * g⁻¹ = _
      rw [ih u]
      group
  have hord : ∀ x : G, x ^ 2 = 1 → Nat.card (Subgroup.zpowers x) ≤ 2 := fun x hx => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)
  have hUcard : Nat.card ↥U ≤ 4 := by
    have hn : Subgroup.zpowers α ≤ Subgroup.normalizer (Subgroup.zpowers β : Set G) :=
      le_normalizer_of_commute fun x hx y hy =>
        comm_of_isElemAbelian hUe (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
    have h := card_sup_mul_card_inf hn
    have h1 := hord α (hΩ.2 α hα)
    have h2 := hord β (hΩ.2 β hβ)
    have h3 : 0 < Nat.card ↥(Subgroup.zpowers α ⊓ Subgroup.zpowers β) := Nat.card_pos
    have h4 : Nat.card ↥U ≤ Nat.card ↥U * Nat.card ↥(Subgroup.zpowers α ⊓ Subgroup.zpowers β) :=
      Nat.le_mul_of_pos_right _ h3
    calc Nat.card ↥U ≤ Nat.card (Subgroup.zpowers α) * Nat.card (Subgroup.zpowers β) := by
          rw [← h]; exact h4
      _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
      _ = 4 := by norm_num
  have hσ24 : σ ^ 24 = 1 := by
    have h1 : orderOf σ ∣ (Nat.card ↥U).factorial := by
      rw [← Nat.card_perm]
      exact orderOf_dvd_natCard σ
    have h2 : (Nat.card ↥U).factorial ∣ 24 := Nat.factorial_dvd_factorial hUcard
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
  have hfixU : ∀ u ∈ U, g ^ 24 * u * (g ^ 24)⁻¹ = u := fun u hu => by
    have := hσ 24 ⟨u, hu⟩
    rw [hσ24] at this
    exact this.symm
  have hk : ∀ k : ℕ, ∀ x ∈ Ω, g ^ k * x * (g ^ k)⁻¹ * x⁻¹ ∈ U := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have e : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ * x⁻¹ =
          (g * (g ^ k * x * (g ^ k)⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
      rw [e]
      exact U.mul_mem (hgUU _ (ih x hx)) (hgU x hx)
  set u := g ^ 24 * ω * (g ^ 24)⁻¹ * ω⁻¹ with hu
  have huU : u ∈ U := hk 24 ω hω
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hUe.2 u huU
  calc g ^ 48 * ω * (g ^ 48)⁻¹ = g ^ 24 * (u * ω) * (g ^ 24)⁻¹ := by
        rw [hu, show (48 : ℕ) = 24 + 24 from rfl, pow_add]; group
    _ = (g ^ 24 * u * (g ^ 24)⁻¹) * (g ^ 24 * ω * (g ^ 24)⁻¹) := by group
    _ = u * (u * ω) := by rw [hfixU u huU, hu]; group
    _ = ω := by rw [← mul_assoc, hu2, one_mul]

end CFSG.Quasithin.H13.L32A.TJ1
