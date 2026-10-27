module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12LiftN
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Cases
public import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem mulEquiv_mem_normalizer_map_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (g : G) :
    e g ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup G') : Set G') ↔
      g ∈ Subgroup.normalizer (H : Set G) := by
  have key : ∀ k : G, e k ∈ H.map e.toMonoidHom ↔ k ∈ H := fun k => by
    rw [Subgroup.mem_map_equiv]
    simp
  have conj : ∀ n : G, e g * e n * (e g)⁻¹ = e (g * n * g⁻¹) := fun n => by simp
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h n
    have := h (e n)
    rwa [conj, key, key] at this
  · intro h n'
    obtain ⟨n, rfl⟩ := e.surjective n'
    rw [conj, key, key]
    exact h n

@[expose] def KS12Config (Q : Type*) [Group Q] : Prop :=
  ∃ (x y g h : Q) (T : Subgroup Q), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
    Nat.card (Subgroup.closure ({x, y} : Set Q)) = 9 ∧ g * x * g⁻¹ = x⁻¹ ∧ g * y * g⁻¹ = y ∧
    h * y * h⁻¹ = y⁻¹ ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ x ∈ Subgroup.normalizer (T : Set Q)

@[expose] def KS12ConfigN (Q : Type*) [Group Q] : Prop :=
  ∃ (x y g h : Q) (T : Subgroup Q), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
    Nat.card (Subgroup.closure ({x, y} : Set Q)) = 9 ∧ g * x * g⁻¹ = x⁻¹ ∧ g * y * g⁻¹ = y ∧
    h * y * h⁻¹ = y⁻¹ ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ x ∈ Subgroup.normalizer (T : Set Q) ∧
    y ∈ Subgroup.normalizer (T : Set Q)

private theorem ks12_transport {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') {x y g h : Q}
    {T : Subgroup Q} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (h9 : Nat.card (Subgroup.closure ({x, y} : Set Q)) = 9) (hgx : g * x * g⁻¹ = x⁻¹)
    (hgy : g * y * g⁻¹ = y) (hhy : h * y * h⁻¹ = y⁻¹) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    (e x) ^ 3 = 1 ∧ (e y) ^ 3 = 1 ∧ e x * e y = e y * e x ∧
      Nat.card (Subgroup.closure ({e x, e y} : Set Q')) = 9 ∧ e g * e x * (e g)⁻¹ = (e x)⁻¹ ∧
      e g * e y * (e g)⁻¹ = e y ∧ e h * e y * (e h)⁻¹ = (e y)⁻¹ ∧
      IsPGroup 2 (T.map e.toMonoidHom) ∧ T.map e.toMonoidHom ≠ ⊥ := by
  refine ⟨by rw [← map_pow, hx3, map_one], by rw [← map_pow, hy3, map_one],
    by rw [← map_mul, ← map_mul, hxy], ?_, by simpa using congrArg e hgx,
    by simpa using congrArg e hgy, by simpa using congrArg e hhy, ?_, ?_⟩
  · have hcl : Subgroup.closure ({e x, e y} : Set Q') =
        (Subgroup.closure ({x, y} : Set Q)).map e.toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      ext w
      simp [Set.image_insert_eq]
    rw [hcl, Subgroup.card_map_of_injective e.injective, h9]
  · exact hT2.map e.toMonoidHom
  · intro hbot
    apply hT1
    exact (Subgroup.map_eq_bot_iff_of_injective T e.injective).mp hbot

theorem KS12Config.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (hQ : KS12Config Q) : KS12Config Q' := by
  obtain ⟨x, y, g, h, T, hx3, hy3, hxy, h9, hgx, hgy, hhy, hT2, hT1, hxT⟩ := hQ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    ks12_transport e hx3 hy3 hxy h9 hgx hgy hhy hT2 hT1
  exact ⟨e x, e y, e g, e h, T.map e.toMonoidHom, a1, a2, a3, a4, a5, a6, a7, a8, a9,
    (mulEquiv_mem_normalizer_map_iff e T x).mpr hxT⟩

theorem KS12ConfigN.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (hQ : KS12ConfigN Q) : KS12ConfigN Q' := by
  obtain ⟨x, y, g, h, T, hx3, hy3, hxy, h9, hgx, hgy, hhy, hT2, hT1, hxT, hyT⟩ := hQ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    ks12_transport e hx3 hy3 hxy h9 hgx hgy hhy hT2 hT1
  exact ⟨e x, e y, e g, e h, T.map e.toMonoidHom, a1, a2, a3, a4, a5, a6, a7, a8, a9,
    (mulEquiv_mem_normalizer_map_iff e T x).mpr hxT,
    (mulEquiv_mem_normalizer_map_iff e T y).mpr hyT⟩

theorem ks12_card_closure_pair {Q : Type*} [Group Q] {x y : Q} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hyx2 : y ≠ x ^ 2) : Nat.card (Subgroup.closure ({x, y} : Set Q)) = 9 :=
  (CFSG.RankThree.Asc83Table.E9Basis.ofNe hx3 hy3 hxy hx1 hy1 hyx hyx2).card

theorem KS12ConfigN.of_involution {Q : Type*} [Group Q] {x y g h t : Q} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hyx2 : y ≠ x ^ 2) (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y)
    (hhy : h * y * h⁻¹ = y⁻¹) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htx : t * x = x * t)
    (hty : t * y = y * t) : KS12ConfigN Q := by
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  have hT1 : Subgroup.zpowers t ≠ ⊥ := fun h => ht1 (by
    have := Subgroup.mem_zpowers t
    rwa [h, Subgroup.mem_bot] at this)
  have hnorm : ∀ w : Q, t * w = w * t → w ∈ Subgroup.normalizer (Subgroup.zpowers t : Set Q) := by
    intro w hw
    have hc : Commute w t := hw.symm
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers t k
    · intro hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hn' : n = t ^ k := by
        calc n = w⁻¹ * (w * n * w⁻¹) * w := by group
          _ = w⁻¹ * t ^ k * w := by rw [hk]
          _ = t ^ k := by rw [mul_assoc, ((hc.zpow_right k).eq).symm, inv_mul_cancel_left]
      rw [hn']
      exact Subgroup.zpow_mem_zpowers t k
  exact ⟨x, y, g, h, Subgroup.zpowers t, hx3, hy3, hxy, ks12_card_closure_pair hx3 hy3 hxy hx1
    hy1 hyx hyx2, hgx, hgy, hhy, hT2, hT1, hnorm x htx, hnorm y hty⟩

theorem KS12Config.of_involution {Q : Type*} [Group Q] {x y g h t : Q} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hyx2 : y ≠ x ^ 2) (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y)
    (hhy : h * y * h⁻¹ = y⁻¹) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htx : t * x = x * t) :
    KS12Config Q := by
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  have hT1 : Subgroup.zpowers t ≠ ⊥ := fun h => ht1 (by
    have := Subgroup.mem_zpowers t
    rwa [h, Subgroup.mem_bot] at this)
  have hc : Commute x t := htx.symm
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers t : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers t k
    · intro hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hn' : n = t ^ k := by
        calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
          _ = x⁻¹ * t ^ k * x := by rw [hk]
          _ = t ^ k := by rw [mul_assoc, ((hc.zpow_right k).eq).symm, inv_mul_cancel_left]
      rw [hn']
      exact Subgroup.zpow_mem_zpowers t k
  exact ⟨x, y, g, h, Subgroup.zpowers t, hx3, hy3, hxy, ks12_card_closure_pair hx3 hy3 hxy hx1
    hy1 hyx hyx2, hgx, hgy, hhy, hT2, hT1, hxN⟩

theorem ks12Concl_of_config {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) {Q : Type} [Group Q]
    (e : X ⧸ Subgroup.center X ≃* Q) (hQ : KS12Config Q) : KS12Concl X := by
  obtain ⟨x, y, g, h, T, hx3, hy3, hxy, h9, hgx, hgy, hhy, hT2, hT1, hxT⟩ :=
    KS12Config.of_mulEquiv e.symm hQ
  exact Or.inr (exists_e9_le_e27_of_quotient_config (Subgroup.center X) le_rfl hZ hx3 hy3 hxy h9
    hgx hgy hhy hT2 hT1 hxT)

theorem ks12Concl_of_configN {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) {Q : Type} [Group Q]
    (e : X ⧸ Subgroup.center X ≃* Q) (hQ : KS12ConfigN Q) : KS12Concl X := by
  obtain ⟨x, y, g, h, T, hx3, hy3, hxy, h9, hgx, hgy, hhy, hT2, hT1, hxT, hyT⟩ :=
    KS12ConfigN.of_mulEquiv e.symm hQ
  exact Or.inl (three_le_localRank_of_quotient_normalizer hZ hx3 hy3 hxy h9 hgx hgy hhy hT2 hT1
    hxT hyT)

end CFSG.RankThree.PartTwo.KFacts
