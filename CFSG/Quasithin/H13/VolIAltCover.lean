module

public import CFSG.Quasithin.H13.VolIF956Core
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

abbrev DnQuot (n : ℕ) : Type :=
  ↥(coreMod n) ⧸ (zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n)

@[expose] def cyc012 : ↥(alternatingGroup (Fin 5)) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def cyc234 : ↥(alternatingGroup (Fin 5)) :=
  ⟨swap 2 3 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem cyc012_pow : cyc012 ^ 3 = 1 := by decide

theorem cyc234_pow : cyc234 ^ 3 = 1 := by decide

@[expose] def IsWord6 {G : Type*} [Monoid G] (g₁ g₂ x : G) : Prop :=
  ∃ a ∈ [1, g₁, g₁ * g₁], ∃ b ∈ [1, g₂, g₂ * g₂], ∃ c ∈ [1, g₁, g₁ * g₁],
    ∃ d ∈ [1, g₂, g₂ * g₂], ∃ e ∈ [1, g₁, g₁ * g₁], ∃ f ∈ [1, g₂, g₂ * g₂],
      x = a * b * c * d * e * f

theorem IsWord6.map {G K : Type*} [Monoid G] [Monoid K] (φ : G →* K) {g₁ g₂ x : G}
    (h : IsWord6 g₁ g₂ x) : IsWord6 (φ g₁) (φ g₂) (φ x) := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := h
  have hL : ∀ g a : G, a ∈ [1, g, g * g] → φ a ∈ [1, φ g, φ g * φ g] := by
    intro g a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl | rfl | rfl
    · exact Or.inl (map_one φ)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (map_mul φ g g))
  exact ⟨_, hL _ _ ha, _, hL _ _ hb, _, hL _ _ hc, _, hL _ _ hd, _, hL _ _ he, _, hL _ _ hf,
    by simp only [map_mul]⟩

theorem alt5_words : ∀ σ : ↥(alternatingGroup (Fin 5)), IsWord6 cyc012 cyc234 σ := by
  unfold IsWord6
  decide +kernel

@[expose] def evenOn {n : ℕ} (i j k : Fin n) : Finset (PermMod n) := Finset.univ.filter fun x =>
  (∀ l, l ≠ i → l ≠ j → l ≠ k → Multiplicative.toAdd x l = 0) ∧
    Multiplicative.toAdd x i + Multiplicative.toAdd x j + Multiplicative.toAdd x k = 0

theorem evenOn_five_012_card : (evenOn (0 : Fin 5) 1 2).card = 4 := by decide

theorem evenOn_five_234_card : (evenOn (2 : Fin 5) 3 4).card = 4 := by decide

theorem comm_mem_evenOn_012 : ∀ m : PermMod 5,
    permAct 5 (cyc012 : Perm (Fin 5)) m * m⁻¹ ∈ evenOn 0 1 2 := by
  decide

theorem comm_mem_evenOn_234 : ∀ m : PermMod 5,
    permAct 5 (cyc234 : Perm (Fin 5)) m * m⁻¹ ∈ evenOn 2 3 4 := by
  decide

theorem allOnes_not_mem : allOnes 5 ∉ coreMod 5 := by
  rw [mem_coreMod]
  decide

theorem card_coreMod_five : Nat.card (coreMod 5) = 16 := by
  have h : (coreMod 5 : Set (PermMod 5)) =
      ↑(Finset.univ.filter fun x : PermMod 5 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

section Module

variable {V : Type*} [CommGroup V]

@[expose] def commMap (t : MulAut V) : V →* V where
  toFun v := t v * v⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commMap_apply (t : MulAut V) (v : V) : commMap t v = t v * v⁻¹ := rfl

theorem eq_one_of_comm_fixed (hV2 : ∀ v : V, v ^ 2 = 1) {t : MulAut V} (ht3 : t ^ 3 = 1)
    (v : V) (hfix : t (t v * v⁻¹) = t v * v⁻¹) : t v * v⁻¹ = 1 := by
  set w := t v * v⁻¹ with hw
  have h1 : t v = w * v := by rw [hw]; group
  have h2 : t (t v) = v := by
    rw [h1, map_mul, hfix, h1, ← mul_assoc, ← pow_two, hV2, one_mul]
  have h3 : t (t (t v)) = v := by
    have := congrArg (fun s : MulAut V => s v) ht3
    simpa [pow_succ, MulAut.mul_apply] using this
  have h4 : t v = v := by
    have := congrArg t h2
    rw [h3] at this
    exact this.symm
  rw [hw, h4, mul_inv_cancel]

theorem comm_mem_sup_of_isWord6 {t₁ t₂ x : MulAut V} (hx : IsWord6 t₁ t₂ x) (v : V) :
    x v * v⁻¹ ∈ (commMap t₁).range ⊔ (commMap t₂).range := by
  set M := (commMap t₁).range ⊔ (commMap t₂).range
  have hmul : ∀ a b : MulAut V, (∀ v, a v * v⁻¹ ∈ M) → (∀ v, b v * v⁻¹ ∈ M) →
      ∀ v, (a * b) v * v⁻¹ ∈ M := by
    intro a b ha hb v
    have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (ha (b v)) (hb v)
  have h1 : ∀ v, (1 : MulAut V) v * v⁻¹ ∈ M := fun v => by
    rw [MulAut.one_apply, mul_inv_cancel]
    exact one_mem _
  have ht₁ : ∀ v, t₁ v * v⁻¹ ∈ M := fun v => mem_sup_left ⟨v, rfl⟩
  have ht₂ : ∀ v, t₂ v * v⁻¹ ∈ M := fun v => mem_sup_right ⟨v, rfl⟩
  have hL : ∀ t : MulAut V, (∀ v, t v * v⁻¹ ∈ M) → ∀ a ∈ [1, t, t * t], ∀ v, a v * v⁻¹ ∈ M := by
    intro t ht a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact h1
    · exact ht
    · exact hmul _ _ ht ht
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := hx
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hL _ ht₁ a ha) (hL _ ht₂ b hb))
    (hL _ ht₁ c hc)) (hL _ ht₂ d hd)) (hL _ ht₁ e he)) (hL _ ht₂ f hf) v

theorem card_commMap_range_le (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} {Z : Subgroup V}
    {β : V →* DnQuot n} (hβk : ∀ v, β v = 1 ↔ v ∈ Z) {t : MulAut V} (ht3 : t ^ 3 = 1)
    (htZ : ∀ z ∈ Z, t z = z) {γ : Perm (Fin n)}
    (hβe : ∀ (v : V) (m : ↥(coreMod n)), β v = QuotientGroup.mk m →
      β (t v) = QuotientGroup.mk (coreAct n γ m))
    (T : Finset (PermMod n)) (hγT : ∀ m : PermMod n, permAct n γ m * m⁻¹ ∈ T) :
    Nat.card (commMap t).range ≤ T.card := by
  let g : ↥(commMap t).range → DnQuot n := fun w => β w
  have hg : Function.Injective g := by
    intro w w' hww'
    have h1 : β ((w : V)⁻¹ * w') = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hww'
    have hZ' : (w : V)⁻¹ * w' ∈ Z := (hβk _).1 h1
    obtain ⟨v, hv⟩ := ((commMap t).range.mul_mem (inv_mem w.2) w'.2 : (w : V)⁻¹ * w' ∈ _)
    have hfix : t (t v * v⁻¹) = t v * v⁻¹ := by
      rw [← commMap_apply, hv]
      exact htZ _ hZ'
    have h2 := eq_one_of_comm_fixed hV2 ht3 v hfix
    rw [← commMap_apply, hv] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have himg : Set.range g ⊆ QuotientGroup.mk '' (Subtype.val ⁻¹' (T : Set (PermMod n))) := by
    rintro _ ⟨⟨_, ⟨v, rfl⟩⟩, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ↥(coreMod n), (QuotientGroup.mk m : DnQuot n) = β v :=
      QuotientGroup.mk_surjective _
    refine ⟨coreAct n γ m * m⁻¹, hγT (m : PermMod n), ?_⟩
    show (QuotientGroup.mk (coreAct n γ m * m⁻¹) : DnQuot n) = β (t v * v⁻¹)
    rw [map_mul, map_inv, hβe v m hm.symm, ← hm, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  calc Nat.card (commMap t).range = Nat.card (Set.range g) :=
        (Nat.card_range_of_injective hg).symm
    _ = (Set.range g).ncard := Nat.card_coe_set_eq _
    _ ≤ (QuotientGroup.mk '' (Subtype.val ⁻¹' (T : Set (PermMod n)))).ncard :=
        Set.ncard_le_ncard himg
    _ ≤ (Subtype.val ⁻¹' (T : Set (PermMod n)) : Set ↥(coreMod n)).ncard :=
        Set.ncard_image_le
    _ = (Subtype.val '' (Subtype.val ⁻¹' (T : Set (PermMod n)) : Set ↥(coreMod n))).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (T : Set (PermMod n)).ncard := Set.ncard_le_ncard (Set.image_preimage_subset _ _)
    _ = T.card := Set.ncard_coe_finset T

end Module

theorem altNaturalCoverFive_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
        AlternatingNatural H ⊤ Z 5 → Z = ⊥ := by
  intro V _ _ hV2 H Z hZ hcomm hnat
  obtain ⟨π₀, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  let π : ↥(alternatingGroup (Fin 5)) →* ↥H := π₀
  set t₁ : MulAut V := ((π cyc012 : ↥H) : MulAut V) with ht₁
  set t₂ : MulAut V := ((π cyc234 : ↥H) : MulAut V) with ht₂
  have hle : commV H ≤ (commMap t₁).range ⊔ (commMap t₂).range := by
    refine (closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
    have hw := (alt5_words σ).map (H.subtype.comp π)
    have hx' : (H.subtype.comp π) σ = x := congrArg Subtype.val hσ
    rw [hx'] at hw
    exact comm_mem_sup_of_isWord6 hw v
  let β' : V →* DnQuot 5 :=
    { toFun := fun v => β ⟨v, mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  have hcard : ∀ γ : ↥(alternatingGroup (Fin 5)), γ ^ 3 = 1 → ∀ T : Finset (PermMod 5),
      (∀ m : PermMod 5, permAct 5 (γ : Perm (Fin 5)) m * m⁻¹ ∈ T) →
      Nat.card (commMap ((π γ : ↥H) : MulAut V)).range ≤ T.card := fun γ hγ T hT =>
    card_commMap_range_le (β := β') hV2 (fun v => hβk ⟨v, mem_top v⟩)
      (by rw [← Subgroup.coe_pow, ← map_pow, hγ, map_one]; rfl) (fun z hz => hZ hz _ (π γ).2)
      (fun v m h => hβe γ ⟨v, mem_top v⟩ m (mem_top _) (permAct_mem_coreMod _ m.2) h) T hT
  have h₁ := hcard cyc012 cyc012_pow (evenOn 0 1 2) comm_mem_evenOn_012
  have h₂ := hcard cyc234 cyc234_pow (evenOn 2 3 4) comm_mem_evenOn_234
  rw [evenOn_five_012_card] at h₁
  rw [evenOn_five_234_card] at h₂
  have hV16 : Nat.card V ≤ 16 := by
    have hM : (⊤ : Subgroup V) ≤ (commMap t₁).range ⊔ (commMap t₂).range := hcomm ▸ hle
    have hN : (commMap t₁).range ≤ normalizer ((commMap t₂).range : Set V) := by
      rw [normalizer_eq_top]
      exact le_top
    have h64 := card_sup_mul_card_inf hN
    have hpos : 0 < Nat.card ↥((commMap t₁).range ⊓ (commMap t₂).range) := Nat.card_pos
    have hsup : Nat.card ↥((commMap t₁).range ⊔ (commMap t₂).range) ≤
        Nat.card (commMap t₁).range * Nat.card (commMap t₂).range := by
      rw [← h64]
      exact Nat.le_mul_of_pos_right _ hpos
    calc Nat.card V = Nat.card (⊤ : Subgroup V) := card_top.symm
      _ ≤ Nat.card ↥((commMap t₁).range ⊔ (commMap t₂).range) := card_le_of_le hM
      _ ≤ Nat.card (commMap t₁).range * Nat.card (commMap t₂).range := hsup
      _ ≤ 4 * 4 := Nat.mul_le_mul h₁ h₂
  have hker : zpowers (allOnes 5) ⊓ coreMod 5 = ⊥ := by
    have h2 : orderOf (allOnes 5) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    rw [mem_zpowers_iff_mem_range_orderOf, h2] at hx1
    simp only [Finset.mem_image, Finset.mem_range] at hx1
    obtain ⟨n, hn, rfl⟩ := hx1
    interval_cases n
    · simp
    · exact absurd (by simpa using hx2) allOnes_not_mem
  have hQ : Nat.card (DnQuot 5) = 16 := by
    have e : (zpowers (allOnes 5) ⊓ coreMod 5).subgroupOf (coreMod 5) = ⊥ := by
      rw [hker, bot_subgroupOf]
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq e).trans
      QuotientGroup.quotientBot).toEquiv, card_coreMod_five]
  have hbij : Function.Bijective β :=
    hβs.bijective_of_nat_card_le (by rw [card_top]; exact hV16.trans hQ.symm.le)
  rw [eq_bot_iff]
  intro z hz
  have h1 : β ⟨z, mem_top _⟩ = β 1 := by rw [(hβk _).2 hz, map_one]
  exact congrArg Subtype.val (hbij.1 h1)

end CFSG.Quasithin.H13.VolI
