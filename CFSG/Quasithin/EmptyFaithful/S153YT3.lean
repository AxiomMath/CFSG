module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Cfg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block

public section

namespace CFSG.Quasithin.YG

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

structure A3Pair (I S K₀ K₁ : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S I
  blk₀ : IsBlock2 I K₀
  blk₁ : IsBlock2 I K₁
  alt₀ : IsAltType K₀ 3
  alt₁ : IsAltType K₁ 3
  comm : ∀ a ∈ K₀, ∀ b ∈ K₁, a * b = b * a
  perm₀ : ∀ t ∈ S, B6.conjSub t K₀ = K₀ ∨ B6.conjSub t K₀ = K₁
  perm₁ : ∀ t ∈ S, B6.conjSub t K₁ = K₀ ∨ B6.conjSub t K₁ = K₁
  gen : I = S ⊔ (K₀ ⊔ K₁)

variable {I S K₀ K₁ : Subgroup G}

theorem mem_normalizer_sup_of_conjSub_perm {X Y : Subgroup G} {t : G}
    (h₁ : B6.conjSub t X = X ∨ B6.conjSub t X = Y) (h₂ : B6.conjSub t Y = X ∨ B6.conjSub t Y = Y)
    (h₃ : B6.conjSub t⁻¹ X = X ∨ B6.conjSub t⁻¹ X = Y)
    (h₄ : B6.conjSub t⁻¹ Y = X ∨ B6.conjSub t⁻¹ Y = Y) :
    t ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ g : G, (B6.conjSub g X = X ∨ B6.conjSub g X = Y) →
      (B6.conjSub g Y = X ∨ B6.conjSub g Y = Y) → B6.conjSub g (X ⊔ Y) ≤ X ⊔ Y := by
    intro g hX hY
    rw [OrderIso.map_sup]
    refine sup_le ?_ ?_
    · rcases hX with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    · rcases hY with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
  exact B6.mem_normalizer_of_conjSub_le (key t h₁ h₂) (key t⁻¹ h₃ h₄)

theorem conjSub_blockU_eq (t : G) (L : Subgroup G) :
    B6.conjSub t (blockU L) = blockU (B6.conjSub t L) :=
  (CFSG.QuasithinUnique.Lin2.blockU_map_equiv (MulAut.conj t) L).symm

theorem mem_blockU_conj_of_conjSub_eq {a : G} {L L' : Subgroup G} (h : B6.conjSub a L = L') {u : G}
    (hu : u ∈ blockU L) : a * u * a⁻¹ ∈ blockU L' := by
  subst h
  rw [← conjSub_blockU_eq, B6.mem_conjSub]
  simpa [mul_assoc] using hu

namespace A3Pair

variable [Finite G] (c : A3Pair I S K₀ K₁)
include c

omit [Finite G] in
theorem le₀ : K₀ ≤ I := c.blk₀.2.1

omit [Finite G] in
theorem le₁ : K₁ ≤ I := c.blk₁.2.1

theorem a4₀ : IsA4Block K₀ (blockU K₀) := IsA4Block.of_alt3 c.blk₀.1 c.alt₀

theorem a4₁ : IsA4Block K₁ (blockU K₁) := IsA4Block.of_alt3 c.blk₁.1 c.alt₁

theorem U₀_le : blockU K₀ ≤ K₀ := c.a4₀.le

theorem U₁_le : blockU K₁ ≤ K₁ := c.a4₁.le

theorem card_blockU₀ : Nat.card (blockU K₀) = 4 := c.a4₀.card_U

theorem card_blockU₁ : Nat.card (blockU K₁) = 4 := c.a4₁.card_U

theorem inf_eq_bot : K₀ ⊓ K₁ = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun x hx =>
    c.a4₀.center_L x hx.1 fun l hl => (c.comm l hl x hx.2).symm

theorem ne : K₀ ≠ K₁ := by
  intro h
  have h1 := c.inf_eq_bot
  rw [← h, inf_idem] at h1
  have h12 := c.a4₀.card_L
  rw [h1, Subgroup.card_bot] at h12
  omega

theorem blockU_inf : blockU K₀ ⊓ blockU K₁ = ⊥ := by
  have h := inf_le_inf c.U₀_le c.U₁_le
  rw [c.inf_eq_bot] at h
  exact le_bot_iff.mp h

theorem comm_blockU : ∀ x ∈ blockU K₀, ∀ y ∈ blockU K₁, x * y = y * x := fun x hx y hy =>
  c.comm x (c.U₀_le hx) y (c.U₁_le hy)

theorem exists_mul_of_mem_blockU_sup {u : G} (hu : u ∈ blockU K₀ ⊔ blockU K₁) :
    ∃ u₀ ∈ blockU K₀, ∃ u₁ ∈ blockU K₁, u = u₀ * u₁ :=
  (Lin2.mem_sup_iff_of_le_normalizer
    (Lin2.le_normalizer_of_commute (A := blockU K₀) (B := blockU K₁) c.comm_blockU)).1 hu

omit [Finite G] in
theorem K₀_le_normalizer₁ : K₀ ≤ Subgroup.normalizer (K₁ : Set G) :=
  Lin2.le_normalizer_of_commute (A := K₁) (B := K₀) fun a ha b hb => (c.comm b hb a ha).symm

omit [Finite G] in
theorem isElemAbelian_blockU₀ : IsElemAbelian 2 (blockU K₀) := AppC.isElemAbelian_blockU c.blk₀.1

omit [Finite G] in
theorem isElemAbelian_blockU₁ : IsElemAbelian 2 (blockU K₁) := AppC.isElemAbelian_blockU c.blk₁.1

theorem isElemAbelian_blockU_sup : IsElemAbelian 2 (blockU K₀ ⊔ blockU K₁) :=
  B2F.isElemAbelian_sup_of_commute c.isElemAbelian_blockU₀ c.isElemAbelian_blockU₁ c.comm_blockU

theorem card_blockU_sup : Nat.card ↥(blockU K₀ ⊔ blockU K₁) = 16 := by
  have h := B2F.card_sup_mul_card_inf_of_commute c.comm_blockU
  rw [c.blockU_inf, Subgroup.card_bot, mul_one, c.card_blockU₀, c.card_blockU₁] at h
  omega

omit [Finite G] in
theorem S_le_normalizer_sup : S ≤ Subgroup.normalizer ((K₀ ⊔ K₁ : Subgroup G) : Set G) := fun t ht =>
  mem_normalizer_sup_of_conjSub_perm (c.perm₀ t ht) (c.perm₁ t ht) (c.perm₀ t⁻¹ (S.inv_mem ht))
    (c.perm₁ t⁻¹ (S.inv_mem ht))

omit [Finite G] in
theorem S_le_normalizer_blockU_sup :
    S ≤ Subgroup.normalizer ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G) := by
  have h₀ : ∀ g ∈ S, B6.conjSub g (blockU K₀) = blockU K₀ ∨ B6.conjSub g (blockU K₀) = blockU K₁ := by
    intro g hg
    rw [conjSub_blockU_eq]
    rcases c.perm₀ g hg with h | h <;> rw [h]
    exacts [Or.inl rfl, Or.inr rfl]
  have h₁ : ∀ g ∈ S, B6.conjSub g (blockU K₁) = blockU K₀ ∨ B6.conjSub g (blockU K₁) = blockU K₁ := by
    intro g hg
    rw [conjSub_blockU_eq]
    rcases c.perm₁ g hg with h | h <;> rw [h]
    exacts [Or.inl rfl, Or.inr rfl]
  intro t ht
  exact mem_normalizer_sup_of_conjSub_perm (h₀ t ht) (h₁ t ht) (h₀ t⁻¹ (S.inv_mem ht))
    (h₁ t⁻¹ (S.inv_mem ht))

theorem blockU_sup_le_pCoreOf : blockU K₀ ⊔ blockU K₁ ≤ pCoreOf 2 I := by
  refine le_pCoreOf_of_le_normalizer 2 (sup_le (c.U₀_le.trans c.le₀) (c.U₁_le.trans c.le₁)) ?_
    (B2F.isPGroup_of_isElemAbelian c.isElemAbelian_blockU_sup)
  rw [c.gen]
  refine sup_le c.S_le_normalizer_blockU_sup (sup_le ?_ ?_)
  · intro k hk
    refine C1.mem_normalizer_sup (C1.le_normalizer_blockU K₀ hk) ?_
    exact Lin2.le_normalizer_of_commute (A := blockU K₁) (B := K₀)
      (fun a ha b hb => (c.comm b hb a (c.U₁_le ha)).symm) hk
  · intro k hk
    refine C1.mem_normalizer_sup ?_ (C1.le_normalizer_blockU K₁ hk)
    exact Lin2.le_normalizer_of_commute (A := blockU K₀) (B := K₁)
      (fun a ha b hb => c.comm a (c.U₀_le ha) b hb) hk

theorem blockU_sup_le_S : blockU K₀ ⊔ blockU K₁ ≤ S :=
  c.blockU_sup_le_pCoreOf.trans c.sylow.pCoreOf_le

theorem U₀_le_S : blockU K₀ ≤ S := le_sup_left.trans c.blockU_sup_le_S

omit [Finite G] in
theorem conjSub_eq₁_of_not_mem {a : G} (ha : a ∈ S) (hn : a ∉ Subgroup.normalizer (K₀ : Set G)) :
    B6.conjSub a K₀ = K₁ := by
  rcases c.perm₀ a ha with h | h
  · exact absurd (ModF.mem_normalizer_of_conjSub_eq h) hn
  · exact h

theorem mem_normalizer₁_of_mem {b : G} (hb : b ∈ S) (hbN : b ∈ Subgroup.normalizer (K₀ : Set G)) :
    b ∈ Subgroup.normalizer (K₁ : Set G) := by
  rcases c.perm₁ b hb with h | h
  · exact absurd ((B6.conjSub b).injective ((B6.conjSub_eq_self hbN).trans h.symm)) c.ne
  · exact ModF.mem_normalizer_of_conjSub_eq h

theorem mem_pCoreOf_of_comm_blockU {x : G} (hxS : x ∈ S)
    (h₀ : ∀ k ∈ K₀, k * x * k⁻¹ * x⁻¹ ∈ blockU K₀) (h₁ : ∀ k ∈ K₁, k * x * k⁻¹ * x⁻¹ ∈ blockU K₁) :
    x ∈ pCoreOf 2 I := by
  have hxI : x ∈ I := c.sylow.le hxS
  refine ModF.mem_pCoreOf_of_conj_mem c.sylow.isPGroup hxI fun y hy => ?_
  have hy' : y ∈ ((S : Subgroup G) : Set G) * ((K₀ ⊔ K₁ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₀ ⊔ K₁) c.S_le_normalizer_sup, ← c.gen]
    exact hy
  obtain ⟨s, hs, k, hk, rfl⟩ := hy'
  have hk' : k ∈ ((K₀ : Subgroup G) : Set G) * ((K₁ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₀ K₁ c.K₀_le_normalizer₁]
    exact hk
  obtain ⟨k₀, hk₀, k₁, hk₁, rfl⟩ := hk'
  have q₀ := h₀ k₀ hk₀
  have q₁ := h₁ k₁ hk₁
  have hq₁K : k₁ * x * k₁⁻¹ * x⁻¹ ∈ K₁ := c.U₁_le q₁
  have hcomm : k₀ * (k₁ * x * k₁⁻¹ * x⁻¹) = (k₁ * x * k₁⁻¹ * x⁻¹) * k₀ := c.comm k₀ hk₀ _ hq₁K
  have e : s * (k₀ * k₁) * x * (s * (k₀ * k₁))⁻¹ =
      s * ((k₁ * x * k₁⁻¹ * x⁻¹) * (k₀ * x * k₀⁻¹ * x⁻¹) * x) * s⁻¹ := by
    have h1 : s * (k₀ * k₁) * x * (s * (k₀ * k₁))⁻¹ =
        s * (k₀ * ((k₁ * x * k₁⁻¹ * x⁻¹) * x) * k₀⁻¹) * s⁻¹ := by group
    rw [h1]
    have h2 : k₀ * ((k₁ * x * k₁⁻¹ * x⁻¹) * x) * k₀⁻¹ =
        (k₀ * (k₁ * x * k₁⁻¹ * x⁻¹) * k₀⁻¹) * (k₀ * x * k₀⁻¹) := by group
    rw [h2]
    have h3 : k₀ * (k₁ * x * k₁⁻¹ * x⁻¹) * k₀⁻¹ = k₁ * x * k₁⁻¹ * x⁻¹ := by
      rw [hcomm]; group
    rw [h3]
    group
  rw [e]
  have hq₀S : k₀ * x * k₀⁻¹ * x⁻¹ ∈ S := c.blockU_sup_le_S (Subgroup.mem_sup_left q₀)
  have hq₁S : k₁ * x * k₁⁻¹ * x⁻¹ ∈ S := c.blockU_sup_le_S (Subgroup.mem_sup_right q₁)
  exact S.mul_mem (S.mul_mem hs (S.mul_mem (S.mul_mem hq₁S hq₀S) hxS)) (S.inv_mem hs)

end A3Pair

end CFSG.Quasithin.YG
