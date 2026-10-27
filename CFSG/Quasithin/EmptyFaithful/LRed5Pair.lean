module

public import CFSG.Quasithin.EmptyFaithful.LRed5Simple

public section

namespace CFSG.Quasithin

namespace LRed5

open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commutator_le_self_gen (X : Subgroup G) : ⁅X, X⁆ ≤ X :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

@[expose] def Centerless (L : Subgroup G) : Prop := ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1

theorem inf_eq_bot_of_comm {L₁ L₂ : Subgroup G} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ : Centerless L₁) : L₁ ⊓ L₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  exact Subgroup.mem_bot.2 (hZ x hx1 fun y hy => (hc y hy x hx2).symm)

theorem sup_le_normalizer_of_comm {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set G) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← hc a ha b hb, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h1 : b * a * b⁻¹ * b = b * (b * a * b⁻¹) := hc _ ha b hb
    rw [inv_mul_cancel_right] at h1
    rw [mul_left_cancel h1]
    exact ha

theorem conj_mem_of_mem_sup {L₁ L₂ : Subgroup G} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {x : G}
    (hx : x ∈ L₁ ⊔ L₂) {l : G} (hl : l ∈ L₁) : x * l * x⁻¹ ∈ L₁ :=
  (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_of_comm hc hx) l).mp hl

theorem le_or_inf_eq_bot {A N : Subgroup G} (hq : CFSG.IsQuasisimple ↥A) (hZ : Centerless A)
    (hN : ∀ x ∈ A, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : A ≤ N ∨ N ⊓ A = ⊥ := by
  have hnorm : ((N ⊓ A).subgroupOf A).Normal := by
    constructor
    intro n hn l
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hN _ l.2 _ hn.1, A.mul_mem (A.mul_mem l.2 hn.2) (A.inv_mem l.2)⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq ((N ⊓ A).subgroupOf A) with
    h | h
  · right
    rw [eq_bot_iff]
    intro x hx
    have hxA : x ∈ A := hx.2
    have hcen' : (⟨x, hxA⟩ : ↥A) ∈ Subgroup.center ↥A :=
      h (show (⟨x, hxA⟩ : ↥A) ∈ (N ⊓ A).subgroupOf A from hx)
    exact Subgroup.mem_bot.2 (hZ x hxA fun y hy => by
      have := Subgroup.mem_center_iff.mp hcen' ⟨y, hy⟩
      exact congrArg Subtype.val this.symm)
  · left
    intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ (N ⊓ A).subgroupOf A := h ▸ Subgroup.mem_top _
    exact this.1

theorem le_of_normal_in_pair {L₁ L₂ N : Subgroup G} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂) (hZ₁ : Centerless L₁)
    (hZ₂ : Centerless L₂) (hNL : N ≤ L₁ ⊔ L₂) (hN : ∀ x ∈ L₁ ⊔ L₂, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hcen : ∀ n ∈ N, (∀ y ∈ L₁ ⊔ L₂, n * y = y * n) → n = 1) (hne : N ≠ ⊥) :
    L₁ ≤ N ∨ L₂ ≤ N := by
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have key : ∀ {A B : Subgroup G}, CFSG.IsQuasisimple ↥A → Centerless A →
      (∀ x ∈ A ⊔ B, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → A ≤ N ∨ N ⊓ A = ⊥ := fun {A B} hqA hZA hNAB =>
    le_or_inf_eq_bot hqA hZA fun x hx n hn => hNAB x (Subgroup.mem_sup_left hx) n hn
  rcases key (B := L₂) hq₁ hZ₁ hN with h1 | h1
  · exact Or.inl h1
  rcases key (B := L₁) hq₂ hZ₂ (by rwa [sup_comm]) with h2 | h2
  · exact Or.inr h2
  exfalso
  apply hne
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨c, hc1, d, hd, hnab⟩ := LRed4.exists_mul_of_mem_sup_comm hc (hNL hn)
  have hn1 : ∀ l ∈ L₁, n * l = l * n := by
    intro l hl
    have hnl : n * l * n⁻¹ ∈ L₁ := by
      rw [← hnab, mul_inv_rev, show c * d * l * (d⁻¹ * c⁻¹) = c * (d * l * d⁻¹) * c⁻¹ by group,
        show d * l * d⁻¹ = l by rw [hc' d hd l hl]; group]
      exact (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_of_comm hc (Subgroup.mem_sup_left hc1)) l).mp hl
    have hu1 : n * l * n⁻¹ * l⁻¹ ∈ L₁ := L₁.mul_mem hnl (L₁.inv_mem hl)
    have hu2 : n * l * n⁻¹ * l⁻¹ ∈ N := by
      have := N.mul_mem hn (hN l (Subgroup.mem_sup_left hl) n⁻¹ (N.inv_mem hn))
      simpa [mul_assoc] using this
    have hu : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L₁ := ⟨hu2, hu1⟩
    rw [h1, Subgroup.mem_bot] at hu
    calc n * l = n * l * n⁻¹ * l⁻¹ * (l * n) := by group
      _ = l * n := by rw [hu, one_mul]
  have hn2 : ∀ l ∈ L₂, n * l = l * n := by
    intro l hl
    have hnl : n * l * n⁻¹ ∈ L₂ := by
      rw [← hnab, mul_inv_rev, show c * d * l * (d⁻¹ * c⁻¹) = c * (d * l * d⁻¹) * c⁻¹ by group,
        show c * (d * l * d⁻¹) * c⁻¹ = d * l * d⁻¹ by
          rw [hc c hc1 _ (L₂.mul_mem (L₂.mul_mem hd hl) (L₂.inv_mem hd))]; group]
      exact L₂.mul_mem (L₂.mul_mem hd hl) (L₂.inv_mem hd)
    have hu1 : n * l * n⁻¹ * l⁻¹ ∈ L₂ := L₂.mul_mem hnl (L₂.inv_mem hl)
    have hu2 : n * l * n⁻¹ * l⁻¹ ∈ N := by
      have := N.mul_mem hn (hN l (Subgroup.mem_sup_right hl) n⁻¹ (N.inv_mem hn))
      simpa [mul_assoc] using this
    have hu : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L₂ := ⟨hu2, hu1⟩
    rw [h2, Subgroup.mem_bot] at hu
    calc n * l = n * l * n⁻¹ * l⁻¹ * (l * n) := by group
      _ = l * n := by rw [hu, one_mul]
  refine Subgroup.mem_bot.2 (hcen n hn fun y hy => ?_)
  obtain ⟨e, he, f, hf, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hc hy
  rw [← mul_assoc, hn1 e he, mul_assoc, hn2 f hf, mul_assoc]

theorem perfect_sup {L₁ L₂ : Subgroup G} (h₁ : ⁅L₁, L₁⁆ = L₁) (h₂ : ⁅L₂, L₂⁆ = L₂) :
    ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ = L₁ ⊔ L₂ := by
  refine le_antisymm (commutator_le_self_gen _) ?_
  calc L₁ ⊔ L₂ = ⁅L₁, L₁⁆ ⊔ ⁅L₂, L₂⁆ := by rw [h₁, h₂]
    _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
      (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem le_factor_of_pair {J G₁ G₂ L₁ L₂ : Subgroup G} (hG : G₁ ⊔ G₂ = J)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hL : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hZ₁ : Centerless L₁) (hL₁J : L₁ ≤ J) (hL₂J : L₂ ≤ J)
    (hLnorm : ∀ x ∈ J, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hperf : ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ = L₁ ⊔ L₂) : L₁ ≤ G₁ ∨ L₁ ≤ G₂ := by
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  set L := L₁ ⊔ L₂ with hLdef
  have hLJ : L ≤ J := sup_le hL₁J hL₂J
  have hN₁ : ∀ x ∈ J, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := fun x hx g hg =>
    conj_mem_of_mem_sup hcomm (hG ▸ hx) hg
  have hN₂ : ∀ x ∈ J, ∀ g ∈ G₂, x * g * x⁻¹ ∈ G₂ := fun x hx g hg =>
    conj_mem_of_mem_sup hcomm' (by rw [sup_comm, hG]; exact hx) hg
  set Y₁ := L ⊓ G₁ with hY₁
  set Y₂ := L ⊓ G₂ with hY₂
  have hYn : ∀ {G' : Subgroup G}, (∀ x ∈ J, ∀ g ∈ G', x * g * x⁻¹ ∈ G') →
      ∀ x ∈ J, ∀ y ∈ L ⊓ G', x * y * x⁻¹ ∈ L ⊓ G' := fun hN x hx y hy =>
    ⟨hLnorm x hx y hy.1, hN x hx y hy.2⟩
  have hcom₁ : ∀ l ∈ L, ∀ g ∈ G₁, l * g * l⁻¹ * g⁻¹ ∈ Y₁ := by
    intro l hl g hg
    refine ⟨?_, ?_⟩
    · have h1 : g * l⁻¹ * g⁻¹ ∈ L := hLnorm g (hG ▸ Subgroup.mem_sup_left hg) l⁻¹ (L.inv_mem hl)
      have := L.mul_mem hl h1
      simpa [mul_assoc] using this
    · exact G₁.mul_mem (hN₁ l (hLJ hl) g hg) (G₁.inv_mem hg)
  have hcom₂ : ∀ l ∈ L, ∀ g ∈ G₂, l * g * l⁻¹ * g⁻¹ ∈ Y₂ := by
    intro l hl g hg
    refine ⟨?_, ?_⟩
    · have h1 : g * l⁻¹ * g⁻¹ ∈ L := hLnorm g (hG ▸ Subgroup.mem_sup_right hg) l⁻¹ (L.inv_mem hl)
      have := L.mul_mem hl h1
      simpa [mul_assoc] using this
    · exact G₂.mul_mem (hN₂ l (hLJ hl) g hg) (G₂.inv_mem hg)
  have hLY : L ≤ Y₁ ⊔ Y₂ := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun l hl l' hl' => ?_
    obtain ⟨g₁, hg₁, g₂, hg₂, hgg⟩ := LRed4.exists_mul_of_mem_sup_comm hcomm (hG ▸ hLJ hl')
    have h1 := hcom₁ l hl g₁ hg₁
    have h2 := hcom₂ l hl g₂ hg₂
    have h2G : l * g₂ * l⁻¹ * g₂⁻¹ ∈ G₂ := h2.2
    have hid : ⁅l, l'⁆ = (l * g₁ * l⁻¹ * g₁⁻¹) * (l * g₂ * l⁻¹ * g₂⁻¹) := by
      rw [← hgg, commutatorElement_def]
      have hcc : g₁ * (l * g₂ * l⁻¹ * g₂⁻¹) = (l * g₂ * l⁻¹ * g₂⁻¹) * g₁ := hcomm g₁ hg₁ _ h2G
      calc l * (g₁ * g₂) * l⁻¹ * (g₁ * g₂)⁻¹
          = (l * g₁ * l⁻¹ * g₁⁻¹) * (g₁ * (l * g₂ * l⁻¹ * g₂⁻¹) * g₁⁻¹) := by group
        _ = (l * g₁ * l⁻¹ * g₁⁻¹) * ((l * g₂ * l⁻¹ * g₂⁻¹) * g₁ * g₁⁻¹) := by rw [hcc]
        _ = (l * g₁ * l⁻¹ * g₁⁻¹) * (l * g₂ * l⁻¹ * g₂⁻¹) := by group
    rw [hid]
    exact (Y₁ ⊔ Y₂).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hL₁Y : ∀ {G' : Subgroup G}, (∀ x ∈ J, ∀ g ∈ G', x * g * x⁻¹ ∈ G') →
      L₁ ≤ L ⊓ G' ∨ (L ⊓ G') ⊓ L₁ = ⊥ := fun hN =>
    le_or_inf_eq_bot hq₁ hZ₁ fun x hx n hn => hYn hN x (hL₁J hx) n hn
  rcases hL₁Y hN₁ with h1 | h1
  · exact Or.inl (h1.trans inf_le_right)
  rcases hL₁Y hN₂ with h2 | h2
  · exact Or.inr (h2.trans inf_le_right)
  exfalso
  have hcentY : ∀ {G' : Subgroup G}, (∀ x ∈ J, ∀ g ∈ G', x * g * x⁻¹ ∈ G') → (L ⊓ G') ⊓ L₁ = ⊥ →
      ∀ y ∈ L ⊓ G', ∀ l ∈ L₁, y * l = l * y := by
    intro G' hN hbot y hy l hl
    have hyL : y ∈ L₁ ⊔ L₂ := hy.1
    have hu1 : y * l * y⁻¹ * l⁻¹ ∈ L ⊓ G' := by
      have := (L ⊓ G').mul_mem hy (hYn hN l (hL₁J hl) y⁻¹ ((L ⊓ G').inv_mem hy))
      simpa [mul_assoc] using this
    have hu2 : y * l * y⁻¹ * l⁻¹ ∈ L₁ :=
      L₁.mul_mem (conj_mem_of_mem_sup hL hyL hl) (L₁.inv_mem hl)
    have hu : y * l * y⁻¹ * l⁻¹ ∈ (L ⊓ G') ⊓ L₁ := ⟨hu1, hu2⟩
    rw [hbot, Subgroup.mem_bot] at hu
    calc y * l = y * l * y⁻¹ * l⁻¹ * (l * y) := by group
      _ = l * y := by rw [hu, one_mul]
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := G64.IsQuasisimple.exists_ne hq₁
  apply hxy
  have hxY : x ∈ Y₁ ⊔ Y₂ := hLY (Subgroup.mem_sup_left hx)
  have hYc : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a := fun a ha b hb => hcomm a ha.2 b hb.2
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hYc hxY
  apply Subtype.ext
  show y₁ * y₂ * y = y * (y₁ * y₂)
  rw [mul_assoc, hcentY hN₂ h2 y₂ hy₂ y hy, ← mul_assoc, hcentY hN₁ h1 y₁ hy₁ y hy, mul_assoc]

theorem mem_normalizer_sup {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) → g ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
    intro g hA hB x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hc hx
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key hA hB x, fun hx => ?_⟩
  have := key (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using this

end Generic

section Factors

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique EmptyFaithfulMultiple

theorem sl2_ne_168_two_pow {n : ℕ} (hn : 1 ≤ n) {β : ℕ} :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 * 2 ^ β := by
  intro hα
  have h168 : 168 * 2 ^ β = 2 ^ (β + 3) * 21 := by
    rw [pow_add]
    ring
  rw [h168] at hα
  obtain ⟨-, hq⟩ := FFL.two_pow_mul_odd_inj (FFL.odd_two_pow_pow_sub_one hn (by norm_num))
    (by decide : Odd 21) hα
  have h22 : (2 ^ n) ^ 2 = 22 := by
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have h11 : 11 ∣ 2 ^ (n * 2) := by
    rw [pow_mul, h22]
    norm_num
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h11)
  omega

theorem factor_card_168 {X : Type} [Group X] [Finite X] (h : B56FactorList X) {α : ℕ}
    (hα : Nat.card X = 168 * 2 ^ α) : Nat.card X = 168 := by
  have h168 : 168 * 2 ^ α = 2 ^ (α + 3) * 21 := by
    rw [pow_add]
    ring
  rcases h with ⟨n, K, _, _, hn, hK, he⟩ | he | ⟨m, K, _, _, hm, hodd, hK, he⟩
  · exfalso
    obtain ⟨e⟩ := he
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    exact sl2_ne_168_two_pow hn (hX ▸ hα)
  · exfalso
    obtain ⟨e⟩ := he
    have hX : Nat.card X = 120 := by
      rw [Nat.card_congr e.toEquiv, LRed4.card_perm_fin]
      norm_num [Nat.factorial]
    have : 1 ≤ 2 ^ α := Nat.one_le_two_pow
    omega
  · obtain ⟨e⟩ := he
    have hX : Nat.card X = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [hX]
      norm_num
    · exfalso
      have hm3 : 3 ≤ m := by
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · have : m = 2 := by omega
          subst this
          exact absurd hodd (by decide)
        · exact h3
      have ho : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
        (FFL.odd_two_pow_pow_sub_one hm (by norm_num)).mul
          (FFL.odd_two_pow_pow_sub_one hm (by norm_num))
      have h3m : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul]; ring_nf
      rw [hX, h3m, mul_comm] at hα
      rw [h168] at hα
      have hα' : 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = 2 ^ (α + 3) * 21 := by
        rw [← hα, h3m]
        ring
      obtain ⟨-, hq⟩ := FFL.two_pow_mul_odd_inj ho (by decide : Odd 21) hα'
      have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      have h64 : 64 ≤ (2 ^ m) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h8 2
      have h512 : 512 ≤ (2 ^ m) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h8 3
      have : 63 * 511 ≤ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega

end Factors

section Solvable

variable {G : Type*} [Group G]

theorem isSolvable_quotient_of_sup {X : Type*} [Group X] {N T₁ : Subgroup X} [N.Normal]
    (hsup : N ⊔ T₁ = ⊤) (hT₁ : Group.IsSolvable T₁) : Group.IsSolvable (X ⧸ N) := by
  have hs : Function.Surjective ((QuotientGroup.mk' N).comp T₁.subtype) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
    have hg : g ∈ N ⊔ T₁ := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨n, hn, t, ht, hnt⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' N t = QuotientGroup.mk' N g
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [← hnt, map_mul, h1, one_mul]
  exact Group.isSolvable_of_surjective hs

theorem le_of_perfect_of_solvable_quotient {X : Type*} [Group X] {N P : Subgroup X} [N.Normal]
    (hsolv : Group.IsSolvable (X ⧸ N)) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  set Q := P.map (QuotientGroup.mk' N) with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, hP]
  by_contra hne
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hne
    intro x hx
    have : QuotientGroup.mk' N x ∈ Q := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have hQs : Group.IsSolvable Q := inferInstance
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.2 hQperf
  exact Group.IsPerfect.not_isSolvable Q hQs

theorem le_of_perfect_of_sup_zpowers {H N P : Subgroup G} {t : G} (hNH : N ≤ H) (htH : t ∈ H)
    (hPH : P ≤ H) (hN : (N.subgroupOf H).Normal) (hsup : N ⊔ Subgroup.zpowers t = H)
    (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have hzH : Subgroup.zpowers t ≤ H := (Subgroup.zpowers_le).2 htH
  have hsup' : N.subgroupOf H ⊔ (Subgroup.zpowers t).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hzH, hsup]
    exact Subgroup.subgroupOf_self _
  have hcomm : ∀ a b : ↥((Subgroup.zpowers t).subgroupOf H), a * b = b * a := by
    rintro ⟨⟨x, hxH⟩, hx⟩ ⟨⟨y, hyH⟩, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    apply Subtype.ext
    apply Subtype.ext
    exact (Commute.zpow_zpow_self t i j).eq
  have hsolv : Group.IsSolvable ↥((Subgroup.zpowers t).subgroupOf H) :=
    Group.isSolvable_of_comm hcomm
  have hP' : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPH, hP]
  have := le_of_perfect_of_solvable_quotient (N := N.subgroupOf H)
    (isSolvable_quotient_of_sup hsup' hsolv) hP'
  intro x hx
  exact this (show (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H from hx)

end Solvable





section PairMain

open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2)
open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

structure PairData (Γ L₁ L₂ : Subgroup (MulAut V)) (t : MulAut V) : Prop where
  le₁ : L₁ ≤ Γ
  le₂ : L₂ ≤ Γ
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  z₁ : Centerless L₁
  z₂ : Centerless L₂
  c₁ : Nat.card ↥L₁ = 168
  c₂ : Nat.card ↥L₂ = 168
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  tΓ : t ∈ Γ
  swap₁ : ∀ x ∈ L₁, t * x * t⁻¹ ∈ L₂
  swap₂ : ∀ y ∈ L₂, t⁻¹ * y * t ∈ L₁
  normal : ∀ g ∈ Γ, ∀ x ∈ L₁ ⊔ L₂, g * x * g⁻¹ ∈ L₁ ⊔ L₂
  cent : ∀ g ∈ Γ, (∀ x ∈ L₁ ⊔ L₂, g * x = x * g) → g = 1
  two : ∃ k : ℕ, Nat.card ↥Γ = Nat.card ↥(L₁ ⊔ L₂) * 2 ^ k
  o2 : pCoreOf 2 Γ = ⊥
  sqtk : G64.IsQuotientOfSQTKCat ↥Γ
  off : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A

variable {Γ L₁ L₂ : Subgroup (MulAut V)} {t : MulAut V}

omit [Finite V] in
theorem ffJ_conj_mem {g : MulAut V} (hg : g ∈ Γ) {j : MulAut V} (hj : j ∈ ffJ Γ) : g * j * g⁻¹ ∈ ffJ Γ :=
  (Subgroup.mem_normalizer_iff.mp (FFL.le_normalizer_ffJ Γ hg) j).mp hj

omit [Finite V] in
theorem pair_le_ffJ (P : PairData Γ L₁ L₂ t) (hJ : ffJ Γ ≠ ⊥) : L₁ ⊔ L₂ ≤ ffJ Γ := by
  have hJΓ : ffJ Γ ≤ Γ := FFL.ffJ_le Γ
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hLΓ : L₁ ⊔ L₂ ≤ Γ := sup_le P.le₁ P.le₂
  have hNne : ffJ Γ ⊓ (L₁ ⊔ L₂) ≠ ⊥ := by
    intro h
    apply hJ
    rw [eq_bot_iff]
    intro j hj
    refine Subgroup.mem_bot.2 (P.cent j (hJΓ hj) fun x hx => ?_)
    have h1 : j * x * j⁻¹ * x⁻¹ ∈ ffJ Γ ⊓ (L₁ ⊔ L₂) := by
      refine ⟨?_, ?_⟩
      · have := (ffJ Γ).mul_mem hj (ffJ_conj_mem (hLΓ hx) ((ffJ Γ).inv_mem hj))
        simpa [mul_assoc] using this
      · have h2 : j * x⁻¹ * j⁻¹ ∈ L₁ ⊔ L₂ := P.normal j (hJΓ hj) _ ((L₁ ⊔ L₂).inv_mem hx)
        have := (L₁ ⊔ L₂).mul_mem (P.normal j (hJΓ hj) x hx) ((L₁ ⊔ L₂).inv_mem hx)
        exact this
    rw [h, Subgroup.mem_bot] at h1
    calc j * x = j * x * j⁻¹ * x⁻¹ * (x * j) := by group
      _ = x * j := by rw [h1, one_mul]
  rcases le_of_normal_in_pair P.comm P.q₁ P.q₂ P.z₁ P.z₂ inf_le_right
    (fun x hx n hn => ⟨ffJ_conj_mem (hLΓ hx) hn.1, P.normal x (hLΓ hx) n hn.2⟩)
    (fun n hn hc => P.cent n (hJΓ hn.1) hc) hNne with h1 | h1
  · have hL₁ : L₁ ≤ ffJ Γ := h1.trans inf_le_left
    have hL₂ : L₂ ≤ ffJ Γ := by
      intro y hy
      have := ffJ_conj_mem (Γ := Γ) (g := t) P.tΓ (hL₁ (P.swap₂ y hy))
      simpa [mul_assoc] using this
    exact sup_le hL₁ hL₂
  · have hL₂ : L₂ ≤ ffJ Γ := h1.trans inf_le_left
    have hL₁ : L₁ ≤ ffJ Γ := by
      intro x hx
      have := ffJ_conj_mem (Γ := Γ) (g := t⁻¹) (Γ.inv_mem P.tΓ) (hL₂ (P.swap₁ x hx))
      simpa [mul_assoc] using this
    exact sup_le hL₁ hL₂

theorem pair_b53 (P : PairData Γ L₁ L₂ t) : B53Hyp (ffJ Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJΓ : ffJ Γ ≤ Γ := FFL.ffJ_le Γ
  have hO : pCoreOf 2 (ffJ Γ) = ⊥ := by
    have hPJ : pCoreOf 2 (ffJ Γ) ≤ Γ := (pCoreOf_le 2 _).trans hJΓ
    have hle : pCoreOf 2 (ffJ Γ) ≤ pCoreOf 2 Γ :=
      le_pCoreOf 2 hPJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hPJ).2
        ((FFL.le_normalizer_ffJ Γ).trans (normalizer_le_normalizer_pCoreOf 2 (ffJ Γ))))
        (pCoreOf_isPGroup 2 _)
    rw [P.o2] at hle
    exact le_bot_iff.1 hle
  refine ⟨hO, (FFL.ffJ_ffJ Γ).symm, ?_⟩
  obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := G64.isQuotientOfSQTKCat_of_le hJΓ P.sqtk
  exact ⟨Y, inferInstance, inferInstance, N, inferInstance, G64.sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

omit [Finite V] in
theorem PairData.normal_subgroupOf (P : PairData Γ L₁ L₂ t) : ((L₁ ⊔ L₂).subgroupOf Γ).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact P.normal g g.2 n hn

omit [Finite V] in
theorem PairData.le_normalizer (P : PairData Γ L₁ L₂ t) :
    Γ ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
  FFL.le_normalizer_of_normal (sup_le P.le₁ P.le₂) P.normal_subgroupOf

omit [Finite V] in
theorem le_genFitting_of_normal {J A L : Subgroup (MulAut V)} (hAL : A ≤ L) (hLJ : L ≤ J)
    (hA : (A.subgroupOf L).Normal) (hL : (L.subgroupOf J).Normal) (hq : CFSG.IsQuasisimple ↥A) :
    A ≤ quasithinGenFitting J := by
  have hsub : CFSG.Open.IsSubnormal A J :=
    CFSG.Open.IsSubnormal.step hAL hA (CFSG.Open.IsSubnormal.step hLJ hL (CFSG.Open.IsSubnormal.refl J))
  have hq' : CFSG.Open.IsQuasisimple ↥A := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hc : CFSG.Open.IsComponentOf A J := ⟨hAL.trans hLJ, hsub, hq'⟩
  exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right

theorem pair_case1_false (P : PairData Γ L₁ L₂ t) (hJ : ffJ Γ ≠ ⊥)
    (hqF : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ Γ))) : False := by
  have hLJ := pair_le_ffJ P hJ
  have hJΓ : ffJ Γ ≤ Γ := FFL.ffJ_le Γ
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hinf : L₁ ⊓ L₂ = ⊥ := inf_eq_bot_of_comm P.comm P.z₁
  have hLJn : ((L₁ ⊔ L₂).subgroupOf (ffJ Γ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).2 (fun g hg => P.le_normalizer (hJΓ hg))
  have hL₁L : (L₁.subgroupOf (L₁ ⊔ L₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le_normalizer_of_comm P.comm)
  have hL₂L : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      ((sup_comm L₁ L₂).le.trans (sup_le_normalizer_of_comm hc'))
  have hL₁F := le_genFitting_of_normal le_sup_left hLJ hL₁L hLJn P.q₁
  have hL₂F := le_genFitting_of_normal le_sup_right hLJ hL₂L hLJn P.q₂
  set F := quasithinGenFitting (ffJ Γ) with hF
  have hFΓ : F ≤ Γ := (quasithinGenFitting_le (ffJ Γ)).trans hJΓ
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLF).2 (fun g hg => P.le_normalizer (hFΓ hg))
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := G64.IsQuasisimple.exists_ne P.q₁
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqF ((L₁ ⊔ L₂).subgroupOf F) with
    h | h
  ·
    apply hab
    have hma : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      h (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have := Subgroup.mem_center_iff.mp hma ⟨b, hL₁F hb⟩
    exact Subtype.ext (congrArg Subtype.val this).symm
  ·
    have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := h ▸ Subgroup.mem_top _
      exact this
    have hL₁Fn : (L₁.subgroupOf F).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁F).2
        (fun g hg => sup_le_normalizer_of_comm P.comm (hFL hg))
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqF (L₁.subgroupOf F) with
      h' | h'
    · apply hab
      have hma : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
        h' (show (⟨a, hL₁F ha⟩ : ↥F) ∈ L₁.subgroupOf F from ha)
      have := Subgroup.mem_center_iff.mp hma ⟨b, hL₁F hb⟩
      exact Subtype.ext (congrArg Subtype.val this).symm
    · have hFL₁ : F ≤ L₁ := fun x hx => by
        have : (⟨x, hx⟩ : ↥F) ∈ L₁.subgroupOf F := h' ▸ Subgroup.mem_top _
        exact this
      have h2 : L₂ ≤ ⊥ := by
        rw [← hinf]
        exact le_inf (hL₂F.trans hFL₁) le_rfl
      have := Subgroup.card_le_of_le h2
      rw [Subgroup.card_bot, P.c₂] at this
      omega

omit [Finite V] in
theorem pair_case4_false (P : PairData Γ L₁ L₂ t) (hJ : ffJ Γ ≠ ⊥) (h4 : B56Case4 (ffJ Γ)) : False := by
  obtain ⟨G₁, G₂, t', hG, hinf, hcomm, ⟨e₁⟩, hc3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
  have hLJ := pair_le_ffJ P hJ
  have hX : G₁ ⊔ G₂ ≤ ffJ Γ := hG ▸ le_sup_left
  have ht'J : t' ∈ ffJ Γ := hG ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t')
  have ht'X : t' ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    mem_normalizer_sup hcomm ht₁ ht₂
  have hJn : ffJ Γ ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [hG]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact ht'X
  have hXn : ((G₁ ⊔ G₂).subgroupOf (ffJ Γ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX).2 hJn
  have hperf₁ : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.1 P.q₁.1
  have hL₁X : L₁ ≤ G₁ ⊔ G₂ :=
    le_of_perfect_of_sup_zpowers hX ht'J ((le_sup_left : L₁ ≤ L₁ ⊔ L₂).trans hLJ) hXn hG.symm hperf₁
  have hdvd := Subgroup.card_dvd_of_le hL₁X
  rw [LRed4.card_sup_of_commute hcomm hinf, P.c₁, hc3,
    Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)] at hdvd
  norm_num [Nat.factorial] at hdvd

omit [Finite V] in
theorem commute_sup_of_comm {A B : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {g : MulAut V} (hA : ∀ a ∈ A, g * a = a * g) (hB : ∀ b ∈ B, g * b = b * g) :
    ∀ x ∈ A ⊔ B, g * x = x * g := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := LRed4.exists_mul_of_mem_sup_comm hc hx
  rw [← mul_assoc, hA a ha, mul_assoc, hB b hb, mul_assoc]

omit [Finite V] in
theorem card_ffJ_pair (P : PairData Γ L₁ L₂ t) (hJ : ffJ Γ ≠ ⊥) :
    ∃ e : ℕ, Nat.card ↥(ffJ Γ) = 168 * 168 * 2 ^ e := by
  have hLJ := pair_le_ffJ P hJ
  have hJΓ : ffJ Γ ≤ Γ := FFL.ffJ_le Γ
  have hinf : L₁ ⊓ L₂ = ⊥ := inf_eq_bot_of_comm P.comm P.z₁
  have hL : Nat.card ↥(L₁ ⊔ L₂) = 168 * 168 := by
    rw [LRed4.card_sup_of_commute P.comm hinf, P.c₁, P.c₂]
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hLJ
  obtain ⟨k, hk⟩ := P.two
  have hdvd := Subgroup.card_dvd_of_le hJΓ
  rw [hd, hk] at hdvd
  have hdk : d ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_left (by rw [hL]; norm_num) hdvd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdk
  exact ⟨e, by rw [hd, hL, he]⟩

omit [Finite V] in
theorem pair_split (P : PairData Γ L₁ L₂ t) (hJ : ffJ Γ ≠ ⊥) {G₁ G₂ : Subgroup (MulAut V)}
    (hG : G₁ ⊔ G₂ = ffJ Γ) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hinf : G₁ ⊓ G₂ = ⊥)
    (hne₁ : G₁ ≠ ⊥) (hne₂ : G₂ ≠ ⊥) :
    (L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∨ L₁ ≤ G₂ ∧ L₂ ≤ G₁) ∧
      ∃ α β : ℕ, Nat.card ↥G₁ = 168 * 2 ^ α ∧ Nat.card ↥G₂ = 168 * 2 ^ β := by
  have hLJ := pair_le_ffJ P hJ
  have hL₁J : L₁ ≤ ffJ Γ := le_sup_left.trans hLJ
  have hL₂J : L₂ ≤ ffJ Γ := le_sup_right.trans hLJ
  have hJΓ : ffJ Γ ≤ Γ := FFL.ffJ_le Γ
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hinfL : L₁ ⊓ L₂ = ⊥ := inf_eq_bot_of_comm P.comm P.z₁
  have hperf₁ : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.1 P.q₁.1
  have hperf₂ : ⁅L₂, L₂⁆ = L₂ := Subgroup.isPerfect_iff.1 P.q₂.1
  have hperf : ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ = L₁ ⊔ L₂ := perfect_sup hperf₁ hperf₂
  have hperf' : ⁅L₂ ⊔ L₁, L₂ ⊔ L₁⁆ = L₂ ⊔ L₁ := perfect_sup hperf₂ hperf₁
  have hLnorm : ∀ x ∈ ffJ Γ, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂ :=
    fun x hx l hl => P.normal x (hJΓ hx) l hl
  have hLnorm' : ∀ x ∈ ffJ Γ, ∀ l ∈ L₂ ⊔ L₁, x * l * x⁻¹ ∈ L₂ ⊔ L₁ := fun x hx l hl => by
    rw [sup_comm] at hl ⊢
    exact hLnorm x hx l hl
  have h1 := le_factor_of_pair hG hcomm P.comm P.q₁ P.z₁ hL₁J hL₂J hLnorm hperf
  have h2 := le_factor_of_pair hG hcomm hc' P.q₂ P.z₂ hL₂J hL₁J hLnorm' hperf'
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hbot : ∀ {A B : Subgroup (MulAut V)}, A ≤ ffJ Γ → (∀ a ∈ B, ∀ b ∈ A, a * b = b * a) →
      L₁ ≤ B → L₂ ≤ B → A = ⊥ := by
    intro A B hAJ hAB hL₁B hL₂B
    rw [eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.2 (P.cent g (hJΓ (hAJ hg)) ?_)
    exact commute_sup_of_comm P.comm (fun a ha => (hAB a (hL₁B ha) g hg).symm)
      (fun b hb => (hAB b (hL₂B hb) g hg).symm)
  have hsplit : L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∨ L₁ ≤ G₂ ∧ L₂ ≤ G₁ := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (hbot (A := G₂) (hG ▸ le_sup_right) hcomm h1 h2) hne₂
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (hbot (A := G₁) (hG ▸ le_sup_left) hcomm' h1 h2) hne₁
  refine ⟨hsplit, ?_⟩
  obtain ⟨e, he⟩ := card_ffJ_pair P hJ
  have hcard : Nat.card ↥G₁ * Nat.card ↥G₂ = 168 * 168 * 2 ^ e := by
    rw [← LRed4.card_sup_of_commute hcomm hinf, hG, he]
  have hd₁ : 168 ∣ Nat.card ↥G₁ ∧ 168 ∣ Nat.card ↥G₂ := by
    rcases hsplit with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨P.c₁ ▸ Subgroup.card_dvd_of_le a, P.c₂ ▸ Subgroup.card_dvd_of_le b⟩
    · exact ⟨P.c₂ ▸ Subgroup.card_dvd_of_le b, P.c₁ ▸ Subgroup.card_dvd_of_le a⟩
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hd₁
  rw [hx, hy] at hcard
  have hxy : x * y = 2 ^ e := by
    have : 168 * 168 * (x * y) = 168 * 168 * 2 ^ e := by rw [← hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  obtain ⟨α, -, hα⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro y hxy)
  obtain ⟨β, -, hβ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left x hxy)
  exact ⟨α, β, by rw [hx, hα], by rw [hy, hβ]⟩

omit [Finite V] in
theorem modComm_sup_eq {L : Subgroup (MulAut V)} {W W' C : Subgroup V} (hcW : commV L ≤ W)
    (hWW' : W ⊔ W' = ⊤) (hinf : W ⊓ W' = C) (hinv' : ∀ l ∈ L, ∀ w ∈ W', l w ∈ W') :
    modComm L W ⊔ C = commV L ⊔ C := by
  apply le_antisymm
  · refine sup_le_sup_right ?_ C
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨(a : MulAut V), a.2, w, rfl⟩
  · refine sup_le ?_ le_sup_right
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [hWW']; exact Subgroup.mem_top v
    obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.1 hv
    have e : x (w * w') * (w * w')⁻¹ = (x w * w⁻¹) * (x w' * w'⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [e]
    have h1 : x w * w⁻¹ ∈ modComm L W ⊔ C :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨x, hx⟩, w, hw, rfl⟩)
    have h2 : x w' * w'⁻¹ ∈ C := by
      rw [← hinf]
      refine ⟨hcW (Subgroup.subset_closure ⟨x, hx, w', rfl⟩), ?_⟩
      exact W'.mul_mem (hinv' x hx w' hw') (W'.inv_mem hw')
    exact (modComm L W ⊔ C).mul_mem h1 (Subgroup.mem_sup_right h2)

omit [Finite V] in
theorem piece_false {L : Subgroup (MulAut V)} {W W' C : Subgroup V} (hc : Nat.card ↥L = 168)
    (hW : B56Piece L W C) (hWW' : W ⊔ W' = ⊤) (hinf : W ⊓ W' = C)
    (hinv' : ∀ l ∈ L, ∀ w ∈ W', l w ∈ W') {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V))) (hsC : ∀ c ∈ C, s c ∈ C)
    (hsC' : ∀ c ∈ C, s⁻¹ c ∈ C) (hout : ¬ ∃ g ∈ L, ∀ x ∈ L, s * x * s⁻¹ = g * x * g⁻¹) : False := by
  have hsN' : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := Subgroup.inv_mem _ hs
  have hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.mp hs l).mp hl
  have hU : ∀ u ∈ commV L ⊔ C, s u ∈ commV L ⊔ C := by
    intro u hu
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer hs ha) (hsC c hc')
  have hU' : ∀ u ∈ commV L ⊔ C, s⁻¹ u ∈ commV L ⊔ C := by
    intro u hu
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer hsN' ha) (hsC' c hc')
  rcases hW with ⟨hWeq, h2 | h5 | ⟨m, K, _, _, hK, π, hπ⟩⟩ | ⟨hWeq, m, K, _, _, hK, hDS⟩ |
    ⟨-, hcW, -, -, hnat⟩
  ·
    obtain ⟨n, K, _, _, hK, π, hπ⟩ := h2
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hK] at h1
    exact sl2_ne (FFL.one_le_of_card hK) (Or.inl hc) h1.symm
  ·
    obtain ⟨π, hπ⟩ := h5
    have h1 := FFL.card_eq_of_realizesVia (G64.symDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card (Equiv.Perm (Fin 5)) at h1
    rw [LRed4.card_perm_fin] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hK] at h1
    rcases sl3_cases (FFL.one_le_of_card hK) with hm | hm
    · subst hm
      have hπ' := FFC.realizesVia_zmod (by rw [hK]; norm_num) hπ
      rw [hWeq] at hπ'
      exact hout (inner_of_natural_section hπ' hU hU' hsC hsC' hL)
    · omega
  ·
    obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := hDS
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at h1
    rcases sl3_cases (FFL.one_le_of_card hK) with hm | hm
    · subst hm
      have hDS' := FFC.DirectSumOfCopies.zmod (K := K) (by rw [hK]; norm_num)
        (show DirectSumOfCopies L W C (FFModel.nat (StatedSL 3 K)) 2 from ⟨I, π, hZI, hind, hsup, hreal⟩)
      rw [hWeq] at hDS'
      exact hout (inner_of_two_natural hDS' hU hU' hsC hsC' hL)
    · omega
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
    rw [modComm_sup_eq hcW hWW' hinf hinv'] at hπ
    exact hout (inner_of_natural_section hπ hU hU' hsC hsC' hL)

omit [Finite V] in
theorem eq_bot_of_commV_eq_bot {L : Subgroup (MulAut V)} (h : commV L = ⊥) : L = ⊥ :=
  CFSG.Quasithin.FixVLat.eq_bot_of_commV_eq_bot h

omit [Finite V] in
theorem direct_false {L : Subgroup (MulAut V)} (hc : Nat.card ↥L = 168) {k : ℕ} (hk : k ≤ 2)
    (hD : DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) {s : MulAut V}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hout : ¬ ∃ g ∈ L, ∀ x ∈ L, s * x * s⁻¹ = g * x * g⁻¹) : False := by
  have hsN' : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := Subgroup.inv_mem _ hs
  have hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.mp hs l).mp hl
  have hU : ∀ u ∈ commV L, s u ∈ commV L := fun u hu => LRed4.commV_invariant_of_normalizer hs hu
  have hU' : ∀ u ∈ commV L, s⁻¹ u ∈ commV L := fun u hu =>
    LRed4.commV_invariant_of_normalizer hsN' hu
  have hZ : ∀ z ∈ (⊥ : Subgroup V), s z ∈ (⊥ : Subgroup V) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hZ' : ∀ z ∈ (⊥ : Subgroup V), s⁻¹ z ∈ (⊥ : Subgroup V) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  interval_cases k
  · obtain ⟨I, π, -, -, hsup, -⟩ := hD
    have h0 : commV L = ⊥ := by
      rw [← hsup]
      simp
    have := eq_bot_of_commV_eq_bot h0
    rw [this, Subgroup.card_bot] at hc
    omega
  · obtain ⟨I, π, -, -, hsup, hreal⟩ := hD
    have hI : (⨆ i : Fin 1, I i) = I 0 :=
      le_antisymm (iSup_le fun i => by rw [Subsingleton.elim i 0]) (le_iSup I 0)
    have hI0 : I 0 = commV L := by rw [← hsup, hI, bot_sup_eq]
    have hπ := hreal 0
    rw [hI0] at hπ
    exact hout (inner_of_natural_section hπ hU hU' hZ hZ' hL)
  · exact hout (inner_of_two_natural hD hU hU' hZ hZ' hL)

omit [Finite V] in
theorem mem_normalizer_of_both {A : Subgroup (MulAut V)} {g : MulAut V}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (h' : ∀ x ∈ A, g⁻¹ * x * g ∈ A) :
    g ∈ Subgroup.normalizer (A : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

omit [Finite V] in
theorem PairData.conj_mem {Γ L₁ L₂ : Subgroup (MulAut V)} {t : MulAut V} (P : PairData Γ L₁ L₂ t)
    {s : MulAut V} (hs₁ : ∀ x ∈ L₁, s * x * s⁻¹ ∈ L₁) (hs₁' : ∀ x ∈ L₁, s⁻¹ * x * s ∈ L₁) :
    t * s * t⁻¹ ∈ Subgroup.normalizer (L₂ : Set (MulAut V)) := by
  refine mem_normalizer_of_both (fun y hy => ?_) (fun y hy => ?_)
  · have h1 := P.swap₂ y hy
    have h2 := hs₁ _ h1
    have h3 := P.swap₁ _ h2
    simpa [mul_assoc] using h3
  ·
    have h1 := P.swap₂ y hy
    have h2 := hs₁' _ h1
    have h3 := P.swap₁ _ h2
    simpa [mul_assoc] using h3

omit [Finite V] in
theorem PairData.outer_swap {Γ L₁ L₂ : Subgroup (MulAut V)} {t : MulAut V} (P : PairData Γ L₁ L₂ t)
    {s : MulAut V} (hout : ¬ ∃ g ∈ L₁, ∀ x ∈ L₁, s * x * s⁻¹ = g * x * g⁻¹) :
    ¬ ∃ g ∈ L₂, ∀ y ∈ L₂, (t * s * t⁻¹) * y * (t * s * t⁻¹)⁻¹ = g * y * g⁻¹ := by
  rintro ⟨g', hg', h⟩
  apply hout
  refine ⟨t⁻¹ * g' * t, P.swap₂ g' hg', fun x hx => ?_⟩
  have h1 := h (t * x * t⁻¹) (P.swap₁ x hx)
  calc s * x * s⁻¹ = t⁻¹ * ((t * s * t⁻¹) * (t * x * t⁻¹) * (t * s * t⁻¹)⁻¹) * t := by group
    _ = t⁻¹ * (g' * (t * x * t⁻¹) * g'⁻¹) * t := by rw [h1]
    _ = (t⁻¹ * g' * t) * x * (t⁻¹ * g' * t)⁻¹ := by group

theorem false_of_pair_outer (h56 : AsB56) (hV : ∀ v : V, v * v = 1) {Γ L₁ L₂ : Subgroup (MulAut V)}
    {t : MulAut V} (P : PairData Γ L₁ L₂ t) {s : MulAut V} (hs : s ∈ Γ)
    (hs₁ : ∀ x ∈ L₁, s * x * s⁻¹ ∈ L₁) (hs₁' : ∀ x ∈ L₁, s⁻¹ * x * s ∈ L₁)
    (hout : ¬ ∃ g ∈ L₁, ∀ x ∈ L₁, s * x * s⁻¹ = g * x * g⁻¹) : False := by
  obtain ⟨A, hA⟩ := P.off
  have hJ : ffJ Γ ≠ ⊥ := fun h => hA.2.1 (le_bot_iff.mp (h ▸ B19.le_ffJ hA))
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  have hLJ := pair_le_ffJ P hJ
  have hL₁J : L₁ ≤ ffJ Γ := le_sup_left.trans hLJ
  have hL₂J : L₂ ≤ ffJ Γ := le_sup_right.trans hLJ
  have hsN : s ∈ Subgroup.normalizer (L₁ : Set (MulAut V)) := mem_normalizer_of_both hs₁ hs₁'
  have hs'N : t * s * t⁻¹ ∈ Subgroup.normalizer (L₂ : Set (MulAut V)) := P.conj_mem hs₁ hs₁'
  have hout' := P.outer_swap hout
  have hsC : ∀ c ∈ fixV (ffJ Γ), s c ∈ fixV (ffJ Γ) := fun c hc =>
    fixV_invariant_of_normalizer (FFL.le_normalizer_ffJ Γ hs) hc
  have hsC' : ∀ c ∈ fixV (ffJ Γ), s⁻¹ c ∈ fixV (ffJ Γ) := fun c hc =>
    fixV_invariant_of_normalizer (Subgroup.inv_mem _ (FFL.le_normalizer_ffJ Γ hs)) hc
  have hs'Γ : t * s * t⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem P.tΓ hs) (Γ.inv_mem P.tΓ)
  have hs'C : ∀ c ∈ fixV (ffJ Γ), (t * s * t⁻¹) c ∈ fixV (ffJ Γ) := fun c hc =>
    fixV_invariant_of_normalizer (FFL.le_normalizer_ffJ Γ hs'Γ) hc
  have hs'C' : ∀ c ∈ fixV (ffJ Γ), (t * s * t⁻¹)⁻¹ c ∈ fixV (ffJ Γ) := fun c hc =>
    fixV_invariant_of_normalizer (Subgroup.inv_mem _ (FFL.le_normalizer_ffJ Γ hs'Γ)) hc
  rcases h56 V hV2 (ffJ Γ) hJ (pair_b53 P) with ⟨hqF, -, -⟩ | h2 | h3 | h4 | h5
  · exact pair_case1_false P hJ hqF
  · exact FFL.false_of_case2 hL₁J (by rw [P.c₁]; norm_num) h2
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hcomm, hf₁, hf₂, W₁, W₂, -, -, hinv₁, hinv₂, hWsup, hWinf, hp₁, hp₂⟩ := h3
    obtain ⟨hsplit, α, β, hα, hβ⟩ := pair_split P hJ hsup hcomm hinf
      (FFL.ne_bot_of_factorList hf₁) (FFL.ne_bot_of_factorList hf₂)
    have h₁ := factor_card_168 hf₁ hα
    have h₂ := factor_card_168 hf₂ hβ
    rcases hsplit with ⟨a, -⟩ | ⟨a, -⟩
    · have hG₁ : L₁ = G₁ := Subgroup.eq_of_le_of_card_ge a (by rw [h₁, P.c₁])
      rw [← hG₁] at hp₁
      exact piece_false P.c₁ hp₁ hWsup hWinf (fun l hl w hw => hinv₂ ⟨l, hL₁J hl⟩ w hw) hsN hsC hsC' hout
    · have hG₂ : L₁ = G₂ := Subgroup.eq_of_le_of_card_ge a (by rw [h₂, P.c₁])
      rw [← hG₂] at hp₂
      exact piece_false P.c₁ hp₂ (by rw [sup_comm]; exact hWsup) (by rw [inf_comm]; exact hWinf)
        (fun l hl w hw => hinv₁ ⟨l, hL₁J hl⟩ w hw) hsN hsC hsC' hout
  · exact pair_case4_false P hJ h4
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e₁⟩, -, -, h₂⟩ := h5
    have hne₁ : G₁ ≠ ⊥ := by
      have := FFL.nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
      exact FFL.ne_bot_of_mulEquiv e₁
    have hne₂ : G₂ ≠ ⊥ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, -, π, hπ⟩
      · have := FFL.nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
        exact FFL.ne_bot_of_mulEquiv e₂
      · have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
        have := FFL.nontrivial_statedSL le_rfl K
        intro hb
        subst hb
        obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(StatedSL 2 K)
        exact hxy (hinj (Subsingleton.elim _ _))
    obtain ⟨hsplit, α, β, hα, hβ⟩ := pair_split P hJ hsup hcomm hinf hne₁ hne₂
    have c₁ : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    have hDS : ∃ k, k ≤ 2 ∧ DirectSumOfCopies G₂ (commV G₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k := by
      rcases h₂ with ⟨-, k, hk, hD⟩ | ⟨n, K, _, _, hK, π, hπ⟩
      · exact ⟨k, hk, hD⟩
      · exfalso
        have h1 := card_eq_of_nat_realizes1527d hπ
        rw [card_statedSL_two1527d, hK, hβ] at h1
        exact sl2_ne_168_two_pow (FFL.one_le_of_card hK) h1.symm
    have c₂ : Nat.card ↥G₂ = 168 := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, hK, π, hπ⟩
      · rw [Nat.card_congr e₂.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
        norm_num
      · exfalso
        have h1 := card_eq_of_nat_realizes1527d hπ
        rw [card_statedSL_two1527d, hK, hβ] at h1
        exact sl2_ne_168_two_pow (FFL.one_le_of_card hK) h1.symm
    obtain ⟨k, hk, hD⟩ := hDS
    rcases hsplit with ⟨-, b⟩ | ⟨a, -⟩
    · have hG₂ : L₂ = G₂ := Subgroup.eq_of_le_of_card_ge b (by rw [c₂, P.c₂])
      rw [← hG₂] at hD
      exact direct_false P.c₂ hk hD hs'N hout'
    · have hG₂ : L₁ = G₂ := Subgroup.eq_of_le_of_card_ge a (by rw [c₂, P.c₁])
      rw [← hG₂] at hD
      exact direct_false P.c₁ hk hD hsN hout

end PairMain

end LRed5

end CFSG.Quasithin
