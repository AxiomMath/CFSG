module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
import CFSG.RankThree.PartTwo.Sec13.Item13Plane

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item2130LStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ¬ IsIrreducibleOn (wStar A) →
      c ∉ L ∧ Nat.card A = 3 * Nat.card (A ⊓ L : Subgroup G) ∧
        9 ≤ Nat.card (A ⊓ L : Subgroup G) ∧ Nat.card A ≤ 3 ^ 4 ∧
        ∀ X : Subgroup G, X ≤ A ⊓ L →
          L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) →
            X = ⊥ ∨ X = A ⊓ L

@[expose] def Item2130Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B N : Subgroup G),
    CFSG.Assembly.IsElemAbelian 3 A → B ≤ A → Nat.card A = 3 * Nat.card B →
    9 ≤ Nat.card B → Nat.card A ≤ 3 ^ 4 → N ≤ Subgroup.normalizer (A : Set G) →
    N ≤ Subgroup.normalizer (B : Set G) →
    (∀ Y : Subgroup G, Y ≤ B → N ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = B) →
    (∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → (∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ B) →
      ∀ a ∈ A, w * a * w⁻¹ = a) →
    ∃ X : Subgroup G, X ≤ A ∧ X ⊓ B = ⊥ ∧ Nat.card X = 3 ∧
      N ≤ Subgroup.normalizer (X : Set G)

@[expose] def Item2130Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → c ∉ L → Nat.card A = 3 * Nat.card (A ⊓ L : Subgroup G) →
    9 ≤ Nat.card (A ⊓ L : Subgroup G) →
    (∀ X : Subgroup G, X ≤ A ⊓ L →
      L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) →
        X = ⊥ ∨ X = A ⊓ L) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
    (∀ b ∈ A ⊓ L, ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∀ x ∈ A ⊓ L, w * x * w⁻¹ = x) ∧ w * c * w⁻¹ = c * b) →
    False

namespace Item2130Proof

variable {G : Type} [Group G]

theorem exists_of_not_isIrreducibleOn {A : Subgroup G} (h : ¬ IsIrreducibleOn (wStar A)) :
    ∃ X : Subgroup G, X ≤ A ∧ X ≠ ⊥ ∧ X ≠ A ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  simp only [IsIrreducibleOn, not_forall, not_or, exists_prop] at h
  obtain ⟨B', hinv, hB1, hBt⟩ := h
  refine ⟨B'.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h0
    apply hB1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective] at h0
  · intro hA
    apply hBt
    rw [eq_top_iff]
    intro a _
    have : (a : G) ∈ B'.map A.subtype := by
      rw [hA]
      exact a.2
    obtain ⟨b, hb, hba⟩ := this
    rwa [Subtype.ext hba] at hb
  · intro w hw
    have hφ := hinv _ ⟨⟨w, hw⟩, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : A.normalizerMonoidHom ⟨w, hw⟩ b ∈ B'.map
          (A.normalizerMonoidHom ⟨w, hw⟩).toMonoidHom := ⟨b, hb, rfl⟩
      rw [hφ] at hb'
      exact ⟨_, hb', rfl⟩
    · rintro ⟨b', hb', hb'x⟩
      have hb'' : b' ∈ B'.map (A.normalizerMonoidHom ⟨w, hw⟩).toMonoidHom := by rwa [hφ]
      obtain ⟨b, hb, hbb'⟩ := hb''
      have e : w * (b : G) * w⁻¹ = w * x * w⁻¹ := by
        rw [← hb'x, ← hbb']
        rfl
      exact ⟨b, hb, mul_left_cancel (mul_right_cancel e)⟩

@[expose] def tSet (A B : Subgroup G) (c : G) : Subgroup G where
  carrier := {b | b ∈ B ∧ ∃ w ∈ Subgroup.normalizer (A : Set G),
    (∀ x ∈ B, w * x * w⁻¹ = x) ∧ w * c * w⁻¹ = c * b}
  mul_mem' := by
    rintro b₁ b₂ ⟨hb₁, w₁, hw₁A, hw₁B, hw₁c⟩ ⟨hb₂, w₂, hw₂A, hw₂B, hw₂c⟩
    refine ⟨B.mul_mem hb₁ hb₂, w₁ * w₂, Subgroup.mul_mem _ hw₁A hw₂A, fun x hx => ?_, ?_⟩
    · calc w₁ * w₂ * x * (w₁ * w₂)⁻¹ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ := by group
        _ = x := by rw [hw₂B x hx, hw₁B x hx]
    · calc w₁ * w₂ * c * (w₁ * w₂)⁻¹ = w₁ * (w₂ * c * w₂⁻¹) * w₁⁻¹ := by group
        _ = (w₁ * c * w₁⁻¹) * (w₁ * b₂ * w₁⁻¹) := by rw [hw₂c]; group
        _ = c * (b₁ * b₂) := by rw [hw₁c, hw₁B b₂ hb₂]; group
  one_mem' := ⟨B.one_mem, 1, Subgroup.one_mem _, fun x _ => by group, by group⟩
  inv_mem' := by
    rintro b ⟨hb, w, hwA, hwB, hwc⟩
    refine ⟨B.inv_mem hb, w⁻¹, Subgroup.inv_mem _ hwA, fun x hx => ?_, ?_⟩
    · have := hwB x hx
      calc w⁻¹ * x * w⁻¹⁻¹ = w⁻¹ * (w * x * w⁻¹) * w := by rw [this]; group
        _ = x := by group
    · have hb' : w⁻¹ * b * w = b := by
        have := hwB b hb
        calc w⁻¹ * b * w = w⁻¹ * (w * b * w⁻¹) * w := by rw [this]
          _ = b := by group
      calc w⁻¹ * c * w⁻¹⁻¹ = w⁻¹ * (w * c * w⁻¹ * b⁻¹) * w := by rw [hwc]; group
        _ = w⁻¹ * (w * c * w⁻¹) * w * (w⁻¹ * b * w)⁻¹ := by group
        _ = c * b⁻¹ := by rw [hb']; group

theorem tSet_le (A B : Subgroup G) (c : G) : tSet A B c ≤ B := fun _ h => h.1

theorem le_normalizer_tSet {A B K : Subgroup G} {c : G}
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hKc : ∀ k ∈ K, k * c * k⁻¹ = c) :
    K ≤ Subgroup.normalizer ((tSet A B c : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, ∀ b ∈ tSet A B c, k * b * k⁻¹ ∈ tSet A B c := by
    rintro k hk b ⟨hb, w, hwA, hwB, hwc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKB hk) b).mp hb, k * w * k⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKA hk) hwA) (Subgroup.inv_mem _ (hKA hk)),
      fun x hx => ?_, ?_⟩
    · have hx' : k⁻¹ * x * k⁻¹⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKB hk)) x).mp hx
      have := hwB _ hx'
      calc k * w * k⁻¹ * x * (k * w * k⁻¹)⁻¹ = k * (w * (k⁻¹ * x * k⁻¹⁻¹) * w⁻¹) * k⁻¹ := by
            group
        _ = x := by rw [this]; group
    · have hkc := hKc k hk
      have hkc' : k⁻¹ * c * k = c := by
        calc k⁻¹ * c * k = k⁻¹ * (k * c * k⁻¹) * k := by rw [hkc]
          _ = c := by group
      calc k * w * k⁻¹ * c * (k * w * k⁻¹)⁻¹ = k * (w * (k⁻¹ * c * k) * w⁻¹) * k⁻¹ := by group
        _ = k * (c * b) * k⁻¹ := by rw [hkc', hwc]
        _ = (k * c * k⁻¹) * (k * b * k⁻¹) := by group
        _ = c * (k * b * k⁻¹) := by rw [hkc]
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key k hk b, fun h => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ h
  have e : k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b := by group
  rwa [e] at this

variable [Finite G]

theorem eq_or_eq_of_le_of_le {A B X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hcard : Nat.card A = 3 * Nat.card B) : X = B ∨ X = A := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBX
  have hXd : Nat.card X ∣ Nat.card A := Subgroup.card_dvd_of_le hXA
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hk3 : k ∣ 3 := by
    rw [hk, hcard, mul_comm 3] at hXd
    exact Nat.dvd_of_mul_dvd_mul_left hBpos hXd
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hBX (le_of_eq (by rw [hk, mul_one]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hXA (le_of_eq (by rw [hk, hcard]; ring))

theorem eq_zpowers_sup {A B : Subgroup G} {c : G} (hcA : c ∈ A) (hBA : B ≤ A) (hcB : c ∉ B)
    (hcard : Nat.card A = 3 * Nat.card B) : A = Subgroup.zpowers c ⊔ B := by
  rcases eq_or_eq_of_le_of_le (le_sup_right : B ≤ Subgroup.zpowers c ⊔ B)
      (sup_le (Subgroup.zpowers_le.mpr hcA) hBA) hcard with h | h
  · have hc : c ∈ Subgroup.zpowers c ⊔ B :=
      (le_sup_left : Subgroup.zpowers c ≤ Subgroup.zpowers c ⊔ B) (Subgroup.mem_zpowers c)
    rw [h] at hc
    exact absurd hc hcB
  · exact h.symm

theorem card_mul_card_le {A B X : Subgroup G} (hXA : X ≤ A) (hBA : B ≤ A) (hXB : X ⊓ B = ⊥) :
    Nat.card X * Nat.card B ≤ Nat.card A := by
  have hinj : Function.Injective (fun p : X × B =>
      (⟨(p.1 : G) * p.2, A.mul_mem (hXA p.1.2) (hBA p.2.2)⟩ : A)) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
    have e : x * y = x' * y' := congrArg Subtype.val hxy
    have hm : x'⁻¹ * x ∈ X ⊓ B := ⟨X.mul_mem (X.inv_mem hx') hx, by
      have : x'⁻¹ * x = y' * y⁻¹ := by
        calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
          _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [e]
          _ = y' * y⁻¹ := by group
      rw [this]
      exact B.mul_mem hy' (B.inv_mem hy)⟩
    rw [hXB, Subgroup.mem_bot, inv_mul_eq_one] at hm
    subst hm
    have : y = y' := mul_left_cancel e
    subst this
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

theorem eq_of_normalized {A B K X : Subgroup G} {c : G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hBA : B ≤ A) (hcB : c ∉ B) (hcard : Nat.card A = 3 * Nat.card B)
    (hB9 : 9 ≤ Nat.card B) (hKc : ∀ k ∈ K, k * c * k⁻¹ = c)
    (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ B → K ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = B)
    (hXA : X ≤ A) (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    X = ⊥ ∨ X = Subgroup.zpowers c ∨ X = B ∨ X = A := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hKXB : K ≤ Subgroup.normalizer ((X ⊓ B : Subgroup G) : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp (hKX hk) x,
      ← Subgroup.mem_normalizer_iff.mp (hKB hk) x]
  rcases hirr _ inf_le_right hKXB with h | h
  ·
    by_cases hX1 : X = ⊥
    · exact Or.inl hX1
    right; left
    obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
    have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
    obtain ⟨i, hi, b, hb, hxcb⟩ :=
      Sec13.exists_pow_mul_of_mem hA hcA (eq_zpowers_sup hcA hBA hcB hcard) (hXA hxX)
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hxcb
      have : x ∈ X ⊓ B := ⟨hxX, hxcb ▸ hb⟩
      rw [h, Subgroup.mem_bot] at this
      exact hx1' this
    have hKb : ∀ k ∈ K, k * b * k⁻¹ = b := by
      intro k hk
      have hkx : k * x * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKX hk) x).mp hxX
      have hkci : k * c ^ i * k⁻¹ = c ^ i := by
        have hkc : k * c = c * k := by
          have := hKc k hk
          calc k * c = k * c * k⁻¹ * k := by group
            _ = c * k := by rw [this]
        rw [(Commute.pow_right hkc i).eq, mul_inv_cancel_right]
      have hkbB : k * b * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKB hk) b).mp hb
      have hexp : k * x * k⁻¹ = c ^ i * (k * b * k⁻¹) := by
        rw [hxcb]
        calc k * (c ^ i * b) * k⁻¹ = (k * c ^ i * k⁻¹) * (k * b * k⁻¹) := by group
          _ = c ^ i * (k * b * k⁻¹) := by rw [hkci]
      have hmem : (k * x * k⁻¹) * x⁻¹ ∈ X ⊓ B := by
        refine ⟨X.mul_mem hkx (X.inv_mem hxX), ?_⟩
        have : (k * x * k⁻¹) * x⁻¹ = (k * b * k⁻¹) * b⁻¹ := by
          rw [hexp, hxcb]
          have hc' : c ^ i ∈ A := A.pow_mem hcA i
          have hkb' : k * b * k⁻¹ ∈ A := hBA hkbB
          calc c ^ i * (k * b * k⁻¹) * (c ^ i * b)⁻¹
              = (k * b * k⁻¹) * c ^ i * (b * c ^ i)⁻¹ := by
                rw [hcomm _ hc' _ hkb', hcomm _ hc' _ (hBA hb)]
            _ = (k * b * k⁻¹) * b⁻¹ := by group
        rw [this]
        exact B.mul_mem hkbB (B.inv_mem hb)
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      rw [hexp, hxcb] at hmem
      exact mul_left_cancel hmem
    have hb1 : b = 1 := by
      have hKzb : K ≤ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
        intro k hk
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨n, rfl⟩
          refine ⟨n, ?_⟩
          change b ^ n = k * b ^ n * k⁻¹
          rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hKb k hk]
        · rintro ⟨n, hn⟩
          refine ⟨n, ?_⟩
          change b ^ n = y
          have h1 : k * b ^ n * k⁻¹ = b ^ n := by
            rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hKb k hk]
          have h2 : k * y * k⁻¹ = k * b ^ n * k⁻¹ := by rw [h1]; exact hn.symm
          exact (mul_left_cancel (mul_right_cancel h2)).symm
      rcases hirr _ (Subgroup.zpowers_le.mpr hb) hKzb with h' | h'
      · exact Subgroup.zpowers_eq_bot.mp h'
      · exfalso
        have hb3 : b ^ 3 = 1 := hA.2 b (hBA hb)
        have : Nat.card B ≤ 3 := by
          rw [← h', Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb3)
        omega
    rw [hb1, mul_one] at hxcb
    have hcX : c ∈ X := by
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · rw [pow_one] at hxcb
        exact hxcb ▸ hxX
      · have : c = x ^ 2 := by
          rw [hxcb]
          calc c = c * c ^ 3 := by rw [hc3, mul_one]
            _ = (c ^ 2) ^ 2 := by group
        rw [this]
        exact X.pow_mem hxX 2
    have hcle : Subgroup.zpowers c ≤ X := Subgroup.zpowers_le.mpr hcX
    have hXcard : Nat.card X ≤ 3 := by
      have h1 := card_mul_card_le hXA hBA h
      rw [hcard] at h1
      have hBpos : 0 < Nat.card B := Nat.card_pos
      exact Nat.le_of_mul_le_mul_right h1 hBpos
    have hc1 : c ≠ 1 := fun h1 => hcB (h1 ▸ B.one_mem)
    have hcord : orderOf c = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc3) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hc1
      · exact h1
    exact (Subgroup.eq_of_le_of_card_ge hcle (by rw [Nat.card_zpowers, hcord]; exact hXcard)).symm
  ·
    have hBX : B ≤ X := by
      rw [← h]
      exact inf_le_left
    rcases eq_or_eq_of_le_of_le hBX hXA hcard with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

end Item2130Proof

open Item2130Proof

theorem item2130_of (h2115 : Item2115) (hL : Item2130LStar) (hS : Item2130Split)
    (hLoc : Item2130Local) : Item2130 := by
  intro G _ _ A E U c L hpair
  by_contra hred
  obtain ⟨hcL, hcard, hB9, hA81, hirr⟩ := hL G A E U c L hpair hred
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hcA : c ∈ A := hEA hpairs.1.1
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := hpairs.2.2.1.1
    rw [← hL']
    exact Subgroup.map_subtype_le _
  set B : Subgroup G := A ⊓ L with hBdef
  set W : Subgroup G := Subgroup.normalizer (A : Set G) with hWdef
  set K : Subgroup G := L ⊓ W with hKdef
  have hBA : B ≤ A := inf_le_left
  have hcB : c ∉ B := fun h => hcL h.2
  have hKc : ∀ k ∈ K, k * c * k⁻¹ = c := fun k hk => by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hLc hk.1)
    rw [this, mul_inv_cancel_right]
  have hKW : K ≤ W := inf_le_right
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hBdef, Subgroup.mem_inf, Subgroup.mem_inf,
      ← Subgroup.mem_normalizer_iff.mp hk.2 x]
    constructor
    · rintro ⟨hxA, hxL⟩
      exact ⟨hxA, L.mul_mem (L.mul_mem hk.1 hxL) (L.inv_mem hk.1)⟩
    · rintro ⟨hxA, hxL⟩
      refine ⟨hxA, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hk.1) hxL) hk.1
      simpa [mul_assoc] using this
  have hcW : ¬ W ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    h2115 G A E U c L hpair
  have hclass : ∀ X : Subgroup G, X ≤ A → K ≤ Subgroup.normalizer (X : Set G) →
      X = ⊥ ∨ X = Subgroup.zpowers c ∨ X = B ∨ X = A := fun X hXA hKX =>
    eq_of_normalized hA hcA hBA hcB hcard hB9 hKc hKB hirr hXA hKX
  obtain ⟨X, hXA, hX1, hXA', hWX⟩ := exists_of_not_isIrreducibleOn hred
  have hWB : W ≤ Subgroup.normalizer (B : Set G) := by
    rcases hclass X hXA (hKW.trans hWX) with h | h | h | h
    · exact absurd h hX1
    · exact absurd (h ▸ hWX) hcW
    · exact h ▸ hWX
    · exact absurd h hXA'
  rcases hirr (tSet A B c) (tSet_le A B c) (le_normalizer_tSet hKW hKB hKc) with hT | hT
  ·
    have hWirr : ∀ Y : Subgroup G, Y ≤ B → W ≤ Subgroup.normalizer (Y : Set G) →
        Y = ⊥ ∨ Y = B := fun Y hYB hWY => hirr Y hYB (hKW.trans hWY)
    have htriv : ∀ w ∈ W, (∀ b ∈ B, w * b * w⁻¹ = b) → (∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ B) →
        ∀ a ∈ A, w * a * w⁻¹ = a := by
      intro w hw hwB hwA
      have hwcA : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA
      have hbB : c⁻¹ * (w * c * w⁻¹) ∈ B := by
        have h1 := hwA c hcA
        have hcomm : (w * c * w⁻¹) * c⁻¹ = c⁻¹ * (w * c * w⁻¹) :=
          congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hwcA⟩ ⟨_, A.inv_mem hcA⟩)
        rwa [hcomm] at h1
      have hbT : c⁻¹ * (w * c * w⁻¹) ∈ tSet A B c :=
        ⟨hbB, w, hw, hwB, by group⟩
      rw [hT, Subgroup.mem_bot, inv_mul_eq_one] at hbT
      have hwc : w * c * w⁻¹ = c := hbT.symm
      intro a ha
      obtain ⟨i, -, b, hb, rfl⟩ :=
        Sec13.exists_pow_mul_of_mem hA hcA (eq_zpowers_sup hcA hBA hcB hcard) ha
      calc w * (c ^ i * b) * w⁻¹ = (w * c * w⁻¹) ^ i * (w * b * w⁻¹) := by
            rw [← MulAut.conj_apply, map_mul, map_pow]
            rfl
        _ = c ^ i * b := by rw [hwc, hwB b hb]
    obtain ⟨Y, hYA, hYB, hY3, hWY⟩ :=
      hS G A B W hA hBA hcard hB9 hA81 le_rfl hWB hWirr htriv
    rcases hclass Y hYA (hKW.trans hWY) with h | h | h | h
    · rw [h, Subgroup.card_bot] at hY3
      omega
    · exact hcW (h ▸ hWY)
    · rw [h, inf_idem] at hYB
      rw [hYB, Subgroup.card_bot] at hB9
      omega
    · rw [h, hcard] at hY3
      omega
  ·
    refine hLoc G A E U c L hpair hcL hcard hB9 hirr hWB fun b hb => ?_
    have hbT : b ∈ tSet A B c := by
      rw [hT]
      exact hb
    obtain ⟨-, w, hw, hwB, hwc⟩ := hbT
    exact ⟨w, hw, hwB, hwc⟩

end CFSG.RankThree.PartTwo.Sec21
