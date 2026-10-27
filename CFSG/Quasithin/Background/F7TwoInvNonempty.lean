module

public import CFSG.Quasithin.Background.F7TwoInvBasic
import CFSG.GroupTheory.BaerSuzuki

public section

namespace CFSG.Quasithin.F7Two

theorem isPGroup_closure_pair_of_involutions {G : Type*} [Group G] {t s : G} (htt : t * t = 1)
    (hss : s * s = 1) {k : ℕ} (hk : (t * s) ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.closure ({t, s} : Set G)) := by
  set r : G := t * s with hr
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have htr : t * r * t⁻¹ = r⁻¹ := by
    calc t * r * t⁻¹ = (t * t) * s * t := by rw [hr, hti]; group
      _ = s * t := by rw [htt]; group
      _ = r⁻¹ := by rw [hr, mul_inv_rev, hti, hsi]
  have hconj : ∀ i : ℤ, r ^ i * t = t * r ^ (-i) := by
    intro i
    have h1 : t * r ^ i * t = r ^ (-i) := by
      have : t * r ^ i * t⁻¹ = r ^ (-i) := by rw [← conj_zpow, htr, inv_zpow']
      rwa [hti] at this
    calc r ^ i * t = t * (t * r ^ i * t) := by
          rw [show t * (t * r ^ i * t) = (t * t) * r ^ i * t by group, htt]; group
      _ = t * r ^ (-i) := by rw [h1]
  have hmain : ∀ z ∈ Subgroup.closure ({t, s} : Set G), ∃ i : ℤ, z = r ^ i ∨ z = t * r ^ i := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨0, Or.inr (by simp)⟩
      · rw [Set.mem_singleton_iff] at hx
        refine ⟨1, Or.inr ?_⟩
        rw [hx, zpow_one, hr, ← mul_assoc, htt, one_mul]
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy
      · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
      · refine ⟨j - i, Or.inr ?_⟩
        rw [hi, hj, ← mul_assoc, hconj, mul_assoc, ← zpow_add, neg_add_eq_sub]
      · exact ⟨i + j, Or.inr (by rw [hi, hj, mul_assoc, ← zpow_add])⟩
      · refine ⟨j - i, Or.inl ?_⟩
        rw [hi, hj, mul_assoc, ← mul_assoc (r ^ i), hconj, mul_assoc t, ← mul_assoc t,
          ← mul_assoc (t * t), htt, one_mul, ← zpow_add, neg_add_eq_sub]
    | inv x _ hx =>
      obtain ⟨i, hi | hi⟩ := hx
      · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
      · refine ⟨i, Or.inr ?_⟩
        rw [hi, mul_inv_rev, hti, ← zpow_neg, hconj, neg_neg]
  intro z
  obtain ⟨i, hi | hi⟩ := hmain z z.2
  · refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  · refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [hi]
    calc (t * r ^ i) ^ 2 = t * (r ^ i * t) * r ^ i := by rw [pow_two]; group
      _ = (t * t) * r ^ (-i) * r ^ i := by rw [hconj]; group
      _ = 1 := by rw [htt, one_mul, ← zpow_add, neg_add_cancel, zpow_zero]

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} {a : Γ}

theorem mem_sup_zpowers_iff (ha2 : a * a = 1) (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) {g : Γ} :
    g ∈ L ⊔ Subgroup.zpowers a ↔ ∃ l ∈ L, g = l ∨ g = l * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  constructor
  · intro hg
    have hsup : L ⊔ Subgroup.zpowers a = Subgroup.closure ((L : Set Γ) ∪ {a}) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
    rw [hsup] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, Or.inl rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨1, L.one_mem, Or.inr (by rw [hx, one_mul])⟩
    | one => exact ⟨1, L.one_mem, Or.inl rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨l₁, hl₁, hx | hx⟩ := hx <;> obtain ⟨l₂, hl₂, hy | hy⟩ := hy
      · exact ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, Or.inl (by rw [hx, hy])⟩
      · exact ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, Or.inr (by rw [hx, hy, mul_assoc])⟩
      · refine ⟨l₁ * (a * l₂ * a⁻¹), L.mul_mem hl₁ (haL l₂ hl₂), Or.inr ?_⟩
        rw [hx, hy]
        group
      · refine ⟨l₁ * (a * l₂ * a⁻¹), L.mul_mem hl₁ (haL l₂ hl₂), Or.inl ?_⟩
        rw [hx, hy]
        calc l₁ * a * (l₂ * a) = l₁ * (a * l₂ * a⁻¹) * (a * a) := by group
          _ = l₁ * (a * l₂ * a⁻¹) := by rw [ha2, mul_one]
    | inv x _ hx =>
      obtain ⟨l, hl, hx | hx⟩ := hx
      · exact ⟨l⁻¹, L.inv_mem hl, Or.inl (by rw [hx])⟩
      · refine ⟨a * l⁻¹ * a⁻¹, haL _ (L.inv_mem hl), Or.inr ?_⟩
        calc x⁻¹ = (l * a)⁻¹ := by rw [hx]
          _ = a⁻¹ * l⁻¹ := mul_inv_rev l a
          _ = a * l⁻¹ := by rw [hai]
          _ = a * l⁻¹ * a⁻¹ * a := by group
  · rintro ⟨l, hl, rfl | rfl⟩
    · exact Subgroup.mem_sup_left hl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))

theorem eq_bot_or_eq_of_normalized (hsimple : IsSimpleGroup ↥L) {X : Subgroup Γ} (hXL : X ≤ L)
    (hX : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X) : X = ⊥ ∨ X = L := by
  have := hsimple
  have : (X.subgroupOf L).Normal := ⟨fun n hn g => hX g g.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf L) with h | h
  · left
    have hd : Disjoint X L := Subgroup.subgroupOf_eq_bot.mp h
    rw [disjoint_iff, inf_eq_left.mpr hXL] at hd
    exact hd
  · right
    exact le_antisymm hXL (Subgroup.subgroupOf_eq_top.mp h)

theorem commutative_of_isPGroup_of_simple {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hsimple : IsSimpleGroup G) (hG : IsPGroup p G) (x y : G) : x * y = y * x := by
  have := hsimple
  have : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact absurd h (Subgroup.nontrivial_iff_ne_bot _ |>.mp inferInstance)
  · have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem invXi_nonempty [Finite Γ] (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a) :
    (invXi L a).Nonempty := by
  by_contra hempty
  have h2 : ∀ x ∈ L, ∃ n : ℕ, (a * x * a⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by
    intro x hx
    by_contra hcon
    exact hempty ⟨x, mem_invXi_iff.mpr ⟨hx, fun n hn => hcon ⟨n, hn⟩⟩⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  set H : Subgroup Γ := L ⊔ Subgroup.zpowers a with hH
  have haH : a ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hLH : L ≤ H := le_sup_left
  have hHN : ∀ g ∈ H, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    obtain ⟨l₀, hl₀, hg' | hg'⟩ := (mem_sup_zpowers_iff ha2 haL).mp hg
    · rw [hg']
      exact L.mul_mem (L.mul_mem hl₀ hl) (L.inv_mem hl₀)
    · have e : l₀ * a * l * (l₀ * a)⁻¹ = l₀ * (a * l * a⁻¹) * l₀⁻¹ := by group
      rw [hg', e]
      exact L.mul_mem (L.mul_mem hl₀ (haL l hl)) (L.inv_mem hl₀)
  have hconj : ∀ g ∈ H, ∃ l ∈ L, g * a * g⁻¹ = l * a * l⁻¹ := by
    intro g hg
    obtain ⟨l₀, hl₀, hg' | hg'⟩ := (mem_sup_zpowers_iff ha2 haL).mp hg
    · exact ⟨l₀, hl₀, by rw [hg']⟩
    · exact ⟨l₀, hl₀, by rw [hg']; group⟩
  have hBS : (⟨a, haH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    obtain ⟨l, hl, hg⟩ := hconj g g.2
    obtain ⟨n, hn⟩ := h2 l hl
    have htt : (⟨a, haH⟩ : ↥H) * ⟨a, haH⟩ = 1 := Subtype.ext ha2
    have hss : g * ⟨a, haH⟩ * g⁻¹ * (g * ⟨a, haH⟩ * g⁻¹) = 1 := by
      calc g * ⟨a, haH⟩ * g⁻¹ * (g * ⟨a, haH⟩ * g⁻¹)
          = g * (⟨a, haH⟩ * ⟨a, haH⟩) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    refine isPGroup_closure_pair_of_involutions htt hss (k := n) (Subtype.ext ?_)
    have hs : ((g * ⟨a, haH⟩ * g⁻¹ : ↥H) : Γ) = l * a * l⁻¹ := hg
    have e : a * (l * a * l⁻¹) = a * l * a⁻¹ * l⁻¹ := by rw [hai]; group
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, hs, e, hn, Subgroup.coe_one]
  have hQn : (CFSG.pCore 2 ↥H).Normal := CFSG.BaerSuzuki.Helpers.pCore_normal 2
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  set Q : Subgroup Γ := (CFSG.pCore 2 ↥H).map H.subtype with hQ
  have hQ2 : IsPGroup 2 ↥Q := hQp.map H.subtype
  have haQ : a ∈ Q := ⟨⟨a, haH⟩, hBS, rfl⟩
  have hQnorm : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    rintro g hg _ ⟨q, hq, rfl⟩
    exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹, hQn.conj_mem q hq ⟨g, hg⟩, rfl⟩
  have hXnorm : ∀ l ∈ L, ∀ x ∈ Q ⊓ L, l * x * l⁻¹ ∈ Q ⊓ L := fun l hl x hx =>
    ⟨hQnorm l (hLH hl) x hx.1, L.mul_mem (L.mul_mem hl hx.2) (L.inv_mem hl)⟩
  rcases eq_bot_or_eq_of_normalized hsimple inf_le_right hXnorm with hX | hX
  · obtain ⟨x, hxL, hx⟩ := hac
    refine hx ?_
    have hxa : x * a * x⁻¹ ∈ Q := hQnorm x (hLH hxL) a haQ
    have hc : a * x * a⁻¹ * x⁻¹ ∈ Q ⊓ L := by
      refine ⟨?_, comm_mem_of_mem haL hxL⟩
      have e : a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact Q.mul_mem haQ (Q.inv_mem hxa)
    rw [hX, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc
  · have hLQ : L ≤ Q := by
      rw [← hX]
      exact inf_le_left
    obtain ⟨x, y, hxy⟩ := hnonab
    exact hxy (commutative_of_isPGroup_of_simple hsimple (hQ2.to_le hLQ) x y)

end CFSG.Quasithin.F7Two
