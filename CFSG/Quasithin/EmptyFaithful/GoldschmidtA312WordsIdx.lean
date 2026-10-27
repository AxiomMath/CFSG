module

public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.Quasithin.A312Words

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure IdxTwoData (Y : Subgroup Γ) (ol : List Γ) (t : Γ) : Prop where
  mem : ∀ g ∈ ol, g ∈ Y
  odd : ∀ g ∈ ol, ∃ m, m % 2 = 1 ∧ g ^ m = 1
  inv : ∀ g ∈ ol, g⁻¹ ∈ ol
  tmem : t ∈ Y
  tsq : t * t = 1
  gen : Y ≤ Subgroup.closure {g | g ∈ ol ++ [t]}

theorem le_perfectCore_of_lFamily' {T B : Subgroup Γ} (hB : B ∈ lFamily T) :
    B ≤ perfectCore (B ⊔ T) := by
  have hBM : B ∈ cComp (B ⊔ T) := hB
  calc B = perfectCore B := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hBM)).symm
    _ ≤ perfectCore (B ⊔ T) := perfectCore_mono (le_of_mem_cComp hBM)

theorem odd_mem_perfectCore' {T B : Subgroup Γ} (hT : IsPGroup 2 T) (hB : B ∈ lFamily T) {x : Γ}
    (hx : x ∈ B ⊔ T) {m : ℕ} (hm : m % 2 = 1) (hxm : x ^ m = 1) : x ∈ perfectCore (B ⊔ T) := by
  have hBA : B ≤ perfectCore (B ⊔ T) := le_perfectCore_of_lFamily' hB
  have hTZ : T ≤ B ⊔ T := le_sup_right
  have hBZ : B ≤ B ⊔ T := le_sup_left
  have hnorm : ((perfectCore (B ⊔ T)).subgroupOf (B ⊔ T)).Normal := perfectCore_normal _
  set N : Subgroup ↥(B ⊔ T) := (perfectCore (B ⊔ T)).subgroupOf (B ⊔ T) with hN
  have hsup : B.subgroupOf (B ⊔ T) ⊔ T.subgroupOf (B ⊔ T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBZ hTZ, Subgroup.subgroupOf_self]
  have hmapB : (B.subgroupOf (B ⊔ T)).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact fun b hb => hBA hb
  have htop : (T.subgroupOf (B ⊔ T)).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
    rw [Subgroup.map_sup, hmapB, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1
  have hT' : IsPGroup 2 ↥(T.subgroupOf (B ⊔ T)) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTZ).symm
  have hQ : IsPGroup 2 (↥(B ⊔ T) ⧸ N) := by
    refine hT'.of_surjective ((QuotientGroup.mk' N).comp (T.subgroupOf (B ⊔ T)).subtype) fun q => ?_
    have hq : q ∈ (T.subgroupOf (B ⊔ T)).map (QuotientGroup.mk' N) := by
      rw [htop]; exact Subgroup.mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hg : (⟨x, hx⟩ : ↥(B ⊔ T)) ^ m = 1 := Subtype.ext (by simpa using hxm)
  exact mem_of_pow_eq_one_odd N hQ hm hg

theorem idxTwo_conj_mem {Y W : Subgroup Γ} {ol : List Γ} {t : Γ} (h : IdxTwoData Y ol t)
    (hn : ∀ g ∈ ol ++ [t], ∀ v ∈ W, g⁻¹ * v * g ∈ W) : ∀ y ∈ Y, ∀ w ∈ W, y⁻¹ * w * y ∈ W := by
  have hinvmem : ∀ g ∈ ol ++ [t], g⁻¹ ∈ ol ++ [t] := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact List.mem_append_left _ (h.inv g hg)
    · have : g = t := by simpa using hg
      subst this
      rw [inv_eq_of_mul_eq_one_right h.tsq]
      exact List.mem_append_right _ (List.mem_singleton_self g)
  have hnormG : ∀ g ∈ ol ++ [t], g ∈ Subgroup.normalizer (W : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      simpa using hn g⁻¹ (hinvmem g hg) x hx
    · intro hx
      simpa [mul_assoc] using hn g hg _ hx
  have hYn : Y ≤ Subgroup.normalizer (W : Set Γ) :=
    h.gen.trans ((Subgroup.closure_le _).mpr hnormG)
  intro y hy w hw
  have := (Subgroup.mem_normalizer_iff.mp (hYn (Y.inv_mem hy)) w).mp hw
  simpa using this

variable [Finite Γ]

theorem perfectCore_quotient {S B Y : Subgroup Γ} {ol : List Γ} {t : Γ} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (h : IdxTwoData Y ol t) :
    (∀ g ∈ ol, g ∈ perfectCore Y) ∧ ⁅Y, Y⁆ ≤ perfectCore Y ∧
      Nat.card Y ≤ 2 * Nat.card (perfectCore Y) := by
  subst hY
  have hol : ∀ g ∈ ol, g ∈ perfectCore (B ⊔ S) := fun g hg => by
    obtain ⟨m, hm, hgm⟩ := h.odd g hg
    exact odd_mem_perfectCore' hS hB (h.mem g hg) hm hgm
  have hnorm : ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).Normal := perfectCore_normal _
  set N : Subgroup ↥(B ⊔ S) := (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S) with hN
  let φ : ↥(B ⊔ S) →* ↥(B ⊔ S) ⧸ N := QuotientGroup.mk' N
  let t' : ↥(B ⊔ S) := ⟨t, h.tmem⟩
  have ht'sq : t' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h.tsq)
  have hgen : ∀ g ∈ Subgroup.closure {x | x ∈ ol ++ [t]},
      ∃ hg : g ∈ B ⊔ S, φ ⟨g, hg⟩ ∈ Subgroup.zpowers (φ t') := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : x ∈ ol ∨ x = t := by simpa using hx
      rcases hx' with hx' | rfl
      · refine ⟨h.mem x hx', ?_⟩
        have : φ ⟨x, h.mem x hx'⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (hol x hx')
        rw [this]; exact Subgroup.one_mem _
      · exact ⟨h.tmem, Subgroup.mem_zpowers _⟩
    | one =>
      refine ⟨(B ⊔ S).one_mem, ?_⟩
      have : (⟨1, (B ⊔ S).one_mem⟩ : ↥(B ⊔ S)) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hxz⟩ := ihx
      obtain ⟨hy, hyz⟩ := ihy
      exact ⟨(B ⊔ S).mul_mem hx hy, by
        have : (⟨x * y, (B ⊔ S).mul_mem hx hy⟩ : ↥(B ⊔ S)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [this, map_mul]; exact Subgroup.mul_mem _ hxz hyz⟩
    | inv x _ ihx =>
      obtain ⟨hx, hxz⟩ := ihx
      exact ⟨(B ⊔ S).inv_mem hx, by
        have : (⟨x⁻¹, (B ⊔ S).inv_mem hx⟩ : ↥(B ⊔ S)) = (⟨x, hx⟩ : ↥(B ⊔ S))⁻¹ := rfl
        rw [this, map_inv]; exact Subgroup.inv_mem _ hxz⟩
  have hall : ∀ y : ↥(B ⊔ S), φ y ∈ Subgroup.zpowers (φ t') := fun y => by
    obtain ⟨hy, hyz⟩ := hgen y.1 (h.gen y.2)
    exact hyz
  refine ⟨hol, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 := hall ⟨g₁, hg₁⟩
    have h2 := hall ⟨g₂, hg₂⟩
    have hc : Commute (φ ⟨g₁, hg₁⟩) (φ ⟨g₂, hg₂⟩) := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h1
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp h2
      rw [← ha, ← hb]
      exact Commute.zpow_zpow_self _ _ _
    have h3 : φ ⁅(⟨g₁, hg₁⟩ : ↥(B ⊔ S)), ⟨g₂, hg₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hc
    have h4 : ⁅(⟨g₁, hg₁⟩ : ↥(B ⊔ S)), ⟨g₂, hg₂⟩⁆ ∈ N := (QuotientGroup.eq_one_iff _).mp h3
    exact h4
  · have hcardQ : Nat.card (↥(B ⊔ S) ⧸ N) ≤ 2 := by
      have hle : Nat.card (↥(B ⊔ S) ⧸ N) ≤ Nat.card (Subgroup.zpowers (φ t')) := by
        refine Nat.card_le_card_of_injective
          (fun q => ⟨q, ?_⟩ : (↥(B ⊔ S) ⧸ N) → Subgroup.zpowers (φ t')) ?_
        · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
          exact hall y
        · intro q1 q2 hq
          exact congrArg Subtype.val hq
      rw [Nat.card_zpowers] at hle
      have h2 : orderOf (φ t') ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [← map_pow, ht'sq, map_one])
      exact hle.trans h2
    have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h6 : Nat.card N = Nat.card (perfectCore (B ⊔ S)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (perfectCore_le _)).toEquiv
    rw [h5, h6]
    exact Nat.mul_le_mul_right _ hcardQ

end CFSG.Quasithin.A312Words
