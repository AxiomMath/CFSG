module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SecQ

public section

namespace CFSG.Quasithin.H13.SecFix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_le_two_mul_of_forall [Finite G] {K X : Subgroup G} (a : G)
    (h : ∀ x ∈ X, x ∈ K ∨ a⁻¹ * x ∈ K) : Nat.card X ≤ 2 * Nat.card K := by
  classical
  let f : ↥X → ↥K ⊕ ↥K := fun x =>
    if hx : (x : G) ∈ K then Sum.inl ⟨x, hx⟩ else
      Sum.inr ⟨a⁻¹ * x, (h x x.2).resolve_left hx⟩
  have hf : Function.Injective f := by
    intro x x' hxx'
    by_cases hx : (x : G) ∈ K <;> by_cases hx' : (x' : G) ∈ K <;>
      simp only [f, hx, hx', ↓reduceDIte] at hxx'
    · exact Subtype.ext (Subtype.mk.inj (Sum.inl.inj hxx'))
    · exact absurd hxx' Sum.inl_ne_inr
    · exact absurd hxx' Sum.inr_ne_inl
    · exact Subtype.ext (mul_left_cancel (Subtype.mk.inj (Sum.inr.inj hxx')))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_sum, ← two_mul] at this

theorem mem_or_of_mem_sup_zpowers {N : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (N : Set G)) (hw2 : w * w ∈ N) :
    ∀ g ∈ N ⊔ Subgroup.zpowers w, g ∈ N ∨ w⁻¹ * g ∈ N := by
  let T : Subgroup G :=
    { carrier := {g | g ∈ N ∨ w⁻¹ * g ∈ N}
      mul_mem' := by
        rintro a b ha hb
        have hc : ∀ n ∈ N, w⁻¹ * n * w ∈ N := fun n hn => by
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) n).mp hn
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (N.mul_mem ha hb)
        · right
          have := N.mul_mem (hc a ha) hb
          rwa [show w⁻¹ * a * w * (w⁻¹ * b) = w⁻¹ * (a * b) by group] at this
        · right
          have := N.mul_mem ha hb
          rwa [show w⁻¹ * a * b = w⁻¹ * (a * b) by group] at this
        · left
          have := N.mul_mem (N.mul_mem hw2 (hc _ ha)) hb
          rwa [show w * w * (w⁻¹ * (w⁻¹ * a) * w) * (w⁻¹ * b) = a * b by group] at this
      one_mem' := Or.inl N.one_mem
      inv_mem' := by
        rintro a ha
        rcases ha with ha | ha
        · exact Or.inl (N.inv_mem ha)
        · right
          have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) _).mp (N.inv_mem ha)
          have := N.mul_mem h1 (N.inv_mem hw2)
          rwa [show w⁻¹ * (w⁻¹ * a)⁻¹ * w⁻¹⁻¹ * (w * w)⁻¹ = w⁻¹ * a⁻¹ by group] at this }
  have hle : N ⊔ Subgroup.zpowers w ≤ T := by
    refine sup_le (fun n hn => Or.inl hn) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [inv_mul_cancel]; exact N.one_mem)
  exact fun g hg => hle hg

theorem card_sup_zpowers_le [Finite G] {N : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (N : Set G)) (hw2 : w * w ∈ N) :
    Nat.card (N ⊔ Subgroup.zpowers w : Subgroup G) ≤ 2 * Nat.card N :=
  card_le_two_mul_of_forall w (mem_or_of_mem_sup_zpowers hw hw2)

namespace ElemSec

variable {A B : Subgroup G} (h : ElemSec A B)
include h

@[expose] def imSub {U X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ X) : Subgroup G where
  carrier := {w | w ∈ nxt U B X ∧ ∃ u ∈ U, Cg (nxt U B (nxt U B X)) w ⁅x₀, u⁆}
  mul_mem' := by
    rintro a b ⟨ha, u, hu, hau⟩ ⟨hb, v, hv, hbv⟩
    obtain ⟨h1, h2, hA1, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
    refine ⟨Subgroup.mul_mem _ ha hb, u * v, U.mul_mem hu hv, ?_⟩
    refine (Cg.mul hau hbv (hA2 (h1.trans hXA hb))).trans ?_
    exact (h.cg_commutator_mul hBX hXA hUX hUB hx₀ hu hv).symm
  one_mem' := ⟨Subgroup.one_mem _, 1, U.one_mem, by
    rw [commutatorElement_def, mul_one, inv_one, mul_one, mul_inv_cancel]
    exact Cg.refl _ _⟩
  inv_mem' := by
    rintro a ⟨ha, u, hu, hau⟩
    obtain ⟨h1, h2, hA1, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
    refine ⟨Subgroup.inv_mem _ ha, u⁻¹, U.inv_mem hu, ?_⟩
    have hm := h.cg_commutator_mul hBX hXA hUX hUB hx₀ hu (U.inv_mem hu)
    have e0 : ⁅x₀, u * u⁻¹⁆ = 1 := by
      rw [mul_inv_cancel, commutatorElement_def]
      group
    rw [e0] at hm
    have hcA : ⁅x₀, u⁆ ∈ A := h1.trans hXA (commutator_mem_nxt hx₀ hu)
    have hinv : Cg (nxt U B (nxt U B X)) (⁅x₀, u⁆⁻¹) (⁅x₀, u⁻¹⁆) := by
      rw [Cg, inv_inv]
      rw [Cg, inv_one, one_mul] at hm
      exact hm
    exact (hau.inv (hA2 (h1.trans hXA ha))).trans hinv

theorem eta_eq_iff [Finite G] {L X Y : Subgroup G} (hLL : oTwoUpper L = L) (hA2 : IsPGroup 2 A)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hBY : B ≤ Y) (hYX : Y ≤ X) (hXA : X ≤ A)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G)) :
    F112W.eta (L ⊔ A) A X = F112W.eta (L ⊔ A) A Y ↔
      ∀ g ∈ L, ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L ⊔ A with hH
  have hUH : A ≤ H := le_sup_right
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := sup_le hLA Subgroup.le_normalizer
  have hUQ : A ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUH hHA hA2
  have hXn : IsNormalIn H A X := F112W.isNormalIn_of_le_normalizer hXA
    (sup_le hLX (h.le_normalizer (hBY.trans hYX) hXA))
  have hYn : IsNormalIn H A Y := F112W.isNormalIn_of_le_normalizer (hYX.trans hXA)
    (sup_le hLY (h.le_normalizer hBY (hYX.trans hXA)))
  obtain ⟨n, hn⟩ := F112W.exists_isChiefSeriesBetween hYn X hXn hYX
  have hadd := F112W.eta_eq_add hUH hYn hn
  have h17 := F112W.isChiefSeriesBetween_zero_iff hUH hUQ hYn hXn hYX
  have hLH : L ≤ oTwoUpper H := by
    rw [← hLL]
    exact oTwoUpper_mono le_sup_left
  constructor
  · intro heq
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    have hc := h17.mp hn
    intro g hg x hx
    exact mul_mem_of_commutator_le ((Subgroup.commutator_mono le_rfl hLH).trans hc) hg hx
  · intro hcent
    have hsec : H ≤ secCent X Y := by
      refine sup_le (fun g hg => ⟨hLX hg, hLY hg, hcent g hg⟩) (fun a ha => ?_)
      exact ⟨h.le_normalizer (hBY.trans hYX) hXA ha, h.le_normalizer hBY (hYX.trans hXA) ha,
        fun x hx => hBY (h.comm a ha x (hXA hx))⟩
    have h0 := h17.mpr (commutator_le_of_le_secCent ((oTwoUpper_le H).trans hsec))
    have := F112W.isChiefSeriesBetween_unique hUH hYn hn h0
    omega

theorem irred_of_eta [Finite G] {L X Y W : Subgroup G} {y : G} (hLL : oTwoUpper L = L)
    (hA2 : IsPGroup 2 A) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hy3 : ∀ x ∈ A, y ^ 3 * x * (y ^ 3)⁻¹ * x⁻¹ ∈ B) (hyL : y ∈ L)
    (hBY : B ≤ Y) (hYW : Y ≤ W) (hWX : W ≤ X) (hXA : X ≤ A)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hη : F112W.eta (L ⊔ A) A X = F112W.eta (L ⊔ A) A Y + 1)
    (hfix : fixMod y X Y = Y) : W = Y ∨ W = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUH : A ≤ L ⊔ A := le_sup_right
  have hWn : IsNormalIn (L ⊔ A) A W := F112W.isNormalIn_of_le_normalizer (hWX.trans hXA)
    (sup_le hLW (h.le_normalizer (hBY.trans hYW) (hWX.trans hXA)))
  have hYn : IsNormalIn (L ⊔ A) A Y := F112W.isNormalIn_of_le_normalizer ((hYW.trans hWX).trans hXA)
    (sup_le hLY (h.le_normalizer hBY ((hYW.trans hWX).trans hXA)))
  have hXn : IsNormalIn (L ⊔ A) A X := F112W.isNormalIn_of_le_normalizer hXA
    (sup_le hLX (h.le_normalizer ((hBY.trans hYW).trans hWX) hXA))
  have h1 := F112W.eta_le_of_le hUH hYn hWn hYW
  have h2 := F112W.eta_le_of_le hUH hWn hXn hWX
  rcases Nat.eq_or_lt_of_le h1 with h3 | h3
  · left
    have hc := (h.eta_eq_iff hLL hA2 hLA hBY hYW (hWX.trans hXA) hLW hLY).mp h3.symm
    apply le_antisymm _ hYW
    intro w hw
    rw [← hfix]
    exact (h.mem_fixMod_iff hBY (hYW.trans hWX) hXA).mpr ⟨hWX hw, hc y hyL w hw⟩
  · right
    have h4 : F112W.eta (L ⊔ A) A X = F112W.eta (L ⊔ A) A W := by omega
    have hc := (h.eta_eq_iff hLL hA2 hLA (hBY.trans hYW) hWX hXA hLX hLW).mp h4
    apply le_antisymm hWX
    have hfW : fixMod y X W = X := by
      apply le_antisymm (fixMod_le y X W)
      intro x hx
      exact (h.mem_fixMod_iff (hBY.trans hYW) hWX hXA).mpr ⟨hx, hc y hyL x hx⟩
    rw [← hfW, h.fixMod_eq_sup hy3 hBY hYW hWX hXA (hLX hyL) (hLW hyL), hfix]
    exact sup_le hYW le_rfl

omit h in
theorem le_normalizer_of_forall {L H : Subgroup G} (hc : ∀ g ∈ L, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    L ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hc g hg x hx, fun hx => ?_⟩
  have := hc g⁻¹ (L.inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit h in
theorem commutator_one_right' (x : G) : ⁅x, (1 : G)⁆ = 1 := by
  rw [commutatorElement_def]
  group

theorem desc_bound [Finite G] {U O L X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hOU : O ≤ U) (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hLc : ∀ g ∈ L, ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ nxt U B X)
    (hgen : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∃ u₃ ∈ U, ∃ u₄ ∈ U,
      U ≤ Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ O)
    (hirr : ∀ W : Subgroup G, nxt U B (nxt U B X) ≤ W → W ≤ nxt U B X →
      L ≤ Subgroup.normalizer (W : Set G) → W = nxt U B (nxt U B X) ∨ W = nxt U B X)
    (hne : nxt U B (nxt U B X) ≠ nxt U B X) :
    Nat.card (nxt U B X) ≤ 16 * Nat.card (nxt U B (nxt U B X)) := by
  obtain ⟨h1, h2, hA1, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
  set X₁ := nxt U B X with hX₁
  set X₂ := nxt U B X₁ with hX₂
  have hBX₂ : B ≤ X₂ := le_nxt U B X₁
  have hX₁A : X₁ ≤ A := h1.trans hXA
  have hX₂A : X₂ ≤ A := h2.trans hX₁A
  obtain ⟨x₀, hx₀, u₀, hu₀, hxu⟩ : ∃ x₀ ∈ X, ∃ u₀ ∈ U, ⁅x₀, u₀⁆ ∉ X₂ := by
    by_contra hall
    push Not at hall
    apply hne
    apply le_antisymm h2
    refine sup_le ?_ hBX₂
    rw [Subgroup.commutator_le]
    exact hall
  set S := h.imSub hBX hXA hUX hUB hx₀ with hS
  have hX₂S : X₂ ≤ S := fun w hw => ⟨h2 hw, 1, U.one_mem, by
    rw [commutator_one_right']
    exact cg_one_iff.mpr hw⟩
  have hSX₁ : S ≤ X₁ := fun w hw => hw.1
  have hLS : L ≤ Subgroup.normalizer (S : Set G) := by
    refine le_normalizer_of_forall fun g hg w hw => ?_
    obtain ⟨hwX₁, u, hu, hwu⟩ := hw
    have hgX₁ : g ∈ Subgroup.normalizer (X₁ : Set G) :=
      mem_normalizer_nxt (hLX hg) (hLU hg) (hLB hg)
    have hgX₂ : g ∈ Subgroup.normalizer (X₂ : Set G) :=
      mem_normalizer_nxt hgX₁ (hLU hg) (hLB hg)
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgX₁ w).mp hwX₁, g * u * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hLU hg) u).mp hu, ?_⟩
    have e1 : g * ⁅x₀, u⁆ * g⁻¹ = ⁅(g * x₀ * g⁻¹ * x₀⁻¹) * x₀, g * u * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    refine (hwu.conj hgX₂).trans ?_
    rw [e1]
    exact h.cg_shift hBX hXA hUX hUB (hLc g hg x₀ hx₀) hx₀
      ((Subgroup.mem_normalizer_iff.mp (hLU hg) u).mp hu)
  have hSeq : S = X₁ := by
    rcases hirr S hX₂S hSX₁ hLS with hS2 | hS1
    · exfalso
      apply hxu
      rw [← hS2]
      exact ⟨commutator_mem_nxt hx₀ hu₀, u₀, hu₀, Cg.refl _ _⟩
    · exact hS1
  obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, u₄, hu₄, hU⟩ := hgen
  set N₁ := X₂ ⊔ Subgroup.zpowers ⁅x₀, u₁⁆ with hN₁
  set N₂ := N₁ ⊔ Subgroup.zpowers ⁅x₀, u₂⁆ with hN₂
  set N₃ := N₂ ⊔ Subgroup.zpowers ⁅x₀, u₃⁆ with hN₃
  set N₄ := N₃ ⊔ Subgroup.zpowers ⁅x₀, u₄⁆ with hN₄
  have hcA : ∀ u ∈ U, ⁅x₀, u⁆ ∈ A := fun u hu => hX₁A (commutator_mem_nxt hx₀ hu)
  have hz : ∀ u ∈ U, Subgroup.zpowers ⁅x₀, u⁆ ≤ A := fun u hu =>
    (Subgroup.zpowers_le).mpr (hcA u hu)
  have hN₁A : N₁ ≤ A := sup_le hX₂A (hz u₁ hu₁)
  have hN₂A : N₂ ≤ A := sup_le hN₁A (hz u₂ hu₂)
  have hN₃A : N₃ ≤ A := sup_le hN₂A (hz u₃ hu₃)
  have hBN₁ : B ≤ N₁ := hBX₂.trans le_sup_left
  have hBN₂ : B ≤ N₂ := hBN₁.trans le_sup_left
  have hBN₃ : B ≤ N₃ := hBN₂.trans le_sup_left
  have hX₂N₄ : X₂ ≤ N₄ := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hgN₄ : ∀ u ∈ U, ⁅x₀, u⁆ ∈ N₄ := by
    let T : Subgroup G :=
      { carrier := {u | u ∈ U ∧ ⁅x₀, u⁆ ∈ N₄}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          exact ⟨U.mul_mem ha hb, mem_of_cg
            ((h.cg_commutator_mul hBX hXA hUX hUB hx₀ ha hb).mono hX₂N₄) (N₄.mul_mem ha' hb')⟩
        one_mem' := ⟨U.one_mem, by rw [commutator_one_right']; exact N₄.one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨U.inv_mem ha, ?_⟩
          have hm := h.cg_commutator_mul hBX hXA hUX hUB hx₀ ha (U.inv_mem ha)
          rw [mul_inv_cancel, commutator_one_right', Cg, inv_one, one_mul] at hm
          have := N₄.mul_mem (N₄.inv_mem ha') (hX₂N₄ hm)
          rwa [inv_mul_cancel_left] at this }
    have hle : Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ O ≤ T := by
      refine sup_le ?_ (fun o ho => ⟨hOU ho, hX₂N₄ (hBX₂
        (conj_mem_iff_commutator_mem.mp (hO o ho x₀ (hXA hx₀))))⟩)
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ⟨hu₁, Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))))⟩
      · exact ⟨hu₂, Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))⟩
      · exact ⟨hu₃, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩
      · exact ⟨hu₄, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
    exact fun u hu => (hle (hU hu)).2
  have hSN₄ : S ≤ N₄ := by
    rintro w ⟨-, u, hu, hwu⟩
    exact mem_of_cg (hwu.mono hX₂N₄) (hgN₄ u hu)
  have hstep : ∀ {N : Subgroup G} {u : G}, B ≤ N → N ≤ A → u ∈ U →
      Nat.card (N ⊔ Subgroup.zpowers ⁅x₀, u⁆ : Subgroup G) ≤ 2 * Nat.card N := by
    intro N u hBN hNA hu
    exact card_sup_zpowers_le (h.le_normalizer hBN hNA (hcA u hu)) (hBN (h.sq _ (hcA u hu)))
  have c1 := hstep hBX₂ hX₂A hu₁
  have c2 := hstep hBN₁ hN₁A hu₂
  have c3 := hstep hBN₂ hN₂A hu₃
  have c4 := hstep hBN₃ hN₃A hu₄
  rw [← hN₁] at c1
  rw [← hN₂] at c2
  rw [← hN₃] at c3
  rw [← hN₄] at c4
  have hcard : Nat.card X₁ ≤ Nat.card N₄ := by
    rw [← hSeq]
    exact Subgroup.card_le_of_le hSN₄
  omega

@[expose] def commIn (S : Set G) (M : Subgroup G) (hBM : B ≤ M) (hMA : M ≤ A) : Subgroup G where
  carrier := {x | x ∈ A ∧ ∀ u ∈ S, ⁅x, u⁆ ∈ M}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, fun u hu => ?_⟩
    have e : ⁅a * b, u⁆ = (a * ⁅b, u⁆ * a⁻¹) * ⁅a, u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer hBM hMA ha) _).mp
      (hb' u hu)) (ha' u hu)
  one_mem' := ⟨A.one_mem, fun u _ => by
    rw [commutatorElement_def]
    simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨A.inv_mem ha, fun u hu => ?_⟩
    have e : ⁅a⁻¹, u⁆ = a⁻¹ * (⁅a, u⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer hBM hMA (A.inv_mem ha)) _).mp
      (M.inv_mem (ha' u hu))

omit h in
theorem card_le_of_relIndex_le [Finite G] {K A : Subgroup G} (hKA : K ≤ A) {n : ℕ}
    (hn : K.relIndex A ≤ n) : Nat.card A ≤ n * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card (H := K) (K := A)
  rw [inf_of_le_left hKA] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hn

omit h in
theorem relIndex_le_of_card_le [Finite G] {K A : Subgroup G} (hKA : K ≤ A) {n : ℕ}
    (hn : Nat.card A ≤ n * Nat.card K) : K.relIndex A ≤ n := by
  have h1 := Subgroup.relIndex_mul_card (H := K) (K := A)
  rw [inf_of_le_left hKA] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  rw [← h1] at hn
  exact Nat.le_of_mul_le_mul_right hn hpos

theorem asc_bound [Finite G] {U O L : Subgroup G}
    (hUB : U ≤ Subgroup.normalizer (B : Set G)) (hOU : O ≤ U)
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hAU : ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ cmod U A B)
    (hLZ : ∀ g ∈ L, ∀ z ∈ cmod U A B, g * z * g⁻¹ * z⁻¹ ∈ B)
    (hgen : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∃ u₃ ∈ U, ∃ u₄ ∈ U,
      U ≤ Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ O)
    (hirr : ∀ W : Subgroup G, cmod U A B ≤ W → W ≤ A →
      L ≤ Subgroup.normalizer (W : Set G) → W = cmod U A B ∨ W = A)
    (hne : cmod U A B ≠ A) :
    Nat.card A ≤ 16 * Nat.card (cmod U A B) := by
  set Z := cmod U A B with hZ
  have hZA : Z ≤ A := fun _ hz => hz.1
  have hBZ : B ≤ Z := h.le_cmod hUB
  obtain ⟨x₀, hx₀, hx₀Z⟩ : ∃ x₀ ∈ A, x₀ ∉ Z := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm hZA hall)
  obtain ⟨u₀, hu₀, hz₀⟩ : ∃ u₀ ∈ U, ⁅x₀, u₀⁆ ∉ B := by
    by_contra hall
    push Not at hall
    exact hx₀Z ⟨hx₀, h.normalizes hx₀, fun u hu => conj_mem_iff_commutator_mem.mpr (hall u hu)⟩
  set z₀ := ⁅x₀, u₀⁆ with hz₀def
  obtain ⟨M, hM⟩ := (Set.toFinite {N : Subgroup G | B ≤ N ∧ N ≤ Z ∧ z₀ ∉ N}).exists_maximal
    ⟨B, le_rfl, hBZ, hz₀⟩
  obtain ⟨hBM, hMZ, hz₀M⟩ := hM.1
  have hMA : M ≤ A := hMZ.trans hZA
  have hAM := h.le_normalizer hBM hMA
  have hidx : ∀ z ∈ Z, z ∉ M → z⁻¹ * z₀ ∈ M := by
    intro z hz hzM
    have hzN : z ∈ Subgroup.normalizer (M : Set G) := hAM (hZA hz)
    have hzz : z * z ∈ M := hBM (h.sq z (hZA hz))
    have hmem : z₀ ∈ M ⊔ Subgroup.zpowers z := by
      by_contra hn
      have hle : M ⊔ Subgroup.zpowers z ≤ M :=
        hM.2 ⟨hBM.trans le_sup_left, sup_le hMZ ((Subgroup.zpowers_le).mpr hz), hn⟩ le_sup_left
      exact hzM (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
    exact (mem_or_of_mem_sup_zpowers hzN hzz z₀ hmem).resolve_left hz₀M
  have hidx2 : ∀ z ∈ Z, z ∉ M → ∀ z' ∈ Z, z' ∉ M → z' * z⁻¹ ∈ M := by
    intro z hz hzM z' hz' hz'M
    have h3 := M.mul_mem (hidx z hz hzM) (M.inv_mem (hidx z' hz' hz'M))
    rw [show z⁻¹ * z₀ * (z'⁻¹ * z₀)⁻¹ = z⁻¹ * z' by group] at h3
    have := (Subgroup.mem_normalizer_iff.mp (hAM (hZA hz)) _).mp h3
    rwa [show z * (z⁻¹ * z') * z⁻¹ = z' * z⁻¹ by group] at this
  have hUM : ∀ u ∈ U, ∀ m ∈ M, u * m * u⁻¹ ∈ M := by
    intro u hu m hm
    have := M.mul_mem (hBM ((hMZ hm).2.2 u hu)) hm
    rwa [show u * m * u⁻¹ * m⁻¹ * m = u * m * u⁻¹ by group] at this
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := by
    refine le_normalizer_of_forall fun g hg m hm => ?_
    have := M.mul_mem (hBM (hLZ g hg m (hMZ hm))) hm
    rwa [show g * m * g⁻¹ * m⁻¹ * m = g * m * g⁻¹ by group] at this
  have hTx : ∀ x ∈ A, ∀ S : Set G, S ⊆ U →
      (∀ u ∈ S, ⁅x, u⁆ ∈ M) → U ≤ Subgroup.closure S ⊔ O → ∀ u ∈ U, ⁅x, u⁆ ∈ M := by
    intro x hx S hSU hS hUS
    let T : Subgroup G :=
      { carrier := {v | v ∈ U ∧ ⁅x, v⁆ ∈ M}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨U.mul_mem ha hb, ?_⟩
          have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact M.mul_mem ha' (hUM a ha _ hb')
        one_mem' := ⟨U.one_mem, by rw [commutator_one_right']; exact M.one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨U.inv_mem ha, ?_⟩
          have e : ⁅x, a⁻¹⁆ = a⁻¹ * (⁅x, a⁆)⁻¹ * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact hUM a⁻¹ (U.inv_mem ha) _ (M.inv_mem ha') }
    have hle : Subgroup.closure S ⊔ O ≤ T := by
      exact sup_le ((Subgroup.closure_le T).mpr fun u hu => ⟨hSU hu, hS u hu⟩)
        (fun o ho => ⟨hOU ho, hBM (conj_mem_iff_commutator_mem.mp (hO o ho x hx))⟩)
    exact fun u hu => (hle (hUS hu)).2
  set Y := h.commIn (U : Set G) M hBM hMA with hY
  have hZY : Z ≤ Y := fun z hz =>
    ⟨hZA hz, fun u hu => hBM (conj_mem_iff_commutator_mem.mp (hz.2.2 u hu))⟩
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_normalizer_of_forall fun g hg x hx => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLA hg) x).mp hx.1, fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hLU (L.inv_mem hg)) u).mp hu
    have e : ⁅g * x * g⁻¹, u⁆ = g * ⁅x, g⁻¹ * u * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLM hg) _).mp (hx.2 _ hu')
  have hYeq : Y = Z := by
    rcases hirr Y hZY (fun _ hx => hx.1) hLY with hYZ | hYA
    · exact hYZ
    · exfalso
      have hx₀Y : x₀ ∈ Y := by rw [hYA]; exact hx₀
      exact hz₀M (hx₀Y.2 u₀ hu₀)
  obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, u₄, hu₄, hU⟩ := hgen
  have hK2 : ∀ u ∈ U, (h.commIn {u} M hBM hMA).relIndex A ≤ 2 := by
    intro u hu
    set K := h.commIn {u} M hBM hMA with hK
    have hKA : K ≤ A := fun _ hx => hx.1
    refine relIndex_le_of_card_le hKA ?_
    by_cases hall : ∀ x ∈ A, ⁅x, u⁆ ∈ M
    · have hAK : A ≤ K := fun x hx => ⟨hx, fun v hv => by
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        exact hall x hx⟩
      have := Subgroup.card_le_of_le hAK
      omega
    · push Not at hall
      obtain ⟨a, ha, hau⟩ := hall
      refine card_le_two_mul_of_forall a fun x hx => ?_
      by_cases hxu : ⁅x, u⁆ ∈ M
      · exact Or.inl ⟨hx, fun v hv => by rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hxu⟩
      · right
        refine ⟨A.mul_mem (A.inv_mem ha) hx, fun v hv => ?_⟩
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        have h1 := hidx2 _ (hAU a ha u hu) hau _ (hAU x hx u hu) hxu
        have e : ⁅a⁻¹ * x, u⁆ = a⁻¹ * (⁅x, u⁆ * (⁅a, u⁆)⁻¹) * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hAM (A.inv_mem ha)) _).mp h1
  set K := h.commIn {u₁} M hBM hMA ⊓ h.commIn {u₂} M hBM hMA ⊓
    h.commIn {u₃} M hBM hMA ⊓ h.commIn {u₄} M hBM hMA with hKdef
  have hKY : K ≤ Y := by
    rintro x ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩
    refine ⟨hx1.1, hTx x hx1.1 {u₁, u₂, u₃, u₄} ?_ ?_ hU⟩
    · intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> assumption
    · intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact hx1.2 _ (Set.mem_singleton _)
      · exact hx2.2 _ (Set.mem_singleton _)
      · exact hx3.2 _ (Set.mem_singleton _)
      · exact hx4.2 _ (Set.mem_singleton _)
  have hKA : K ≤ A := hKY.trans (hYeq ▸ hZA)
  have hrel : K.relIndex A ≤ 16 := by
    have i1 := Subgroup.relIndex_inf_le (H := h.commIn {u₁} M hBM hMA ⊓ h.commIn {u₂} M hBM hMA ⊓
      h.commIn {u₃} M hBM hMA) (K := h.commIn {u₄} M hBM hMA) (L := A)
    have i2 := Subgroup.relIndex_inf_le (H := h.commIn {u₁} M hBM hMA ⊓ h.commIn {u₂} M hBM hMA)
      (K := h.commIn {u₃} M hBM hMA) (L := A)
    have i3 := Subgroup.relIndex_inf_le (H := h.commIn {u₁} M hBM hMA)
      (K := h.commIn {u₂} M hBM hMA) (L := A)
    have k1 := hK2 u₁ hu₁
    have k2 := hK2 u₂ hu₂
    have k3 := hK2 u₃ hu₃
    have k4 := hK2 u₄ hu₄
    calc K.relIndex A ≤ _ := i1
      _ ≤ _ := Nat.mul_le_mul_right _ (i2.trans (Nat.mul_le_mul_right _ i3))
      _ ≤ 2 * 2 * 2 * 2 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul k1 k2) k3) k4
      _ = 16 := by norm_num
  have hcard := card_le_of_relIndex_le hKA hrel
  have hKZ : Nat.card K ≤ Nat.card Z := by
    rw [← hYeq]
    exact Subgroup.card_le_of_le hKY
  calc Nat.card A ≤ 16 * Nat.card K := hcard
    _ ≤ 16 * Nat.card Z := Nat.mul_le_mul_left _ hKZ

theorem card_le_fixMod [Finite G] {U O L : Subgroup G} {y : G}
    (hA2 : IsPGroup 2 A) (hU2 : IsPGroup 2 U)
    (hUA : U ≤ Subgroup.normalizer (A : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hOU : O ≤ U) (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hLL : oTwoUpper L = L)
    (hyL : y ∈ L) (hy3 : ∀ x ∈ A, y ^ 3 * x * (y ^ 3)⁻¹ * x⁻¹ ∈ B)
    (hnorm : ∀ u ∈ U, u * (y * u * y⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) ∈ O)
    (hsurj : ∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * y⁻¹)⁻¹) ∈ O)
    (hgen : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∃ u₃ ∈ U, ∃ u₄ ∈ U,
      U ≤ Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ O)
    (hfaith : ¬ ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ B)
    (hone : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A B + 1) :
    Nat.card A ≤ 16 * Nat.card (fixMod y A B) ∧ Nat.card (fixMod y A B) < Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyA := hLA hyL
  have hyB := hLB hyL
  have hyU := hLU hyL
  obtain ⟨h1, h2, -, -⟩ := h.nxt_facts h.le le_rfl hUA hUB
  set A₁ := nxt U B A with hA₁
  set A₂ := nxt U B A₁ with hA₂
  set Z := cmod U A B with hZ
  have hBA₁ : B ≤ A₁ := le_nxt U B A
  have hBA₂ : B ≤ A₂ := le_nxt U B A₁
  have hLA₁ : L ≤ Subgroup.normalizer (A₁ : Set G) := fun g hg =>
    mem_normalizer_nxt (hLA hg) (hLU hg) (hLB hg)
  have hLA₂ : L ≤ Subgroup.normalizer (A₂ : Set G) := fun g hg =>
    mem_normalizer_nxt (hLA₁ hg) (hLU hg) (hLB hg)
  have hUA₁ : U ≤ Subgroup.normalizer (A₁ : Set G) := le_normalizer_nxt hUA hUB
  have hLZ' : L ≤ Subgroup.normalizer (Z : Set G) := fun g hg =>
    mem_normalizer_cmod (hLU hg) (hLA hg) (hLB hg)
  have hBZ : B ≤ Z := h.le_cmod hUB
  have hZA : Z ≤ A := fun _ hz => hz.1
  have hmono : ∀ {X Y : Subgroup G}, B ≤ Y → Y ≤ X → X ≤ A →
      L ≤ Subgroup.normalizer (X : Set G) → L ≤ Subgroup.normalizer (Y : Set G) →
      F112W.eta (L ⊔ A) A Y ≤ F112W.eta (L ⊔ A) A X := by
    intro X Y hBY hYX hXA hLX hLY
    exact F112W.eta_le_of_le le_sup_right
      (F112W.isNormalIn_of_le_normalizer (hYX.trans hXA)
        (sup_le hLY (h.le_normalizer hBY (hYX.trans hXA))))
      (F112W.isNormalIn_of_le_normalizer hXA (sup_le hLX (h.le_normalizer (hBY.trans hYX) hXA)))
      hYX
  have hA₁B : A₁ ≠ B := by
    intro he
    apply hfaith
    intro x hx u hu
    have := commutator_mem_nxt (U := U) (B := B) hx hu
    rwa [← hA₁, he] at this
  have hZne : Z ≠ A := by
    intro he
    apply hfaith
    intro x hx u hu
    have hxZ : x ∈ Z := by rw [he]; exact hx
    exact conj_mem_iff_commutator_mem.mp (hxZ.2.2 u hu)
  have hfixLe : ∀ {X Y : Subgroup G}, B ≤ Y → Y ≤ X → X ≤ A →
      (∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ Y) → fixMod y X Y = X := fun hBY hYX hXA hc =>
    le_antisymm (fixMod_le y _ _) fun x hx =>
      (h.mem_fixMod_iff hBY hYX hXA).mpr ⟨hx, hc x hx⟩
  by_cases hD : ∀ g ∈ L, ∀ x ∈ A, g * x * g⁻¹ * x⁻¹ ∈ A₁
  ·
    have hfpf : fixMod y A₁ A₂ = A₂ :=
      h.desc_fpf h.le le_rfl hUA hUB hyA hyA hyU hyB hO hnorm (hD y hyL)
    have hlt₂ : A₂ < A₁ := h.commutator_sup_lt hU2 hA2 hUA hUB hUA₁
      (lt_of_le_of_ne hBA₁ (Ne.symm hA₁B)) h1
    have e1 : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A A₁ :=
      (h.eta_eq_iff hLL hA2 hLA hBA₁ h1 le_rfl hLA hLA₁).mpr hD
    have e2 : F112W.eta (L ⊔ A) A A₁ ≠ F112W.eta (L ⊔ A) A A₂ := by
      intro heq
      have hc := (h.eta_eq_iff hLL hA2 hLA hBA₂ h2 h1 hLA₁ hLA₂).mp heq
      have := hfixLe hBA₂ h2 h1 (hc y hyL)
      rw [hfpf] at this
      exact (ne_of_lt hlt₂) this
    have m1 := hmono hBA₂ h2 h1 hLA₁ hLA₂
    have m2 := hmono le_rfl hBA₂ (h2.trans h1) hLA₂ hLB
    have e3 : F112W.eta (L ⊔ A) A A₁ = F112W.eta (L ⊔ A) A A₂ + 1 := by omega
    have e4 : F112W.eta (L ⊔ A) A A₂ = F112W.eta (L ⊔ A) A B := by omega
    have hcA₂ := (h.eta_eq_iff hLL hA2 hLA le_rfl hBA₂ (h2.trans h1) hLA₂ hLB).mp e4
    have hirr : ∀ W : Subgroup G, A₂ ≤ W → W ≤ A₁ → L ≤ Subgroup.normalizer (W : Set G) →
        W = A₂ ∨ W = A₁ := fun W hW1 hW2 hLW =>
      h.irred_of_eta hLL hA2 hLA hy3 hyL hBA₂ hW1 hW2 h1 hLA₁ hLA₂ hLW e3 hfpf
    have hbound := h.desc_bound h.le le_rfl hUA hUB hOU hO hLA hLU hLB hD hgen hirr
      (ne_of_lt hlt₂)
    have hfA : fixMod y A A₁ = A := hfixLe hBA₁ h1 le_rfl (hD y hyL)
    have hfA₂ : fixMod y A₂ B = A₂ := hfixLe le_rfl hBA₂ (h2.trans h1) (hcA₂ y hyL)
    have c1 := h.card_fixMod_mul hy3 le_rfl hBA₁ h1 le_rfl hyA (hLA₁ hyL)
    have c2 := h.card_fixMod_mul hy3 le_rfl hBA₂ h2 h1 (hLA₁ hyL) (hLA₂ hyL)
    rw [hfA] at c1
    rw [hfpf, hfA₂] at c2
    have c3 : Nat.card (fixMod y A₁ B) = Nat.card A₂ :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos c2
    rw [c3] at c1
    have hlt : Nat.card A₂ < Nat.card A₁ := Subgroup.card_lt_of_lt hlt₂
    have hpos : 0 < Nat.card A₂ := Nat.card_pos
    constructor
    ·
      have : Nat.card A * Nat.card A₂ ≤ (16 * Nat.card (fixMod y A B)) * Nat.card A₂ := by
        rw [← c1]
        calc Nat.card (fixMod y A B) * Nat.card A₁
            ≤ Nat.card (fixMod y A B) * (16 * Nat.card A₂) := Nat.mul_le_mul_left _ hbound
          _ = 16 * Nat.card (fixMod y A B) * Nat.card A₂ := by ring
      exact Nat.le_of_mul_le_mul_right this hpos
    · by_contra hge
      push Not at hge
      have : Nat.card A * Nat.card A₂ < Nat.card (fixMod y A B) * Nat.card A₁ :=
        calc Nat.card A * Nat.card A₂ < Nat.card A * Nat.card A₁ :=
              Nat.mul_lt_mul_of_pos_left hlt (Nat.card_pos)
          _ ≤ Nat.card (fixMod y A B) * Nat.card A₁ := Nat.mul_le_mul_right _ hge
      omega
  ·
    have hne1 : F112W.eta (L ⊔ A) A A ≠ F112W.eta (L ⊔ A) A A₁ := fun heq =>
      hD ((h.eta_eq_iff hLL hA2 hLA hBA₁ h1 le_rfl hLA hLA₁).mp heq)
    have m1 := hmono hBA₁ h1 le_rfl hLA hLA₁
    have m2 := hmono le_rfl hBA₁ h1 hLA₁ hLB
    have e1 : F112W.eta (L ⊔ A) A A₁ = F112W.eta (L ⊔ A) A B := by omega
    have hcA₁ := (h.eta_eq_iff hLL hA2 hLA le_rfl hBA₁ h1 hLA₁ hLB).mp e1
    have hA₂B : A₂ = B := by
      by_contra hne
      have hBlt : B < A₂ := lt_of_le_of_ne hBA₂ (Ne.symm hne)
      have hyc : ∀ x ∈ A₁, y * x * y⁻¹ * x⁻¹ ∈ A₂ := fun x hx => hBA₂ (hcA₁ y hyL x hx)
      have hfpf2 := h.desc_fpf hBA₁ h1 hUA₁ hUB hyA (hLA₁ hyL) hyU hyB hO hnorm hyc
      have hlt₃ := h.commutator_sup_lt hU2 hA2 hUA hUB (le_normalizer_nxt hUA₁ hUB) hBlt
        (h2.trans h1)
      have hA₃A₂ : nxt U B A₂ ≤ A₂ := hlt₃.le
      have hfix3 := hfixLe (le_nxt U B A₂) hA₃A₂ (h2.trans h1)
        (fun w hw => le_nxt U B A₂ (hcA₁ y hyL w (h2 hw)))
      rw [hfpf2] at hfix3
      exact (ne_of_lt hlt₃) hfix3
    have hAU : ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ Z := by
      intro x hx u hu
      have hw : ⁅x, u⁆ ∈ A₁ := commutator_mem_nxt hx hu
      refine ⟨h1 hw, h.normalizes (h1 hw), fun v hv => ?_⟩
      have hc : ⁅⁅x, u⁆, v⁆ ∈ A₂ := commutator_mem_nxt hw hv
      rw [hA₂B] at hc
      exact conj_mem_iff_commutator_mem.mpr hc
    by_cases hA1 : ∀ g ∈ L, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ B
    ·
      have hfpf := h.asc_fpf hUA hUB hOU hAU (hA1 y hyL) hO hsurj hyA hyU hyB
      have eZ : F112W.eta (L ⊔ A) A Z = F112W.eta (L ⊔ A) A B :=
        (h.eta_eq_iff hLL hA2 hLA le_rfl hBZ hZA hLZ' hLB).mpr hA1
      have eAZ : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A Z + 1 := by omega
      have hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ A → L ≤ Subgroup.normalizer (W : Set G) →
          W = Z ∨ W = A := fun W hW1 hW2 hLW =>
        h.irred_of_eta hLL hA2 hLA hy3 hyL hBZ hW1 hW2 le_rfl hLA hLZ' hLW eAZ hfpf
      have hbound := h.asc_bound hUB hOU hO hLU hLA hAU hA1 hgen hirr hZne
      have hfZ : fixMod y Z B = Z := hfixLe le_rfl hBZ hZA (hA1 y hyL)
      have c1 := h.card_fixMod_mul hy3 le_rfl hBZ hZA le_rfl hyA (hLZ' hyL)
      rw [hfpf, hfZ] at c1
      have hF : Nat.card (fixMod y A B) = Nat.card Z :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos c1
      rw [hF]
      exact ⟨hbound, Subgroup.card_lt_of_lt (lt_of_le_of_ne hZA hZne)⟩
    ·
      exfalso
      have hne2 : F112W.eta (L ⊔ A) A Z ≠ F112W.eta (L ⊔ A) A B := fun heq =>
        hA1 ((h.eta_eq_iff hLL hA2 hLA le_rfl hBZ hZA hLZ' hLB).mp heq)
      have m3 := hmono le_rfl hBZ hZA hLZ' hLB
      have m4 := hmono hBZ hZA le_rfl hLA hLZ'
      have eAZ : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A Z := by omega
      have hcAZ := (h.eta_eq_iff hLL hA2 hLA hBZ hZA le_rfl hLA hLZ').mp eAZ
      have hA₁Z : A₁ ≤ Z := sup_le (Subgroup.commutator_le.mpr fun x hx u hu => hAU x hx u hu) hBZ
      exact hfaith (h.asc_zero hUA hOU hA₁Z (hcAZ y hyL) (hcA₁ y hyL) hO hsurj hyU)

end ElemSec

end CFSG.Quasithin.H13.SecFix
