module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.SecFix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

structure ElemSec (A B : Subgroup G) : Prop where
  le : B ≤ A
  normalizes : A ≤ Subgroup.normalizer (B : Set G)
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ B
  sq : ∀ x ∈ A, x * x ∈ B

@[expose] def fixMod (g : G) (X Y : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ Subgroup.normalizer (Y : Set G) ∧ g * x * g⁻¹ * x⁻¹ ∈ Y}
  mul_mem' := by
    rintro a b ⟨haX, haN, ha⟩ ⟨hbX, hbN, hb⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haN hbN, ?_⟩
    have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact Y.mul_mem ha ((Subgroup.mem_normalizer_iff.mp haN _).mp hb)
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨haX, haN, ha⟩
    refine ⟨X.inv_mem haX, Subgroup.inv_mem _ haN, ?_⟩
    have e : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (Y.inv_mem ha)

theorem fixMod_le (g : G) (X Y : Subgroup G) : fixMod g X Y ≤ X := fun _ hx => hx.1

@[expose] def secCent (X Y : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧ g ∈ Subgroup.normalizer (Y : Set G) ∧
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Y}
  mul_mem' := by
    rintro a b ⟨haX, haY, ha⟩ ⟨hbX, hbY, hb⟩
    refine ⟨Subgroup.mul_mem _ haX hbX, Subgroup.mul_mem _ haY hbY, fun x hx => ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp haY _).mp (hb x hx)) (ha x hx)
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haX, haY, ha⟩
    refine ⟨Subgroup.inv_mem _ haX, Subgroup.inv_mem _ haY, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haX) x).mp hx
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact Y.inv_mem (ha _ hx')

theorem commutator_le_of_le_secCent {X Y S : Subgroup G} (hS : S ≤ secCent X Y) :
    ⁅X, S⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro x hx s hs
  have h := ((hS hs).2.2 x hx)
  have e : ⁅x, s⁆ = (s * x * s⁻¹ * x⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Y.inv_mem h

theorem mul_mem_of_commutator_le {X Y S : Subgroup G} (h : ⁅X, S⁆ ≤ Y) {s x : G} (hs : s ∈ S)
    (hx : x ∈ X) : s * x * s⁻¹ * x⁻¹ ∈ Y := by
  have h1 := h (Subgroup.commutator_mem_commutator hx hs)
  have e : s * x * s⁻¹ * x⁻¹ = ⁅x, s⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Y.inv_mem h1

namespace ElemSec

variable {A B : Subgroup G} (h : ElemSec A B)
include h

theorem le_normalizer {Y : Subgroup G} (hBY : B ≤ Y) (hYA : Y ≤ A) :
    A ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have hc := h.comm x hx w (hYA hw)
    have e : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
    rw [e]
    exact Y.mul_mem (hBY hc) hw
  · intro hw
    have hc := h.comm x⁻¹ (A.inv_mem hx) (x * w * x⁻¹) (hYA hw)
    have e : w = (x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ * (x * w * x⁻¹)⁻¹) * (x * w * x⁻¹) := by group
    rw [e]
    exact Y.mul_mem (hBY hc) hw

theorem mem_fixMod_iff {Y X : Subgroup G} (hBY : B ≤ Y) (hYX : Y ≤ X) (hXA : X ≤ A) {g x : G} :
    x ∈ fixMod g X Y ↔ x ∈ X ∧ g * x * g⁻¹ * x⁻¹ ∈ Y :=
  ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx =>
    ⟨hx.1, h.le_normalizer hBY (hYX.trans hXA) (hXA hx.1), hx.2⟩⟩

theorem le_fixMod {Y X : Subgroup G} (hBY : B ≤ Y) (hYX : Y ≤ X) (hXA : X ≤ A) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) : Y ≤ fixMod g X Y := by
  intro x hx
  refine (h.mem_fixMod_iff hBY hYX hXA).mpr ⟨hYX hx, ?_⟩
  exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hgY x).mp hx) (Y.inv_mem hx)

omit h in
theorem fixMod_inf {X Y Z : Subgroup G} (hZX : Z ≤ X) (g : G) :
    fixMod g X Y ⊓ Z = fixMod g Z Y := by
  ext x
  constructor
  · rintro ⟨⟨-, hxN, hx⟩, hxZ⟩
    exact ⟨hxZ, hxN, hx⟩
  · rintro ⟨hxZ, hxN, hx⟩
    exact ⟨⟨hZX hxZ, hxN, hx⟩, hxZ⟩

theorem fixMod_mono_right {X Y Z : Subgroup G} (hBY : B ≤ Y) (hYZ : Y ≤ Z) (hZX : Z ≤ X)
    (hXA : X ≤ A) (g : G) : fixMod g X Y ≤ fixMod g X Z := by
  intro x hx
  rw [h.mem_fixMod_iff hBY (hYZ.trans hZX) hXA] at hx
  exact (h.mem_fixMod_iff (hBY.trans hYZ) hZX hXA).mpr ⟨hx.1, hYZ hx.2⟩

theorem exists_fixMod_mul {g : G} (hg3 : ∀ x ∈ A, g ^ 3 * x * (g ^ 3)⁻¹ * x⁻¹ ∈ B)
    {X Y Z : Subgroup G} (hBY : B ≤ Y) (hYZ : Y ≤ Z) (hZX : Z ≤ X) (hXA : X ≤ A)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    {x : G} (hx : x ∈ X) (hxZ : g * x * g⁻¹ * x⁻¹ ∈ Z) :
    ∃ f ∈ fixMod g X Y, f⁻¹ * x ∈ Z := by
  have hcX : ∀ w ∈ X, g * w * g⁻¹ ∈ X := fun w hw => (Subgroup.mem_normalizer_iff.mp hgX w).mp hw
  set x₁ := g * x * g⁻¹ with hx₁
  set x₂ := g * x₁ * g⁻¹ with hx₂
  have hx₁X : x₁ ∈ X := hcX x hx
  have hx₂X : x₂ ∈ X := hcX x₁ hx₁X
  have hxA := hXA hx
  have hx₁A := hXA hx₁X
  have hx₂A := hXA hx₂X
  refine ⟨x * x₁ * x₂, ?_, ?_⟩
  · refine (h.mem_fixMod_iff hBY (hYZ.trans hZX) hXA).mpr
      ⟨X.mul_mem (X.mul_mem hx hx₁X) hx₂X, hBY ?_⟩
    have h3 : g * x₂ * g⁻¹ * x⁻¹ ∈ B := by
      have := hg3 x hxA
      have e : g * x₂ * g⁻¹ * x⁻¹ = g ^ 3 * x * (g ^ 3)⁻¹ * x⁻¹ := by
        rw [hx₂, hx₁, pow_three]
        group
      rw [e]
      exact this
    have hB1 : (x₁ * x₂) * (g * x₂ * g⁻¹ * x⁻¹) * (x₁ * x₂)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (h.normalizes (A.mul_mem hx₁A hx₂A)) _).mp h3
    have hB2 := h.comm (x₁ * x₂) (A.mul_mem hx₁A hx₂A) x hxA
    have e : g * (x * x₁ * x₂) * g⁻¹ * (x * x₁ * x₂)⁻¹ =
        ((x₁ * x₂) * (g * x₂ * g⁻¹ * x⁻¹) * (x₁ * x₂)⁻¹) * (x₁ * x₂ * x * (x₁ * x₂)⁻¹ * x⁻¹) := by
      rw [hx₂, hx₁]
      group
    rw [e]
    exact B.mul_mem hB1 hB2
  ·
    set z₁ := g * x * g⁻¹ * x⁻¹ with hz₁
    have hz₁' : g * z₁ * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hgZ z₁).mp hxZ
    have hAZ := h.le_normalizer (hBY.trans hYZ) (hZX.trans hXA)
    have hc : x * (g * z₁ * g⁻¹ * z₁) * x⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hAZ hxA) _).mp (Z.mul_mem hz₁' hxZ)
    have hsq : x * x ∈ Z := hYZ (hBY (h.sq x hxA))
    have e : (x * x₁ * x₂)⁻¹ * x = (z₁ * (x * (g * z₁ * g⁻¹ * z₁) * x⁻¹) * (x * x))⁻¹ := by
      rw [hx₂, hx₁, hz₁]
      group
    rw [e]
    exact Z.inv_mem (Z.mul_mem (Z.mul_mem hxZ hc) hsq)

theorem fixMod_eq_sup {g : G} (hg3 : ∀ x ∈ A, g ^ 3 * x * (g ^ 3)⁻¹ * x⁻¹ ∈ B)
    {X Y Z : Subgroup G} (hBY : B ≤ Y) (hYZ : Y ≤ Z) (hZX : Z ≤ X) (hXA : X ≤ A)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    fixMod g X Z = fixMod g X Y ⊔ Z := by
  apply le_antisymm
  · intro x hx
    rw [h.mem_fixMod_iff (hBY.trans hYZ) hZX hXA] at hx
    obtain ⟨f, hf, hfx⟩ := h.exists_fixMod_mul hg3 hBY hYZ hZX hXA hgX hgZ hx.1 hx.2
    have e : x = f * (f⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf) (Subgroup.mem_sup_right hfx)
  · exact sup_le (h.fixMod_mono_right hBY hYZ hZX hXA g)
      (h.le_fixMod (hBY.trans hYZ) hZX hXA hgZ)

theorem card_fixMod_mul {g : G} (hg3 : ∀ x ∈ A, g ^ 3 * x * (g ^ 3)⁻¹ * x⁻¹ ∈ B)
    {X Y Z : Subgroup G} (hBY : B ≤ Y) (hYZ : Y ≤ Z) (hZX : Z ≤ X) (hXA : X ≤ A)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    Nat.card (fixMod g X Y) * Nat.card Z = Nat.card (fixMod g X Z) * Nat.card (fixMod g Z Y) := by
  have hN : fixMod g X Y ≤ Subgroup.normalizer (Z : Set G) :=
    (fixMod_le g X Y).trans (hXA.trans (h.le_normalizer (hBY.trans hYZ) (hZX.trans hXA)))
  have hc := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  rw [sup_comm, ← h.fixMod_eq_sup hg3 hBY hYZ hZX hXA hgX hgZ, inf_comm,
    ElemSec.fixMod_inf hZX g] at hc
  rw [hc, mul_comm]

theorem commutator_sup_lt [Finite G] {U X : Subgroup G} (hU : IsPGroup 2 U) (hA2 : IsPGroup 2 A)
    (hUA : U ≤ Subgroup.normalizer (A : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hBX : B < X) (hXA : X ≤ A) :
    ⁅X, U⁆ ⊔ B < X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := A ⊔ U with hT
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hA2 hU hUA
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := sup_le h.normalizes hUB
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (h.le_normalizer hBX.le hXA) hUX
  have hXT : X ≤ T := hXA.trans le_sup_left
  have hBn : IsNormalIn T T B := F112W.isNormalIn_of_le_normalizer (hBX.le.trans hXT) hTB
  have hXn : IsNormalIn T T X := F112W.isNormalIn_of_le_normalizer hXT hTX
  obtain ⟨M, hM⟩ :=
    (Set.toFinite {K : Subgroup G | IsNormalIn T T K ∧ B ≤ K ∧ K < X}).exists_maximal
      ⟨B, hBn, le_rfl, hBX⟩
  have hMs : IsNormalIn T T M ∧ B ≤ M ∧ M < X := hM.1
  have hstep : IsChiefStep T T M X := by
    refine ⟨hXn, hMs.1, hMs.2.2, fun K hK hMK hKX => ?_⟩
    by_cases hKX' : K = X
    · exact Or.inr hKX'
    · exact Or.inl (le_antisymm
        (hM.2 ⟨hK, hMs.2.1.trans hMK, lt_of_le_of_ne hKX hKX'⟩ hMK) hMK)
  have h16 := F112W.commutator_le_of_isChiefStep hT2 le_rfl Subgroup.le_normalizer hstep hXT
  have hle : ⁅X, U⁆ ⊔ B ≤ M :=
    sup_le ((Subgroup.commutator_mono le_rfl le_sup_right).trans h16) hMs.2.1
  exact lt_of_le_of_lt hle hMs.2.2

end ElemSec

end CFSG.Quasithin.H13.SecFix
