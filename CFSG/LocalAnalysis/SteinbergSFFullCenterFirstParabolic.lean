module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterRadicalTwoCores

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterParabolic

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

@[ext] structure Heis (K : Type*) where
  x : K
  y : K
  z : K

namespace Heis

variable {K : Type*} [CommRing K]

instance : Mul (Heis K) := ⟨fun p p' => ⟨p.x + p'.x + p.z * p'.y, p.y + p'.y, p.z + p'.z⟩⟩

instance : One (Heis K) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heis K) := ⟨fun p => ⟨-p.x + p.z * p.y, -p.y, -p.z⟩⟩

@[simp] theorem mul_x (p p' : Heis K) : (p * p').x = p.x + p'.x + p.z * p'.y := rfl

@[simp] theorem mul_y (p p' : Heis K) : (p * p').y = p.y + p'.y := rfl

@[simp] theorem mul_z (p p' : Heis K) : (p * p').z = p.z + p'.z := rfl

@[simp] theorem one_x : (1 : Heis K).x = 0 := rfl

@[simp] theorem one_y : (1 : Heis K).y = 0 := rfl

@[simp] theorem one_z : (1 : Heis K).z = 0 := rfl

@[simp] theorem inv_x (p : Heis K) : p⁻¹.x = -p.x + p.z * p.y := rfl

@[simp] theorem inv_y (p : Heis K) : p⁻¹.y = -p.y := rfl

@[simp] theorem inv_z (p : Heis K) : p⁻¹.z = -p.z := rfl

instance : Group (Heis K) where
  mul_assoc p p' p'' := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

theorem mk_mul_mk (x y z x' y' z' : K) :
    (⟨x, y, z⟩ : Heis K) * ⟨x', y', z'⟩ = ⟨x + x' + z * y', y + y', z + z'⟩ := rfl

@[simp] theorem conj_y (p q : Heis K) : (p * q * p⁻¹).y = q.y := by simp

@[simp] theorem conj_z (p q : Heis K) : (p * q * p⁻¹).z = q.z := by simp

theorem conj_root_x (p : Heis K) : (p * ⟨0, 0, 1⟩ * p⁻¹).x = -p.y := by
  simp only [mul_x, mul_z, inv_x, inv_y]
  ring

variable (K) in
@[expose] def planeXY : Subgroup (Heis K) where
  carrier := {p | p.z = 0}
  mul_mem' := by
    intro p p' hp hp'
    change p.z = 0 at hp
    change p'.z = 0 at hp'
    change (p * p').z = 0
    rw [mul_z, hp, hp', add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro p hp
    change p.z = 0 at hp
    change p⁻¹.z = 0
    rw [inv_z, hp, neg_zero]

variable (K) in
@[expose] def planeXZ : Subgroup (Heis K) where
  carrier := {p | p.y = 0}
  mul_mem' := by
    intro p p' hp hp'
    change p.y = 0 at hp
    change p'.y = 0 at hp'
    change (p * p').y = 0
    rw [mul_y, hp, hp', add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro p hp
    change p.y = 0 at hp
    change p⁻¹.y = 0
    rw [inv_y, hp, neg_zero]

theorem mem_planeXY {p : Heis K} : p ∈ planeXY K ↔ p.z = 0 := Iff.rfl

theorem mem_planeXZ {p : Heis K} : p ∈ planeXZ K ↔ p.y = 0 := Iff.rfl

theorem card_planeXY : Nat.card (planeXY K) = Nat.card K ^ 2 := by
  rw [sq, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun p => ((p : Heis K).x, (p : Heis K).y)
      invFun := fun q => ⟨⟨q.1, q.2, 0⟩, rfl⟩
      left_inv := fun p => Subtype.ext (Heis.ext rfl rfl p.2.symm)
      right_inv := fun _ => rfl }

theorem card_planeXZ : Nat.card (planeXZ K) = Nat.card K ^ 2 := by
  rw [sq, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun p => ((p : Heis K).x, (p : Heis K).z)
      invFun := fun q => ⟨⟨q.1, 0, q.2⟩, rfl⟩
      left_inv := fun p => Subtype.ext (Heis.ext rfl p.2.symm rfl)
      right_inv := fun _ => rfl }

section CharTwo

variable [CharP K 2]

theorem mul_self (p : Heis K) : p * p = ⟨p.z * p.y, 0, 0⟩ := by
  ext
  · rw [mul_x, CharTwo.add_self_eq_zero, zero_add]
  · rw [mul_y, CharTwo.add_self_eq_zero]
  · rw [mul_z, CharTwo.add_self_eq_zero]

theorem mul_self_eq_one_iff (p : Heis K) : p * p = 1 ↔ p.z * p.y = 0 := by
  rw [mul_self]
  constructor
  · intro h
    exact congrArg Heis.x h
  · intro h
    ext <;> simp [h]

theorem planeXY_comm_sq {p p' : Heis K} (hp : p ∈ planeXY K) (hp' : p' ∈ planeXY K) :
    p * p' = p' * p ∧ p * p = 1 := by
  rw [mem_planeXY] at hp hp'
  refine ⟨?_, (mul_self_eq_one_iff p).mpr (by rw [hp, zero_mul])⟩
  ext <;> simp [hp, hp'] <;> ring

theorem planeXZ_comm_sq {p p' : Heis K} (hp : p ∈ planeXZ K) (hp' : p' ∈ planeXZ K) :
    p * p' = p' * p ∧ p * p = 1 := by
  rw [mem_planeXZ] at hp hp'
  refine ⟨?_, (mul_self_eq_one_iff p).mpr (by rw [hp, mul_zero])⟩
  ext <;> simp [hp, hp'] <;> ring

end CharTwo

theorem le_planeXY_or_le_planeXZ {F : Type*} [Field F] [CharP F 2] (S : Subgroup (Heis F))
    (hS : ∀ p ∈ S, p * p = 1) : S ≤ planeXY F ∨ S ≤ planeXZ F := by
  by_cases hXY : S ≤ planeXY F
  · exact Or.inl hXY
  refine Or.inr fun p' hp'S => ?_
  by_contra hp'y
  refine hXY fun p hpS => ?_
  by_contra hpz
  rw [mem_planeXY] at hpz
  rw [mem_planeXZ] at hp'y
  have h1 := (mul_self_eq_one_iff p).mp (hS p hpS)
  have h2 := (mul_self_eq_one_iff p').mp (hS p' hp'S)
  have hpy : p.y = 0 := (mul_eq_zero.mp h1).resolve_left hpz
  have hp'z : p'.z = 0 := (mul_eq_zero.mp h2).resolve_right hp'y
  have h3 := (mul_self_eq_one_iff (p * p')).mp (hS _ (mul_mem hpS hp'S))
  rw [mul_y, mul_z, hpy, hp'z, zero_add, add_zero] at h3
  exact (mul_eq_zero.mp h3).elim hpz hp'y

end Heis

theorem vec2_ext {K : Type*} {v w : Fin 2 → K} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  funext j
  fin_cases j
  · exact h0
  · exact h1

@[expose] def RootAct {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
    [Finite K] (φ : L ≃* antiSp K) (i : Axis) (g : G) (c : K) : Prop :=
  ∀ a ∈ pull φ (rootA K i),
    psiG φ i (g * a * g⁻¹) = ![psiG φ i a 0 + c * psiG φ i a 1, psiG φ i a 1]

section Transport

variable {X : Type*} [Group X]

theorem mem_map_mk'_iff {D S : Subgroup X} [D.Normal] (hDS : D ≤ S) (x : X) :
    (x : X ⧸ D) ∈ S.map (QuotientGroup.mk' D) ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : y⁻¹ * x ∈ D := QuotientGroup.eq.mp hyx
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact mul_mem hy (hDS h1)
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {F : Type*} [Field F] [CharP F 2]

theorem maximal_elementaryAbelian (ι : X ≃* Heis F) {E H : Subgroup X}
    (hE : ∀ x, x ∈ E ↔ (ι x).z = 0) (hH : ∀ x, x ∈ H ↔ (ι x).y = 0) :
    (∀ S : Subgroup X, Maximal (fun S : Subgroup X => IsElementaryAbelian 2 S) S ↔
      S = E ∨ S = H) ∧ Nat.card E = Nat.card F ^ 2 ∧ Nat.card H = Nat.card F ^ 2 := by
  have hEA : IsElementaryAbelian 2 E := isElementaryAbelian_of
    (fun x hx y hy => ι.injective (by
      rw [map_mul, map_mul]
      exact (Heis.planeXY_comm_sq ((hE x).mp hx) ((hE y).mp hy)).1))
    (fun x hx => ι.injective (by
      rw [map_mul, map_one]
      exact (Heis.planeXY_comm_sq ((hE x).mp hx) ((hE x).mp hx)).2))
  have hHA : IsElementaryAbelian 2 H := isElementaryAbelian_of
    (fun x hx y hy => ι.injective (by
      rw [map_mul, map_mul]
      exact (Heis.planeXZ_comm_sq ((hH x).mp hx) ((hH y).mp hy)).1))
    (fun x hx => ι.injective (by
      rw [map_mul, map_one]
      exact (Heis.planeXZ_comm_sq ((hH x).mp hx) ((hH x).mp hx)).2))
  have dich : ∀ S : Subgroup X, IsElementaryAbelian 2 S → S ≤ E ∨ S ≤ H := by
    intro S hS
    have h2 : ∀ p ∈ S.map ι.toMonoidHom, p * p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← sq, h1, map_one]
    rcases Heis.le_planeXY_or_le_planeXZ _ h2 with h | h
    · exact Or.inl fun x hx => (hE x).mpr (h ⟨x, hx, rfl⟩)
    · exact Or.inr fun x hx => (hH x).mpr (h ⟨x, hx, rfl⟩)
  have hEH : ¬ E ≤ H := fun hle => by
    have h1 := (hH _).mp (hle ((hE (ι.symm ⟨0, 1, 0⟩)).mpr (by simp)))
    simp at h1
  have hHE : ¬ H ≤ E := fun hle => by
    have h1 := (hE _).mp (hle ((hH (ι.symm ⟨0, 0, 1⟩)).mpr (by simp)))
    simp at h1
  have hcard : ∀ (S : Subgroup X) (P : Subgroup (Heis F)), (∀ x, x ∈ S ↔ ι x ∈ P) →
      Nat.card S = Nat.card P := fun S P hSP => by
    have e : S.map ι.toMonoidHom = P := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hSP x).mp hx
      · intro hp
        exact ⟨ι.symm p, (hSP _).mpr (by simpa using hp), by simp⟩
    rw [← card_map_of_injective (f := ι.toMonoidHom) ι.injective, e]
  refine ⟨fun S => ⟨fun ⟨hS, hmax⟩ => ?_, ?_⟩, (hcard E _ hE).trans Heis.card_planeXY,
    (hcard H _ hH).trans Heis.card_planeXZ⟩
  · rcases dich S hS with h | h
    · exact Or.inl (le_antisymm h (hmax hEA h))
    · exact Or.inr (le_antisymm h (hmax hHA h))
  · rintro (rfl | rfl)
    · refine ⟨hEA, fun S' hS' hle => ?_⟩
      rcases dich S' hS' with h | h
      · exact h
      · exact absurd (hle.trans h) hEH
    · refine ⟨hHA, fun S' hS' hle => ?_⟩
      rcases dich S' hS' with h | h
      · exact absurd (hle.trans h) hHE
      · exact h

end Transport

structure ParabolicFacts {G : Type} [Group G] (K : Type) [Field K] (n : ℕ) (t : G)
    (C Q ZP U A A' D E Qi R H : Subgroup G) : Prop where
  isPGroup : IsPGroup 2 R
  card : Nat.card R = 2 * (2 ^ n) ^ 7
  mul_eq : (Q : Set G) * (E : Set G) = R
  E_normal : E ≤ R ∧ (E.subgroupOf R).Normal
  inf_C : R ⊓ C = Q
  orbit : {x : G | ∃ r ∈ R, x = r⁻¹ * t * r} = {x | ∃ a ∈ A, x = t * a}
  normalizer_Q : R ⊓ normalizer (Q : Set G) = H
  normalizer_Qi : R ⊓ normalizer (Qi : Set G) = H
  normalizer_A : R ⊓ normalizer (A' : Set G) = H
  H_normal : H ≤ R ∧ (H.subgroupOf R).Normal
  index_H : H.relIndex R = 2 ^ n
  quotient : ∃ _ : (D.subgroupOf R).Normal, ∃ ι : (↥R ⧸ D.subgroupOf R) ≃* Heis K,
    (∀ r : R, ((r : G) ∈ E ↔ (ι r).z = 0) ∧ ((r : G) ∈ Qi ↔ (ι r).x = 0 ∧ (ι r).y = 0) ∧
      ((r : G) ∈ H ↔ (ι r).y = 0) ∧ ((r : G) ∈ H ⊓ E ↔ (ι r).y = 0 ∧ (ι r).z = 0)) ∧
    (∀ S : Subgroup (↥R ⧸ D.subgroupOf R),
      Maximal (fun S : Subgroup (↥R ⧸ D.subgroupOf R) => IsElementaryAbelian 2 S) S ↔
        S = (E.subgroupOf R).map (QuotientGroup.mk' (D.subgroupOf R)) ∨
          S = (H.subgroupOf R).map (QuotientGroup.mk' (D.subgroupOf R))) ∧
    Nat.card ((E.subgroupOf R).map (QuotientGroup.mk' (D.subgroupOf R))) = (2 ^ n) ^ 2 ∧
    Nat.card ((H.subgroupOf R).map (QuotientGroup.mk' (D.subgroupOf R))) = (2 ^ n) ^ 2
  quotient_Hi : ∃ _ : (D.subgroupOf (H ⊓ E)).Normal, ∃ _ : (U.subgroupOf ZP).Normal,
    ∃ θ : (↥(H ⊓ E) ⧸ D.subgroupOf (H ⊓ E)) ≃* (↥ZP ⧸ U.subgroupOf ZP),
      ∀ x : ↥(H ⊓ E), ∃ z : ZP, (z : G) = t⁻¹ * ((x : G)⁻¹ * t * x) ∧ θ x = z
  mem_Hi : ∀ e ∈ E, e ∈ H ↔ t⁻¹ * (e⁻¹ * t * e) ∈ ZP
  card_Hi : Nat.card (H ⊓ E : Subgroup G) = 2 * (2 ^ n) ^ 5
  sq_E : closure {x : G | ∃ y ∈ E, x = y * y} = A
  sq_D : closure {x : G | ∃ y ∈ D, x = y * y} = U
  center_D : (center D).map D.subtype = A

section Overgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem Q_le_N (h : FCHyp L K n φ t) (i : Axis) : 𝐐 ≤ 𝐍[i] :=
  (h.Q_le_M i).trans (h.twoCore.M_le_normalizer_B φ i)

theorem Q_le_normalizer_E (h : FCHyp L K n φ t) (i : Axis) :
    𝐐 ≤ normalizer ((𝐄[i] : Subgroup G) : Set G) := fun _ hq =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ he => conj_mem_pCore_map (Q_le_N h i hq) he

theorem R_mul (h : FCHyp L K n φ t) (i : Axis) :
    (𝐐 : Set G) * (𝐄[i] : Set G) = 𝐑[i] :=
  (coe_mul_of_left_le_normalizer_right _ _ (Q_le_normalizer_E h i)).symm

theorem R_isPGroup (h : FCHyp L K n φ t) (i : Axis) : IsPGroup 2 𝐑[i] :=
  IsPGroup.to_sup_of_normal_right' h.setup.Q_two (CFSG.pCore_isPGroup.map _) (Q_le_normalizer_E h i)

theorem R_le_N (h : FCHyp L K n φ t) (i : Axis) : 𝐑[i] ≤ 𝐍[i] :=
  sup_le (Q_le_N h i) (map_subtype_le _)

theorem D_le_R (h : FCHyp L K n φ t) (i : Axis) : 𝐃[i] ≤ 𝐑[i] :=
  (h.D_le_E i).trans le_sup_right

theorem Qi_le_R (h : FCHyp L K n φ t) (i : Axis) : 𝐐[i] ≤ 𝐑[i] :=
  sup_le le_sup_left (D_le_R h i)

theorem Q_inf_E (h : FCHyp L K n φ t) (i : Axis) : 𝐐 ⊓ 𝐄[i] = 𝐁[i] := by
  apply le_antisymm
  · intro x hx
    rw [← E_inf_C h i]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, h.setup.Q_le_C (mem_inf.mp hx).1⟩
  · exact le_inf (FCHyp.B_le_Q i) ((h.B_le_D i).trans (h.D_le_E i))

theorem card_R (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐑[i] = 2 * Nat.card K ^ 7 := by
  have h1 := card_sup_mul_card_inf 𝐄[i] 𝐐 (Q_le_normalizer_E h i)
  rw [sup_comm, inf_comm, Q_inf_E h i, h.card_B, h.card_Q, card_E h i] at h1
  have hq : 0 < 2 * Nat.card K ^ 3 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : Nat.card 𝐑[i] * (2 * Nat.card K ^ 3) = 2 * Nat.card K ^ 7 * (2 * Nat.card K ^ 3) := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem R_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐑[i] ⊓ 𝐂 = 𝐐 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
    have hx' : x ∈ (𝐐 : Set G) * (𝐄[i] : Set G) := by
      rw [R_mul h i]
      exact hxR
    obtain ⟨q, hq, e, he, rfl⟩ := hx'
    have heC : e ∈ 𝐂 := by
      have := mul_mem (inv_mem (h.setup.Q_le_C hq)) hxC
      rwa [inv_mul_cancel_left] at this
    have heB : e ∈ 𝐁[i] := by
      rw [← E_inf_C h i]
      exact mem_inf.mpr ⟨he, heC⟩
    exact mul_mem hq (FCHyp.B_le_Q i heB)
  · exact le_inf le_sup_left h.setup.Q_le_C

theorem orbit_R (h : FCHyp L K n φ t) (i : Axis) :
    {x : G | ∃ r ∈ 𝐑[i], x = r⁻¹ * t * r} = {x | ∃ a ∈ 𝐀[i], x = t * a} := by
  apply le_antisymm
  · rw [← h.orbit_N i]
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, R_le_N h i hr, rfl⟩
  · rw [← orbit_E h i]
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, mem_sup_right he, rfl⟩

theorem conj_mem_E (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {e : G}
    (he : e ∈ 𝐄[i]) : r * e * r⁻¹ ∈ 𝐄[i] :=
  conj_mem_pCore_map (R_le_N h i hr) he

theorem E_normal_R (h : FCHyp L K n φ t) (i : Axis) : ((𝐄[i]).subgroupOf 𝐑[i]).Normal :=
  ⟨fun _ he r => mem_subgroupOf.mpr (conj_mem_E h i r.2 (mem_subgroupOf.mp he))⟩

theorem D_normal_R (h : FCHyp L K n φ t) (i : Axis) : ((𝐃[i]).subgroupOf 𝐑[i]).Normal :=
  ⟨fun _ hd r => mem_subgroupOf.mpr (h.conj_mem_D i (R_le_N h i r.2) (mem_subgroupOf.mp hd))⟩

omit [Finite G] in
theorem sq_pow_pred (h : FCHyp L K n φ t) (x : K) : (x ^ 2) ^ 2 ^ (n - 1) = x := by
  have := Fintype.ofFinite K
  have hn : 1 ≤ n := by have := h.setup.two_le; omega
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn, ← h.setup.card_K, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

omit [Finite G] in
theorem psiG_ZP_one (h : FCHyp L K n φ t) (i : Axis) {z : G} (hz : z ∈ 𝐙) :
    psiG φ i z 1 = 0 := by
  obtain ⟨w, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hz
  cases i
  · rw [psiG_one_uElt h.setup.card_K (by have := h.setup.two_le; omega)]
    simp
  · rw [psiG_two_uElt]
    simp

omit [Finite G] in
theorem exists_psiG_U_swap (h : FCHyp L K n φ t) (i : Axis) (x : K) :
    ∃ u ∈ 𝐔[i.swap], psiG φ i u = ![x, 0] := by
  cases i
  · refine ⟨((φ.symm (uElt 0 0 (x ^ 2) 0) : L) : G), symm_mem_pull.mpr ⟨x ^ 2, rfl⟩, ?_⟩
    rw [psiG_one_uElt h.setup.card_K (by have := h.setup.two_le; omega), sq_pow_pred h x]
    simp
  · exact ⟨((φ.symm (uElt 0 x 0 0) : L) : G), symm_mem_pull.mpr ⟨x, rfl⟩, psiG_two_uElt φ 0 x 0⟩

omit [Finite G] in
theorem exists_psiG_ZP (h : FCHyp L K n φ t) (i : Axis) (x : K) :
    ∃ z ∈ 𝐙, psiG φ i z = ![x, 0] := by
  obtain ⟨u, hu, hψ⟩ := exists_psiG_U_swap h i x
  exact ⟨u, pull_mono φ (rootU_le_center _) hu, hψ⟩

omit [Finite G] in
theorem psiG_one_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) :
    psiG φ i a 1 = 0 ↔ a ∈ 𝐙 := by
  refine ⟨fun ha1 => ?_, psiG_ZP_one h i⟩
  obtain ⟨z, hz, hψz⟩ := exists_psiG_ZP h i (psiG φ i a 0)
  have hzA : z ∈ 𝐀[i] := pull_mono φ (center_le_rootA i) hz
  have heq : psiG φ i a = psiG φ i z := by
    rw [hψz]
    refine vec2_ext ?_ ?_
    · simp
    · simpa using ha1
  have hu := (psiG_eq_iff h.twoCore φ i ha hzA).mp heq
  have e : a = z * (a⁻¹ * z)⁻¹ := by group
  rw [e]
  exact mul_mem hz (inv_mem (pull_mono φ (rootU_le_center i) hu))

omit [Finite G] [Finite K] in
theorem P_eq_A_sup_A : 𝐏 = 𝐀[Axis.one] ⊔ 𝐀[Axis.two] := by
  rw [← pull_sup]
  exact congrArg (pull φ) antiUnipotent_eq_radA1_sup_radA2

omit [Finite G] [Finite K] in
theorem B_sup_A_eq_Q (i : Axis) : 𝐁[i] ⊔ 𝐀[i.swap] = 𝐐 := by
  apply le_antisymm
  · exact sup_le (FCHyp.B_le_Q i) ((pull_mono φ (rootA_le_antiUnipotent _)).trans le_sup_left)
  · refine sup_le ?_ (zpowers_le.mpr (mem_sup_left (mem_sup_left (mem_zpowers t))))
    rw [P_eq_A_sup_A]
    cases i
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

omit [Finite G] [Finite K] in
theorem B_sup_B_eq_Q : 𝐁[Axis.one] ⊔ 𝐁[Axis.two] = 𝐐 := by
  apply le_antisymm
  · exact sup_le (FCHyp.B_le_Q _) (FCHyp.B_le_Q _)
  · refine sup_le ?_ (zpowers_le.mpr (mem_sup_left (mem_sup_left (mem_zpowers t))))
    rw [P_eq_A_sup_A]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)

omit [Finite G] [Finite K] in
theorem mem_ZP_of_mem_B_inf_B (h : FCHyp L K n φ t) {x : G} (h1 : x ∈ 𝐁[Axis.one])
    (h2 : x ∈ 𝐁[Axis.two]) : x ∈ 𝐙 ∨ t * x ∈ 𝐙 := by
  have hA : 𝐀[Axis.one] ⊓ 𝐀[Axis.two] = 𝐙 := by
    rw [← pull_inf]
    exact congrArg (pull φ) radA1_inf_radA2
  rw [mem_zpowers_sup_iff h.setup.t_mul_t (TwoCoreSetup.comm_pull φ h.twoCore)] at h1 h2
  have htL : ∀ {a b : G}, a ∈ L → t * b ∈ L → b = a → False := by
    rintro a b ha hb rfl
    apply h.twoCore.t_not_mem
    have := mul_mem hb (inv_mem ha)
    rwa [mul_inv_cancel_right] at this
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (hA ▸ mem_inf.mpr ⟨h1, h2⟩)
  · exact (htL (pull_le φ _ h1) (pull_le φ _ h2) rfl).elim
  · exact (htL (pull_le φ _ h2) (pull_le φ _ h1) rfl).elim
  · exact Or.inr (hA ▸ mem_inf.mpr ⟨h1, h2⟩)

theorem rootAct_mul (h : FCHyp L K n φ t) (i : Axis) {g g' : G} {c c' : K}
    (hg : RootAct φ i g c) (hg' : RootAct φ i g' c') (hg'N : g' ∈ 𝐍[i]) :
    RootAct φ i (g * g') (c + c') := by
  intro a ha
  have ha' : g' * a * g'⁻¹ ∈ 𝐀[i] := (h.actHyp i).conj_A g' hg'N a ha
  rw [show g * g' * a * (g * g')⁻¹ = g * (g' * a * g'⁻¹) * g⁻¹ by group, hg _ ha', hg' a ha]
  refine vec2_ext ?_ ?_
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp

theorem rootAct_inv (h : FCHyp L K n φ t) (i : Axis) {g : G} {c : K} (hg : RootAct φ i g c)
    (hgN : g ∈ 𝐍[i]) : RootAct φ i g⁻¹ (-c) := by
  intro a ha
  have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ 𝐀[i] := (h.actHyp i).conj_A g⁻¹ (inv_mem hgN) a ha
  have h1 := hg _ ha'
  rw [show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a by group] at h1
  have e1 : psiG φ i (g⁻¹ * a * g⁻¹⁻¹) 1 = psiG φ i a 1 := by rw [h1]; simp
  have e0 : psiG φ i (g⁻¹ * a * g⁻¹⁻¹) 0 = psiG φ i a 0 - c * psiG φ i a 1 := by
    rw [congrFun h1 0, e1]
    simp
  refine vec2_ext ?_ ?_
  · rw [e0]
    simp only [Matrix.cons_val_zero]
    ring
  · rw [e1]
    simp

omit [Finite G] in
theorem rootAct_unique (h : FCHyp L K n φ t) (i : Axis) {g : G} {c c' : K}
    (hc : RootAct φ i g c) (hc' : RootAct φ i g c') : c = c' := by
  obtain ⟨a, ha, hψ⟩ := exists_psiG_eq h.twoCore φ i ![0, 1]
  have := congrFun ((hc a ha).symm.trans (hc' a ha)) 0
  simpa [hψ] using this

omit [Finite G] [CharP K 2] [Finite K] in
theorem rootAct_one [CharP K 2] [Finite K] (i : Axis) : RootAct φ i 1 0 := by
  intro a _
  rw [one_mul, inv_one, mul_one]
  refine vec2_ext ?_ ?_ <;> simp

theorem rootAct_E (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) :
    RootAct φ i e 0 := by
  intro a ha
  rw [h.E_lin i he ha]
  refine vec2_ext ?_ ?_ <;> simp

theorem mem_E_of_rootAct (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgN : g ∈ 𝐍[i])
    (hg : RootAct φ i g 0) : g ∈ 𝐄[i] := by
  rw [← kernel_A h i hgN]
  intro a ha
  refine ((h.actHyp i).psi_eq_iff ha ((h.actHyp i).conj_A g hgN a ha)).mp ?_
  rw [hg a ha]
  refine vec2_ext ?_ ?_ <;> simp

omit [Finite G] in
theorem exists_rootAct_P (h : FCHyp L K n φ t) (i : Axis) (c : K) :
    ∃ q ∈ 𝐏, RootAct φ i q c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hn : 1 ≤ n := by have := h.setup.two_le; omega
  cases i
  · refine ⟨((φ.symm (uElt c 0 0 0) : L) : G),
      symm_mem_pull.mpr (uElt_mem_antiUnipotent c 0 0 0), fun a ha => ?_⟩
    obtain ⟨w, ⟨B, C, D, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull ha
    have e : uElt c 0 0 0 * uElt 0 B C D * (uElt c 0 0 0)⁻¹ =
        uElt 0 (B + c * D) (C + c ^ 2 * D) D := by
      rw [uElt_inv, uElt_mul, uElt_mul]
      congr 1
      · linear_combination c * h2
      · ring
      · linear_combination (c * B) * h2
      · ring
    rw [symm_conj_eq, e, psiG_one_uElt h.setup.card_K hn, psiG_one_uElt h.setup.card_K hn]
    refine vec2_ext ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [add_pow_char_pow, mul_pow, sq_pow_pred h c]
    · simp
  · refine ⟨((φ.symm (uElt 0 0 0 c) : L) : G),
      symm_mem_pull.mpr (uElt_mem_antiUnipotent 0 0 0 c), fun a ha => ?_⟩
    obtain ⟨w, ⟨A, B, C, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull ha
    have e : uElt 0 0 0 c * uElt A B C 0 * (uElt 0 0 0 c)⁻¹ = uElt A (B + A * c) C 0 := by
      rw [uElt_inv, uElt_mul, uElt_mul]
      congr 1
      · ring
      · ring
      · ring
      · linear_combination c * h2
    rw [symm_conj_eq, e, psiG_two_uElt, psiG_two_uElt]
    refine vec2_ext ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp

theorem semilinear (h : FCHyp L K n φ t) (i : Axis) {g : G} (hg : g ∈ 𝐍[i]) :
    ∃ (A₀ : GL (Fin 2) K) (k : ℕ), k < n ∧ ∀ a ∈ 𝐀[i],
      psiG φ i (g * a * g⁻¹) =
        (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun j => psiG φ i a j ^ 2 ^ k := by
  obtain ⟨μ, hμ, -, hsemi, -⟩ := linear_action h i
  obtain ⟨A₀, k, hk, hA⟩ := hsemi ⟨g, hg⟩
  exact ⟨A₀, k, hk, fun a ha => by rw [← hμ ⟨g, hg⟩ a ha, hA]⟩

theorem rootAct_of (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgN : g ∈ 𝐍[i])
    (hgZ : ∀ z ∈ 𝐙, g * z = z * g) (hg2 : ∃ m : ℕ, g ^ 2 ^ m = 1) : ∃ c, RootAct φ i g c := by
  obtain ⟨A₀, k, hk, hA⟩ := semilinear h i hgN
  set M : Matrix (Fin 2) (Fin 2) K := (A₀ : Matrix (Fin 2) (Fin 2) K)
  have hpow0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hfix : ∀ x : K, M *ᵥ ![x ^ 2 ^ k, 0] = ![x, 0] := by
    intro x
    obtain ⟨z, hz, hψz⟩ := exists_psiG_ZP h i x
    have h1 := hA z (pull_mono φ (center_le_rootA i) hz)
    rw [show g * z * g⁻¹ = z by rw [hgZ z hz, mul_inv_cancel_right], hψz] at h1
    rw [h1]
    congr 1
    refine vec2_ext ?_ ?_ <;> simp [hpow0]
  have hf0 := congrFun (hfix 1) 0
  have hf1 := congrFun (hfix 1) 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hf0 hf1
  have hk0 : k = 0 := by
    refine eq_zero_of_frobRingEquiv_pow_eq_one (by have := h.setup.two_le; omega)
      h.setup.card_K hk (RingEquiv.ext fun x => ?_)
    rw [frobRingEquiv_pow_apply]
    have := congrFun (hfix x) 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hf0] at this
    exact this
  subst hk0
  have hlin : ∀ a ∈ 𝐀[i], psiG φ i (g * a * g⁻¹) =
      ![psiG φ i a 0 + M 0 1 * psiG φ i a 1, M 1 1 * psiG φ i a 1] := by
    intro a ha
    rw [hA a ha]
    refine vec2_ext ?_ ?_ <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hf0, hf1]
  have hpowN : ∀ N : ℕ, ∀ a ∈ 𝐀[i],
      psiG φ i (g ^ N * a * (g ^ N)⁻¹) 1 = M 1 1 ^ N * psiG φ i a 1 := by
    intro N
    induction N with
    | zero => intro a _; simp
    | succ N ih =>
      intro a ha
      have ha' : g ^ N * a * (g ^ N)⁻¹ ∈ 𝐀[i] :=
        (h.actHyp i).conj_A (g ^ N) (pow_mem hgN N) a ha
      rw [pow_succ', show g * g ^ N * a * (g * g ^ N)⁻¹ = g * (g ^ N * a * (g ^ N)⁻¹) * g⁻¹ by
        group, hlin _ ha']
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [ih a ha]
      ring
  obtain ⟨m, hm⟩ := hg2
  obtain ⟨a₂, ha₂, hψ₂⟩ := exists_psiG_eq h.twoCore φ i ![0, 1]
  have h3 := hpowN (2 ^ m) a₂ ha₂
  rw [hm, one_mul, inv_one, mul_one, hψ₂] at h3
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_one] at h3
  have hw : M 1 1 = 1 := by
    have h4 : (M 1 1 - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, ← h3, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h4)
  exact ⟨M 0 1, fun a ha => by rw [hlin a ha, hw, one_mul]⟩

theorem mem_R_of_rootAct (h : FCHyp L K n φ t) (i : Axis) {g : G} (hgN : g ∈ 𝐍[i]) {c : K}
    (hg : RootAct φ i g c) : g ∈ 𝐑[i] := by
  obtain ⟨q, hq, hqc⟩ := exists_rootAct_P h i c
  have hqN : q ∈ 𝐍[i] := Q_le_N h i (mem_sup_left hq)
  have h1 := rootAct_mul h i (rootAct_inv h i hqc hqN) hg hgN
  rw [neg_add_cancel] at h1
  have he := mem_E_of_rootAct h i (mul_mem (inv_mem hqN) hgN) h1
  have e : g = q * (q⁻¹ * g) := by group
  rw [e]
  exact mul_mem (mem_sup_left (mem_sup_left hq)) (mem_sup_right he)

omit [Finite G] in
theorem exists_two_pow_eq_one {X : Subgroup G} (hX : IsPGroup 2 X) {g : G} (hg : g ∈ X) :
    ∃ m : ℕ, g ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := hX ⟨g, hg⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem rootAct_of_mem_R (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) :
    ∃ c, RootAct φ i r c := by
  have hr' : r ∈ (𝐐 : Set G) * (𝐄[i] : Set G) := by
    rw [R_mul h i]
    exact hr
  obtain ⟨q, hq, e, he, rfl⟩ := hr'
  obtain ⟨c, hc⟩ := rootAct_of h i (Q_le_N h i hq) (fun z hz => h.Q_comm_ZP hq hz)
    (exists_two_pow_eq_one h.setup.Q_two hq)
  exact ⟨c + 0, rootAct_mul h i hc (rootAct_E h i he) (map_subtype_le _ he)⟩

theorem H_le_R (h : FCHyp L K n φ t) (i : Axis) : 𝐇 ≤ 𝐑[i] := by
  intro x hx
  have hY := sup_le (h.Qi_le_Y Axis.one) (h.Qi_le_Y Axis.two) hx
  have hxN : x ∈ 𝐍[i] := by
    cases i
    · exact hY.1.2
    · exact hY.2
  have hxZ : ∀ z ∈ 𝐙, x * z = z * x := fun z hz =>
    FCHyp.comm_ZP_of (fun u hu => h.H_centralizes_U Axis.one hx hu)
      (fun u hu => h.H_centralizes_U Axis.two hx hu) hz
  obtain ⟨c, hc⟩ := rootAct_of h i hxN hxZ (exists_two_pow_eq_one h.H_facts.2.1 hx)
  exact mem_R_of_rootAct h i hxN hc

noncomputable def rootParam (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) : K :=
  Classical.choose (rootAct_of_mem_R h i r.2)

theorem rootAct_rootParam (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    RootAct φ i r (rootParam h i r) :=
  Classical.choose_spec (rootAct_of_mem_R h i r.2)

theorem rootParam_eq (h : FCHyp L K n φ t) (i : Axis) {r : 𝐑[i]} {c : K}
    (hc : RootAct φ i r c) : rootParam h i r = c :=
  rootAct_unique h i (rootAct_rootParam h i r) hc

theorem conj_t_mem_A (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) :
    t⁻¹ * (r * t * r⁻¹) ∈ 𝐀[i] :=
  (h.actHyp i).conj_t r (R_le_N h i hr)

@[expose] noncomputable def parabolicHom (h : FCHyp L K n φ t) (i : Axis) : 𝐑[i] →* Heis K where
  toFun r := ⟨psiG φ i (t⁻¹ * ((r : G) * t * (r : G)⁻¹)) 0,
    psiG φ i (t⁻¹ * ((r : G) * t * (r : G)⁻¹)) 1, rootParam h i r⟩
  map_one' := by
    have h1 : psiG φ i (t⁻¹ * ((1 : G) * t * (1 : G)⁻¹)) = 0 := by
      rw [one_mul, inv_one, mul_one, inv_mul_cancel]
      exact (psiG_eq_zero_iff h.twoCore φ i (one_mem _)).mpr (one_mem _)
    ext
    · exact congrFun h1 0
    · exact congrFun h1 1
    · exact rootParam_eq h i (rootAct_one i)
  map_mul' r s := by
    have har := conj_t_mem_A h i r.2
    have has := conj_t_mem_A h i s.2
    have hras : (r : G) * (t⁻¹ * ((s : G) * t * (s : G)⁻¹)) * (r : G)⁻¹ ∈ 𝐀[i] :=
      (h.actHyp i).conj_A r (R_le_N h i r.2) _ has
    have e : t⁻¹ * (((r * s : 𝐑[i]) : G) * t * ((r * s : 𝐑[i]) : G)⁻¹) =
        t⁻¹ * ((r : G) * t * (r : G)⁻¹) *
          ((r : G) * (t⁻¹ * ((s : G) * t * (s : G)⁻¹)) * (r : G)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    have hψ := psiG_mul h.twoCore φ i har hras
    rw [rootAct_rootParam h i r _ has, ← e] at hψ
    ext
    · show psiG φ i (t⁻¹ * (((r * s : 𝐑[i]) : G) * t * ((r * s : 𝐑[i]) : G)⁻¹)) 0 = _
      rw [hψ]
      simp only [Pi.add_apply, Matrix.cons_val_zero, Heis.mul_x]
      ring
    · show psiG φ i (t⁻¹ * (((r * s : 𝐑[i]) : G) * t * ((r * s : 𝐑[i]) : G)⁻¹)) 1 = _
      rw [hψ]
      simp
    · exact rootParam_eq h i (rootAct_mul h i (rootAct_rootParam h i r)
        (rootAct_rootParam h i s) (R_le_N h i s.2))

theorem parabolicHom_apply (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    parabolicHom h i r = ⟨psiG φ i (t⁻¹ * ((r : G) * t * (r : G)⁻¹)) 0,
      psiG φ i (t⁻¹ * ((r : G) * t * (r : G)⁻¹)) 1, rootParam h i r⟩ := rfl

theorem parabolicHom_z_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    (parabolicHom h i r).z = 0 ↔ (r : G) ∈ 𝐄[i] := by
  show rootParam h i r = 0 ↔ _
  constructor
  · intro h0
    have h1 := rootAct_rootParam h i r
    rw [h0] at h1
    exact mem_E_of_rootAct h i (R_le_N h i r.2) h1
  · intro he
    exact rootParam_eq h i (rootAct_E h i he)

theorem parabolicHom_xy_eq_zero_iff (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    (parabolicHom h i r).x = 0 ∧ (parabolicHom h i r).y = 0 ↔
      t⁻¹ * ((r : G) * t * (r : G)⁻¹) ∈ 𝐔[i] := by
  rw [← psiG_eq_zero_iff h.twoCore φ i (conj_t_mem_A h i r.2)]
  constructor
  · rintro ⟨h0, h1⟩
    exact vec2_ext h0 h1
  · intro h0
    exact ⟨congrFun h0 0, congrFun h0 1⟩

theorem parabolicHom_D (h : FCHyp L K n φ t) (i : Axis) {r : 𝐑[i]} (hr : (r : G) ∈ 𝐃[i]) :
    parabolicHom h i r = 1 := by
  have hz := (parabolicHom_z_eq_zero_iff h i r).mpr (h.D_le_E i hr)
  have hU : t⁻¹ * ((r : G) * t * (r : G)⁻¹) ∈ 𝐔[i] := by
    have h1 := h.twoCore.conj_t_mem φ i (inv_mem (map_subtype_le _ hr : (r : G) ∈ 𝐌[i]))
    rw [inv_inv] at h1
    rw [h.twoCore.t_inv]
    exact h1
  have hxy := (parabolicHom_xy_eq_zero_iff h i r).mpr hU
  ext
  · exact hxy.1
  · exact hxy.2
  · exact hz

theorem parabolicHom_Q (h : FCHyp L K n φ t) (i : Axis) {r : 𝐑[i]} (hr : (r : G) ∈ 𝐐) :
    (parabolicHom h i r).x = 0 ∧ (parabolicHom h i r).y = 0 := by
  rw [parabolicHom_xy_eq_zero_iff, mem_centralizer_singleton_iff.mp (h.setup.Q_le_C hr),
    mul_inv_cancel_right, inv_mul_cancel]
  exact one_mem _

theorem mem_Qi_iff (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    (r : G) ∈ 𝐐[i] ↔ (parabolicHom h i r).x = 0 ∧ (parabolicHom h i r).y = 0 := by
  constructor
  · intro hr
    have hr' : (r : G) ∈ (𝐐 : Set G) * (𝐃[i] : Set G) := by
      rw [(h.Qi_facts i).1]
      exact hr
    obtain ⟨q, hq, d, hd, hqd⟩ := hr'
    have e : r = ⟨q, mem_sup_left hq⟩ * ⟨d, D_le_R h i hd⟩ := Subtype.ext hqd.symm
    rw [e, map_mul, parabolicHom_D h i (r := ⟨d, D_le_R h i hd⟩) hd, mul_one]
    exact parabolicHom_Q h i hq
  · intro hxy
    have hU := (parabolicHom_xy_eq_zero_iff h i r).mp hxy
    have hrM : (r : G) ∈ 𝐌[i] := by
      refine (h.aff_zero_eq_zero_iff i ⟨r, R_le_N h i r.2⟩).mp ?_
      rw [(h.actHyp i).aff_zero]
      exact (psiG_eq_zero_iff h.twoCore φ i (conj_t_mem_A h i r.2)).mpr hU
    have hr' : (r : G) ∈ (𝐐 : Set G) * (𝐄[i] : Set G) := by
      rw [R_mul h i]
      exact r.2
    obtain ⟨q, hq, e, he, hqe⟩ := hr'
    have heM : e ∈ 𝐌[i] := by
      have h1 := mul_mem (inv_mem (h.Q_le_M i hq)) hrM
      rwa [← hqe, inv_mul_cancel_left] at h1
    have heD : e ∈ 𝐃[i] := by
      rw [← (coreFacts h i).E_inf_M]
      exact mem_inf.mpr ⟨he, heM⟩
    rw [← hqe]
    exact mul_mem (mem_sup_left hq) (mem_sup_right heD)

theorem mem_H_iff_ZP (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) :
    r ∈ 𝐇 ↔ t⁻¹ * (r * t * r⁻¹) ∈ 𝐙 := by
  constructor
  · intro hrH
    have hmem : r * t * r⁻¹ ∈ {x : G | ∃ g ∈ 𝐇, x = g⁻¹ * t * g} :=
      ⟨r⁻¹, inv_mem hrH, by rw [inv_inv]⟩
    rw [h.orbit_H] at hmem
    obtain ⟨z, hz, hzr⟩ := hmem
    rw [hzr, inv_mul_cancel_left]
    exact hz
  · intro hz
    have hmem : t * (t⁻¹ * (r * t * r⁻¹)) ∈ {x : G | ∃ z ∈ 𝐙, x = t * z} := ⟨_, hz, rfl⟩
    rw [← h.orbit_H, mul_inv_cancel_left] at hmem
    obtain ⟨g, hg, hgr⟩ := hmem
    have hgrC : g * r ∈ 𝐂 := by
      rw [mem_centralizer_singleton_iff]
      calc g * r * t = g * (r * t * r⁻¹) * r := by group
        _ = g * (g⁻¹ * t * g) * r := by rw [hgr]
        _ = t * (g * r) := by group
    have hgrQ : g * r ∈ 𝐐 := by
      rw [← R_inf_C h i]
      exact mem_inf.mpr ⟨mul_mem (H_le_R h i hg) hr, hgrC⟩
    have e : r = g⁻¹ * (g * r) := by group
    rw [e]
    exact mul_mem (inv_mem hg) ((le_sup_left.trans le_sup_left : 𝐐 ≤ 𝐇) hgrQ)

theorem mem_H_iff (h : FCHyp L K n φ t) (i : Axis) (r : 𝐑[i]) :
    (r : G) ∈ 𝐇 ↔ (parabolicHom h i r).y = 0 := by
  rw [mem_H_iff_ZP h i r.2, ← psiG_one_eq_zero_iff h i (conj_t_mem_A h i r.2)]
  rfl

theorem ker_parabolicHom (h : FCHyp L K n φ t) (i : Axis) :
    (parabolicHom h i).ker = (𝐃[i]).subgroupOf 𝐑[i] := by
  ext r
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h1
    have hQi : (r : G) ∈ 𝐐[i] := (mem_Qi_iff h i r).mpr ⟨by rw [h1]; rfl, by rw [h1]; rfl⟩
    have hE : (r : G) ∈ 𝐄[i] := (parabolicHom_z_eq_zero_iff h i r).mp (by rw [h1]; rfl)
    rw [← (coreFacts h i).E_inf_M]
    exact mem_inf.mpr ⟨hE, h.Qi_le_M i hQi⟩
  · exact parabolicHom_D h i

theorem parabolicHom_surjective (h : FCHyp L K n φ t) (i : Axis) :
    Function.Surjective (parabolicHom h i) := by
  intro p
  obtain ⟨e, he, htr⟩ := translations_mem_E h i ![p.x, p.y]
  obtain ⟨q, hq, hqc⟩ := exists_rootAct_P h i p.z
  set e' : 𝐑[i] := ⟨e, mem_sup_right he⟩
  set q' : 𝐑[i] := ⟨q, mem_sup_left (mem_sup_left hq)⟩
  refine ⟨e' * q', ?_⟩
  have hψe : psiG φ i (t⁻¹ * ((e : G) * t * (e : G)⁻¹)) = ![p.x, p.y] := by
    have h1 := (h.actHyp i).aff_zero e
    rw [htr, zero_add] at h1
    exact h1.symm
  have hqxy := parabolicHom_Q h i (r := q') (mem_sup_left hq)
  have hqz : (parabolicHom h i q').z = p.z := rootParam_eq h i hqc
  have hez : (parabolicHom h i e').z = 0 := (parabolicHom_z_eq_zero_iff h i e').mpr he
  rw [map_mul]
  ext
  · rw [Heis.mul_x, hqxy.2, mul_zero, add_zero, hqxy.1, add_zero]
    exact congrFun hψe 0
  · rw [Heis.mul_y, hqxy.2, add_zero]
    exact congrFun hψe 1
  · rw [Heis.mul_z, hez, hqz, zero_add]

theorem exists_parabolicEquiv (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐃[i]).subgroupOf 𝐑[i]).Normal,
      ∃ ι : (↥𝐑[i] ⧸ (𝐃[i]).subgroupOf 𝐑[i]) ≃* Heis K, ∀ r : 𝐑[i], ι r = parabolicHom h i r := by
  have := D_normal_R h i
  refine ⟨this, (QuotientGroup.quotientMulEquivOfEq (ker_parabolicHom h i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (parabolicHom_surjective h i)), fun r => ?_⟩
  rfl

omit [Finite G] [Finite K] in
theorem D_le_H (i : Axis) : 𝐃[i] ≤ 𝐇 := by
  cases i
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right.trans le_sup_right

omit [Finite G] [Finite K] in
theorem Qi_le_H (i : Axis) : 𝐐[i] ≤ 𝐇 := by
  cases i
  · exact le_sup_left
  · exact le_sup_right

theorem conj_mem_H (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {x : G}
    (hx : x ∈ 𝐇) : r * x * r⁻¹ ∈ 𝐇 := by
  set r' : 𝐑[i] := ⟨r, hr⟩
  set x' : 𝐑[i] := ⟨x, H_le_R h i hx⟩
  have h1 := (mem_H_iff h i x').mp hx
  have h2 : ((r' * x' * r'⁻¹ : 𝐑[i]) : G) ∈ 𝐇 := by
    rw [mem_H_iff h i, map_mul, map_mul, map_inv, Heis.conj_y]
    exact h1
  exact h2

theorem H_normal_R (h : FCHyp L K n φ t) (i : Axis) : ((𝐇 : Subgroup G).subgroupOf 𝐑[i]).Normal :=
  ⟨fun _ hx r => mem_subgroupOf.mpr (conj_mem_H h i r.2 (mem_subgroupOf.mp hx))⟩

theorem R_le_normalizer_H (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ≤ normalizer ((𝐇 : Subgroup G) : Set G) := fun _ hr =>
  RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hx => conj_mem_H h i hr hx

theorem relIndex_H (h : FCHyp L K n φ t) (i : Axis) :
    (𝐇 : Subgroup G).relIndex 𝐑[i] = Nat.card K := by
  have h1 := relIndex_mul_card 𝐇 𝐑[i]
  rw [inf_of_le_left (H_le_R h i), h.H_facts.2.2, card_R h i] at h1
  have hq : 0 < 2 * Nat.card K ^ 6 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h2 : (𝐇 : Subgroup G).relIndex 𝐑[i] * (2 * Nat.card K ^ 6) =
      Nat.card K * (2 * Nat.card K ^ 6) := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem R_inf_normalizer_Qi (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ⊓ normalizer ((𝐐[i] : Subgroup G) : Set G) = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrN⟩ := mem_inf.mp hr
    obtain ⟨q, hq, hqc⟩ := exists_rootAct_P h i 1
    set r' : 𝐑[i] := ⟨r, hrR⟩
    set q' : 𝐑[i] := ⟨q, mem_sup_left (mem_sup_left hq)⟩
    have hqQi : q ∈ 𝐐[i] := mem_sup_left (mem_sup_left hq)
    have h1 : ((r' * q' * r'⁻¹ : 𝐑[i]) : G) ∈ 𝐐[i] := (mem_normalizer_iff.mp hrN q).mp hqQi
    have h2 := ((mem_Qi_iff h i _).mp h1).1
    have hFq : parabolicHom h i q' = ⟨0, 0, 1⟩ := by
      have hxy := parabolicHom_Q h i (r := q') (mem_sup_left hq)
      ext
      · exact hxy.1
      · exact hxy.2
      · exact rootParam_eq h i hqc
    rw [map_mul, map_mul, map_inv, hFq, Heis.conj_root_x, neg_eq_zero] at h2
    exact (mem_H_iff h i r').mpr h2
  · exact le_inf (H_le_R h i) (h.H_le_normalizer_Qi i)

theorem R_inf_normalizer_Q (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ⊓ normalizer (𝐐 : Set G) = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrN⟩ := mem_inf.mp hr
    rw [← R_inf_normalizer_Qi h i]
    exact mem_inf.mpr ⟨hrR, RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hy =>
      conj_mem_sup (fun q hq => (mem_normalizer_iff.mp hrN q).mp hq)
        (fun _ hd => h.conj_mem_D i (R_le_N h i hrR) hd) hy⟩
  · exact le_inf (H_le_R h i) h.H_le_normalizer_Q

theorem R_inf_normalizer_A (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ⊓ normalizer (𝐀[i.swap] : Set G) = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrN⟩ := mem_inf.mp hr
    rw [← R_inf_normalizer_Q h i]
    refine mem_inf.mpr ⟨hrR, ?_⟩
    rw [← B_sup_A_eq_Q i]
    exact RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hy =>
      conj_mem_sup (fun b hb => (mem_normalizer_iff.mp (R_le_N h i hrR) b).mp hb)
        (fun a ha => (mem_normalizer_iff.mp hrN a).mp ha) hy
  · refine le_inf (H_le_R h i) fun x hx => h.N_le_normalizer_A i.swap ?_
    have hY := sup_le (h.Qi_le_Y Axis.one) (h.Qi_le_Y Axis.two) hx
    cases i
    · exact hY.2
    · exact hY.1.2

theorem R_inf_R (h : FCHyp L K n φ t) : 𝐑[Axis.one] ⊓ 𝐑[Axis.two] = 𝐇 := by
  apply le_antisymm
  · intro r hr
    obtain ⟨h1, h2⟩ := mem_inf.mp hr
    rw [← R_inf_normalizer_Q h Axis.one]
    refine mem_inf.mpr ⟨h1, ?_⟩
    rw [← B_sup_B_eq_Q]
    exact RootAxisTwoCore.mem_normalizer_of_conj_le fun _ hy =>
      conj_mem_sup (fun b hb => (mem_normalizer_iff.mp (R_le_N h _ h1) b).mp hb)
        (fun b hb => (mem_normalizer_iff.mp (R_le_N h _ h2) b).mp hb) hy
  · exact le_inf (H_le_R h _) (H_le_R h _)

omit [Finite G] [Finite K] [CharP K 2] in
theorem commutator_mem_closure_sq {X : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    x⁻¹ * (y⁻¹ * x * y) ∈ closure {w : G | ∃ v ∈ X, w = v * v} := by
  have e : x⁻¹ * (y⁻¹ * x * y) = (x⁻¹ * x⁻¹) * ((x * y⁻¹) * (x * y⁻¹)) * (y * y) := by group
  rw [e]
  exact mul_mem (mul_mem (subset_closure ⟨x⁻¹, inv_mem hx, rfl⟩)
    (subset_closure ⟨x * y⁻¹, mul_mem hx (inv_mem hy), rfl⟩)) (subset_closure ⟨y, hy, rfl⟩)

theorem mul_self_mem_D (h : FCHyp L K n φ t) (i : Axis) {y : G} (hy : y ∈ 𝐇) :
    y * y ∈ 𝐃[i] := by
  set y' : 𝐑[i] := ⟨y, H_le_R h i hy⟩
  have hy0 := (mem_H_iff h i y').mp hy
  have h1 : y' * y' ∈ (parabolicHom h i).ker := by
    rw [MonoidHom.mem_ker, map_mul, Heis.mul_self, hy0, mul_zero]
    rfl
  rw [ker_parabolicHom] at h1
  exact h1

theorem closure_sq_H (h : FCHyp L K n φ t) : closure {x : G | ∃ y ∈ 𝐇, x = y * y} = 𝐙 := by
  set X := closure {x : G | ∃ y ∈ 𝐇, x = y * y} with hX
  have hZX : 𝐙 ≤ X := by
    rw [← h.setup.closure_sq_eq rfl]
    exact closure_mono fun x ⟨y, hy, hxy⟩ => ⟨y, (le_sup_left.trans le_sup_left : 𝐐 ≤ 𝐇) hy, hxy⟩
  have hXD : X ≤ 𝐃[Axis.one] ⊓ 𝐃[Axis.two] := (closure_le _).mpr fun x ⟨y, hy, hxy⟩ =>
    hxy ▸ mem_inf.mpr ⟨mul_self_mem_D h _ hy, mul_self_mem_D h _ hy⟩
  have hXB : ∀ w ∈ X, w ∈ 𝐁[Axis.one] ∧ w ∈ 𝐁[Axis.two] := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp (hXD hw)
    have hwQ : w ∈ 𝐐 := by
      rw [← h.Q1_inf_Q2]
      exact mem_inf.mpr ⟨mem_sup_right hw1, mem_sup_right hw2⟩
    refine ⟨?_, ?_⟩
    · rw [← h.Q_inf_D Axis.one]
      exact mem_inf.mpr ⟨hwQ, hw1⟩
    · rw [← h.Q_inf_D Axis.two]
      exact mem_inf.mpr ⟨hwQ, hw2⟩
  have htX : t ∉ X := by
    intro htX
    obtain ⟨a, ha, hψa⟩ := exists_psiG_eq h.twoCore φ Axis.one ![0, 1]
    have haZ : a ∉ 𝐙 := fun haZ => by
      have h1 := psiG_ZP_one h Axis.one haZ
      rw [hψa] at h1
      simp at h1
    have hmem : t * a ∈ {x : G | ∃ r ∈ 𝐑[Axis.one], x = r⁻¹ * t * r} := by
      rw [orbit_R h]
      exact ⟨a, ha, rfl⟩
    obtain ⟨r, hr, hra⟩ := hmem
    have hrX : t * a ∈ X := by
      have h1 := Setup.conj_mem_closure_sq (R_le_normalizer_H h _ (inv_mem hr)) htX
      rwa [inv_inv, ← hra] at h1
    obtain ⟨hB1, hB2⟩ := hXB _ hrX
    rcases mem_ZP_of_mem_B_inf_B h hB1 hB2 with h1 | h1
    · apply h.twoCore.t_not_mem
      have h2 := mul_mem (pull_le φ _ h1) (inv_mem (pull_le φ _ ha))
      rwa [mul_inv_cancel_right] at h2
    · rw [← mul_assoc, h.setup.t_mul_t, one_mul] at h1
      exact haZ h1
  refine le_antisymm (fun w hw => ?_) hZX
  obtain ⟨hB1, hB2⟩ := hXB w hw
  rcases mem_ZP_of_mem_B_inf_B h hB1 hB2 with h1 | h1
  · exact h1
  · refine absurd ?_ htX
    have h2 := mul_mem (hZX h1) (inv_mem hw)
    rwa [mul_inv_cancel_right] at h2

theorem mul_self_mem_ZP (h : FCHyp L K n φ t) {y : G} (hy : y ∈ 𝐇) : y * y ∈ 𝐙 :=
  closure_sq_H h ▸ subset_closure ⟨y, hy, rfl⟩

theorem closure_sq_E (h : FCHyp L K n φ t) (i : Axis) :
    closure {x : G | ∃ y ∈ 𝐄[i], x = y * y} = 𝐀[i] := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨e, he, rfl⟩
    have ha := conj_t_mem_A h i (mem_sup_right he : e ∈ 𝐑[i])
    obtain ⟨M, hM⟩ : ∃ M : SL₂ K,
        ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ psiG φ i (t⁻¹ * (e * t * e⁻¹))) 1 = 0 := by
      by_cases hv : psiG φ i (t⁻¹ * (e * t * e⁻¹)) = 0
      · exact ⟨1, by rw [hv, Matrix.mulVec_zero]; rfl⟩
      · have h10 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
        obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hv h10
        exact ⟨M, by rw [hM]; simp⟩
    obtain ⟨hsC, hsA, -, hsN⟩ := h.symm_s_mem i M
    set s : G := ((φ.symm (sHom K i M) : L) : G) with hs
    have he' : s * e * s⁻¹ ∈ 𝐄[i] := conj_mem_pCore_map hsN he
    have hsts : s * t * s⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp hsC, mul_inv_cancel_right]
    have e1 : t⁻¹ * ((s * e * s⁻¹) * t * (s * e * s⁻¹)⁻¹) = s * (t⁻¹ * (e * t * e⁻¹)) * s⁻¹ := by
      calc t⁻¹ * ((s * e * s⁻¹) * t * (s * e * s⁻¹)⁻¹)
          = (s * t * s⁻¹)⁻¹ * ((s * e * s⁻¹) * (s * t * s⁻¹) * (s * e * s⁻¹)⁻¹) := by
            rw [hsts]
        _ = s * (t⁻¹ * (e * t * e⁻¹)) * s⁻¹ := by group
    have h1 : t⁻¹ * ((s * e * s⁻¹) * t * (s * e * s⁻¹)⁻¹) ∈ 𝐙 := by
      rw [e1, ← psiG_one_eq_zero_iff h i (psiG_conj_s h.twoCore φ i M ha).1,
        (psiG_conj_s h.twoCore φ i M ha).2]
      exact hM
    have h2 : s * e * s⁻¹ ∈ 𝐇 := (mem_H_iff_ZP h i (mem_sup_right he')).mpr h1
    have h3 : (s * e * s⁻¹) * (s * e * s⁻¹) ∈ 𝐀[i] :=
      pull_mono φ (center_le_rootA i) (mul_self_mem_ZP h h2)
    have h4 := (mem_normalizer_iff.mp (inv_mem hsA) _).mp h3
    rwa [show s⁻¹ * ((s * e * s⁻¹) * (s * e * s⁻¹)) * s⁻¹⁻¹ = e * e by group] at h4
  · intro a ha
    have hmem : t * a ∈ {x : G | ∃ e ∈ 𝐄[i], x = e⁻¹ * t * e} := by
      rw [orbit_E h i]
      exact ⟨a, ha, rfl⟩
    obtain ⟨e, he, hea⟩ := hmem
    have htE : t ∈ 𝐄[i] := h.D_le_E i (h.B_le_D i (mem_sup_left (mem_zpowers t)))
    have e1 : a = t⁻¹ * (e⁻¹ * t * e) := by rw [← hea]; group
    rw [e1]
    exact commutator_mem_closure_sq htE he

theorem closure_sq_D (h : FCHyp L K n φ t) (i : Axis) :
    closure {x : G | ∃ y ∈ 𝐃[i], x = y * y} = 𝐔[i] := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨d, hd, rfl⟩
    have hdZ := mul_self_mem_ZP h (D_le_H i hd)
    have hdA : d * d ∈ 𝐀[i] := pull_mono φ (center_le_rootA i) hdZ
    have hdet : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      simp [Matrix.det_fin_two]
    set M : SL₂ K := ⟨!![1, 0; 1, 1], hdet⟩
    have hsd : ((φ.symm (sHom K i M) : L) : G) * d * ((φ.symm (sHom K i M) : L) : G)⁻¹ ∈ 𝐃[i] :=
      conj_mem_pCore_map (h.symm_s_mem_M i M) hd
    have h1 := psiG_ZP_one h i (mul_self_mem_ZP h (D_le_H i hsd))
    rw [show ((φ.symm (sHom K i M) : L) : G) * d * ((φ.symm (sHom K i M) : L) : G)⁻¹ *
        (((φ.symm (sHom K i M) : L) : G) * d * ((φ.symm (sHom K i M) : L) : G)⁻¹) =
        ((φ.symm (sHom K i M) : L) : G) * (d * d) * ((φ.symm (sHom K i M) : L) : G)⁻¹ by group,
      (psiG_conj_s h.twoCore φ i M hdA).2] at h1
    have h0 := psiG_ZP_one h i hdZ
    have h2 : psiG φ i (d * d) 0 = 0 := by
      simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] using h1
    exact (psiG_eq_zero_iff h.twoCore φ i hdA).mp (vec2_ext h2 h0)
  · intro u hu
    obtain ⟨_, e, he, -⟩ := h.quotient_D i
    obtain ⟨q, hq⟩ := e.surjective ⟨u, hu⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := he d
    rw [hq] at h1
    have htD : t ∈ 𝐃[i] := h.B_le_D i (mem_sup_left (mem_zpowers t))
    have h2 : u = t⁻¹ * ((d : G)⁻¹ * t * d) := h1
    rw [h2]
    exact commutator_mem_closure_sq htD d.2

theorem mem_H_iff_E (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) :
    e ∈ 𝐇 ↔ t⁻¹ * (e⁻¹ * t * e) ∈ 𝐙 := by
  rw [← inv_mem_iff (x := e), mem_H_iff_ZP h i (inv_mem (mem_sup_right he)), inv_inv]

theorem quotient_Hi (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐃[i]).subgroupOf (𝐇 ⊓ 𝐄[i])).Normal, ∃ _ : ((𝐔[i]).subgroupOf 𝐙).Normal,
      ∃ θ : (↥(𝐇 ⊓ 𝐄[i]) ⧸ (𝐃[i]).subgroupOf (𝐇 ⊓ 𝐄[i])) ≃* (↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙),
        ∀ x : ↥(𝐇 ⊓ 𝐄[i]), ∃ z : 𝐙, (z : G) = t⁻¹ * ((x : G)⁻¹ * t * x) ∧ θ x = z := by
  have hUZ : ((𝐔[i]).subgroupOf 𝐙).Normal := ⟨fun u hu z => by
    rw [mem_subgroupOf] at hu ⊢
    have hc : (z : G) * u = u * z :=
      Setup.comm_P_ZP (Setup.ZP_le_PG z.2) (pull_mono φ (rootU_le_center i) hu)
    rw [coe_mul, coe_mul, coe_inv, hc, mul_inv_cancel_right]
    exact hu⟩
  have hDH : ((𝐃[i]).subgroupOf (𝐇 ⊓ 𝐄[i])).Normal := ⟨fun _ hd x => mem_subgroupOf.mpr
    (h.conj_mem_D i (map_subtype_le _ (mem_inf.mp x.2).2) (mem_subgroupOf.mp hd))⟩
  have hmem : ∀ x : ↥(𝐇 ⊓ 𝐄[i]), t⁻¹ * ((x : G)⁻¹ * t * x) ∈ 𝐙 := fun x =>
    (mem_H_iff_E h i (mem_inf.mp x.2).2).mp (mem_inf.mp x.2).1
  have hmk : ∀ a b : 𝐙, (a : ↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙) = b ↔ psiG φ i a = psiG φ i b :=
    fun a b => by
      rw [QuotientGroup.eq, mem_subgroupOf, psiG_eq_iff h.twoCore φ i
        (pull_mono φ (center_le_rootA i) a.2) (pull_mono φ (center_le_rootA i) b.2)]
      rfl
  let f : ↥(𝐇 ⊓ 𝐄[i]) →* ↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙 :=
    { toFun := fun x => ((⟨_, hmem x⟩ : 𝐙) : ↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙)
      map_one' := by
        rw [← QuotientGroup.mk_one, hmk]
        congr 1
        simp
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, hmk]
        have hxA := pull_mono φ (center_le_rootA i) (hmem x)
        have hyA := pull_mono φ (center_le_rootA i) (hmem y)
        have hyE : (y : G)⁻¹ ∈ 𝐄[i] := inv_mem (mem_inf.mp y.2).2
        have hyx := h.E_lin i hyE hxA
        rw [inv_inv] at hyx
        have hyxA : (y : G)⁻¹ * (t⁻¹ * ((x : G)⁻¹ * t * x)) * y ∈ 𝐀[i] := by
          have := (h.actHyp i).conj_A _ (map_subtype_le _ hyE) _ hxA
          rwa [inv_inv] at this
        have e : t⁻¹ * (((x * y : ↥(𝐇 ⊓ 𝐄[i])) : G)⁻¹ * t * ((x * y : ↥(𝐇 ⊓ 𝐄[i])) : G)) =
            t⁻¹ * ((y : G)⁻¹ * t * y) * ((y : G)⁻¹ * (t⁻¹ * ((x : G)⁻¹ * t * x)) * y) := by
          simp only [coe_mul]
          group
        show psiG φ i (t⁻¹ * (((x * y : ↥(𝐇 ⊓ 𝐄[i])) : G)⁻¹ * t *
          ((x * y : ↥(𝐇 ⊓ 𝐄[i])) : G))) = psiG φ i (t⁻¹ * ((x : G)⁻¹ * t * x) *
            (t⁻¹ * ((y : G)⁻¹ * t * y)))
        rw [e, psiG_mul h.twoCore φ i hyA hyxA, hyx, psiG_mul h.twoCore φ i hxA hyA, add_comm] }
  have hf : ∀ x, f x = ((⟨_, hmem x⟩ : 𝐙) : ↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙) := fun _ => rfl
  have hker : (𝐃[i]).subgroupOf (𝐇 ⊓ 𝐄[i]) = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    change (x : G) ∈ 𝐃[i] ↔ t⁻¹ * ((x : G)⁻¹ * t * x) ∈ 𝐔[i]
    have hxE := (mem_inf.mp x.2).2
    constructor
    · intro hx
      rw [h.twoCore.t_inv]
      exact h.twoCore.conj_t_mem φ i (map_subtype_le _ hx)
    · intro hu
      have hxM : (x : G) ∈ 𝐌[i] := FCHyp.mem_M_of (h.N_le_normalizer_U i (map_subtype_le _ hxE))
        hu (by rw [mul_inv_cancel_left])
      rw [← (coreFacts h i).E_inf_M]
      exact mem_inf.mpr ⟨hxE, hxM⟩
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hmz : t * z ∈ {x : G | ∃ e ∈ 𝐄[i], x = e⁻¹ * t * e} := by
      rw [orbit_E h i]
      exact ⟨z, pull_mono φ (center_le_rootA i) z.2, rfl⟩
    obtain ⟨e, he, hez⟩ := hmz
    have hz : t⁻¹ * (e⁻¹ * t * e) = z := by rw [← hez, inv_mul_cancel_left]
    have heH : e ∈ 𝐇 := (mem_H_iff_E h i he).mpr (by rw [hz]; exact z.2)
    refine ⟨⟨e, mem_inf.mpr ⟨heH, he⟩⟩, ?_⟩
    rw [hf]
    exact congrArg _ (Subtype.ext hz)
  exact ⟨hDH, hUZ, (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj), fun x => ⟨⟨_, hmem x⟩, rfl, rfl⟩⟩

theorem card_Hi (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card (𝐇 ⊓ 𝐄[i] : Subgroup G) = 2 * Nat.card K ^ 5 := by
  obtain ⟨_, _, θ, -⟩ := quotient_Hi h i
  have hDle : 𝐃[i] ≤ 𝐇 ⊓ 𝐄[i] := le_inf (D_le_H i) (h.D_le_E i)
  have h1 := card_eq_card_quotient_mul_card_subgroup ((𝐃[i]).subgroupOf (𝐇 ⊓ 𝐄[i]))
  have h2 := card_eq_card_quotient_mul_card_subgroup ((𝐔[i]).subgroupOf 𝐙)
  rw [Nat.card_congr θ.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hDle).toEquiv,
    h.card_D i] at h1
  rw [Nat.card_congr (subgroupOfEquivOfLe (pull_mono φ (rootU_le_center i))).toEquiv,
    FCHyp.card_ZP, FCHyp.card_U i] at h2
  have hq : 0 < Nat.card K := Nat.card_pos
  have h3 : Nat.card (↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙) = Nat.card K := by
    have h4 : Nat.card (↥𝐙 ⧸ (𝐔[i]).subgroupOf 𝐙) * Nat.card K = Nat.card K * Nat.card K := by
      rw [← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hq h4
  rw [h1, h3]
  ring

theorem quotient_R (h : FCHyp L K n φ t) (i : Axis) :
    ∃ _ : ((𝐃[i]).subgroupOf 𝐑[i]).Normal,
      ∃ ι : (↥𝐑[i] ⧸ (𝐃[i]).subgroupOf 𝐑[i]) ≃* Heis K,
      (∀ r : 𝐑[i], ((r : G) ∈ 𝐄[i] ↔ (ι r).z = 0) ∧
        ((r : G) ∈ 𝐐[i] ↔ (ι r).x = 0 ∧ (ι r).y = 0) ∧ ((r : G) ∈ 𝐇 ↔ (ι r).y = 0) ∧
        ((r : G) ∈ 𝐇 ⊓ 𝐄[i] ↔ (ι r).y = 0 ∧ (ι r).z = 0)) ∧
      (∀ S : Subgroup (↥𝐑[i] ⧸ (𝐃[i]).subgroupOf 𝐑[i]),
        Maximal (fun S : Subgroup (↥𝐑[i] ⧸ (𝐃[i]).subgroupOf 𝐑[i]) =>
          IsElementaryAbelian 2 S) S ↔
          S = ((𝐄[i]).subgroupOf 𝐑[i]).map (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i])) ∨
            S = ((𝐇 : Subgroup G).subgroupOf 𝐑[i]).map
              (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i]))) ∧
      Nat.card (((𝐄[i]).subgroupOf 𝐑[i]).map (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i]))) =
        Nat.card K ^ 2 ∧
      Nat.card (((𝐇 : Subgroup G).subgroupOf 𝐑[i]).map
        (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i]))) = Nat.card K ^ 2 := by
  obtain ⟨hn, ι, hι⟩ := exists_parabolicEquiv h i
  have himg : ∀ r : 𝐑[i], ((r : G) ∈ 𝐄[i] ↔ (ι r).z = 0) ∧
      ((r : G) ∈ 𝐐[i] ↔ (ι r).x = 0 ∧ (ι r).y = 0) ∧ ((r : G) ∈ 𝐇 ↔ (ι r).y = 0) ∧
      ((r : G) ∈ 𝐇 ⊓ 𝐄[i] ↔ (ι r).y = 0 ∧ (ι r).z = 0) := fun r => by
    rw [hι r]
    refine ⟨(parabolicHom_z_eq_zero_iff h i r).symm, mem_Qi_iff h i r, mem_H_iff h i r, ?_⟩
    rw [mem_inf, mem_H_iff h i r, parabolicHom_z_eq_zero_iff h i r]
  have hDE : (𝐃[i]).subgroupOf 𝐑[i] ≤ (𝐄[i]).subgroupOf 𝐑[i] := fun _ hx =>
    mem_subgroupOf.mpr (h.D_le_E i (mem_subgroupOf.mp hx))
  have hDH : (𝐃[i]).subgroupOf 𝐑[i] ≤ (𝐇 : Subgroup G).subgroupOf 𝐑[i] := fun _ hx =>
    mem_subgroupOf.mpr (D_le_H i (mem_subgroupOf.mp hx))
  have hE : ∀ x, x ∈ ((𝐄[i]).subgroupOf 𝐑[i]).map (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i])) ↔
      (ι x).z = 0 := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mem_map_mk'_iff hDE, mem_subgroupOf, (himg r).1]
  have hH : ∀ x, x ∈ ((𝐇 : Subgroup G).subgroupOf 𝐑[i]).map
      (QuotientGroup.mk' ((𝐃[i]).subgroupOf 𝐑[i])) ↔ (ι x).y = 0 := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    rw [mem_map_mk'_iff hDH, mem_subgroupOf, (himg r).2.2.1]
  obtain ⟨hmax, hcE, hcH⟩ := maximal_elementaryAbelian ι hE hH
  exact ⟨hn, ι, himg, hmax, hcE, hcH⟩

theorem parabolicFacts (h : FCHyp L K n φ t) (i : Axis) :
    ParabolicFacts K n t 𝐂 𝐐 𝐙 𝐔[i] 𝐀[i] 𝐀[i.swap] 𝐃[i] 𝐄[i] 𝐐[i] 𝐑[i] 𝐇 := by
  have hq := h.setup.card_K
  obtain ⟨hn, ι, himg, hmax, hcE, hcH⟩ := quotient_R h i
  exact
    { isPGroup := R_isPGroup h i
      card := by rw [card_R h i, hq]
      mul_eq := R_mul h i
      E_normal := ⟨le_sup_right, E_normal_R h i⟩
      inf_C := R_inf_C h i
      orbit := orbit_R h i
      normalizer_Q := R_inf_normalizer_Q h i
      normalizer_Qi := R_inf_normalizer_Qi h i
      normalizer_A := R_inf_normalizer_A h i
      H_normal := ⟨H_le_R h i, H_normal_R h i⟩
      index_H := by rw [relIndex_H h i, hq]
      quotient := ⟨hn, ι, himg, hmax, by rw [hcE, hq], by rw [hcH, hq]⟩
      quotient_Hi := quotient_Hi h i
      mem_Hi := fun _ he => mem_H_iff_E h i he
      card_Hi := by rw [card_Hi h i, hq]
      sq_E := closure_sq_E h i
      sq_D := closure_sq_D h i
      center_D := (coreFacts h i).center_D }

end Overgroup

end FullCenterParabolic

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

theorem standard_symplectic_four_full_center_first_parabolic_overgroups
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let C := centralizer ({(t : G)} : Set G)
    let U : Axis → Subgroup G := fun i => ((rootU K i).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun i => ((rootA K i).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ U i
    let B : Axis → Subgroup G := fun i => zpowers (t : G) ⊔ A i
    let M : Axis → Subgroup G := fun i => normalizer (V i : Set G)
    let N : Axis → Subgroup G := fun i => normalizer (B i : Set G)
    let D : Axis → Subgroup G := fun i => (CFSG.pCore 2 (M i)).map (M i).subtype
    let E : Axis → Subgroup G := fun i => (CFSG.pCore 2 (N i)).map (N i).subtype
    let Qi : Axis → Subgroup G := fun i => Q ⊔ D i
    let R : Axis → Subgroup G := fun i => Q ⊔ E i
    let H := Qi Axis.one ⊔ Qi Axis.two
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    (∀ i : Axis, ParabolicFacts K n (t : G) C Q ZP (U i) (A i) (A i.swap) (D i) (E i) (Qi i)
        (R i) H) ∧
      R Axis.one ⊓ R Axis.two = H ∧
      ((Qi Axis.one : Set G) * (Qi Axis.two : Set G) = H ∧ IsPGroup 2 H ∧
        Nat.card H = 2 * (2 ^ n) ^ 6) ∧
      H ⊓ C = Q ∧ (center H).map H.subtype = ZP ∧
      closure {x : G | ∃ y ∈ H, x = y * y} = ZP := by
  intro TG PG Q ZP C U A V B M N D E Qi R H hfull
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨hTG₀, hF⟩ := FCHyp.of_setup hS (hO := hO) hLn hfull'
  have hTG : TG = zpowers (t : G) := hTG₀
  clear_value ZP PG TG
  subst hTG hPG hZP
  obtain ⟨hH1, hH2, hH3⟩ := hF.H_facts
  exact ⟨fun i => parabolicFacts hF i, R_inf_R hF, ⟨hH1, hH2, hH3.trans (by rw [hK])⟩,
    hF.H_inf_C, hF.center_H, closure_sq_H hF⟩

end CFSG.LocalAnalysis.SymplecticFourStandard
