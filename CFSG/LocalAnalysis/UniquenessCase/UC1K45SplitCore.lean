module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open CFSG.Quasithin Subgroup
open scoped commutatorElement

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

def sigOne : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

def sigTwo : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

def sigThree : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 1 2

def sgLoc : Fin 4 → Equiv.Perm (Fin 5) := ![1, sigOne, sigTwo, sigThree]

theorem sgLoc_injective : Function.Injective sgLoc := by decide +kernel

theorem sgLoc_mul : ∀ k j : Fin 4, ∃ m, sgLoc k * sgLoc j = sgLoc m := by decide +kernel

theorem sgLoc_inv : ∀ k : Fin 4, ∃ m, (sgLoc k)⁻¹ = sgLoc m := by decide +kernel

def V4 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := Set.range sgLoc
  one_mem' := ⟨0, by decide +kernel⟩
  mul_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨j, rfl⟩
    obtain ⟨m, hm⟩ := sgLoc_mul k j
    exact ⟨m, hm.symm⟩
  inv_mem' := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨m, hm⟩ := sgLoc_inv k
    exact ⟨m, hm.symm⟩

theorem sigOne_alt : sigOne ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sigTwo_alt : sigTwo ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sigOne_sq : sigOne * sigOne = 1 := by decide +kernel

theorem sigTwo_sq : sigTwo * sigTwo = 1 := by decide +kernel

theorem sigOne_comm_sigTwo : sigOne * sigTwo = sigTwo * sigOne := by decide +kernel

theorem sigOne_ne_one : sigOne ≠ 1 := by decide +kernel

theorem sigTwo_ne_one : sigTwo ≠ 1 := by decide +kernel

theorem sigOne_mul_sigTwo_ne_one : sigOne * sigTwo ≠ 1 := by decide +kernel

theorem V4_le_alt : V4 ≤ alternatingGroup (Fin 5) := by
  rintro x ⟨k, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases k <;> decide +kernel

theorem card_V4 : Nat.card V4 = 4 := by
  have h : Nat.card (Set.range sgLoc) = Nat.card (Fin 4) :=
    Nat.card_range_of_injective sgLoc_injective
  rw [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h
  exact h

theorem index_V4 : V4.index = 30 := by
  have h := Subgroup.card_mul_index V4
  rw [card_V4] at h
  have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide +kernel
  rw [hperm] at h
  omega

theorem relIndex_V4 : V4.relIndex (alternatingGroup (Fin 5)) = 15 := by
  have h := Subgroup.relIndex_mul_index V4_le_alt
  rw [index_V4, alternatingGroup.index_eq_two] at h
  omega

theorem card_coreMod_five : Nat.card (G6.coreMod 5) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem coreMod_sq : ∀ w : G6.coreMod 5, w * w = 1 := by decide +kernel

theorem coreMod_mul_self_mul_self (a m : G6.coreMod 5) : a * (a * m) * m = 1 := by
  calc a * (a * m) * m = (a * a) * (m * m) := by ac_rfl
    _ = 1 := by rw [coreMod_sq, coreMod_sq, mul_one]

def aMod : MulAut (G6.coreMod 5) := G6.coreAct 5 sigOne

def bMod : MulAut (G6.coreMod 5) := G6.coreAct 5 sigTwo

theorem fix_a_eq_range : ∀ w : G6.coreMod 5, aMod w = w → ∃ m, aMod m * m = w := by
  decide +kernel

theorem fix_b_eq_range : ∀ w : G6.coreMod 5, bMod w = w → ∃ m, bMod m * m = w := by
  decide +kernel

theorem fix_socle_eq_range : ∀ u : G6.coreMod 5, aMod u = u → bMod u = u →
    ∃ m, aMod (bMod m * m) * (bMod m * m) = u := by
  decide +kernel

theorem a_sq_zero : ∀ x : G6.coreMod 5, aMod (aMod x * x) * (aMod x * x) = 1 := by
  decide +kernel

theorem aMod_sq : ∀ x : G6.coreMod 5, aMod (aMod x) = x := by
  intro x
  have h : aMod * aMod = 1 := by
    show G6.coreAct 5 sigOne * G6.coreAct 5 sigOne = 1
    rw [← map_mul, sigOne_sq, map_one]
  rw [← MulAut.mul_apply, h]
  rfl

theorem bMod_sq : ∀ x : G6.coreMod 5, bMod (bMod x) = x := by
  intro x
  have h : bMod * bMod = 1 := by
    show G6.coreAct 5 sigTwo * G6.coreAct 5 sigTwo = 1
    rw [← map_mul, sigTwo_sq, map_one]
  rw [← MulAut.mul_apply, h]
  rfl

theorem aMod_comm_bMod : ∀ x : G6.coreMod 5, aMod (bMod x) = bMod (aMod x) := by
  intro x
  show G6.coreAct 5 sigOne (G6.coreAct 5 sigTwo x) = G6.coreAct 5 sigTwo (G6.coreAct 5 sigOne x)
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, sigOne_comm_sigTwo]

theorem commutator_mul_conj {G : Type*} [Group G] (x y t : G) (hx : x * x = 1) (hy : y * y = 1)
    (ht : t * t = 1) :
    ⁅x * t, y⁆ = ⁅x, y⁆ * (y * (x * (⁅y, t⁆ : G) * x⁻¹) * y⁻¹) := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
    inv_eq_of_mul_eq_one_right ht]
  have hR : (x * y * x * y) * (y * (x * (y * t * y * t) * x) * y)
      = x * t * y * t * x * y := by
    calc
      (x * y * x * y) * (y * (x * (y * t * y * t) * x) * y)
          = x * y * x * (y * y) * x * y * t * y * t * x * y := by group
      _ = x * y * x * 1 * x * y * t * y * t * x * y := by rw [hy]
      _ = x * y * x * x * y * t * y * t * x * y := by rw [mul_one]
      _ = x * y * (x * x) * y * t * y * t * x * y := by group
      _ = x * y * 1 * y * t * y * t * x * y := by rw [hx]
      _ = x * y * y * t * y * t * x * y := by rw [mul_one]
      _ = x * (y * y) * t * y * t * x * y := by group
      _ = x * 1 * t * y * t * x * y := by rw [hy]
      _ = x * t * y * t * x * y := by rw [mul_one]
  rw [hR]
  group

theorem conj_commutator_left {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1) :
    a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * ⁅a, b⁆ * a⁻¹
      = b * a⁻¹ * b⁻¹ * a⁻¹ := by
        rw [commutatorElement_def,
          show a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ = (a * a) * b * a⁻¹ * b⁻¹ * a⁻¹ by group,
          ha, one_mul]
    _ = b * a * b * a := by rw [ha', hb']
    _ = ⁅a, b⁆⁻¹ := by
        rw [commutatorElement_def]
        simp only [mul_inv_rev, inv_inv, ha', hb']
        group

theorem conj_commutator_right {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1) :
    b * ⁅a, b⁆ * b⁻¹ = ⁅a, b⁆⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc b * ⁅a, b⁆ * b⁻¹
      = b * a * b * a⁻¹ * (b⁻¹ * b⁻¹) := by
        rw [commutatorElement_def,
          show b * (a * b * a⁻¹ * b⁻¹) * b⁻¹ = b * a * b * a⁻¹ * (b⁻¹ * b⁻¹) by group]
    _ = b * a * b * a⁻¹ := by rw [← mul_inv_rev, hb, inv_one, mul_one]
    _ = ⁅a, b⁆⁻¹ := by
        rw [commutatorElement_def]
        simp only [mul_inv_rev, inv_inv, ha', hb']
        group

private theorem le_normalizer_of_commute' {K : Type*} [Group K] {A B : Subgroup K}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set K) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 := hc a ha b hb
    have : b * a * b⁻¹ = a := by rw [← h1]; group
    rw [this]; exact ha
  · intro ha'
    have h1 := hc _ ha' b⁻¹ (B.inv_mem hb)
    have : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← h1]
        _ = b * a * b⁻¹ := by group
    rw [this]; exact ha'

private theorem zpow_of_mul_self' {M : Type*} [Group M] {w : M} (hw : w * w = 1) (i : ℤ) :
    w ^ i = 1 ∨ w ^ i = w := by
  have h2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  rcases Int.even_or_odd' i with ⟨k, hk | hk⟩
  · left; rw [hk, zpow_mul, h2, one_zpow]
  · right; rw [hk, zpow_add, zpow_mul, zpow_one, h2, one_zpow, one_mul]

private theorem mem_zpowers_sup_pair' {M : Type*} [Group M] {u v : M} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) {x : M} :
    x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  constructor
  · intro hx
    have hn : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v : Set M) := by
      refine le_normalizer_of_commute' fun c hc d hd => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_zpow (show Commute u v from huv) j i).eq).symm
    have hx' : x ∈ ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup M) : Set M) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rcases zpow_of_mul_self' hu i with h1 | h1 <;> rcases zpow_of_mul_self' hv j with h2 | h2 <;>
      simp [h1, h2]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private theorem closure_pair_eq_sup' {M : Type*} [Group M] (u v : M) :
    Subgroup.closure ({u, v} : Set M) = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  rfl

theorem exists_involution_lifting {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (hr : η.range = alternatingGroup (Fin 5))
    (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v))
    (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) (hσsq : σ * σ = 1)
    (hfix : ∀ w : G6.coreMod 5, G6.coreAct 5 σ w = w → ∃ m, G6.coreAct 5 σ m * m = w) :
    ∃ α : Γ, η α = σ ∧ α ^ 2 = 1 := by
  classical
  have hσ' : σ ∈ η.range := by rw [hr]; exact hσ
  obtain ⟨g, hg⟩ := hσ'
  have hVg : g ^ 2 ∈ V := by
    rw [← hk, MonoidHom.mem_ker, map_pow, hg, pow_two, hσsq]
  have hconj : MulAut.conjNormal g ⟨g ^ 2, hVg⟩ = ⟨g ^ 2, hVg⟩ := by
    ext
    rw [MulAut.conjNormal_apply]
    group
  have hw : G6.coreAct 5 σ (θ ⟨g ^ 2, hVg⟩) = θ ⟨g ^ 2, hVg⟩ := by
    have h := hθ g ⟨g ^ 2, hVg⟩
    rw [hconj, hg] at h
    exact h.symm
  obtain ⟨m, hm⟩ := hfix (θ ⟨g ^ 2, hVg⟩) hw
  let μ : ↥V := θ.symm m
  have hμ : θ μ = m := θ.apply_symm_apply m
  have hkerμ : η (μ : Γ) = 1 := MonoidHom.mem_ker.mp (hk.symm ▸ μ.2)
  have hηα : η (g * (μ : Γ)) = σ := by rw [map_mul, hg, hkerμ, mul_one]
  have hαker : (g * (μ : Γ)) ^ 2 ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_pow, hηα, pow_two, hσsq]
  have hαmem : (g * (μ : Γ)) ^ 2 ∈ V := hk ▸ hαker
  have hαfac : (⟨(g * (μ : Γ)) ^ 2, hαmem⟩ : ↥V)
      = MulAut.conjNormal g μ * ⟨g ^ 2, hVg⟩ * μ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, MulAut.conjNormal_apply, pow_two]
    group
  have hαsqV : (⟨(g * (μ : Γ)) ^ 2, hαmem⟩ : ↥V) = 1 := by
    refine θ.injective ?_
    rw [hαfac, map_mul, map_mul, hθ g μ, hg, hμ, ← hm, map_one]
    exact coreMod_mul_self_mul_self _ _
  exact ⟨g * (μ : Γ), hηα, Subtype.ext_iff.mp hαsqV⟩

theorem exists_involutions_lifting {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (hr : η.range = alternatingGroup (Fin 5))
    (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v)) :
    ∃ α₀ β₀ : Γ, η α₀ = sigOne ∧ η β₀ = sigTwo ∧ α₀ ^ 2 = 1 ∧ β₀ ^ 2 = 1 := by
  obtain ⟨α₀, hηα₀, hα₀sq⟩ := exists_involution_lifting V η hk hr θ hθ sigOne sigOne_alt
    sigOne_sq (by simpa only [aMod] using fix_a_eq_range)
  obtain ⟨β₀, hηβ₀, hβ₀sq⟩ := exists_involution_lifting V η hk hr θ hθ sigTwo sigTwo_alt
    sigTwo_sq (by simpa only [bMod] using fix_b_eq_range)
  exact ⟨α₀, β₀, hηα₀, hηβ₀, hα₀sq, hβ₀sq⟩
theorem correction_value (m : G6.coreMod 5) :
    bMod (aMod (bMod (aMod m * m) * (aMod m * m))) =
      aMod (bMod m * m) * (bMod m * m) := by
  have haτ : aMod (aMod m * m) = aMod m * m := by
    rw [map_mul, aMod_sq]
    ac_rfl
  have hbτ : bMod (aMod m * m) = aMod (bMod m) * bMod m := by
    rw [map_mul, aMod_comm_bMod]
  calc bMod (aMod (bMod (aMod m * m) * (aMod m * m)))
      = bMod (aMod (bMod (aMod m * m)) * aMod (aMod m * m)) := by rw [map_mul]
    _ = bMod (bMod (aMod (aMod m * m)) * aMod (aMod m * m)) := by rw [aMod_comm_bMod]
    _ = bMod (bMod (aMod m * m) * (aMod m * m)) := by rw [haτ]
    _ = bMod (bMod (aMod m * m)) * bMod (aMod m * m) := by rw [map_mul]
    _ = (aMod m * m) * bMod (aMod m * m) := by rw [bMod_sq]
    _ = (aMod m * m) * (aMod (bMod m) * bMod m) := by rw [hbτ]
    _ = aMod (bMod m * m) * (bMod m * m) := by rw [map_mul]; ac_rfl

theorem commutator_socle_fixed {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v))
    {α₀ β₀ : Γ} (hηα₀ : η α₀ = sigOne) (hηβ₀ : η β₀ = sigTwo)
    (hc_mem : ⁅α₀, β₀⁆ ∈ V) (hα₀mul : α₀ * α₀ = 1) (hβ₀mul : β₀ * β₀ = 1) :
    aMod (θ ⟨⁅α₀, β₀⁆, hc_mem⟩) = θ ⟨⁅α₀, β₀⁆, hc_mem⟩ ∧
      bMod (θ ⟨⁅α₀, β₀⁆, hc_mem⟩) = θ ⟨⁅α₀, β₀⁆, hc_mem⟩ := by
  have hc_sqV : (⟨⁅α₀, β₀⁆, hc_mem⟩ : ↥V) * ⟨⁅α₀, β₀⁆, hc_mem⟩ = 1 :=
    θ.injective (by rw [map_mul, coreMod_sq, map_one])
  have hc_sq : (⁅α₀, β₀⁆ : Γ) * ⁅α₀, β₀⁆ = 1 := by
    simpa using congrArg Subtype.val hc_sqV
  have hconj_a : MulAut.conjNormal α₀ ⟨⁅α₀, β₀⁆, hc_mem⟩ = ⟨⁅α₀, β₀⁆, hc_mem⟩ := by
    ext
    rw [MulAut.conjNormal_apply]
    show α₀ * (⁅α₀, β₀⁆ : Γ) * α₀⁻¹ = (⁅α₀, β₀⁆ : Γ)
    rw [conj_commutator_left α₀ β₀ hα₀mul hβ₀mul, inv_eq_of_mul_eq_one_right hc_sq]
  have hconj_b : MulAut.conjNormal β₀ ⟨⁅α₀, β₀⁆, hc_mem⟩ = ⟨⁅α₀, β₀⁆, hc_mem⟩ := by
    ext
    rw [MulAut.conjNormal_apply]
    show β₀ * (⁅α₀, β₀⁆ : Γ) * β₀⁻¹ = (⁅α₀, β₀⁆ : Γ)
    rw [conj_commutator_right α₀ β₀ hα₀mul hβ₀mul, inv_eq_of_mul_eq_one_right hc_sq]
  constructor
  · have h := hθ α₀ ⟨⁅α₀, β₀⁆, hc_mem⟩
    rw [hconj_a, hηα₀] at h
    exact h.symm
  · have h := hθ β₀ ⟨⁅α₀, β₀⁆, hc_mem⟩
    rw [hconj_b, hηβ₀] at h
    exact h.symm

theorem correction_involution {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v))
    {α₀ : Γ} (hηα₀ : η α₀ = sigOne) (hα₀sq : α₀ ^ 2 = 1) (m : G6.coreMod 5)
    (τ : ↥V) (hτ : θ τ = aMod m * m) :
    η (α₀ * (τ : Γ)) = sigOne ∧ (α₀ * (τ : Γ)) ^ 2 = 1 := by
  have hkerτ : η (τ : Γ) = 1 := MonoidHom.mem_ker.mp (hk.symm ▸ τ.2)
  have hηα : η (α₀ * (τ : Γ)) = sigOne := by rw [map_mul, hηα₀, hkerτ, mul_one]
  have hαker : (α₀ * (τ : Γ)) ^ 2 ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_pow, hηα, pow_two, sigOne_sq]
  have hαmem : (α₀ * (τ : Γ)) ^ 2 ∈ V := hk ▸ hαker
  have hα₀memV : α₀ ^ 2 ∈ V := hα₀sq.symm ▸ V.one_mem
  have hα₀V : (⟨α₀ ^ 2, hα₀memV⟩ : ↥V) = 1 := Subtype.ext hα₀sq
  have hαfac : (⟨(α₀ * (τ : Γ)) ^ 2, hαmem⟩ : ↥V)
      = MulAut.conjNormal α₀ τ * ⟨α₀ ^ 2, hα₀memV⟩ * τ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, MulAut.conjNormal_apply, pow_two]
    group
  have hαsqV : (⟨(α₀ * (τ : Γ)) ^ 2, hαmem⟩ : ↥V) = 1 := by
    refine θ.injective ?_
    rw [map_one, hαfac, map_mul, map_mul, hθ α₀ τ, hηα₀, hτ, hα₀V, map_one, mul_one]
    exact a_sq_zero m
  exact ⟨hηα, Subtype.ext_iff.mp hαsqV⟩

theorem correction_commutes {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v))
    {α₀ β₀ : Γ} (hηα₀ : η α₀ = sigOne) (hηβ₀ : η β₀ = sigTwo)
    (hα₀sq : α₀ ^ 2 = 1) (hβ₀sq : β₀ ^ 2 = 1) (hc_mem : ⁅α₀, β₀⁆ ∈ V) (m : G6.coreMod 5)
    (hm : aMod (bMod m * m) * (bMod m * m) = θ ⟨⁅α₀, β₀⁆, hc_mem⟩)
    (τ : ↥V) (hτ : θ τ = aMod m * m) :
    ⁅α₀ * (τ : Γ), β₀⁆ = 1 := by
  have hα₀mul : α₀ * α₀ = 1 := by simpa [pow_two] using hα₀sq
  have hβ₀mul : β₀ * β₀ = 1 := by simpa [pow_two] using hβ₀sq
  have hτsqV : (τ : ↥V) * τ = 1 := θ.injective (by rw [map_mul, coreMod_sq, map_one])
  have hτsq : (τ : Γ) * (τ : Γ) = 1 := by simpa using congrArg Subtype.val hτsqV
  have hkerτ : η (τ : Γ) = 1 := MonoidHom.mem_ker.mp (hk.symm ▸ τ.2)
  have hbt_mem : ⁅β₀, (τ : Γ)⁆ ∈ V := by
    rw [commutatorElement_def]
    exact V.mul_mem ((inferInstance : V.Normal).conj_mem (τ : Γ) τ.2 β₀) (V.inv_mem τ.2)
  have hbt_eq : (⟨⁅β₀, (τ : Γ)⁆, hbt_mem⟩ : ↥V) = MulAut.conjNormal β₀ τ * τ⁻¹ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
  have hθbt : θ ⟨⁅β₀, (τ : Γ)⁆, hbt_mem⟩ = bMod (aMod m * m) * (aMod m * m) := by
    rw [hbt_eq, map_mul, hθ β₀ τ, hηβ₀, hτ, map_inv, hτ,
      inv_eq_of_mul_eq_one_right (coreMod_sq _)]
    rfl
  have hmem : ⁅α₀ * (τ : Γ), β₀⁆ ∈ V := by
    have h : ⁅α₀ * (τ : Γ), β₀⁆ ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, map_mul, hηα₀, hkerτ, mul_one, hηβ₀]
      decide +kernel
    exact hk ▸ h
  have hformulaV : (⟨⁅α₀ * (τ : Γ), β₀⁆, hmem⟩ : ↥V)
      = ⟨⁅α₀, β₀⁆, hc_mem⟩ * MulAut.conjNormal β₀
          (MulAut.conjNormal α₀ ⟨⁅β₀, (τ : Γ)⁆, hbt_mem⟩) := by
    ext
    simp only [Subgroup.coe_mul, MulAut.conjNormal_apply]
    exact commutator_mul_conj α₀ β₀ (τ : Γ) hα₀mul hβ₀mul hτsq
  have hθformula : θ ⟨⁅α₀ * (τ : Γ), β₀⁆, hmem⟩ = 1 := by
    rw [hformulaV, map_mul, hθ β₀ (MulAut.conjNormal α₀ ⟨⁅β₀, (τ : Γ)⁆, hbt_mem⟩),
      hθ α₀ ⟨⁅β₀, (τ : Γ)⁆, hbt_mem⟩, hηβ₀, hηα₀, hθbt]
    change θ ⟨⁅α₀, β₀⁆, hc_mem⟩ *
      bMod (aMod (bMod (aMod m * m) * (aMod m * m))) = 1
    rw [correction_value m, ← hm]
    exact coreMod_sq _
  have hV : (⟨⁅α₀ * (τ : Γ), β₀⁆, hmem⟩ : ↥V) = 1 := θ.injective (by rw [hθformula, map_one])
  exact Subtype.ext_iff.mp hV
theorem adjust_to_commute {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V)
    (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v))
    (α₀ β₀ : Γ) (hηα₀ : η α₀ = sigOne) (hηβ₀ : η β₀ = sigTwo)
    (hα₀sq : α₀ ^ 2 = 1) (hβ₀sq : β₀ ^ 2 = 1) :
    ∃ α : Γ, η α = sigOne ∧ α ^ 2 = 1 ∧ ⁅α, β₀⁆ = 1 := by
  classical
  have hα₀mul : α₀ * α₀ = 1 := by simpa [pow_two] using hα₀sq
  have hβ₀mul : β₀ * β₀ = 1 := by simpa [pow_two] using hβ₀sq
  have hc_mem : ⁅α₀, β₀⁆ ∈ V := by
    rw [← hk, MonoidHom.mem_ker, map_commutatorElement, hηα₀, hηβ₀]
    decide +kernel
  obtain ⟨hu_a, hu_b⟩ := commutator_socle_fixed V η hk θ hθ hηα₀ hηβ₀ hc_mem hα₀mul hβ₀mul
  obtain ⟨m, hm⟩ := fix_socle_eq_range (θ ⟨⁅α₀, β₀⁆, hc_mem⟩) hu_a hu_b
  let τ : ↥V := θ.symm (aMod m * m)
  have hτ : θ τ = aMod m * m := θ.apply_symm_apply _
  obtain ⟨hηα, hαsq⟩ := correction_involution V η hk θ hθ hηα₀ hα₀sq m τ hτ
  exact ⟨α₀ * (τ : Γ), hηα, hαsq,
    correction_commutes V η hk θ hθ hηα₀ hηβ₀ hα₀sq hβ₀sq hc_mem m hm τ hτ⟩

theorem isPGroup_of_coreMod_iso {Γ : Type} [Group Γ] (V : Subgroup Γ)
    (θ : ↥V ≃* ↥(G6.coreMod 5)) : IsPGroup 2 ↥V := by
  apply IsPGroup.of_card (n := 4)
  rw [Nat.card_congr θ.toEquiv, card_coreMod_five]
  norm_num

theorem sylow_comap_v4 {Γ : Type} [Group Γ] [Finite Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (hr : η.range = alternatingGroup (Fin 5))
    (θ : ↥V ≃* ↥(G6.coreMod 5)) :
    IsPGroup 2 (V4.comap η) ∧ (V4.comap η).index = 15 := by
  have hVp : IsPGroup 2 ↥V := isPGroup_of_coreMod_iso V θ
  have hV4p : IsPGroup 2 V4 := by
    apply IsPGroup.of_card (n := 2)
    rw [card_V4]
    norm_num
  refine ⟨IsPGroup.comap_of_ker_isPGroup hV4p η ?_, ?_⟩
  · rw [hk]; exact hVp
  · rw [Subgroup.index_comap, hr, relIndex_V4]

theorem closure_sigOne_sigTwo :
    Subgroup.closure ({sigOne, sigTwo} : Set (Equiv.Perm (Fin 5))) = V4 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Subgroup.one_mem _
    · change sigOne ∈ Subgroup.closure ({sigOne, sigTwo} : Set (Equiv.Perm (Fin 5)))
      exact Subgroup.subset_closure (by simp)
    · change sigTwo ∈ Subgroup.closure ({sigOne, sigTwo} : Set (Equiv.Perm (Fin 5)))
      exact Subgroup.subset_closure (by simp)
    · change sigThree ∈ Subgroup.closure ({sigOne, sigTwo} : Set (Equiv.Perm (Fin 5)))
      rw [show sigThree = sigOne * sigTwo by decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem map_closure_eq_v4 {Γ : Type} [Group Γ] {η : Γ →* Equiv.Perm (Fin 5)} {α β₀ : Γ}
    (hηα : η α = sigOne) (hηβ₀ : η β₀ = sigTwo) :
    (Subgroup.closure ({α, β₀} : Set Γ)).map η = V4 := by
  rw [MonoidHom.map_closure, Set.image_pair, hηα, hηβ₀, closure_sigOne_sigTwo]

theorem complement_pair_le {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V)
    {α β₀ : Γ} (hηα : η α = sigOne) (hηβ₀ : η β₀ = sigTwo) :
    Subgroup.closure ({α, β₀} : Set Γ) ≤ V4.comap η := by
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rw [hx]
    show η α ∈ V4
    rw [hηα]; exact ⟨1, rfl⟩
  · rw [hx]
    show η β₀ ∈ V4
    rw [hηβ₀]; exact ⟨2, rfl⟩

theorem complement_pair_bot {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V)
    {α β₀ : Γ} (hηα : η α = sigOne) (hηβ₀ : η β₀ = sigTwo)
    (hαsq : α ^ 2 = 1) (hβsq : β₀ ^ 2 = 1) (hcomm : ⁅α, β₀⁆ = 1) :
    V ⊓ Subgroup.closure ({α, β₀} : Set Γ) = ⊥ := by
  have hα2 : α * α = 1 := by simpa [pow_two] using hαsq
  have hβ2 : β₀ * β₀ = 1 := by simpa [pow_two] using hβsq
  have hαβ : α * β₀ = β₀ * α := commutatorElement_eq_one_iff_mul_comm.mp hcomm
  have hKsup : Subgroup.closure ({α, β₀} : Set Γ) =
      Subgroup.zpowers α ⊔ Subgroup.zpowers β₀ := closure_pair_eq_sup' α β₀
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxK⟩ := Subgroup.mem_inf.mp hx
  have hηx : η x = 1 := MonoidHom.mem_ker.mp (hk.symm ▸ hxV)
  rw [hKsup] at hxK
  rcases (mem_zpowers_sup_pair' hα2 hβ2 hαβ).1 hxK with h | h | h | h
  · exact h
  · exact absurd (hηα ▸ (h ▸ hηx)) sigOne_ne_one
  · exact absurd (hηβ₀ ▸ (h ▸ hηx)) sigTwo_ne_one
  · rw [h, map_mul, hηα, hηβ₀] at hηx
    exact absurd hηx sigOne_mul_sigTwo_ne_one

theorem comap_le_sup_complement {Γ : Type} [Group Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) {α β₀ : Γ}
    (hηα : η α = sigOne) (hηβ₀ : η β₀ = sigTwo) :
    V4.comap η ≤ V ⊔ Subgroup.closure ({α, β₀} : Set Γ) := by
  have hmapK : (Subgroup.closure ({α, β₀} : Set Γ)).map η = V4 := map_closure_eq_v4 hηα hηβ₀
  intro p hp
  have hp' : η p ∈ (Subgroup.closure ({α, β₀} : Set Γ)).map η := by rw [hmapK]; exact hp
  obtain ⟨k, hkK, hkp⟩ := hp'
  have hmem : k⁻¹ * p ∈ V := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hkp, inv_mul_cancel]
  have hp_eq : p = k * (k⁻¹ * p) := by group
  rw [hp_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkK) (Subgroup.mem_sup_left hmem)

theorem exists_complement_of_delta5 {Γ : Type} [Group Γ] [Finite Γ] (V : Subgroup Γ) [V.Normal]
    (η : Γ →* Equiv.Perm (Fin 5)) (hk : η.ker = V) (hr : η.range = alternatingGroup (Fin 5))
    (θ : ↥V ≃* ↥(G6.coreMod 5))
    (hθ : ∀ (g : Γ) (v : ↥V), θ (MulAut.conjNormal g v) = G6.coreAct 5 (η g) (θ v)) :
    ∃ K : Subgroup Γ, V ⊓ K = ⊥ ∧ V ⊔ K = ⊤ := by
  classical
  have hVcomm : ∀ a b : ↥V, a * b = b * a := fun a b =>
    θ.injective (by rw [map_mul, map_mul, mul_comm])
  haveI : IsMulCommutative ↥V := ⟨⟨hVcomm⟩⟩
  have hVp : IsPGroup 2 ↥V := isPGroup_of_coreMod_iso V θ
  obtain ⟨hV4p, hindex⟩ := sylow_comap_v4 V η hk hr θ
  let P : Sylow 2 Γ := hV4p.toSylow (by rw [hindex]; decide)
  have hPcoe : (P : Subgroup Γ) = V4.comap η := rfl
  obtain ⟨α₀, β₀, hηα₀, hηβ₀, hα₀sq, hβ₀sq⟩ := exists_involutions_lifting V η hk hr θ hθ
  obtain ⟨α, hηα, hαsq, hcomm⟩ :=
    adjust_to_commute V η hk θ hθ α₀ β₀ hηα₀ hηβ₀ hα₀sq hβ₀sq
  let K : Subgroup Γ := Subgroup.closure ({α, β₀} : Set Γ)
  have hKP : K ≤ V4.comap η := by
    dsimp only [K]; exact complement_pair_le V η hk hηα hηβ₀
  have hVKbot : V ⊓ K = ⊥ := by
    dsimp only [K]; exact complement_pair_bot V η hk hηα hηβ₀ hαsq hβ₀sq hcomm
  have hP0le : V4.comap η ≤ V ⊔ K := by
    dsimp only [K]; exact comap_le_sup_complement V η hk hηα hηβ₀
  have hVP : V ≤ V4.comap η := by
    intro v hv
    show η v ∈ V4
    rw [show η v = 1 from MonoidHom.mem_ker.mp (hk.symm ▸ hv)]
    exact V4.one_mem
  have hsup : V ⊔ K = V4.comap η := le_antisymm (sup_le hVP hKP) hP0le
  exact (gaschutz hVp P).mpr ⟨K, by rw [hPcoe]; exact hKP, hVKbot, by rw [hPcoe, hsup]⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
