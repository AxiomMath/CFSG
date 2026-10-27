module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open Equiv
open scoped commutatorElement

namespace Mod6

@[expose] def E6 : Type := Fin 3 × Fin 2 → Multiplicative (ZMod 2)

instance : CommGroup E6 := Pi.commGroup

instance : DecidableEq E6 :=
  inferInstanceAs (DecidableEq (Fin 3 × Fin 2 → Multiplicative (ZMod 2)))

instance : Fintype E6 := inferInstanceAs (Fintype (Fin 3 × Fin 2 → Multiplicative (ZMod 2)))

instance : CoeFun E6 (fun _ => Fin 3 × Fin 2 → Multiplicative (ZMod 2)) := ⟨fun f => f⟩

theorem mul_apply' (f g : E6) (p : Fin 3 × Fin 2) : (f * g) p = f p * g p := rfl

@[expose] def actE (σ : Perm (Fin 3)) (e : Bool) (f : E6) : E6 := fun p =>
  f (σ⁻¹ p.1, p.2) * (if p.2 = 0 ∧ e = true then f (σ⁻¹ p.1, 1) else 1)

@[expose] def kap1 : E6 := fun p => if p.2 = 0 then Multiplicative.ofAdd 1 else 1

@[expose] def kap2 : E6 := fun p => if p.2 = 0 then 1 else Multiplicative.ofAdd 1

@[expose] def kap3 : E6 := fun _ => Multiplicative.ofAdd 1

@[expose] def g1 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

@[expose] def mS (p : Fin 3 × Fin 2) (a : Multiplicative (ZMod 2)) : E6 := Pi.mulSingle p a

@[expose] def badB (f : E6) : Bool := decide (f ≠ 1 ∧ ∃ k, f (k, 0) = 1 ∧ f (k, 1) = 1)

@[expose] def diagB (f : E6) : Bool := decide (∀ i j, f (i, j) = f (0, j))

@[expose] def kP : Fin 3 → E6 → Bool
  | 0 => fun f => decide (f = 1)
  | 1 => fun f => decide (f = 1 ∨ f = kap1)
  | 2 => diagB

set_option maxRecDepth 100000 in
theorem inv_eq_self : ∀ f : E6, f⁻¹ = f := by decide +kernel

set_option maxRecDepth 100000 in
theorem actE_comp : ∀ σ τ : Perm (Fin 3), ∀ e e' : Bool, ∀ f : E6,
    actE σ e (actE τ e' f) = actE (σ * τ) (xor e e') f := by decide +kernel

set_option maxRecDepth 100000 in
theorem actE_one : ∀ f : E6, actE 1 false f = f := by decide +kernel

theorem actE_mul_apply (σ : Perm (Fin 3)) (e : Bool) (f g : E6) :
    actE σ e (f * g) = actE σ e f * actE σ e g := by
  funext p
  change f (σ⁻¹ p.1, p.2) * g (σ⁻¹ p.1, p.2) *
      (if p.2 = 0 ∧ e = true then f (σ⁻¹ p.1, 1) * g (σ⁻¹ p.1, 1) else 1) =
    (f (σ⁻¹ p.1, p.2) * (if p.2 = 0 ∧ e = true then f (σ⁻¹ p.1, 1) else 1)) *
      (g (σ⁻¹ p.1, p.2) * (if p.2 = 0 ∧ e = true then g (σ⁻¹ p.1, 1) else 1))
  split_ifs
  · exact mul_mul_mul_comm _ _ _ _
  · simp

set_option maxRecDepth 100000 in
theorem exists_rot_swap : ∀ σ : Perm (Fin 3), ∃ a : Fin 3, ∃ b : Fin 2,
    σ = finRotate 3 ^ (a : ℕ) * swap 1 2 ^ (b : ℕ) := by decide +kernel

set_option maxRecDepth 100000 in
theorem key_bad : ∀ f : E6, diagB f = true ∨ badB f = true ∨
    ∃ σ : Perm (Fin 3), ∃ e : Bool, badB (f * actE σ e f) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem diag_cases : ∀ f : E6, diagB f = true → f = 1 ∨ f = kap1 ∨ f = kap2 ∨ f = kap3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kap_facts : actE 1 true kap2 = kap3 ∧ actE 1 true kap3 = kap2 ∧ actE 1 true kap1 = kap1 ∧
    kap2 * kap3 = kap1 ∧ kap1 * kap2 = kap3 := by decide +kernel

theorem inv_all (K : Subgroup E6) (h1 : ∀ f ∈ K, actE (finRotate 3) false f ∈ K)
    (h2 : ∀ f ∈ K, actE (swap 1 2) false f ∈ K) (h3 : ∀ f ∈ K, actE 1 true f ∈ K) :
    ∀ σ e, ∀ f ∈ K, actE σ e f ∈ K := by
  have hrot : ∀ a : ℕ, ∀ f ∈ K, actE (finRotate 3 ^ a) false f ∈ K := by
    intro a
    induction a with
    | zero => intro f hf; simpa [actE_one] using hf
    | succ n ih =>
      intro f hf
      have := actE_comp (finRotate 3) (finRotate 3 ^ n) false false f
      rw [← pow_succ'] at this
      rw [← show xor false false = false from rfl, ← this]
      exact h1 _ (ih f hf)
  have hswap : ∀ b : ℕ, b < 2 → ∀ f ∈ K, actE (swap 1 2 ^ b) false f ∈ K := by
    intro b hb f hf
    interval_cases b
    · simpa [actE_one] using hf
    · simpa using h2 f hf
  intro σ e f hf
  obtain ⟨a, b, rfl⟩ := exists_rot_swap σ
  have e1 : actE 1 e f ∈ K := by
    cases e
    · simpa [actE_one] using hf
    · exact h3 f hf
  have e2 := hswap b b.2 _ e1
  have e3 := hrot a _ e2
  have := actE_comp (finRotate 3 ^ (a : ℕ)) (swap 1 2 ^ (b : ℕ)) false false (actE 1 e f)
  have h4 := actE_comp (finRotate 3 ^ (a : ℕ) * swap 1 2 ^ (b : ℕ)) 1 false e f
  rw [mul_one, show xor false e = e by cases e <;> rfl] at h4
  rw [← h4]
  rw [show xor false false = false from rfl] at this
  rw [← this]
  exact e3

theorem classify (K : Subgroup E6) (h1 : ∀ f ∈ K, actE (finRotate 3) false f ∈ K)
    (h2 : ∀ f ∈ K, actE (swap 1 2) false f ∈ K) (h3 : ∀ f ∈ K, actE 1 true f ∈ K)
    (hm : ∀ f ∈ K, ∀ k, f (k, 0) = 1 → f (k, 1) = 1 → f = 1) :
    ∃ n : Fin 3, ∀ f, f ∈ K ↔ kP n f = true := by
  have hinv := inv_all K h1 h2 h3
  have hdiag : ∀ f ∈ K, diagB f = true := by
    intro f hf
    rcases key_bad f with h | h | ⟨σ, e, h⟩
    · exact h
    · obtain ⟨hne, k, hk0, hk1⟩ := of_decide_eq_true h
      exact absurd (hm f hf k hk0 hk1) hne
    · obtain ⟨hne, k, hk0, hk1⟩ := of_decide_eq_true h
      exact absurd (hm _ (K.mul_mem hf (hinv σ e f hf)) k hk0 hk1) hne
  obtain ⟨hk23, hk32, hk11, hk231, hk123⟩ := kap_facts
  by_cases h2' : kap2 ∈ K
  · have h3' : kap3 ∈ K := hk23 ▸ hinv 1 true _ h2'
    have h1' : kap1 ∈ K := hk231 ▸ K.mul_mem h2' h3'
    refine ⟨2, fun f => ⟨fun hf => hdiag f hf, fun hf => ?_⟩⟩
    rcases diag_cases f hf with rfl | rfl | rfl | rfl
    exacts [K.one_mem, h1', h2', h3']
  · have h3' : kap3 ∉ K := fun h => h2' (hk32 ▸ hinv 1 true _ h)
    by_cases h1' : kap1 ∈ K
    · refine ⟨1, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
      · rcases diag_cases f (hdiag f hf) with rfl | rfl | rfl | rfl
        · simp [kP]
        · simp [kP]
        · exact absurd hf h2'
        · exact absurd hf h3'
      · rcases of_decide_eq_true hf with rfl | rfl
        exacts [K.one_mem, h1']
    · refine ⟨0, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
      · rcases diag_cases f (hdiag f hf) with rfl | rfl | rfl | rfl
        · simp [kP]
        · exact absurd hf h1'
        · exact absurd hf h2'
        · exact absurd hf h3'
      · rw [show f = 1 from of_decide_eq_true hf]
        exact K.one_mem

set_option maxRecDepth 100000 in
theorem actE_one_vec : ∀ σ : Perm (Fin 3), ∀ e : Bool, actE σ e 1 = 1 := by decide +kernel

theorem mz_cases : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = g1 := by
  decide +kernel

@[expose] def actHom (σ : Perm (Fin 3)) (e : Bool) : E6 →* E6 where
  toFun := actE σ e
  map_one' := actE_one_vec σ e
  map_mul' := actE_mul_apply σ e

@[expose] def rg (σ : Perm (Fin 3)) (e : Bool) : Subgroup E6 :=
  (actHom σ e * MonoidHom.id E6).range

theorem mem_rg {σ : Perm (Fin 3)} {e : Bool} {f : E6} :
    f ∈ rg σ e ↔ ∃ g, actE σ e g * g = f := Iff.rfl

theorem actE_mem_rg {σ : Perm (Fin 3)} {e : Bool} {f : E6} (h : f ∈ rg σ e) :
    actE σ e f ∈ rg σ e := by
  obtain ⟨g, rfl⟩ := mem_rg.mp h
  exact ⟨actE σ e g, by simp [actHom, actE_mul_apply, mul_comm]⟩

variable {G : Type} [Group G]

theorem map_inv_E6 (Φ : E6 →* G) (f : E6) : Φ f⁻¹ = (Φ f)⁻¹ := map_inv Φ f

structure Pre6 (X V Y : Subgroup G) where
  Φ : E6 →* G
  mem : ∀ f, Φ f ∈ V
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq : ∀ a ∈ V, a * a = 1
  YV : Y ≤ V
  nY : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y

structure Dict6 (X V Y : Subgroup G) extends Pre6 X V Y where
  gen : ∀ v ∈ V, ∃ f, ∃ y ∈ Y, v = Φ f * y

namespace Pre6

variable {X V Y : Subgroup G} (D : Pre6 X V Y)

@[expose] def K : Subgroup E6 := Y.comap D.Φ

theorem mem_K {f : E6} : f ∈ D.K ↔ D.Φ f ∈ Y := Iff.rfl

@[expose] def Ψ (A : Subgroup E6) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ y ∈ Y, g = D.Φ a * y}
  one_mem' := ⟨1, A.one_mem, 1, Y.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, y, hy, rfl⟩ ⟨b, hb, y', hy', rfl⟩
    refine ⟨a * b, A.mul_mem ha hb, y * y', Y.mul_mem hy hy', ?_⟩
    rw [map_mul]
    have := D.comm y (D.YV hy) (D.Φ b) (D.mem b)
    calc D.Φ a * y * (D.Φ b * y') = D.Φ a * (y * D.Φ b) * y' := by group
      _ = D.Φ a * (D.Φ b * y) * y' := by rw [this]
      _ = D.Φ a * D.Φ b * (y * y') := by group
  inv_mem' := by
    rintro _ ⟨a, ha, y, hy, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, y⁻¹, Y.inv_mem hy, ?_⟩
    rw [map_inv_E6, mul_inv_rev]
    exact D.comm _ (V.inv_mem (D.YV hy)) _ (V.inv_mem (D.mem a))

theorem Φ_mem_Ψ {A : Subgroup E6} {a : E6} (ha : a ∈ A) : D.Φ a ∈ D.Ψ A :=
  ⟨a, ha, 1, Y.one_mem, by simp⟩

theorem Y_le_Ψ (A : Subgroup E6) : Y ≤ D.Ψ A := fun y hy => ⟨1, A.one_mem, y, hy, by simp⟩

theorem Ψ_le_V (A : Subgroup E6) : D.Ψ A ≤ V := by
  rintro _ ⟨a, _, y, hy, rfl⟩
  exact V.mul_mem (D.mem a) (D.YV hy)

theorem Ψ_mono {A B : Subgroup E6} (h : A ≤ B) : D.Ψ A ≤ D.Ψ B := by
  rintro _ ⟨a, ha, y, hy, rfl⟩
  exact ⟨a, h ha, y, hy, rfl⟩

theorem Φ_inv (f : E6) : (D.Φ f)⁻¹ = D.Φ f := by rw [← map_inv_E6, inv_eq_self]

theorem mem_sup_of_Φ_mem {B : Subgroup E6} {a : E6} (h : D.Φ a ∈ D.Ψ B) : a ∈ B ⊔ D.K := by
  obtain ⟨b, hb, y, hy, he⟩ := h
  have h1 : a * b⁻¹ ∈ D.K := by
    rw [mem_K, map_mul, map_inv_E6, he]
    have := D.comm (D.Φ b) (D.mem b) y (D.YV hy)
    have h3 : D.Φ b * y * (D.Φ b)⁻¹ = y := by rw [this]; group
    rw [h3]
    exact hy
  have h2 : a = (a * b⁻¹) * b := (inv_mul_cancel_right a b).symm
  rw [h2, sup_comm]
  exact Subgroup.mul_mem_sup h1 hb

theorem Ψ_le_iff {A B : Subgroup E6} : D.Ψ A ≤ D.Ψ B ↔ A ≤ B ⊔ D.K := by
  constructor
  · intro h a ha
    exact D.mem_sup_of_Φ_mem (h (D.Φ_mem_Ψ ha))
  · intro h g hg
    obtain ⟨a, ha, y, hy, rfl⟩ := hg
    obtain ⟨b, hb, k, hk, hab⟩ := Subgroup.mem_sup.mp (h ha)
    refine ⟨b, hb, D.Φ k * y, Y.mul_mem hk hy, ?_⟩
    rw [← hab, map_mul]
    group

theorem Ψ_sup (A B : Subgroup E6) : D.Ψ (A ⊔ B) = D.Ψ A ⊔ D.Ψ B := by
  apply le_antisymm
  · rintro _ ⟨a, ha, y, hy, rfl⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Subgroup.mem_sup.mp ha
    rw [map_mul, mul_assoc]
    refine Subgroup.mul_mem_sup (D.Φ_mem_Ψ ha₁) ?_
    exact (D.Ψ B).mul_mem (D.Φ_mem_Ψ ha₂) (D.Y_le_Ψ B hy)
  · exact sup_le (D.Ψ_mono le_sup_left) (D.Ψ_mono le_sup_right)

theorem Ψ_inf (A B : Subgroup E6) : D.Ψ A ⊓ D.Ψ B = D.Ψ ((A ⊔ D.K) ⊓ (B ⊔ D.K)) := by
  apply le_antisymm
  · rintro _ ⟨hA, hB⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := hA
    have hΦ : D.Φ a ∈ D.Ψ B := by
      have := (D.Ψ B).mul_mem hB ((D.Ψ B).inv_mem (D.Y_le_Ψ B hy))
      simpa using this
    refine ⟨a, ⟨(le_sup_left : A ≤ A ⊔ D.K) ha, D.mem_sup_of_Φ_mem hΦ⟩, y, hy, rfl⟩
  · refine le_inf ?_ ?_
    · exact (D.Ψ_le_iff (A := _) (B := A)).mpr (by
        refine fun a ha => ?_
        have := ha.1
        simpa using this)
    · exact (D.Ψ_le_iff (A := _) (B := B)).mpr (by
        refine fun a ha => ?_
        have := ha.2
        simpa using this)

theorem map_le_normalizer (A : Subgroup E6) : A.map D.Φ ≤ Subgroup.normalizer (Y : Set G) := by
  rintro _ ⟨a, _, rfl⟩
  have key : ∀ y ∈ Y, D.Φ a * y * (D.Φ a)⁻¹ = y := fun y hy => by
    rw [D.comm _ (D.mem a) y (D.YV hy)]; group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [key y hy]; exact hy
  · intro hy
    have h2 := D.comm _ (V.inv_mem (D.mem a)) _ (D.YV hy)
    have h3 : y = D.Φ a * y * (D.Φ a)⁻¹ := by
      calc y = (D.Φ a)⁻¹ * (D.Φ a * y * (D.Φ a)⁻¹) * D.Φ a := by group
        _ = D.Φ a * y * (D.Φ a)⁻¹ := by rw [h2]; group
    rw [h3]
    exact hy

theorem Ψ_eq_sup (A : Subgroup E6) : D.Ψ A = A.map D.Φ ⊔ Y := by
  apply le_antisymm
  · rintro _ ⟨a, ha, y, hy, rfl⟩
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ ha) hy
  · exact sup_le (by rintro _ ⟨a, ha, rfl⟩; exact D.Φ_mem_Ψ ha) (D.Y_le_Ψ A)

theorem card_Ψ [Finite G] (A : Subgroup E6) :
    Nat.card (D.Ψ A) * Nat.card D.K = Nat.card Y * Nat.card ↥(A ⊔ D.K) := by
  have h1 : Y.relIndex (D.Ψ A) = D.K.relIndex A := by
    rw [D.Ψ_eq_sup, show D.K = Y.comap D.Φ from rfl, Subgroup.relIndex_comap]
    have := Subgroup.normal_subgroupOf_of_le_normalizer (D.map_le_normalizer A)
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer (D.map_le_normalizer A)
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient (A.map D.Φ) Y
        (D.map_le_normalizer A)).toEquiv.symm
  have h2 : D.K.relIndex (A ⊔ D.K) = D.K.relIndex A := Subgroup.relIndex_sup_right A D.K
  have h3 := Subgroup.relIndex_mul_card Y (D.Ψ A)
  have h4 := Subgroup.relIndex_mul_card D.K (A ⊔ D.K)
  rw [inf_eq_left.mpr (D.Y_le_Ψ A), h1] at h3
  rw [inf_eq_left.mpr le_sup_right, h2] at h4
  rw [← h3, ← h4]
  ring

end Pre6

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

theorem Ψ_top : D.Ψ ⊤ = V :=
  le_antisymm (D.toPre6.Ψ_le_V _) fun v hv => by
    obtain ⟨f, y, hy, rfl⟩ := D.gen v hv
    exact ⟨f, trivial, y, hy, rfl⟩

end Dict6

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

@[expose] def Acts (x : G) (σ : Perm (Fin 3)) (e : Bool) : Prop :=
  ∀ f, x * D.Φ f * x⁻¹ * (D.Φ (actE σ e f))⁻¹ ∈ Y

theorem acts_of_basis {x : G} {σ : Perm (Fin 3)} {e : Bool}
    (h : ∀ p : Fin 3 × Fin 2, x * D.Φ (mS p g1) * x⁻¹ * (D.Φ (actE σ e (mS p g1)))⁻¹ ∈ Y) :
    D.Acts x σ e := by
  let T : Subgroup E6 :=
    { carrier := {f | x * D.Φ f * x⁻¹ * (D.Φ (actE σ e f))⁻¹ ∈ Y}
      one_mem' := by
        show x * D.Φ 1 * x⁻¹ * (D.Φ (actE σ e 1))⁻¹ ∈ Y
        rw [actE_one_vec, map_one]
        simp
      mul_mem' := by
        intro f g hf hg
        have hf' : x * D.Φ f * x⁻¹ * (D.Φ (actE σ e f))⁻¹ ∈ Y := hf
        have hg' : x * D.Φ g * x⁻¹ * (D.Φ (actE σ e g))⁻¹ ∈ Y := hg
        show x * D.Φ (f * g) * x⁻¹ * (D.Φ (actE σ e (f * g)))⁻¹ ∈ Y
        have hcomm := D.comm _ (V.inv_mem (D.mem (actE σ e f))) _ (D.YV hg')
        rw [actE_mul_apply, map_mul, map_mul, mul_inv_rev]
        have e2 : x * (D.Φ f * D.Φ g) * x⁻¹ * ((D.Φ (actE σ e g))⁻¹ * (D.Φ (actE σ e f))⁻¹) =
            (x * D.Φ f * x⁻¹ * (D.Φ (actE σ e f))⁻¹) *
              (x * D.Φ g * x⁻¹ * (D.Φ (actE σ e g))⁻¹) := by
          calc _ = (x * D.Φ f * x⁻¹) * ((x * D.Φ g * x⁻¹ * (D.Φ (actE σ e g))⁻¹) *
                (D.Φ (actE σ e f))⁻¹) := by group
            _ = (x * D.Φ f * x⁻¹) * ((D.Φ (actE σ e f))⁻¹ *
                (x * D.Φ g * x⁻¹ * (D.Φ (actE σ e g))⁻¹)) := by rw [hcomm]
            _ = _ := by group
        rw [e2]
        exact Y.mul_mem hf' hg'
      inv_mem' := by
        intro f hf
        rwa [inv_eq_self] }
  intro f
  have hmem : ∀ p : Fin 3 × Fin 2, mS p (f p) ∈ T := by
    intro p
    rcases mz_cases (f p) with h1 | h1
    · rw [h1]
      have h0 : mS p (1 : Multiplicative (ZMod 2)) = 1 := Pi.mulSingle_one p
      rw [h0]
      exact T.one_mem
    · rw [h1]
      exact h p
  have h2 : (∏ p : Fin 3 × Fin 2, mS p (f p)) = f :=
    Finset.univ_prod_mulSingle (f : Fin 3 × Fin 2 → Multiplicative (ZMod 2))
  have h3 := T.prod_mem (t := Finset.univ) (f := fun p => mS p (f p)) (fun p _ => hmem p)
  exact (congrArg (fun z => z ∈ T) h2).mp h3

end Dict6

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

theorem conj_Ψ {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} {e : Bool} (h : D.Acts x σ e)
    {A B : Subgroup E6} (hAB : ∀ f ∈ A, actE σ e f ∈ B) :
    ∀ g ∈ D.Ψ A, x * g * x⁻¹ ∈ D.Ψ B := by
  rintro _ ⟨a, ha, y, hy, rfl⟩
  have h1 := h a
  have hy' := D.nY x hx y hy
  have hc := D.comm _ (D.YV h1) _ (D.mem (actE σ e a))
  have h2 : x * (D.Φ a * y) * x⁻¹ = D.Φ (actE σ e a) *
      ((x * D.Φ a * x⁻¹ * (D.Φ (actE σ e a))⁻¹) * (x * y * x⁻¹)) := by
    calc x * (D.Φ a * y) * x⁻¹ = (x * D.Φ a * x⁻¹) * (x * y * x⁻¹) := by group
      _ = ((x * D.Φ a * x⁻¹ * (D.Φ (actE σ e a))⁻¹) * D.Φ (actE σ e a)) * (x * y * x⁻¹) := by
          group
      _ = (D.Φ (actE σ e a) * (x * D.Φ a * x⁻¹ * (D.Φ (actE σ e a))⁻¹)) * (x * y * x⁻¹) := by
          rw [hc]
      _ = _ := by group
  rw [h2]
  exact ⟨actE σ e a, hAB a ha, _, Y.mul_mem h1 hy', rfl⟩

theorem K_inv {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} {e : Bool} (h : D.Acts x σ e)
    {f : E6} (hf : f ∈ D.K) : actE σ e f ∈ D.K := by
  rw [Pre6.mem_K]
  have h1 := h f
  have h2 := D.nY x hx _ hf
  have : D.Φ (actE σ e f) =
      (x * D.Φ f * x⁻¹ * (D.Φ (actE σ e f))⁻¹)⁻¹ * (x * D.Φ f * x⁻¹) := by group
  rw [this]
  exact Y.mul_mem (Y.inv_mem h1) h2

theorem comm_formula {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} {e : Bool} (h : D.Acts x σ e)
    (f : E6) {y : G} (hy : y ∈ Y) :
    ∃ c ∈ Y, ⁅x, D.Φ f * y⁆ = D.Φ (actE σ e f * f) * c := by
  have h1 := h f
  have hy' := D.nY x hx y hy
  have hc := D.comm _ (D.YV h1) _ (D.mem (actE σ e f))
  obtain ⟨a', ha'Y, ha'⟩ : ∃ a' ∈ Y, x * D.Φ f * x⁻¹ = D.Φ (actE σ e f) * a' := by
    refine ⟨_, h1, ?_⟩
    rw [← hc]; group
  have hcY : a' * (x * y * x⁻¹) * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem ha'Y hy') (Y.inv_mem hy)
  have hc2 := D.comm _ (V.inv_mem (D.mem f)) _ (D.YV hcY)
  refine ⟨_, hcY, ?_⟩
  calc ⁅x, D.Φ f * y⁆ = (x * D.Φ f * x⁻¹) * (x * y * x⁻¹) * y⁻¹ * (D.Φ f)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (D.Φ (actE σ e f) * a') * (x * y * x⁻¹) * y⁻¹ * (D.Φ f)⁻¹ := by rw [ha']
    _ = D.Φ (actE σ e f) * ((a' * (x * y * x⁻¹) * y⁻¹) * (D.Φ f)⁻¹) := by group
    _ = D.Φ (actE σ e f) * ((D.Φ f)⁻¹ * (a' * (x * y * x⁻¹) * y⁻¹)) := by rw [← hc2]
    _ = _ := by rw [map_mul, D.Φ_inv f]; group

end Dict6

theorem commutator_zpowers_le [Finite G] {W N : Subgroup G} {x : G}
    (hN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h : ∀ v ∈ W, ⁅x, v⁆ ∈ N) :
    ⁅W, Subgroup.zpowers x⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro v hv t ht
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x ^ n = t := Submonoid.mem_powers_iff _ _ |>.mp
    (mem_powers_iff_mem_zpowers.mpr ht)
  have key : ∀ n : ℕ, ⁅x ^ n, v⁆ ∈ N := by
    intro n
    induction n with
    | zero => simp [N.one_mem]
    | succ n ih =>
      have e : ⁅x ^ (n + 1), v⁆ = x * ⁅x ^ n, v⁆ * x⁻¹ * ⁅x, v⁆ := by
        simp only [commutatorElement_def, pow_succ']; group
      rw [e]
      exact N.mul_mem (hN _ ih) (h v hv)
  rw [← commutatorElement_inv]
  exact N.inv_mem (key n)

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

theorem comm_sup [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} {e : Bool}
    (h : D.Acts x σ e) : ⁅V, Subgroup.zpowers x⁆ ⊔ Y = D.Ψ (rg σ e) := by
  have hN : ∀ n ∈ D.Ψ (rg σ e), x * n * x⁻¹ ∈ D.Ψ (rg σ e) :=
    D.conj_Ψ hx h (fun f hf => actE_mem_rg hf)
  have key : ∀ v ∈ V, ⁅x, v⁆ ∈ D.Ψ (rg σ e) := by
    intro v hv
    obtain ⟨f, y, hy, rfl⟩ := D.gen v hv
    obtain ⟨c, hc, hcomm⟩ := D.comm_formula hx h f hy
    rw [hcomm]
    exact (D.Ψ _).mul_mem (D.Φ_mem_Ψ ⟨f, rfl⟩) (D.Y_le_Ψ _ hc)
  apply le_antisymm
  · exact sup_le (commutator_zpowers_le hN key) (D.Y_le_Ψ _)
  · rintro _ ⟨r, hr, y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := mem_rg.mp hr
    obtain ⟨c, hc, hcomm⟩ := D.comm_formula hx h g (Y.one_mem)
    rw [mul_one] at hcomm
    have h1 : ⁅x, D.Φ g⁆ ∈ ⁅V, Subgroup.zpowers x⁆ := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (D.mem g)
        (Subgroup.mem_zpowers x))
    have h2 : D.Φ (actE σ e g * g) = ⁅x, D.Φ g⁆ * c⁻¹ := by rw [hcomm]; group
    show D.Φ (actE σ e g * g) * y ∈ _
    rw [h2, mul_assoc]
    exact Subgroup.mul_mem_sup h1 (Y.mul_mem (Y.inv_mem hc) hy)

theorem comm_le_iff [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} {e : Bool}
    (h : D.Acts x σ e) {B : Subgroup E6} :
    ⁅V, Subgroup.zpowers x⁆ ≤ D.Ψ B ↔ rg σ e ≤ B ⊔ D.K := by
  rw [← D.Ψ_le_iff, ← D.comm_sup hx h]
  exact ⟨fun hle => sup_le hle (D.Y_le_Ψ B), fun hle => le_sup_left.trans hle⟩

end Dict6

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

include D

theorem coprime_aux {x : G} (hx3 : x ^ 3 = 1) (hxY : ∀ y ∈ Y, x * y * x⁻¹ = y) {v : G}
    (h : x * v * x⁻¹ * v⁻¹ ∈ Y) : x * v * x⁻¹ = v := by
  obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, x * v * x⁻¹ = y * v := ⟨_, h, by group⟩
  have e2 : x * (x * v * x⁻¹) * x⁻¹ = v := by
    rw [hy]
    calc x * (y * v) * x⁻¹ = (x * y * x⁻¹) * (x * v * x⁻¹) := by group
      _ = y * (y * v) := by rw [hxY y hyY, hy]
      _ = (y * y) * v := by group
      _ = v := by rw [D.sq y (D.YV hyY)]; group
  have e3 : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    have e : x ^ 3 = x * x * x := by rw [pow_succ, pow_succ, pow_one]
    have : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * v * (x ^ 3)⁻¹ := by
      rw [e]; group
    rw [this, hx3]; group
  rw [e2] at e3
  exact e3

theorem fix_iff [Finite G] {x : G} (hx : x ∈ X) (hx3 : x ^ 3 = 1)
    (hxY : ∀ y ∈ Y, x * y * x⁻¹ = y) {σ : Perm (Fin 3)} {e : Bool} (h : D.Acts x σ e) :
    V ⊓ Subgroup.centralizer ({x} : Set G) = Y ↔ ∀ f, actE σ e f * f ∈ D.K → f ∈ D.K := by
  constructor
  · intro hC f hf
    obtain ⟨c, hc, hcomm⟩ := D.comm_formula hx h f (Y.one_mem)
    have h1 : x * D.Φ f * x⁻¹ * (D.Φ f)⁻¹ ∈ Y := by
      have : ⁅x, D.Φ f * 1⁆ = x * D.Φ f * x⁻¹ * (D.Φ f)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [← this, hcomm]
      exact Y.mul_mem hf hc
    have h2 := D.coprime_aux hx3 hxY h1
    have h3 : D.Φ f ∈ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨D.mem f, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc D.Φ f * x = (x * D.Φ f * x⁻¹) * x := by rw [h2]
        _ = x * D.Φ f := by group
    rw [hC] at h3
    exact h3
  · intro hK
    apply le_antisymm
    · rintro v ⟨hv, hvc⟩
      obtain ⟨f, y, hy, rfl⟩ := D.gen v hv
      have hcen : x * (D.Φ f * y) = (D.Φ f * y) * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp hvc).symm
      obtain ⟨c, hc, hcomm⟩ := D.comm_formula hx h f hy
      have h1 : ⁅x, D.Φ f * y⁆ = 1 := by
        rw [commutatorElement_def, hcen]; group
      have h2 : D.Φ (actE σ e f * f) = c⁻¹ := by
        rw [h1] at hcomm
        exact eq_inv_of_mul_eq_one_left hcomm.symm
      have h3 : actE σ e f * f ∈ D.K := by
        rw [Pre6.mem_K, h2]; exact Y.inv_mem hc
      exact Y.mul_mem (hK f h3) hy
    · intro y hy
      refine ⟨D.YV hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc y * x = (x * y * x⁻¹) * x := by rw [hxY y hy]
        _ = x * y := by group

end Dict6

@[expose] def zmHom (x : G) (hx : x * x = 1) : Multiplicative (ZMod 2) →* G where
  toFun a := if a = 1 then 1 else x
  map_one' := by simp
  map_mul' := by
    intro a b
    rcases mz_cases a with rfl | rfl <;> rcases mz_cases b with rfl | rfl
    · simp
    · have : g1 ≠ 1 := by decide
      simp [this]
    · have : g1 ≠ 1 := by decide
      simp [this]
    · have h1 : g1 ≠ 1 := by decide
      have h2 : g1 * g1 = 1 := by
        decide
      simp [h1, h2, hx]

theorem exists_Phi {V : Subgroup G} (hc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hs : ∀ a ∈ V, a * a = 1) (w : Fin 3 × Fin 2 → G) (hw : ∀ p, w p ∈ V) :
    ∃ Φ : E6 →* G, (∀ f, Φ f ∈ V) ∧
      ∀ p, Φ (mS p g1) = w p := by
  let φ : ∀ p : Fin 3 × Fin 2, Multiplicative (ZMod 2) →* G := fun p => zmHom (w p) (hs _ (hw p))
  have hφ : ∀ p a, φ p a ∈ V := by
    intro p a
    show (if a = 1 then 1 else w p) ∈ V
    split_ifs
    · exact V.one_mem
    · exact hw p
  have hcomm : Pairwise fun p q => ∀ x y, Commute (φ p x) (φ q y) :=
    fun p q _ x y => hc _ (hφ p x) _ (hφ q y)
  let Φ0 : (Fin 3 × Fin 2 → Multiplicative (ZMod 2)) →* G := MonoidHom.noncommPiCoprod φ hcomm
  have hΦ0 : ∀ f, Φ0 f ∈ V := by
    intro f
    show MonoidHom.noncommPiCoprod φ hcomm f ∈ V
    rw [MonoidHom.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _ fun p _ => hφ p _
  refine ⟨{ toFun := fun f => Φ0 f, map_one' := map_one Φ0, map_mul' := fun a b => map_mul Φ0 a b },
    fun f => hΦ0 f, fun p => ?_⟩
  show Φ0 (Pi.mulSingle p g1) = w p
  have := MonoidHom.noncommPiCoprod_mulSingle (hcomm := hcomm) φ p g1
  rw [show Φ0 (Pi.mulSingle p g1) = φ p g1 from this]
  show (if g1 = 1 then 1 else w p) = w p
  have h1 : g1 ≠ 1 := by decide
  simp [h1]

@[expose] def usub (i : Fin 3) : Subgroup E6 where
  carrier := {f | ∀ k, k ≠ i → f (k, 0) = 1 ∧ f (k, 1) = 1}
  one_mem' := fun _ _ => ⟨rfl, rfl⟩
  mul_mem' := by
    intro f g hf hg k hk
    exact ⟨by rw [mul_apply', (hf k hk).1, (hg k hk).1, mul_one],
      by rw [mul_apply', (hf k hk).2, (hg k hk).2, mul_one]⟩
  inv_mem' := by
    intro f hf k hk
    have h1 := (hf k hk).1
    have h2 := (hf k hk).2
    exact ⟨by show (f (k, 0))⁻¹ = 1; rw [h1]; decide, by show (f (k, 1))⁻¹ = 1; rw [h2]; decide⟩

@[expose] def uel (i : Fin 3) (a b : Multiplicative (ZMod 2)) : E6 := fun p =>
  if p.1 = i then (if p.2 = 0 then a else b) else 1

theorem uel_mem (i : Fin 3) (a b : Multiplicative (ZMod 2)) : uel i a b ∈ usub i := by
  intro k hk
  simp [uel, hk]

set_option maxRecDepth 100000 in
theorem mem_usub_aux : ∀ i : Fin 3, ∀ f : E6, (∀ k, k ≠ i → f (k, 0) = 1 ∧ f (k, 1) = 1) →
    ∃ a b, f = uel i a b := by decide +kernel

theorem mem_usub_iff (i : Fin 3) (f : E6) : f ∈ usub i ↔ ∃ a b, f = uel i a b := by
  constructor
  · intro hf
    exact mem_usub_aux i f hf
  · rintro ⟨a, b, rfl⟩
    exact uel_mem i a b

theorem mul_self_E6 (f : E6) : f * f = 1 := by
  have := mul_inv_cancel f
  rwa [inv_eq_self f] at this

theorem card_E6 : Nat.card E6 = 64 := by
  rw [Nat.card_eq_fintype_card]
  have : Fintype.card E6 = 64 := by decide +kernel
  exact this

set_option maxRecDepth 100000 in
theorem fact_card_K : ∀ n : Fin 3, (Finset.univ.filter fun f : E6 => kP n f = true).card =
    2 ^ n.val := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_rot_fix : ∀ σ : Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 → ∀ n : Fin 3,
    ((∀ f : E6, kP n (actE σ false f * f) = true → kP n f = true) ↔ n = 2) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fact_stab_false : ∀ σ : Perm (Fin 3), σ 0 = 0 → σ ≠ 1 → ∀ n : Fin 3,
    ((∀ g : E6, ∃ a b : Multiplicative (ZMod 2),
      kP n (actE σ false g * g * uel 0 a b) = true) ↔ n = 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_stab_true : ∀ σ : Perm (Fin 3), σ 0 = 0 → ∀ n : Fin 3,
    ¬ ∀ g : E6, ∃ a b : Multiplicative (ZMod 2),
      kP n (actE σ true g * g * uel 0 a b) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_stab_cover : ∀ σ : Perm (Fin 3), σ 0 = 0 → σ ≠ 1 →
    ∀ a b : Multiplicative (ZMod 2), ∃ g : E6,
      kP 2 (uel 0 a b * (actE σ false g * g)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_pair : ∀ i j : Fin 3, i ≠ j → ∀ f : E6, ∃ a b c d : Multiplicative (ZMod 2),
    kP 2 (f * uel i a b * uel j c d) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_q_card : (Finset.univ.filter fun f : E6 =>
    ∃ g : E6, kP 2 (f * (actE 1 true g * g)) = true).card = 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_q_inter : (Finset.univ.filter fun f : E6 =>
    (∃ g : E6, kP 2 (f * (actE 1 true g * g)) = true) ∧
      ∃ a b : Multiplicative (ZMod 2), kP 2 (f * uel 0 a b) = true).card = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fact_rg_one_false : ∀ g : E6, actE 1 false g * g = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fact_split : ∀ f : E6, ∀ k : Fin 3, f (k, 0) = 1 → f (k, 1) = 1 →
    ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      f = uel i (f (i, 0)) (f (i, 1)) * uel j (f (j, 0)) (f (j, 1)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem actE_basis : ∀ (σ : Perm (Fin 3)) (e : Bool) (i : Fin 3) (j : Fin 2),
    actE σ e (mS (i, j) g1) =
      mS (σ i, j) g1 * (if j = 1 ∧ e = true then mS (σ i, 0) g1 else 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem uel_eq : ∀ (i : Fin 3) (a b : Multiplicative (ZMod 2)),
    uel i a b = mS (i, 0) a * mS (i, 1) b := by decide +kernel

set_option maxRecDepth 100000 in
theorem mS_cases : ∀ (p : Fin 3 × Fin 2) (a : Multiplicative (ZMod 2)),
    mS p a = if a = 1 then 1 else mS p g1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uel_eq_one_iff : ∀ (i : Fin 3) (a b : Multiplicative (ZMod 2)),
    uel i a b = 1 ↔ a = 1 ∧ b = 1 := by decide +kernel

theorem Phi_mS {G : Type} [Group G] (Φ : E6 →* G) (w : Fin 3 × Fin 2 → G)
    (hΦ : ∀ p, Φ (mS p g1) = w p) (p : Fin 3 × Fin 2) (a : Multiplicative (ZMod 2)) :
    Φ (mS p a) = if a = 1 then 1 else w p := by
  rw [mS_cases p a]
  split_ifs
  · exact map_one Φ
  · exact hΦ p

theorem Phi_uel {G : Type} [Group G] (Φ : E6 →* G) (w : Fin 3 × Fin 2 → G)
    (hΦ : ∀ p, Φ (mS p g1) = w p) (i : Fin 3) (a b : Multiplicative (ZMod 2)) :
    Φ (uel i a b) = (if a = 1 then 1 else w (i, 0)) * (if b = 1 then 1 else w (i, 1)) := by
  rw [uel_eq, map_mul, Phi_mS Φ w hΦ, Phi_mS Φ w hΦ]

theorem mem_sup3 {A B C : Subgroup E6} {f u r k : E6} (hu : u ∈ A) (hr : r ∈ B) (hk : k ∈ C)
    (h : f * u * r = k) : f ∈ A ⊔ B ⊔ C := by
  have : f = u * r * k := by
    rw [← h]
    calc f = f * (u * u) * (r * r) := by rw [mul_self_E6, mul_self_E6]; group
      _ = u * r * (f * u * r) := by
        have hc : ∀ a b : E6, a * b = b * a := mul_comm
        calc f * (u * u) * (r * r) = (f * u * r) * u * r := by
              simp only [mul_comm, mul_left_comm]
          _ = u * r * (f * u * r) := by
              simp only [mul_comm, mul_left_comm]
  rw [this]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hu hr) hk

theorem mem_rg_sup_iff {K : Subgroup E6} {σ : Perm (Fin 3)} {e : Bool} {f : E6} :
    f ∈ rg σ e ⊔ K ↔ ∃ g : E6, f * (actE σ e g * g) ∈ K := by
  constructor
  · intro hf
    obtain ⟨r, hr, k, hk, rfl⟩ := Subgroup.mem_sup.mp hf
    obtain ⟨g, rfl⟩ := mem_rg.mp hr
    refine ⟨g, ?_⟩
    have : actE σ e g * g * k * (actE σ e g * g) = k := by
      rw [mul_comm (actE σ e g * g) k, mul_assoc, mul_self_E6, mul_one]
    rw [this]; exact hk
  · rintro ⟨g, hg⟩
    have : f = (actE σ e g * g) * (f * (actE σ e g * g)) := by
      rw [mul_comm f, ← mul_assoc, mul_self_E6, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ hg

theorem mem_usub_sup_iff {K : Subgroup E6} {n : Fin 3} (hn : ∀ f, f ∈ K ↔ kP n f = true)
    {i : Fin 3} {f : E6} :
    f ∈ usub i ⊔ K ↔ ∃ a b : Multiplicative (ZMod 2), kP n (f * uel i a b) = true := by
  constructor
  · intro hf
    obtain ⟨u, hu, k, hk, rfl⟩ := Subgroup.mem_sup.mp hf
    obtain ⟨a, b, rfl⟩ := (mem_usub_iff i u).mp hu
    refine ⟨a, b, (hn _).mp ?_⟩
    have : uel i a b * k * uel i a b = k := by
      rw [mul_comm (uel i a b) k, mul_assoc, mul_self_E6, mul_one]
    rw [this]; exact hk
  · rintro ⟨a, b, h⟩
    have : f = uel i a b * (f * uel i a b) := by
      rw [mul_comm f, ← mul_assoc, mul_self_E6, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup (uel_mem i a b) ((hn _).mpr h)

theorem card_of_mem_iff' (S : Subgroup E6) (P : E6 → Prop) [DecidablePred P]
    (h : ∀ f, f ∈ S ↔ P f) : Nat.card S = (Finset.univ.filter P).card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_subtype]

namespace Dict6

variable {X V Y : Subgroup G} (D : Dict6 X V Y)

@[expose] def HasK (n : Fin 3) : Prop := ∀ f, f ∈ D.K ↔ kP n f = true

variable {D} {n : Fin 3}

theorem card_K (hn : D.HasK n) : Nat.card D.K = 2 ^ n.val := by
  rw [card_of_mem_iff' D.K (fun f => kP n f = true) hn]
  exact fact_card_K n

theorem card_V [Finite G] (hY : Nat.card Y = 4) (hn : D.HasK n) :
    Nat.card V * 2 ^ n.val = 256 := by
  have h := D.card_Ψ ⊤
  rw [D.Ψ_top, top_sup_eq, Subgroup.card_top, card_E6, hY, card_K hn] at h
  exact h

theorem card_V_eq (hY : Nat.card Y = 4) (hn : D.HasK n) [Finite G] :
    Nat.card V = 2 ^ (8 - n.val) := by
  have h := card_V hY hn
  have h2 : (2 : ℕ) ^ n.val ∣ 2 ^ 8 := Nat.pow_dvd_pow 2 (by omega)
  have : n.val < 3 := n.2
  interval_cases hv : n.val <;> omega

theorem card_V_eq_iff (hY : Nat.card Y = 4) (hn : D.HasK n) [Finite G] :
    Nat.card V = 2 ^ 6 ↔ n = 2 := by
  have h := card_V hY hn
  have : n.val < 3 := n.2
  constructor
  · intro h6
    rw [h6] at h
    have : n.val = 2 := by interval_cases hv : n.val <;> omega
    exact Fin.ext this
  · intro h2
    rw [h2] at h
    simp at h
    omega

theorem rg_le_usub_sup_iff {σ : Perm (Fin 3)} {e : Bool} (hn : D.HasK n) :
    rg σ e ≤ usub 0 ⊔ D.K ↔ ∀ g : E6, ∃ a b : Multiplicative (ZMod 2),
      kP n (actE σ e g * g * uel 0 a b) = true := by
  constructor
  · intro h g
    exact (mem_usub_sup_iff hn).mp (h ⟨g, rfl⟩)
  · intro h r hr
    obtain ⟨g, rfl⟩ := mem_rg.mp hr
    exact (mem_usub_sup_iff hn).mpr (h g)

theorem card_rg_sup [Finite G] (hn : D.HasK n) (σ : Perm (Fin 3)) (e : Bool) :
    Nat.card ↥(rg σ e ⊔ D.K) =
      (Finset.univ.filter fun f : E6 => ∃ g : E6, kP n (f * (actE σ e g * g)) = true).card := by
  refine card_of_mem_iff' _ _ fun f => ?_
  rw [mem_rg_sup_iff]
  exact exists_congr fun g => hn _

theorem rot_fix [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} (h : D.Acts x σ false)
    (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) (hx3 : x ^ 3 = 1) (hxY : ∀ y ∈ Y, x * y * x⁻¹ = y)
    (hn : D.HasK n) : V ⊓ Subgroup.centralizer ({x} : Set G) = Y ↔ n = 2 := by
  rw [D.fix_iff hx hx3 hxY h, ← fact_rot_fix σ hσ1 hσ3 n]
  constructor
  · intro H f hf
    exact (hn f).mp (H f ((hn _).mpr hf))
  · intro H f hf
    exact (hn f).mpr (H f ((hn _).mp hf))

theorem stab_le_iff [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} (h : D.Acts x σ false)
    (hσ0 : σ 0 = 0) (hσ1 : σ ≠ 1) (hn : D.HasK n) :
    ⁅V, Subgroup.zpowers x⁆ ≤ D.Ψ (usub 0) ↔ n = 2 := by
  rw [D.comm_le_iff hx h, rg_le_usub_sup_iff hn]
  exact fact_stab_false σ hσ0 hσ1 n

theorem stab_not_le [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} (h : D.Acts x σ true)
    (hσ0 : σ 0 = 0) (hn : D.HasK n) : ¬ ⁅V, Subgroup.zpowers x⁆ ≤ D.Ψ (usub 0) := by
  rw [D.comm_le_iff hx h, rg_le_usub_sup_iff hn]
  exact fact_stab_true σ hσ0 n

theorem stab_sup_eq [Finite G] {x : G} (hx : x ∈ X) {σ : Perm (Fin 3)} (h : D.Acts x σ false)
    (hσ0 : σ 0 = 0) (hσ1 : σ ≠ 1) (hn : D.HasK n) (h2 : n = 2) :
    ⁅V, Subgroup.zpowers x⁆ ⊔ Y = D.Ψ (usub 0) := by
  subst h2
  rw [D.comm_sup hx h]
  apply le_antisymm
  · exact D.Ψ_le_iff.mpr ((rg_le_usub_sup_iff hn).mpr ((fact_stab_false σ hσ0 hσ1 2).mpr rfl))
  · refine D.Ψ_le_iff.mpr fun f hf => ?_
    obtain ⟨a, b, rfl⟩ := (mem_usub_iff 0 f).mp hf
    obtain ⟨g, hg⟩ := fact_stab_cover σ hσ0 hσ1 a b
    exact (mem_rg_sup_iff).mpr ⟨g, (hn _).mpr hg⟩

theorem pair_sup (hn : D.HasK 2) {i j : Fin 3} (hij : i ≠ j) :
    D.Ψ (usub i) ⊔ D.Ψ (usub j) = V := by
  apply le_antisymm
  · exact sup_le (D.Ψ_le_V _) (D.Ψ_le_V _)
  · have hle : (⊤ : Subgroup E6) ≤ (usub i ⊔ usub j) ⊔ D.K := by
      intro f _
      obtain ⟨a, b, c, d, h⟩ := fact_pair i j hij f
      exact mem_sup3 (uel_mem i a b) (uel_mem j c d) ((hn _).mpr h) rfl
    calc V = D.Ψ ⊤ := D.Ψ_top.symm
      _ ≤ D.Ψ (usub i ⊔ usub j) := D.Ψ_le_iff.mpr hle
      _ = D.Ψ (usub i) ⊔ D.Ψ (usub j) := D.Ψ_sup _ _

theorem comm_eq_rg [Finite G] {Q : Subgroup G} {y : G}
    (hQ : ∀ b ∈ Q, b ∈ X ∧ ∃ e, D.Acts b 1 e) (hy : y ∈ Q) (hyA : D.Acts y 1 true)
    (hYQ : Y ≤ ⁅V, Q⁆) : ⁅V, Q⁆ = D.Ψ (rg 1 true) := by
  have hyX : y ∈ X := (hQ y hy).1
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv b hb
    obtain ⟨hbX, e, hAb⟩ := hQ b hb
    have h1 : ⁅v, b⁆ ∈ ⁅V, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers b)
    have h2 : ⁅V, Subgroup.zpowers b⁆ ≤ D.Ψ (rg 1 e) := le_sup_left.trans (D.comm_sup hbX hAb).le
    refine D.Ψ_mono ?_ (h2 h1)
    cases e
    · intro r hr
      obtain ⟨g, rfl⟩ := mem_rg.mp hr
      rw [fact_rg_one_false g]
      exact (rg 1 true).one_mem
    · exact le_rfl
  · rw [← D.comm_sup hyX hyA]
    exact sup_le (Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hy)) hYQ

theorem card_Ψ_rg_one [Finite G] (hY : Nat.card Y = 4) (hn : D.HasK 2) :
    Nat.card (D.Ψ (rg 1 true)) = 16 := by
  have h2 := D.card_Ψ (rg 1 true)
  rw [card_rg_sup hn, fact_q_card, hY, card_K hn] at h2
  simpa using Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 4) (h2.trans (by norm_num))

theorem card_Ψ_rg_one_inter [Finite G] (hY : Nat.card Y = 4) (hn : D.HasK 2) :
    Nat.card ↥(D.Ψ (rg 1 true) ⊓ D.Ψ (usub 0)) = 8 := by
  rw [D.Ψ_inf]
  have h2 := D.card_Ψ ((rg 1 true ⊔ D.K) ⊓ (usub 0 ⊔ D.K))
  have hK : D.K ≤ (rg 1 true ⊔ D.K) ⊓ (usub 0 ⊔ D.K) := le_inf le_sup_right le_sup_right
  rw [sup_eq_left.mpr hK, hY, card_K hn] at h2
  have h3 : Nat.card ↥((rg 1 true ⊔ D.K) ⊓ (usub 0 ⊔ D.K)) = 8 := by
    rw [card_of_mem_iff' _ (fun f : E6 => (∃ g : E6, kP 2 (f * (actE 1 true g * g)) = true) ∧
      ∃ a b : Multiplicative (ZMod 2), kP 2 (f * uel 0 a b) = true) (fun f => ?_)]
    · exact fact_q_inter
    · rw [Subgroup.mem_inf, mem_rg_sup_iff, mem_usub_sup_iff hn]
      exact and_congr (exists_congr fun g => hn _) Iff.rfl
  rw [h3] at h2
  simpa using Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 4) (h2.trans (by norm_num))

theorem meet_of (hinj : ∀ i, ∀ f ∈ usub i, f ∈ D.K → f = 1)
    (hZ : ∀ i j, i ≠ j → D.Ψ (usub i) ⊓ D.Ψ (usub j) ≤ Y) :
    ∀ f ∈ D.K, ∀ k : Fin 3, f (k, 0) = 1 → f (k, 1) = 1 → f = 1 := by
  intro f hf k h0 h1
  obtain ⟨i, j, hij, -, -, hfe⟩ := fact_split f k h0 h1
  generalize hu : uel i (f (i, 0)) (f (i, 1)) = u at hfe
  generalize hv : uel j (f (j, 0)) (f (j, 1)) = v at hfe
  have hui : u ∈ usub i := hu ▸ uel_mem _ _ _
  have hvj : v ∈ usub j := hv ▸ uel_mem _ _ _
  have hΦf : D.Φ u * D.Φ v ∈ Y := by rw [← map_mul, ← hfe]; exact hf
  have h1' : D.Φ u ∈ D.Ψ (usub j) := by
    have : D.Φ u = (D.Φ u * D.Φ v) * (D.Φ v)⁻¹ := by group
    rw [this]
    exact (D.Ψ _).mul_mem (D.Y_le_Ψ _ hΦf) ((D.Ψ _).inv_mem (D.Φ_mem_Ψ hvj))
  have hu_K : u ∈ D.K := hZ i j hij ⟨D.Φ_mem_Ψ hui, h1'⟩
  have hv_K : v ∈ D.K := by
    have : D.Φ v = (D.Φ u)⁻¹ * (D.Φ u * D.Φ v) := by group
    rw [Pre6.mem_K, this]
    exact Y.mul_mem (Y.inv_mem hu_K) hΦf
  rw [hfe, hinj i u hui hu_K, hinj j v hvj hv_K, one_mul]

theorem exists_hasK {x₁ x₂ x₃ : G} (h1 : x₁ ∈ X) (h2 : x₂ ∈ X) (h3 : x₃ ∈ X)
    (a1 : D.Acts x₁ (finRotate 3) false) (a2 : D.Acts x₂ (swap 1 2) false)
    (a3 : D.Acts x₃ 1 true)
    (hm : ∀ f ∈ D.K, ∀ k : Fin 3, f (k, 0) = 1 → f (k, 1) = 1 → f = 1) :
    ∃ n : Fin 3, D.HasK n :=
  classify D.K (fun _ hf => D.K_inv h1 a1 hf) (fun _ hf => D.K_inv h2 a2 hf)
    (fun _ hf => D.K_inv h3 a3 hf) hm

end Dict6

end Mod6

end CFSG.Quasithin.F53.Stellmacher.S43
