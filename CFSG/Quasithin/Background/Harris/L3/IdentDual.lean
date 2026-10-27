module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Quasithin.G11

local instance (priority := high) zmod2AddCommGroup : AddCommGroup (ZMod 2) := Ring.toAddCommGroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def kerSub {A : Type*} [AddCommGroup A] (θ : V →+ A) : Submodule (ZMod 2) V where
  carrier := {v | θ v = 0}
  add_mem' := fun {a b} ha hb => by
    change θ (a + b) = 0
    rw [map_add, show θ a = 0 from ha, show θ b = 0 from hb, add_zero]
  zero_mem' := map_zero θ
  smul_mem' := fun c v hv => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa using hv

theorem mem_kerSub {A : Type*} [AddCommGroup A] (θ : V →+ A) (v : V) :
    v ∈ kerSub θ ↔ θ v = 0 := Iff.rfl

theorem exists_invariant_form {L : Subgroup (GLV V)} (hsd : SelfDual L ⊤) :
    ∃ B : LinearMap.BilinForm (ZMod 2) V, (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ k ∈ L, ∀ x y : V, B (k x) (k y) = B x y := by
  obtain ⟨B, ⟨-, hr⟩, hinv⟩ := hsd
  let e : V →ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V) :=
    (Submodule.topEquiv (R := ZMod 2) (M := V)).symm.toLinearMap
  refine ⟨B.compl₁₂ e e, fun y hy => ?_, fun k hk x y => ?_⟩
  · have h0 : e y = 0 := hr (e y) fun x' => by
      have h : e x'.1 = x' := Subtype.ext rfl
      have h2 := hy x'.1
      simp only [LinearMap.compl₁₂_apply] at h2
      rwa [h] at h2
    simpa [e] using h0
  · exact hinv k hk (e x) (e y) (e (k x)) (e (k y)) rfl rfl

theorem card_le_mul_card_fixed [Finite V] {L : Subgroup (GLV V)} (hsd : SelfDual L ⊤)
    (Q : Set (GLV V)) (hQ : Q ⊆ (L : Set (GLV V))) (W : Submodule (ZMod 2) V)
    (hW : ∀ q ∈ Q, ∀ v, (q : GLV V) v - v ∈ W) :
    Nat.card V ≤ Nat.card W * Nat.card {y : V // ∀ q ∈ Q, (q : GLV V) y = y} := by
  classical
  obtain ⟨B, hsep, hinv⟩ := exists_invariant_form hsd
  have hfin : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let Φ : V →ₗ[ZMod 2] (W →ₗ[ZMod 2] ZMod 2) :=
    (LinearMap.lcomp (ZMod 2) (ZMod 2) W.subtype).comp B.flip
  have hker : ∀ y ∈ LinearMap.ker Φ, ∀ q ∈ Q, (q : GLV V) y = y := by
    intro y hy q hq
    have hy' : ∀ w ∈ W, B w y = 0 := fun w hw => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨w, hw⟩
      simpa [Φ] using this
    have hk : ∀ x, B x ((q : GLV V) y - y) = 0 := by
      intro x
      have hx : (q : GLV V) ((q : GLV V).symm x) = x := by simp
      have h1 := hinv (q : GLV V) (hQ hq) ((q : GLV V).symm x) y
      have h2 := hy' _ (hW q hq ((q : GLV V).symm x))
      rw [LinearMap.map_sub₂, sub_eq_zero] at h2
      rw [map_sub, ← hx, h1, ← h2]
      simp
    exact sub_eq_zero.mp (hsep _ hk)
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : Module.finrank (ZMod 2) (LinearMap.range Φ) ≤ Module.finrank (ZMod 2) W := by
    calc Module.finrank (ZMod 2) (LinearMap.range Φ)
        ≤ Module.finrank (ZMod 2) (W →ₗ[ZMod 2] ZMod 2) := Submodule.finrank_le _
      _ = Module.finrank (ZMod 2) W := Subspace.dual_finrank_eq
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardK : Nat.card (LinearMap.ker Φ) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker Φ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : Nat.card (LinearMap.ker Φ) ≤
      Nat.card {y : V // ∀ q ∈ Q, (q : GLV V) y = y} :=
    Nat.card_le_card_of_injective (fun y => ⟨y.1, hker y.1 y.2⟩) fun a b h =>
      Subtype.ext (by simpa using congrArg Subtype.val h)
  calc Nat.card V = 2 ^ (Module.finrank (ZMod 2) (LinearMap.range Φ) +
        Module.finrank (ZMod 2) (LinearMap.ker Φ)) := by rw [hcardV, hrn]
    _ ≤ 2 ^ (Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) (LinearMap.ker Φ)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card W * Nat.card (LinearMap.ker Φ) := by rw [hcardW, hcardK, pow_add]
    _ ≤ _ := Nat.mul_le_mul_left _ hle

end CFSG.Quasithin.G11.Harris.L3
