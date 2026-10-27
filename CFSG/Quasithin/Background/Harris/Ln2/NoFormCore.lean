module

public import CFSG.Quasithin.Background.Harris.Ln2.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix

theorem fixed_of_orth {k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod 2))
    (hsurj : ∀ y, ∃ x, M *ᵥ x = y) (P : Finset (Fin k))
    (hP : ∀ v q, q ∉ P → (M *ᵥ v - v) q = 0)
    (f : LinearMap.BilinForm (ZMod 2) (Fin k → ZMod 2)) (hf : f.Nondegenerate)
    (hinv : ∀ x y, f (M *ᵥ x) (M *ᵥ y) = f x y) (x : Fin k → ZMod 2)
    (hx : ∀ p ∈ P, f x (Pi.single p 1) = 0) : M *ᵥ x = x := by
  have h1 : ∀ v, f x (M *ᵥ v - v) = 0 := by
    intro v
    have hw : M *ᵥ v - v = ∑ q, (M *ᵥ v - v) q • (Pi.single q 1 : Fin k → ZMod 2) := by
      funext r
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hw, map_sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : q ∈ P
    · rw [map_smul, hx q hq, smul_zero]
    · rw [hP v q hq, zero_smul, map_zero]
  have h2 : ∀ v, f (M *ᵥ x - x) (M *ᵥ v) = 0 := by
    intro v
    have h3 : f x (M *ᵥ v) = f x v := by simpa [sub_eq_zero] using h1 v
    have h4 : f (M *ᵥ x - x) (M *ᵥ v) = f (M *ᵥ x) (M *ᵥ v) - f x (M *ᵥ v) := by simp
    rw [h4, hinv, h3, sub_self]
  refine sub_eq_zero.mp (hf.1 _ fun y => ?_)
  obtain ⟨v, rfl⟩ := hsurj y
  exact h2 v

theorem no_form {k : ℕ} {ι : Type} (M : ι → Matrix (Fin k) (Fin k) (ZMod 2))
    (hsurj : ∀ i y, ∃ x, M i *ᵥ x = y) (P : Finset (Fin k))
    (hP : ∀ i v q, q ∉ P → (M i *ᵥ v - v) q = 0) {c : ℕ}
    (hfix : Nat.card {x : Fin k → ZMod 2 // ∀ i, M i *ᵥ x = x} ≤ 2 ^ c) (hlt : P.card + c < k)
    (f : LinearMap.BilinForm (ZMod 2) (Fin k → ZMod 2)) (hf : f.Nondegenerate)
    (hinv : ∀ i x y, f (M i *ᵥ x) (M i *ᵥ y) = f x y) : False := by
  let Φ : (Fin k → ZMod 2) →ₗ[ZMod 2] (↥P → ZMod 2) :=
    LinearMap.pi fun p => f.flip (Pi.single (p : Fin k) 1)
  have hker : ∀ x ∈ LinearMap.ker Φ, ∀ i, M i *ᵥ x = x := by
    intro x hx i
    refine fixed_of_orth (M i) (hsurj i) P (hP i) f hf (hinv i) x fun p hp => ?_
    have := congr_fun (LinearMap.mem_ker.mp hx) ⟨p, hp⟩
    simpa [Φ] using this
  have hcard : Nat.card (LinearMap.ker Φ) ≤ 2 ^ c := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : LinearMap.ker Φ => (⟨x.1, hker x.1 x.2⟩ : {x : Fin k → ZMod 2 // ∀ i, M i *ᵥ x = x}))
      fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)) hfix
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
  have hrk : Module.finrank (ZMod 2) (LinearMap.ker Φ) ≤ c :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : Module.finrank (ZMod 2) (LinearMap.range Φ) ≤ P.card := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  rw [Module.finrank_fin_fun] at h1
  omega

theorem not_selfDual_of_form {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {k : ℕ} {G ι : Type}
    [Group G] {L : Subgroup (CFSG.Quasithin.G11.GLV V)} {θ : ↥L ≃* G}
    {τ : Representation (ZMod 2) G (Fin k → ZMod 2)} {β : V ≃ₗ[ZMod 2] (Fin k → ZMod 2)}
    (h : ActsAs L θ τ β) (g : ι → G)
    (hno : ∀ f : LinearMap.BilinForm (ZMod 2) (Fin k → ZMod 2), f.Nondegenerate →
      (∀ i x y, f (τ (g i) x) (τ (g i) y) = f x y) → False) :
    ¬ CFSG.Quasithin.G11.SelfDual L ⊤ := by
  rintro ⟨f, hnd, hinv⟩
  let e : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] (Fin k → ZMod 2) := Submodule.topEquiv.trans β
  refine hno (LinearMap.BilinForm.congr e f) (hnd.congr e) fun i x y => ?_
  set l : ↥L := θ.symm (g i) with hl
  have hg : θ l = g i := θ.apply_symm_apply _
  have key : ∀ x : Fin k → ZMod 2, e.symm (τ (g i) x) =
      ⟨(l : CFSG.Quasithin.G11.GLV V) (e.symm x : V), trivial⟩ := by
    intro x
    apply e.injective
    rw [e.apply_symm_apply]
    change _ = β ((l : CFSG.Quasithin.G11.GLV V) (e.symm x : V))
    rw [h l, hg]
    change _ = τ (g i) (e (e.symm x))
    rw [e.apply_symm_apply]
  rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply, key, key]
  exact hinv (l : CFSG.Quasithin.G11.GLV V) l.2 (e.symm x) (e.symm y) _ _ rfl rfl

end CFSG.Quasithin.G11.Harris.Ln2
