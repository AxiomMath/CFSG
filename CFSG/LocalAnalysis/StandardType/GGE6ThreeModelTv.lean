module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNoTv
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNoTvTop
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

section Tv

variable {L' : Type} [Group L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

private lemma adAct_zero_E6 (u : WeylGroup .E6) :
    adAct .E6 3 u (0 : Fin Tag.E6.rank → ZMod 3) = 0 := by
  funext i
  simp only [adAct]
  exact Finset.sum_eq_zero fun j _ => by simp

private lemma card_fixed_congr {X Y : Type} (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (h : ∀ x : X, e (f x) = g (e x)) :
    Nat.card {x : X // f x = x} = Nat.card {y : Y // g y = y} :=
  Nat.card_congr (Equiv.subtypeEquiv e fun x =>
    ⟨fun hx => by rw [← h, hx], fun hy => e.injective (by rw [h, hy])⟩)

theorem GGE6ThreeData.not_isTransvection
    (h : GGE6ThreeData Z A Φ T w) (α : Subgroup.normalizer (A : Set (MulAut L'))) :
    ¬ GGIsTransvection 3 (A.normalizerMonoidHom α) := by
  intro htv
  obtain ⟨hfix, hN₂⟩ := htv
  obtain ⟨c, u, hc, hfull⟩ := h.full (α : MulAut L') α.2
  rcases h.card_cases with ⟨_, hsurj'⟩ | ⟨_, hmem⟩
  ·
    have hinj : Function.Injective (fun a : A => Multiplicative.toAdd (Φ a)) :=
      fun _ _ hab => h.injective (Multiplicative.toAdd.injective hab)
    have hsurj : Function.Surjective (fun a : A => Multiplicative.toAdd (Φ a)) := by
      intro v
      obtain ⟨a, ha⟩ := hsurj' v
      exact ⟨a, by change Multiplicative.toAdd (Φ a) = v; rw [ha, toAdd_ofAdd]⟩
    let e : A ≃ (Fin 6 → ZMod 3) := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    have he_coe : ∀ a : A, e a = Multiplicative.toAdd (Φ a) := fun _ => rfl
    have hE : ∀ a : A, e (A.normalizerMonoidHom α a) = c • adAct .E6 3 u (e a) := by
      intro a
      rw [he_coe, he_coe]
      exact hfull a (A.normalizerMonoidHom α a)
        (Subgroup.normalizerMonoidHom_apply_apply_coe A α a)
    have hfixV : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // c • adAct .E6 3 u x = x} * 3
        = Nat.card (Fin Tag.E6.rank → ZMod 3) := by
      rw [card_fixed_congr e (A.normalizerMonoidHom α)
        (fun x => c • adAct .E6 3 u x) hE, Nat.card_congr e] at hfix
      exact hfix
    have hNV : ∀ x : Fin Tag.E6.rank → ZMod 3,
        c • adAct .E6 3 u (c • adAct .E6 3 u x - x) = c • adAct .E6 3 u x - x := by
      intro x
      let b : A := e.symm x
      have hb : e b = x := e.apply_symm_apply x
      have he_mul : ∀ a b : A, e (a * b) = e a + e b := by
        intro a b
        have h := congrArg Multiplicative.toAdd (map_mul Φ a b)
        rw [toAdd_mul] at h
        exact h
      have he_inv : ∀ a : A, e a⁻¹ = - e a := by
        intro a
        have h := congrArg Multiplicative.toAdd (map_inv Φ a)
        rw [toAdd_inv] at h
        exact h
      have h1 : e (A.normalizerMonoidHom α (b⁻¹ * A.normalizerMonoidHom α b))
          = e (b⁻¹ * A.normalizerMonoidHom α b) := congrArg e (hN₂ b)
      rw [hE (b⁻¹ * A.normalizerMonoidHom α b)] at h1
      have key : e (b⁻¹ * A.normalizerMonoidHom α b)
          = e (A.normalizerMonoidHom α b) - e b := by
        rw [he_mul, he_inv]
        abel
      rw [key, hE b, hb] at h1
      exact h1
    exact not_isTransvection_top c hc u hfixV hNV
  ·
    have hinj : Function.Injective
        (fun a : A => (⟨Multiplicative.toAdd (Φ a), hmem a⟩ : NoOffRest.hypE6)) := by
      intro a b hab
      exact h.injective (Multiplicative.toAdd.injective (Subtype.ext_iff.mp hab))
    have hsurj : Function.Surjective
        (fun a : A => (⟨Multiplicative.toAdd (Φ a), hmem a⟩ : NoOffRest.hypE6)) := by
      intro x
      obtain ⟨a, ha⟩ := h.exists_eq_of_mem_hypE6 x.2
      refine ⟨a, Subtype.ext ?_⟩
      have ha' : (Φ a : Multiplicative (Fin Tag.E6.rank → ZMod 3)) =
          Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3) := ha
      exact congrArg Multiplicative.toAdd ha'
    let e : A ≃ NoOffRest.hypE6 :=
      Equiv.ofBijective _ ⟨hinj, hsurj⟩
    have he_coe : ∀ a : A,
        (e a : NoOffRest.hypE6) = ⟨Multiplicative.toAdd (Φ a), hmem a⟩ := fun _ => rfl
    have he_coe_val : ∀ a : A,
        (e a : Fin Tag.E6.rank → ZMod 3) = Multiplicative.toAdd (Φ a) := fun _ => rfl
    let t' : NoOffRest.hypE6 →+ NoOffRest.hypE6 :=
      { toFun := fun x => ⟨c • adAct .E6 3 u (x : Fin Tag.E6.rank → ZMod 3),
          NoOffRest.mem_hypE6.mpr (by
            have hx := NoOffRest.mem_hypE6.mp x.2
            rw [NoOffRest.kDotP_smul, NoOffRest.kDot_adAct, hx, mul_zero])⟩
        map_zero' := by
          apply Subtype.ext
          show c • adAct .E6 3 u (0 : Fin Tag.E6.rank → ZMod 3) = 0
          rw [adAct_zero_E6, smul_zero]
        map_add' := by
          intro x y
          apply Subtype.ext
          show c • adAct .E6 3 u ((x : Fin Tag.E6.rank → ZMod 3)
              + (y : Fin Tag.E6.rank → ZMod 3))
            = c • adAct .E6 3 u (x : Fin Tag.E6.rank → ZMod 3)
              + c • adAct .E6 3 u (y : Fin Tag.E6.rank → ZMod 3)
          rw [NoOffRest.adAct_add, smul_add] }
    have ht'_val : ∀ x : NoOffRest.hypE6,
        ((t' x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
          c • adAct .E6 3 u (x : Fin Tag.E6.rank → ZMod 3) := by
      intro x
      rfl
    have hE : ∀ a : A, e (A.normalizerMonoidHom α a) = t' (e a) := by
      intro a
      apply Subtype.ext
      rw [he_coe_val, ht'_val, he_coe_val]
      exact hfull a (A.normalizerMonoidHom α a)
        (Subgroup.normalizerMonoidHom_apply_apply_coe A α a)
    have hfixV : Nat.card {x : NoOffRest.hypE6 // t' x = x} * 3
        = Nat.card NoOffRest.hypE6 := by
      rw [card_fixed_congr e (A.normalizerMonoidHom α) t' hE, Nat.card_congr e] at hfix
      exact hfix
    have hNV : ∀ x : NoOffRest.hypE6, t' (t' x - x) = t' x - x := by
      intro x
      let b : A := e.symm x
      have hb : e b = x := e.apply_symm_apply x
      have he_mul : ∀ a b : A, e (a * b) = e a + e b := by
        intro a b
        apply Subtype.ext
        show Multiplicative.toAdd (Φ (a * b))
          = Multiplicative.toAdd (Φ a) + Multiplicative.toAdd (Φ b)
        rw [map_mul, toAdd_mul]
      have he_inv : ∀ a : A, e a⁻¹ = - e a := by
        intro a
        apply Subtype.ext
        show Multiplicative.toAdd (Φ a⁻¹) = -Multiplicative.toAdd (Φ a)
        rw [map_inv, toAdd_inv]
      have h1 : e (A.normalizerMonoidHom α (b⁻¹ * A.normalizerMonoidHom α b))
          = e (b⁻¹ * A.normalizerMonoidHom α b) := congrArg e (hN₂ b)
      rw [hE (b⁻¹ * A.normalizerMonoidHom α b)] at h1
      have key : e (b⁻¹ * A.normalizerMonoidHom α b)
          = e (A.normalizerMonoidHom α b) - e b := by
        rw [he_mul, he_inv]
        abel
      rw [key, hE b, hb] at h1
      exact h1
    exact not_isTransvection_hypE6 c hc u t' ht'_val hfixV hNV

end Tv

end CFSG.StandardType
