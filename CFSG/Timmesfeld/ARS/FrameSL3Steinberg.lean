module

public import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal Matrix

abbrev α₁ (F : Type) [Field F] : Fin (SpecialLinear.rootDatum 2 F).rank :=
  ⟨0, by simp [SpecialLinear.rootDatum]⟩

abbrev α₂ (F : Type) [Field F] : Fin (SpecialLinear.rootDatum 2 F).rank :=
  ⟨1, by simp [SpecialLinear.rootDatum]⟩

namespace FrameSL3

variable {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def steinbergGen (x : Fin 3 → Fin 3 → F → G) (s : Fin 3 × Fin 3 × F) : G :=
  if s.1 = s.2.1 then 1 else x s.1 s.2.1 s.2.2

omit [Field F] in
theorem steinbergGen_of_ne (x : Fin 3 → Fin 3 → F → G) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    steinbergGen x (i, j, c) = x i j c := by
  simp [steinbergGen, hij]

theorem steinbergGen_rels {x : Fin 3 → Fin 3 → F → G}
    (hadd : ∀ i j : Fin 3, i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d))
    (hcomm : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
      ⁅x i j c, x k l d⁆ =
        if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) :
    ∀ r ∈ CFSG.Open.steinbergSLRels 3 F, FreeGroup.lift (steinbergGen x) r = 1 := by
  rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hex, rfl⟩)
  · simp [steinbergGen]
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, steinbergGen_of_ne x hij]
    rw [hadd i j hij c d, mul_inv_cancel]
  · have hc := hcomm i j k l hij hkl hex c d
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, steinbergGen_of_ne x hij,
      steinbergGen_of_ne x hkl]
    by_cases hjk : j = k
    · subst hjk
      have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
      rw [ite_eq_left rfl] at hc ⊢
      rw [FreeGroup.lift_apply_of, steinbergGen_of_ne x hil, ← hc, commutatorElement_def,
        mul_inv_cancel]
    · rw [ite_eq_right hjk] at hc ⊢
      by_cases hil : i = l
      · subst hil
        rw [ite_eq_left rfl] at hc ⊢
        have hkj : k ≠ j := fun h => hjk h.symm
        rw [FreeGroup.lift_apply_of, steinbergGen_of_ne x hkj, ← hc, commutatorElement_def,
          mul_inv_cancel]
      · rw [ite_eq_right hil] at hc ⊢
        rw [map_one, inv_one, mul_one, ← commutatorElement_def, hc]

theorem exists_hom_of_steinberg [Finite F] {x : Fin 3 → Fin 3 → F → G}
    (hadd : ∀ i j : Fin 3, i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d))
    (hcomm : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
      ⁅x i j c, x k l d⁆ =
        if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) :
    ∃ ρ : SpecialLinearGroup (Fin (2 + 1)) F →* G, ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      ρ (SpecialLinearGroup.transvection hij c) = x i j c := by
  obtain ⟨φ, hφ⟩ := CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv (m := 2) (F := F)
    le_rfl
  let ψ : PresentedGroup (CFSG.Open.steinbergSLRels 3 F) →* G :=
    PresentedGroup.toGroup (steinbergGen_rels hadd hcomm)
  refine ⟨ψ.comp φ.symm.toMonoidHom, fun i j hij c => ?_⟩
  have hφ' : SpecialLinearGroup.transvection hij c = φ (PresentedGroup.of (i, j, c)) := by
    apply Subtype.ext
    rw [hφ i j c hij, SpecialLinearGroup.transvection_coe]
    rfl
  rw [MonoidHom.comp_apply, hφ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  change PresentedGroup.toGroup (steinbergGen_rels hadd hcomm) (PresentedGroup.of (i, j, c)) =
    x i j c
  rw [PresentedGroup.toGroup.of, steinbergGen_of_ne x hij]

theorem map_rootSubgroup_eq {ρ : SpecialLinearGroup (Fin (2 + 1)) F →* G} {i j : Fin 3}
    (hij : i ≠ j) {x : F → G} (hρ : ∀ c, ρ (SpecialLinearGroup.transvection hij c) = x c)
    {H : Subgroup G} (hH : Set.range x = H) : (SpecialLinear.rootSubgroup 2 F hij).map ρ = H := by
  rw [SpecialLinear.rootSubgroup, MonoidHom.map_range]
  ext g
  rw [MonoidHom.mem_range, ← SetLike.mem_coe, ← hH]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, by
      rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply, hρ]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, by
      rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply, hρ, toAdd_ofAdd]⟩

@[expose] def fam (a b c a' b' c' : F → G) : Fin 3 → Fin 3 → F → G
  | 0, 1 => a
  | 1, 2 => b
  | 0, 2 => c
  | 1, 0 => a'
  | 2, 1 => b'
  | 2, 0 => c'
  | _, _ => fun _ => 1

section Fam

variable {a b c a' b' c' : F → G}

theorem fam_add (ha : ∀ s t, a (s + t) = a s * a t) (hb : ∀ s t, b (s + t) = b s * b t)
    (hc : ∀ s t, c (s + t) = c s * c t) (ha' : ∀ s t, a' (s + t) = a' s * a' t)
    (hb' : ∀ s t, b' (s + t) = b' s * b' t) (hc' : ∀ s t, c' (s + t) = c' s * c' t) :
    ∀ i j : Fin 3, i ≠ j → ∀ s t : F,
      fam a b c a' b' c' i j s * fam a b c a' b' c' i j t = fam a b c a' b' c' i j (s + t) := by
  intro i j hij s t
  fin_cases i <;> fin_cases j <;> simp [fam, ha, hb, hc, ha', hb', hc'] at hij ⊢

theorem inv_eq_of_add [CharP F 2] {f : F → G} (hf : ∀ s t, f (s + t) = f s * f t) (s : F) :
    (f s)⁻¹ = f s := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← hf, CharTwo.add_self_eq_zero, h0]

theorem commutatorElement_eq_one_of_add {f : F → G}
    (hf : ∀ s t, f (s + t) = f s * f t) (s t : F) : ⁅f s, f t⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm, ← hf, ← hf, add_comm]

theorem commutatorElement_swap [CharP F 2] {x y z : F → G}
    (hz : ∀ s t, z (s + t) = z s * z t) (h : ∀ s t, ⁅x s, y t⁆ = z (s * t)) (s t : F) :
    ⁅y s, x t⁆ = z (s * t) := by
  rw [← commutatorElement_inv, h, inv_eq_of_add hz, mul_comm]

theorem fam_comm [CharP F 2] (ha : ∀ s t, a (s + t) = a s * a t)
    (hb : ∀ s t, b (s + t) = b s * b t) (hc : ∀ s t, c (s + t) = c s * c t)
    (ha' : ∀ s t, a' (s + t) = a' s * a' t) (hb' : ∀ s t, b' (s + t) = b' s * b' t)
    (hc' : ∀ s t, c' (s + t) = c' s * c' t)
    (hac : ∀ s t, Commute (a s) (c t)) (hab' : ∀ s t, Commute (a s) (b' t))
    (hbc : ∀ s t, Commute (b s) (c t)) (hba' : ∀ s t, Commute (b s) (a' t))
    (ha'c' : ∀ s t, Commute (a' s) (c' t)) (hb'c' : ∀ s t, Commute (b' s) (c' t))
    (r₁ : ∀ s t, ⁅a s, b t⁆ = c (s * t)) (r₂ : ∀ s t, ⁅a' s, c t⁆ = b (s * t))
    (r₃ : ∀ s t, ⁅a s, c' t⁆ = b' (s * t)) (r₄ : ∀ s t, ⁅a' s, b' t⁆ = c' (s * t))
    (r₅ : ∀ s t, ⁅b' s, c t⁆ = a (s * t)) (r₆ : ∀ s t, ⁅b s, c' t⁆ = a' (s * t)) :
    ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ s t : F,
      ⁅fam a b c a' b' c' i j s, fam a b c a' b' c' k l t⁆ =
        if j = k then fam a b c a' b' c' i l (s * t)
        else if i = l then fam a b c a' b' c' k j (-(s * t)) else 1 := by
  have hcomm : ∀ {x y : F → G}, (∀ s t, Commute (x s) (y t)) →
      (∀ s t, ⁅x s, y t⁆ = 1) ∧ ∀ s t, ⁅y s, x t⁆ = 1 := fun h =>
    ⟨fun s t => commutatorElement_eq_one_iff_commute.2 (h s t),
      fun s t => commutatorElement_eq_one_iff_commute.2 (h t s).symm⟩
  have e₁ := hcomm hac
  have e₂ := hcomm hab'
  have e₃ := hcomm hbc
  have e₄ := hcomm hba'
  have e₅ := hcomm ha'c'
  have e₆ := hcomm hb'c'
  intro i j k l hij hkl hex s t
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [fam, CharTwo.neg_eq] at hij hkl hex ⊢
  all_goals first
    | exact commutatorElement_eq_one_of_add ha s t | exact commutatorElement_eq_one_of_add hb s t
    | exact commutatorElement_eq_one_of_add hc s t | exact commutatorElement_eq_one_of_add ha' s t
    | exact commutatorElement_eq_one_of_add hb' s t | exact commutatorElement_eq_one_of_add hc' s t
    | exact e₁.1 s t | exact e₁.2 s t | exact e₂.1 s t | exact e₂.2 s t
    | exact e₃.1 s t | exact e₃.2 s t | exact e₄.1 s t | exact e₄.2 s t
    | exact e₅.1 s t | exact e₅.2 s t | exact e₆.1 s t | exact e₆.2 s t
    | exact r₁ s t | exact r₂ s t | exact r₃ s t | exact r₄ s t | exact r₅ s t | exact r₆ s t
    | exact commutatorElement_swap hc r₁ s t | exact commutatorElement_swap hb r₂ s t
    | exact commutatorElement_swap hb' r₃ s t | exact commutatorElement_swap hc' r₄ s t
    | exact commutatorElement_swap ha r₅ s t | exact commutatorElement_swap ha' r₆ s t

end Fam

variable (F)

theorem rootGroup_α₁ :
    (SpecialLinear.rootDatum 2 F).rootGroup (Pi.single (α₁ F) 1) =
      SpecialLinear.rootSubgroup 2 F (show (0 : Fin 3) ≠ 1 by decide) := by
  change SpecialLinear.rootGroup 2 F (Pi.single (0 : Fin 2) 1) = _
  exact SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

theorem rootGroup_α₂ :
    (SpecialLinear.rootDatum 2 F).rootGroup (Pi.single (α₂ F) 1) =
      SpecialLinear.rootSubgroup 2 F (show (1 : Fin 3) ≠ 2 by decide) := by
  change SpecialLinear.rootGroup 2 F (Pi.single (1 : Fin 2) 1) = _
  exact SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

theorem rootGroup_α₁₂ :
    (SpecialLinear.rootDatum 2 F).rootGroup (fun _ => 1) =
      SpecialLinear.rootSubgroup 2 F (show (0 : Fin 3) ≠ 2 by decide) :=
  SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

theorem rootGroup_neg_α₁ :
    (SpecialLinear.rootDatum 2 F).rootGroup (-Pi.single (α₁ F) 1) =
      SpecialLinear.rootSubgroup 2 F (show (1 : Fin 3) ≠ 0 by decide) := by
  change SpecialLinear.rootGroup 2 F (-Pi.single (0 : Fin 2) 1) = _
  exact SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

theorem rootGroup_neg_α₂ :
    (SpecialLinear.rootDatum 2 F).rootGroup (-Pi.single (α₂ F) 1) =
      SpecialLinear.rootSubgroup 2 F (show (2 : Fin 3) ≠ 1 by decide) := by
  change SpecialLinear.rootGroup 2 F (-Pi.single (1 : Fin 2) 1) = _
  exact SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

theorem rootGroup_neg_α₁₂ :
    (SpecialLinear.rootDatum 2 F).rootGroup (-fun _ => 1) =
      SpecialLinear.rootSubgroup 2 F (show (2 : Fin 3) ≠ 0 by decide) := by
  change SpecialLinear.rootGroup 2 F (-fun _ => 1) = _
  exact SpecialLinear.rootGroup_eq 2 F _ (by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd])

end FrameSL3

end CFSG.Timmesfeld.ARS
