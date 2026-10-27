module

public import CFSG.YGroups.Y443.Abelianization
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443ArmLength monsterY443Rels
  monsterY443SpiderWord monsterY443Node MonsterY443Derived)

namespace Y443

theorem pow_inv_swap {G : Type*} [Group G] {x y : G} {m : ℕ} (h : (x⁻¹ * y) ^ m = 1) :
    (x * y⁻¹) ^ m = 1 := by
  have e : x * y⁻¹ = x * (x⁻¹ * y)⁻¹ * x⁻¹ := by group
  rw [e, conj_pow, inv_pow, h, inv_one, mul_one, mul_inv_cancel]

theorem pow_swap_mul {G : Type*} [Group G] {x y : G} {m : ℕ} (h : (x * y) ^ m = 1) :
    (y * x) ^ m = 1 := by
  have e : y * x = x⁻¹ * (x * y) * (x⁻¹)⁻¹ := by group
  rw [e, conj_pow, h, mul_one, mul_inv_cancel]

end Y443

abbrev E443Gen : Type := Σ i : Fin 3, Fin (monsterY443ArmLength i)

@[expose] def e443Lt : MonsterY443Gen → MonsterY443Gen → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some ⟨i, j⟩, some ⟨i', j'⟩ => i < i' ∨ (i = i' ∧ j.val < j'.val)

@[expose] def e443U : MonsterY443Gen → FreeGroup E443Gen
  | none => 1
  | some g => FreeGroup.of g

@[expose] def e443Node (i : Fin 3) (j : ℕ) (hj : j < monsterY443ArmLength i) :
    FreeGroup E443Gen :=
  FreeGroup.of ⟨i, ⟨j, hj⟩⟩

@[expose] def e443R : FreeGroup E443Gen :=
  e443Node 0 0 (by decide) * (e443Node 0 1 (by decide))⁻¹ * (e443Node 1 0 (by decide))⁻¹ *
    e443Node 1 1 (by decide) * e443Node 2 0 (by decide) * (e443Node 2 1 (by decide))⁻¹

@[expose] def e443RSharp : FreeGroup E443Gen :=
  (e443Node 0 0 (by decide))⁻¹ * e443Node 0 1 (by decide) * e443Node 1 0 (by decide) *
    (e443Node 1 1 (by decide))⁻¹ * (e443Node 2 0 (by decide))⁻¹ * e443Node 2 1 (by decide)

@[expose] def e443Rels : Set (FreeGroup E443Gen) :=
  {w | ∃ s t, e443Lt s t ∧ MonsterY443Adj s t ∧ w = ((e443U s)⁻¹ * e443U t) ^ 3} ∪
  {w | ∃ s t, e443Lt s t ∧ ¬ MonsterY443Adj s t ∧ w = ((e443U s)⁻¹ * e443U t) ^ 2} ∪
  {(e443R * e443RSharp) ^ 5}

abbrev E443 : Type := PresentedGroup e443Rels

@[expose] def e443u (s : MonsterY443Gen) : E443 := PresentedGroup.mk e443Rels (e443U s)

@[simp] theorem e443u_none : e443u none = 1 := by
  simp only [e443u, e443U, map_one]

@[simp] theorem e443u_some (g : E443Gen) : e443u (some g) = PresentedGroup.of g := rfl

section Data

local instance : DecidableRel e443Lt := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold e443Lt <;> infer_instance

local instance : DecidableRel MonsterY443Adj := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold MonsterY443Adj <;>
    infer_instance

theorem e443_even_presentation_data :
    Nat.card E443Gen = 11 ∧
      Nat.card {p : MonsterY443Gen × MonsterY443Gen // e443Lt p.1 p.2} = 66 ∧
      Nat.card {p : MonsterY443Gen × MonsterY443Gen //
        e443Lt p.1 p.2 ∧ MonsterY443Adj p.1 p.2} = 11 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Nat.card_eq_fintype_card] <;> decide

end Data

theorem e443Lt_ne {s t : MonsterY443Gen} (h : e443Lt s t) : s ≠ t := by
  rcases s with _ | ⟨i, j⟩ <;> rcases t with _ | ⟨i', j'⟩
  · exact h.elim
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · exact h.elim
  · intro h'
    cases h'
    rcases h with h | ⟨-, h⟩ <;> omega

theorem e443Lt_total {s t : MonsterY443Gen} (h : s ≠ t) : e443Lt s t ∨ e443Lt t s := by
  rcases s with _ | ⟨i, j⟩ <;> rcases t with _ | ⟨i', j'⟩
  · exact absurd rfl h
  · exact Or.inl trivial
  · exact Or.inr trivial
  · by_cases hi : i = i'
    · subst hi
      have hj : j.val ≠ j'.val := fun hj => h (by rw [Fin.ext hj])
      rcases Nat.lt_or_gt_of_ne hj with hj | hj
      · exact Or.inl (Or.inr ⟨rfl, hj⟩)
      · exact Or.inr (Or.inr ⟨rfl, hj⟩)
    · rcases lt_or_gt_of_ne hi with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inr (Or.inl hi)

theorem e443_rel_adj {s t : MonsterY443Gen} (hlt : e443Lt s t) (h : MonsterY443Adj s t) :
    ((e443u s)⁻¹ * e443u t) ^ 3 = 1 := by
  have := PresentedGroup.one_of_mem (rels := e443Rels)
    (x := ((e443U s)⁻¹ * e443U t) ^ 3) (Or.inl (Or.inl ⟨s, t, hlt, h, rfl⟩))
  rwa [map_pow, map_mul, map_inv] at this

theorem e443_rel_nadj {s t : MonsterY443Gen} (hlt : e443Lt s t) (h : ¬ MonsterY443Adj s t) :
    ((e443u s)⁻¹ * e443u t) ^ 2 = 1 := by
  have := PresentedGroup.one_of_mem (rels := e443Rels)
    (x := ((e443U s)⁻¹ * e443U t) ^ 2) (Or.inl (Or.inr ⟨s, t, hlt, h, rfl⟩))
  rwa [map_pow, map_mul, map_inv] at this

theorem e443_rel_spider :
    (PresentedGroup.mk e443Rels e443R * PresentedGroup.mk e443Rels e443RSharp) ^ 5 = 1 := by
  have := PresentedGroup.one_of_mem (rels := e443Rels)
    (x := (e443R * e443RSharp) ^ 5) (Or.inr rfl)
  rwa [map_pow, map_mul] at this

theorem e443_pow_adj {s t : MonsterY443Gen} (h : MonsterY443Adj s t) :
    ((e443u s)⁻¹ * e443u t) ^ 3 = 1 := by
  have hne : s ≠ t := fun hst => Y443.not_adj_self s (hst ▸ h)
  rcases e443Lt_total hne with hlt | hlt
  · exact e443_rel_adj hlt h
  · have h2 := e443_rel_adj hlt (Y443.adj_symm h)
    have : (e443u s)⁻¹ * e443u t = ((e443u t)⁻¹ * e443u s)⁻¹ := by group
    rw [this, inv_pow, h2, inv_one]

theorem e443_pow_nadj {s t : MonsterY443Gen} (hne : s ≠ t) (h : ¬ MonsterY443Adj s t) :
    ((e443u s)⁻¹ * e443u t) ^ 2 = 1 := by
  rcases e443Lt_total hne with hlt | hlt
  · exact e443_rel_nadj hlt h
  · have h2 := e443_rel_nadj hlt (fun h' => h (Y443.adj_symm h'))
    have : (e443u s)⁻¹ * e443u t = ((e443u t)⁻¹ * e443u s)⁻¹ := by group
    rw [this, inv_pow, h2, inv_one]

@[expose] def e443Ext {H : Type*} [One H] (f : E443Gen → H) : MonsterY443Gen → H
  | none => 1
  | some g => f g

theorem e443_lift_U {H : Type*} [Group H] (f : E443Gen → H) (s : MonsterY443Gen) :
    FreeGroup.lift f (e443U s) = e443Ext f s := by
  rcases s with _ | g
  · simp only [e443U, map_one, e443Ext]
  · simp only [e443U, FreeGroup.lift_apply_of, e443Ext]

theorem e443_lift_R {H : Type*} [Group H] (f : E443Gen → H) :
    FreeGroup.lift f e443R =
      f ⟨0, ⟨0, by decide⟩⟩ * (f ⟨0, ⟨1, by decide⟩⟩)⁻¹ * (f ⟨1, ⟨0, by decide⟩⟩)⁻¹ *
        f ⟨1, ⟨1, by decide⟩⟩ * f ⟨2, ⟨0, by decide⟩⟩ * (f ⟨2, ⟨1, by decide⟩⟩)⁻¹ := by
  simp only [e443R, e443Node, Fin.isValue, map_mul, FreeGroup.lift_apply_of, map_inv]

theorem e443_lift_RSharp {H : Type*} [Group H] (f : E443Gen → H) :
    FreeGroup.lift f e443RSharp =
      (f ⟨0, ⟨0, by decide⟩⟩)⁻¹ * f ⟨0, ⟨1, by decide⟩⟩ * f ⟨1, ⟨0, by decide⟩⟩ *
        (f ⟨1, ⟨1, by decide⟩⟩)⁻¹ * (f ⟨2, ⟨0, by decide⟩⟩)⁻¹ * f ⟨2, ⟨1, by decide⟩⟩ := by
  simp only [e443RSharp, e443Node, Fin.isValue, map_mul, map_inv, FreeGroup.lift_apply_of]

@[expose] noncomputable def e443Lift {H : Type*} [Group H] (f : E443Gen → H)
    (hadj : ∀ s t, e443Lt s t → MonsterY443Adj s t → ((e443Ext f s)⁻¹ * e443Ext f t) ^ 3 = 1)
    (hnadj : ∀ s t, e443Lt s t → ¬ MonsterY443Adj s t →
      ((e443Ext f s)⁻¹ * e443Ext f t) ^ 2 = 1)
    (hspider : (FreeGroup.lift f e443R * FreeGroup.lift f e443RSharp) ^ 5 = 1) : E443 →* H :=
  PresentedGroup.toGroup (f := f) (by
    rintro r (((⟨s, t, hlt, ha, rfl⟩ | ⟨s, t, hlt, hn, rfl⟩)) | rfl)
    · rw [map_pow, map_mul, map_inv, e443_lift_U, e443_lift_U]
      exact hadj s t hlt ha
    · rw [map_pow, map_mul, map_inv, e443_lift_U, e443_lift_U]
      exact hnadj s t hlt hn
    · rw [map_pow, map_mul]
      exact hspider)

@[simp] theorem e443Lift_of {H : Type*} [Group H] (f : E443Gen → H) {hadj hnadj hspider}
    (g : E443Gen) : e443Lift f hadj hnadj hspider (PresentedGroup.of g) = f g :=
  PresentedGroup.toGroup.of _

theorem e443Lift_mk {H : Type*} [Group H] (f : E443Gen → H) {hadj hnadj hspider}
    (x : FreeGroup E443Gen) :
    e443Lift f hadj hnadj hspider (PresentedGroup.mk e443Rels x) = FreeGroup.lift f x :=
  rfl

theorem e443_ext_alpha (s : MonsterY443Gen) :
    e443Ext (fun g : E443Gen => (PresentedGroup.of g : E443)⁻¹) s = (e443u s)⁻¹ := by
  rcases s with _ | g
  · simp only [e443Ext, e443u_none, inv_one]
  · simp only [e443Ext, e443u_some]

theorem e443_lift_alpha_R :
    FreeGroup.lift (fun g : E443Gen => (PresentedGroup.of g : E443)⁻¹) e443R =
      PresentedGroup.mk e443Rels e443RSharp := by
  simp only [e443R, e443RSharp, e443Node, map_mul, map_inv, inv_inv, FreeGroup.lift_apply_of]
  rfl

theorem e443_lift_alpha_RSharp :
    FreeGroup.lift (fun g : E443Gen => (PresentedGroup.of g : E443)⁻¹) e443RSharp =
      PresentedGroup.mk e443Rels e443R := by
  simp only [e443R, e443RSharp, e443Node, map_mul, map_inv, inv_inv, FreeGroup.lift_apply_of]
  rfl

@[expose] noncomputable def e443AlphaHom : E443 →* E443 :=
  e443Lift (fun g : E443Gen => (PresentedGroup.of g : E443)⁻¹)
    (fun s t hlt h => by
      rw [e443_ext_alpha, e443_ext_alpha, inv_inv]
      exact Y443.pow_inv_swap (e443_rel_adj hlt h))
    (fun s t hlt h => by
      rw [e443_ext_alpha, e443_ext_alpha, inv_inv]
      exact Y443.pow_inv_swap (e443_rel_nadj hlt h))
    (by
      rw [e443_lift_alpha_R, e443_lift_alpha_RSharp]
      exact Y443.pow_swap_mul e443_rel_spider)

theorem e443AlphaHom_of (g : E443Gen) :
    e443AlphaHom (PresentedGroup.of g) = (PresentedGroup.of g)⁻¹ :=
  e443Lift_of _ g

theorem e443AlphaHom_mk (x : FreeGroup E443Gen) :
    e443AlphaHom (PresentedGroup.mk e443Rels x) =
      FreeGroup.lift (fun g : E443Gen => (PresentedGroup.of g : E443)⁻¹) x :=
  e443Lift_mk _ x

theorem e443AlphaHom_comp_self : e443AlphaHom.comp e443AlphaHom = MonoidHom.id E443 := by
  refine PresentedGroup.ext fun g => ?_
  rw [MonoidHom.comp_apply, e443AlphaHom_of, map_inv, e443AlphaHom_of, inv_inv,
    MonoidHom.id_apply]

@[expose] noncomputable def e443Alpha : MulAut E443 :=
  MonoidHom.toMulEquiv e443AlphaHom e443AlphaHom e443AlphaHom_comp_self e443AlphaHom_comp_self

theorem e443Alpha_apply (x : E443) : e443Alpha x = e443AlphaHom x := rfl

@[simp] theorem e443Alpha_of (g : E443Gen) :
    e443Alpha (PresentedGroup.of g) = (PresentedGroup.of g)⁻¹ :=
  e443AlphaHom_of g

theorem e443Alpha_u (s : MonsterY443Gen) : e443Alpha (e443u s) = (e443u s)⁻¹ := by
  rcases s with _ | g
  · simp only [e443u_none, map_one, inv_one]
  · simp only [e443u_some, e443Alpha_of]

theorem e443Alpha_R : e443Alpha (PresentedGroup.mk e443Rels e443R) =
    PresentedGroup.mk e443Rels e443RSharp :=
  (e443AlphaHom_mk e443R).trans e443_lift_alpha_R

theorem e443Alpha_RSharp : e443Alpha (PresentedGroup.mk e443Rels e443RSharp) =
    PresentedGroup.mk e443Rels e443R :=
  (e443AlphaHom_mk e443RSharp).trans e443_lift_alpha_RSharp

theorem e443Alpha_mul_self : e443Alpha * e443Alpha = 1 :=
  MulEquiv.ext fun x => DFunLike.congr_fun e443AlphaHom_comp_self x

theorem e443Alpha_trans_self : e443Alpha.trans e443Alpha = MulEquiv.refl E443 :=
  e443Alpha_mul_self

theorem e443Alpha_unique {β : MulAut E443}
    (hβ : ∀ g, β (PresentedGroup.of g) = (PresentedGroup.of g)⁻¹) : β = e443Alpha := by
  refine MulEquiv.ext fun x => ?_
  have h : (β : E443 →* E443) = e443AlphaHom :=
    PresentedGroup.ext fun g => (hβ g).trans (e443AlphaHom_of g).symm
  exact DFunLike.congr_fun h x

namespace Y443

theorem z2_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  revert x
  decide

theorem z2_eps_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
  decide

@[expose] def z2Hom {H : Type*} [Group H] (h : H) (hh : h * h = 1) :
    Multiplicative (ZMod 2) →* H where
  toFun x := if x = 1 then 1 else h
  map_one' := by simp only [↓reduceIte]
  map_mul' x y := by
    rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;>
      simp only [mul_one, one_mul, z2_eps_mul_self, ↓reduceIte, ofAdd_eq_one, one_ne_zero, hh]

@[simp] theorem z2Hom_one {H : Type*} [Group H] (h : H) (hh : h * h = 1) : z2Hom h hh 1 = 1 :=
  map_one _

@[simp] theorem z2Hom_ofAdd_one {H : Type*} [Group H] (h : H) (hh : h * h = 1) :
    z2Hom h hh (Multiplicative.ofAdd 1) = h := by
  simp only [z2Hom, MonoidHom.coe_mk, OneHom.coe_mk, ofAdd_eq_one, one_ne_zero, ↓reduceIte]

end Y443

@[expose] noncomputable def e443Act : Multiplicative (ZMod 2) →* MulAut E443 :=
  Y443.z2Hom e443Alpha e443Alpha_mul_self

@[simp] theorem e443Act_ofAdd_one : e443Act (Multiplicative.ofAdd 1) = e443Alpha :=
  Y443.z2Hom_ofAdd_one _ _

@[simp] theorem e443Act_one : e443Act 1 = 1 := map_one _

theorem e443Act_unique {φ : Multiplicative (ZMod 2) →* MulAut E443}
    (h : φ (Multiplicative.ofAdd 1) = e443Alpha) : φ = e443Act := by
  refine MonoidHom.ext fun x => ?_
  rcases Y443.z2_cases x with rfl | rfl
  · rw [map_one, map_one]
  · rw [h, e443Act_ofAdd_one]

section Semi

open SemidirectProduct (inl inr rightHom)

theorem e443_inr_eps_mul_self :
    (inr (Multiplicative.ofAdd 1) : E443 ⋊[e443Act] Multiplicative (ZMod 2)) *
      inr (Multiplicative.ofAdd 1) = 1 := by
  rw [← map_mul, Y443.z2_eps_mul_self, map_one]

theorem e443_inr_eps_inv :
    (inr (Multiplicative.ofAdd 1) : E443 ⋊[e443Act] Multiplicative (ZMod 2))⁻¹ =
      inr (Multiplicative.ofAdd 1) :=
  inv_eq_of_mul_eq_one_right e443_inr_eps_mul_self

theorem e443_inr_mul_inl_mul_inr (u : E443) :
    (inr (Multiplicative.ofAdd 1) : E443 ⋊[e443Act] Multiplicative (ZMod 2)) * inl u *
      inr (Multiplicative.ofAdd 1) = inl (e443Alpha u) := by
  have h := SemidirectProduct.inl_aut (φ := e443Act) (Multiplicative.ofAdd 1) u
  rw [e443Act_ofAdd_one, map_inv, e443_inr_eps_inv] at h
  exact h.symm

theorem e443_inr_mul_inl (u : E443) :
    (inr (Multiplicative.ofAdd 1) : E443 ⋊[e443Act] Multiplicative (ZMod 2)) * inl u =
      inl (e443Alpha u) * inr (Multiplicative.ofAdd 1) := by
  rw [← e443_inr_mul_inl_mul_inr, mul_assoc, e443_inr_eps_mul_self, mul_one]

@[expose] noncomputable def e443PsiGen (s : MonsterY443Gen) :
    E443 ⋊[e443Act] Multiplicative (ZMod 2) :=
  inr (Multiplicative.ofAdd 1) * inl (e443u s)

theorem e443PsiGen_none : e443PsiGen none = inr (Multiplicative.ofAdd 1) := by
  simp only [e443PsiGen, e443u_none, map_one, mul_one]

theorem e443PsiGen_mul (s t : MonsterY443Gen) :
    e443PsiGen s * e443PsiGen t = inl ((e443u s)⁻¹ * e443u t) := by
  have h := e443_inr_mul_inl_mul_inr (e443u s)
  rw [e443Alpha_u] at h
  calc e443PsiGen s * e443PsiGen t
      = (inr (Multiplicative.ofAdd 1) * inl (e443u s) * inr (Multiplicative.ofAdd 1)) *
          inl (e443u t) := by simp only [e443PsiGen, mul_assoc]
    _ = inl ((e443u s)⁻¹ * e443u t) := by rw [h, map_mul]

theorem e443PsiGen_word (g11 g12 g21 g22 g31 g32 : E443Gen) :
    e443PsiGen none * e443PsiGen (some g11) * e443PsiGen (some g12) * e443PsiGen none *
      e443PsiGen (some g21) * e443PsiGen (some g22) * e443PsiGen none *
        e443PsiGen (some g31) * e443PsiGen (some g32) =
      inl (PresentedGroup.of g11 * (PresentedGroup.of g12)⁻¹ * (PresentedGroup.of g21)⁻¹ *
        PresentedGroup.of g22 * PresentedGroup.of g31 * (PresentedGroup.of g32)⁻¹) *
          inr (Multiplicative.ofAdd 1) := by
  have e1 : e443PsiGen none * e443PsiGen (some g11) * e443PsiGen (some g12) * e443PsiGen none *
      e443PsiGen (some g21) * e443PsiGen (some g22) * e443PsiGen none *
        e443PsiGen (some g31) * e443PsiGen (some g32) =
      (e443PsiGen none * e443PsiGen (some g11)) * (e443PsiGen (some g12) * e443PsiGen none) *
        (e443PsiGen (some g21) * e443PsiGen (some g22)) *
          (e443PsiGen none * e443PsiGen (some g31)) * e443PsiGen (some g32) := by
    simp only [mul_assoc]
  have e2 : e443PsiGen (some g32) =
      inl (e443Alpha (PresentedGroup.of g32)) * inr (Multiplicative.ofAdd 1) := by
    rw [e443PsiGen, e443u_some, e443_inr_mul_inl]
  rw [e1, e443PsiGen_mul, e443PsiGen_mul, e443PsiGen_mul, e443PsiGen_mul, e2, ← mul_assoc,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2

theorem e443PsiGen_spider :
    FreeGroup.lift e443PsiGen monsterY443SpiderWord =
      inl (PresentedGroup.mk e443Rels e443R) * inr (Multiplicative.ofAdd 1) := by
  simp only [monsterY443SpiderWord, monsterY443Node, map_mul, FreeGroup.lift_apply_of]
  rw [e443PsiGen_word]
  simp only [e443R, e443Node, map_mul, map_inv]
  rfl

theorem e443PsiGen_spider_pow :
    (inl (PresentedGroup.mk e443Rels e443R) * inr (Multiplicative.ofAdd 1) :
      E443 ⋊[e443Act] Multiplicative (ZMod 2)) ^ 10 = 1 := by
  have h2 : (inl (PresentedGroup.mk e443Rels e443R) * inr (Multiplicative.ofAdd 1) :
      E443 ⋊[e443Act] Multiplicative (ZMod 2)) ^ 2 =
      inl (PresentedGroup.mk e443Rels e443R * PresentedGroup.mk e443Rels e443RSharp) := by
    rw [pow_two, mul_assoc, ← mul_assoc (inr _), e443_inr_mul_inl_mul_inr, e443Alpha_R,
      map_mul]
  rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, h2, ← map_pow, e443_rel_spider, map_one]

theorem e443PsiGen_rels : ∀ r ∈ monsterY443Rels, FreeGroup.lift e443PsiGen r = 1 := by
  rintro r (((⟨s, rfl⟩ | ⟨s, t, hadj, rfl⟩) | ⟨s, t, hne, hnadj, rfl⟩) | rfl)
  · rw [map_pow, FreeGroup.lift_apply_of, pow_two, e443PsiGen_mul, inv_mul_cancel, map_one]
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, e443PsiGen_mul,
      ← map_pow, e443_pow_adj hadj, map_one]
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, e443PsiGen_mul,
      ← map_pow, e443_pow_nadj hne hnadj, map_one]
  · rw [map_pow, e443PsiGen_spider]
    exact e443PsiGen_spider_pow

@[expose] noncomputable def e443PsiHom :
    MonsterY443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := e443PsiGen) e443PsiGen_rels

theorem e443PsiHom_of (s : MonsterY443Gen) :
    e443PsiHom (PresentedGroup.of s) = e443PsiGen s :=
  PresentedGroup.toGroup.of _

end Semi

namespace Y443

theorem pgen_inv (s : MonsterY443Gen) :
    (PresentedGroup.of s : MonsterY443)⁻¹ = PresentedGroup.of s :=
  inv_eq_of_mul_eq_one_right (gen_mul_self s)

theorem pgen_cancel (y : MonsterY443) :
    (PresentedGroup.of none : MonsterY443) * ((PresentedGroup.of none : MonsterY443) * y) = y := by
  rw [← mul_assoc, gen_mul_self, one_mul]

theorem pgen_mk (x : MonsterY443Gen) :
    PresentedGroup.mk monsterY443Rels (FreeGroup.of x) = (PresentedGroup.of x : MonsterY443) :=
  rfl

end Y443

@[expose] noncomputable def e443PhiGen (g : E443Gen) : MonsterY443 :=
  PresentedGroup.of none * PresentedGroup.of (some g)

theorem e443_phi_ext (s : MonsterY443Gen) :
    e443Ext e443PhiGen s = (PresentedGroup.of none : MonsterY443) * PresentedGroup.of s := by
  rcases s with _ | g
  · simp only [e443Ext, Y443.gen_mul_self]
  · simp only [e443Ext, e443PhiGen]

theorem e443_phi_pair (s t : MonsterY443Gen) :
    ((PresentedGroup.of none : MonsterY443) * PresentedGroup.of s)⁻¹ *
      (PresentedGroup.of none * PresentedGroup.of t) =
        PresentedGroup.of s * PresentedGroup.of t := by
  rw [mul_inv_rev, Y443.pgen_inv, Y443.pgen_inv]
  calc PresentedGroup.of s * PresentedGroup.of none *
        (PresentedGroup.of none * PresentedGroup.of t)
      = PresentedGroup.of s * (PresentedGroup.of none * PresentedGroup.of none) *
        PresentedGroup.of t := by simp only [mul_assoc]
    _ = _ := by rw [Y443.gen_mul_self, mul_one]

theorem e443_phi_lift_R :
    FreeGroup.lift e443PhiGen e443R =
      PresentedGroup.mk monsterY443Rels monsterY443SpiderWord * PresentedGroup.of none := by
  simp only [e443R, e443Node, monsterY443SpiderWord, monsterY443Node, map_mul, map_inv,
    FreeGroup.lift_apply_of, e443PhiGen, Y443.pgen_mk, mul_inv_rev, Y443.pgen_inv, mul_assoc,
    Y443.pgen_cancel]

theorem e443_phi_lift_RSharp :
    FreeGroup.lift e443PhiGen e443RSharp =
      PresentedGroup.of none * PresentedGroup.mk monsterY443Rels monsterY443SpiderWord := by
  simp only [e443RSharp, e443Node, monsterY443SpiderWord, monsterY443Node, map_mul, map_inv,
    FreeGroup.lift_apply_of, e443PhiGen, Y443.pgen_mk, mul_inv_rev, Y443.pgen_inv, mul_assoc,
    Y443.pgen_cancel]

@[expose] noncomputable def e443PhiHom : E443 →* MonsterY443 :=
  e443Lift e443PhiGen
    (fun s t _ h => by
      rw [e443_phi_ext, e443_phi_ext, e443_phi_pair]
      exact Y443.gen_pair_adj h)
    (fun s t hlt h => by
      rw [e443_phi_ext, e443_phi_ext, e443_phi_pair]
      exact Y443.gen_pair_nonadj (e443Lt_ne hlt) h)
    (by
      rw [e443_phi_lift_R, e443_phi_lift_RSharp]
      have e : PresentedGroup.mk monsterY443Rels monsterY443SpiderWord *
            (PresentedGroup.of none : MonsterY443) *
          ((PresentedGroup.of none : MonsterY443) *
            PresentedGroup.mk monsterY443Rels monsterY443SpiderWord) =
          PresentedGroup.mk monsterY443Rels monsterY443SpiderWord ^ 2 := by
        rw [pow_two, mul_assoc, Y443.pgen_cancel]
      rw [e, ← pow_mul]
      exact Y443.spider_pow)

theorem e443PhiHom_of (g : E443Gen) :
    e443PhiHom (PresentedGroup.of g) = PresentedGroup.of none * PresentedGroup.of (some g) :=
  e443Lift_of _ g

theorem e443PhiHom_u (s : MonsterY443Gen) :
    e443PhiHom (e443u s) = (PresentedGroup.of none : MonsterY443) * PresentedGroup.of s := by
  rcases s with _ | g
  · simp only [e443u_none, map_one, Y443.gen_mul_self]
  · exact e443PhiHom_of g

@[expose] noncomputable def e443EpsHom : Multiplicative (ZMod 2) →* MonsterY443 :=
  Y443.z2Hom (PresentedGroup.of none) (Y443.gen_mul_self none)

@[simp] theorem e443EpsHom_one : e443EpsHom 1 = 1 := map_one _

@[simp] theorem e443EpsHom_ofAdd_one :
    e443EpsHom (Multiplicative.ofAdd 1) = PresentedGroup.of none :=
  Y443.z2Hom_ofAdd_one _ _

theorem e443_phi_compat (x : Multiplicative (ZMod 2)) :
    e443PhiHom.comp (e443Act x).toMonoidHom =
      (MulAut.conj (e443EpsHom x)).toMonoidHom.comp e443PhiHom := by
  rcases Y443.z2_cases x with rfl | rfl
  · refine MonoidHom.ext fun u => ?_
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
      MulAut.coe_one, Function.comp_apply, id_eq, map_one]
  · refine PresentedGroup.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e443Act_ofAdd_one, e443Alpha_of,
      map_inv, e443PhiHom_of, e443EpsHom_ofAdd_one, MulAut.conj_apply, Y443.pgen_cancel,
      Y443.pgen_inv, mul_inv_rev]

section Psi

open SemidirectProduct (inl inr rightHom)

@[expose] noncomputable def e443PsiInvHom :
    E443 ⋊[e443Act] Multiplicative (ZMod 2) →* MonsterY443 :=
  SemidirectProduct.lift e443PhiHom e443EpsHom e443_phi_compat

theorem e443PsiInv_comp_psi : e443PsiInvHom.comp e443PsiHom = MonoidHom.id MonsterY443 := by
  refine PresentedGroup.ext fun s => ?_
  rw [MonoidHom.comp_apply, e443PsiHom_of, e443PsiGen, map_mul, e443PsiInvHom,
    SemidirectProduct.lift_inr, SemidirectProduct.lift_inl, e443EpsHom_ofAdd_one, e443PhiHom_u,
    Y443.pgen_cancel, MonoidHom.id_apply]

theorem e443Psi_comp_phi :
    e443PsiHom.comp e443PhiHom =
      (inl : E443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)) := by
  refine PresentedGroup.ext fun g => ?_
  rw [MonoidHom.comp_apply, e443PhiHom_of, map_mul, e443PsiHom_of, e443PsiHom_of,
    e443PsiGen_mul, e443u_none, inv_one, one_mul, e443u_some]

theorem e443Psi_comp_eps :
    e443PsiHom.comp e443EpsHom =
      (inr : Multiplicative (ZMod 2) →* E443 ⋊[e443Act] Multiplicative (ZMod 2)) := by
  refine MonoidHom.ext fun x => ?_
  rcases Y443.z2_cases x with rfl | rfl
  · simp only [map_one]
  · rw [MonoidHom.comp_apply, e443EpsHom_ofAdd_one, e443PsiHom_of, e443PsiGen_none]

theorem e443Psi_comp_psiInv : e443PsiHom.comp e443PsiInvHom = MonoidHom.id _ := by
  refine SemidirectProduct.hom_ext ?_ ?_
  · rw [MonoidHom.comp_assoc, e443PsiInvHom, SemidirectProduct.lift_comp_inl, e443Psi_comp_phi]
    rfl
  · rw [MonoidHom.comp_assoc, e443PsiInvHom, SemidirectProduct.lift_comp_inr, e443Psi_comp_eps]
    rfl

@[expose] noncomputable def e443Psi : MonsterY443 ≃* E443 ⋊[e443Act] Multiplicative (ZMod 2) :=
  MonoidHom.toMulEquiv e443PsiHom e443PsiInvHom e443PsiInv_comp_psi e443Psi_comp_psiInv

theorem e443Psi_a : e443Psi (PresentedGroup.of none) = inr (Multiplicative.ofAdd 1) := by
  rw [← e443PsiGen_none]
  exact e443PsiHom_of none

theorem e443Psi_x (g : E443Gen) :
    e443Psi (PresentedGroup.of (some g)) =
      inr (Multiplicative.ofAdd 1) * inl (PresentedGroup.of g) :=
  e443PsiHom_of (some g)

theorem e443Psi_unique {f : MonsterY443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)}
    (ha : f (PresentedGroup.of none) = inr (Multiplicative.ofAdd 1))
    (hx : ∀ g, f (PresentedGroup.of (some g)) =
      inr (Multiplicative.ofAdd 1) * inl (PresentedGroup.of g)) :
    f = e443Psi.toMonoidHom := by
  refine PresentedGroup.ext fun s => ?_
  rcases s with _ | g
  · exact ha.trans e443Psi_a.symm
  · exact (hx g).trans (e443Psi_x g).symm

theorem e443_rightHom_comp_psi :
    (rightHom : E443 ⋊[e443Act] Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)).comp
      e443PsiHom = y443Parity := by
  refine PresentedGroup.ext fun s => ?_
  rw [MonoidHom.comp_apply, e443PsiHom_of, e443PsiGen, map_mul, y443Parity_of]
  simp only [SemidirectProduct.rightHom_inr, SemidirectProduct.rightHom_inl, mul_one]

theorem y443_mem_derived_iff {x : MonsterY443} : x ∈ MonsterY443Derived ↔ y443Parity x = 1 := by
  rw [← MonoidHom.mem_ker, y443Parity_ker]

theorem e443Psi_mem_range_inl_iff (x : MonsterY443) :
    x ∈ MonsterY443Derived ↔
      e443Psi x ∈ (inl : E443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, y443_mem_derived_iff, MonoidHom.mem_ker,
    ← e443_rightHom_comp_psi]
  rfl

theorem e443_range_inl_normal :
    ((inl : E443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem e443Psi_map_derived :
    MonsterY443Derived.map e443Psi.toMonoidHom =
      (inl : E443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)).range := by
  ext y
  rw [Subgroup.mem_map_equiv, e443Psi_mem_range_inl_iff]
  simp only [MulEquiv.apply_symm_apply, MonoidHom.mem_range]

end Psi

section Phi

open SemidirectProduct (inl inr rightHom)

theorem y443Parity_comp_phi : y443Parity.comp e443PhiHom = 1 := by
  refine PresentedGroup.ext fun g => ?_
  rw [MonoidHom.comp_apply, e443PhiHom_of, map_mul, y443Parity_of, y443Parity_of,
    MonoidHom.one_apply]
  exact Y443.z2_eps_mul_self

theorem e443PhiHom_mem (u : E443) : e443PhiHom u ∈ MonsterY443Derived := by
  rw [y443_mem_derived_iff, ← MonoidHom.comp_apply, y443Parity_comp_phi]
  rfl

theorem e443_ax_mem_derived (g : E443Gen) :
    (PresentedGroup.of none * PresentedGroup.of (some g) : MonsterY443) ∈ MonsterY443Derived := by
  rw [← e443PhiHom_of]
  exact e443PhiHom_mem _

theorem e443Psi_phiHom (u : E443) : e443Psi (e443PhiHom u) = inl u :=
  DFunLike.congr_fun e443Psi_comp_phi u

theorem e443PhiHom_injective : Function.Injective e443PhiHom := by
  intro u v h
  have h1 := congrArg e443Psi h
  rw [e443Psi_phiHom, e443Psi_phiHom] at h1
  exact SemidirectProduct.inl_injective h1

@[expose] noncomputable def e443Phi : E443 ≃* MonsterY443Derived :=
  MulEquiv.ofBijective (e443PhiHom.codRestrict MonsterY443Derived e443PhiHom_mem)
    ⟨fun u v h => e443PhiHom_injective (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      obtain ⟨u, hu⟩ := (e443Psi_mem_range_inl_iff y).1 hy
      refine ⟨u, Subtype.ext (e443Psi.injective ?_)⟩
      rw [← hu]
      exact e443Psi_phiHom u⟩

@[simp] theorem e443Phi_coe (u : E443) : (e443Phi u : MonsterY443) = e443PhiHom u := rfl

theorem e443Phi_of (g : E443Gen) :
    e443Phi (PresentedGroup.of g) =
      ⟨PresentedGroup.of none * PresentedGroup.of (some g), e443_ax_mem_derived g⟩ :=
  Subtype.ext (e443PhiHom_of g)

theorem e443Phi_unique {f : E443 →* MonsterY443Derived}
    (hf : ∀ g, (f (PresentedGroup.of g) : MonsterY443) =
      PresentedGroup.of none * PresentedGroup.of (some g)) :
    f = e443Phi.toMonoidHom :=
  PresentedGroup.ext fun g => Subtype.ext ((hf g).trans (e443PhiHom_of g).symm)

theorem e443Psi_phi (u : E443) : e443Psi (e443Phi u : MonsterY443) = inl u :=
  e443Psi_phiHom u

end Phi

theorem y443_derived_presentation_isomorphism :
    ((∀ g, e443Alpha (PresentedGroup.of g) = (PresentedGroup.of g)⁻¹) ∧
      e443Alpha * e443Alpha = 1 ∧
      ∀ β : MulAut E443, (∀ g, β (PresentedGroup.of g) = (PresentedGroup.of g)⁻¹) →
        β = e443Alpha) ∧
    (e443Act (Multiplicative.ofAdd 1) = e443Alpha ∧
      ∀ φ : Multiplicative (ZMod 2) →* MulAut E443, φ (Multiplicative.ofAdd 1) = e443Alpha →
        φ = e443Act) ∧
    (e443Psi (PresentedGroup.of none) = SemidirectProduct.inr (Multiplicative.ofAdd 1) ∧
      ∀ g, e443Psi (PresentedGroup.of (some g)) =
        SemidirectProduct.inr (Multiplicative.ofAdd 1) *
          SemidirectProduct.inl (PresentedGroup.of g)) ∧
    Function.Bijective e443Psi ∧
    MonsterY443Derived.map e443Psi.toMonoidHom =
      (SemidirectProduct.inl : E443 →* E443 ⋊[e443Act] Multiplicative (ZMod 2)).range ∧
    (∀ g, (e443Phi (PresentedGroup.of g) : MonsterY443) =
      PresentedGroup.of none * PresentedGroup.of (some g)) ∧
    Function.Bijective e443Phi :=
  ⟨⟨e443Alpha_of, e443Alpha_mul_self, fun _ h => e443Alpha_unique h⟩,
    ⟨e443Act_ofAdd_one, fun _ h => e443Act_unique h⟩,
    ⟨e443Psi_a, e443Psi_x⟩, e443Psi.bijective, e443Psi_map_derived,
    fun g => congrArg Subtype.val (e443Phi_of g), e443Phi.bijective⟩

end CFSG.YGroups
