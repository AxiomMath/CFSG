module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.Factors

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

variable {X G : Type*} [Group X] [Group G] (φ : X →* G)

@[expose] def act (x : X) (J : Subgroup G) : Subgroup G :=
  J.map (MulAut.conj (φ x)).toMonoidHom

variable {φ}

theorem mem_act_iff {x : X} {J : Subgroup G} {g : G} :
    g ∈ act φ x J ↔ (φ x)⁻¹ * g * φ x ∈ J := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hj
  · intro h
    exact ⟨(φ x)⁻¹ * g * φ x, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem act_one (J : Subgroup G) : act φ 1 J = J := by
  ext g
  simp [mem_act_iff]

theorem act_mul (x y : X) (J : Subgroup G) : act φ (x * y) J = act φ x (act φ y J) := by
  ext g
  simp only [mem_act_iff, map_mul, mul_inv_rev]
  simp [mul_assoc]

theorem act_inv_act (x : X) (J : Subgroup G) : act φ x⁻¹ (act φ x J) = J := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (x : X) (J : Subgroup G) : act φ x (act φ x⁻¹ J) = J := by
  rw [← act_mul, mul_inv_cancel, act_one]

@[expose] noncomputable def actEquiv (x : X) (J : Subgroup G) : J ≃* act φ x J :=
  Subgroup.equivMapOfInjective J (MulAut.conj (φ x)).toMonoidHom (MulAut.conj (φ x)).injective

@[expose] def IsInv (φ : X →* G) (S : Set (Subgroup G)) : Prop :=
  ∀ x : X, ∀ J ∈ S, act φ x J ∈ S

@[expose] def fixer (φ : X →* G) (S : Set (Subgroup G)) : Subgroup X where
  carrier := {x | ∀ J ∈ S, act φ x J = J}
  one_mem' := fun J _ => act_one J
  mul_mem' := fun {a b} ha hb J hJ => by rw [act_mul, hb J hJ, ha J hJ]
  inv_mem' := fun {a} ha J hJ => by
    calc act φ a⁻¹ J = act φ a⁻¹ (act φ a J) := by rw [ha J hJ]
      _ = J := act_inv_act a J

theorem mem_fixer_iff {S : Set (Subgroup G)} {x : X} :
    x ∈ fixer φ S ↔ ∀ J ∈ S, act φ x J = J := Iff.rfl

@[expose] def cen (φ : X →* G) (S : Set (Subgroup G)) : Subgroup X where
  carrier := {x | ∀ J ∈ S, ∀ j ∈ J, j * φ x = φ x * j}
  one_mem' := fun J _ j _ => by simp
  mul_mem' := fun {a b} ha hb J hJ j hj => by
    simp only [map_mul]
    calc j * (φ a * φ b) = (j * φ a) * φ b := by group
      _ = (φ a * j) * φ b := by rw [ha J hJ j hj]
      _ = φ a * (j * φ b) := by group
      _ = φ a * (φ b * j) := by rw [hb J hJ j hj]
      _ = φ a * φ b * j := by group
  inv_mem' := fun {a} ha J hJ j hj => by
    simp only [map_inv]
    have h := ha J hJ j hj
    calc j * (φ a)⁻¹ = (φ a)⁻¹ * (φ a * j) * (φ a)⁻¹ := by group
      _ = (φ a)⁻¹ * (j * φ a) * (φ a)⁻¹ := by rw [h]
      _ = (φ a)⁻¹ * j := by group

theorem mem_cen_iff {S : Set (Subgroup G)} {x : X} :
    x ∈ cen φ S ↔ ∀ J ∈ S, ∀ j ∈ J, j * φ x = φ x * j := Iff.rfl

theorem cen_le_fixer (S : Set (Subgroup G)) : cen φ S ≤ fixer φ S := by
  intro x hx J hJ
  ext g
  rw [mem_act_iff]
  constructor
  · intro h
    have hc := hx J hJ _ h
    have e : (φ x)⁻¹ * g * φ x = g := by
      have h1 : φ x * ((φ x)⁻¹ * g * φ x) = g * φ x := by group
      rw [← hc] at h1
      exact mul_right_cancel h1
    rw [e] at h
    exact h
  · intro hg
    have hc := hx J hJ g hg
    have : (φ x)⁻¹ * g * φ x = g := by
      calc (φ x)⁻¹ * g * φ x = (φ x)⁻¹ * (g * φ x) := by group
        _ = (φ x)⁻¹ * (φ x * g) := by rw [hc]
        _ = g := by group
    rw [this]
    exact hg

theorem fixer_normal {S : Set (Subgroup G)} (hS : IsInv φ S) : (fixer φ S).Normal := by
  refine ⟨fun y hy x J hJ => ?_⟩
  have h1 : act φ x⁻¹ J ∈ S := hS x⁻¹ J hJ
  have h2 : act φ y (act φ x⁻¹ J) = act φ x⁻¹ J := hy _ h1
  calc act φ (x * y * x⁻¹) J = act φ x (act φ y (act φ x⁻¹ J)) := by
        rw [act_mul, act_mul]
    _ = J := by rw [h2, act_act_inv]

theorem cen_normal {S : Set (Subgroup G)} (hS : IsInv φ S) : (cen φ S).Normal := by
  refine ⟨fun c hc x J hJ j hj => ?_⟩
  have h1 : act φ x⁻¹ J ∈ S := hS x⁻¹ J hJ
  have hj' : (φ x)⁻¹ * j * φ x ∈ act φ x⁻¹ J := by
    rw [mem_act_iff, map_inv, inv_inv]
    have : φ x * ((φ x)⁻¹ * j * φ x) * (φ x)⁻¹ = j := by group
    rw [this]
    exact hj
  have h := hc _ h1 _ hj'
  simp only [map_mul, map_inv] at h ⊢
  calc j * (φ x * φ c * (φ x)⁻¹)
      = φ x * (((φ x)⁻¹ * j * φ x) * φ c) * (φ x)⁻¹ := by group
    _ = φ x * (φ c * ((φ x)⁻¹ * j * φ x)) * (φ x)⁻¹ := by rw [h]
    _ = φ x * φ c * (φ x)⁻¹ * j := by group

@[expose] def permAct (φ : X →* G) (S : Set (Subgroup G)) (hS : IsInv φ S) :
    X →* Equiv.Perm S where
  toFun x :=
    { toFun := fun J => ⟨act φ x J, hS x J J.2⟩
      invFun := fun J => ⟨act φ x⁻¹ J, hS x⁻¹ J J.2⟩
      left_inv := fun J => Subtype.ext (act_inv_act (φ := φ) x J.1)
      right_inv := fun J => Subtype.ext (act_act_inv (φ := φ) x J.1) }
  map_one' := Equiv.ext fun J => Subtype.ext (act_one (φ := φ) J.1)
  map_mul' x y := Equiv.ext fun J => Subtype.ext (act_mul (φ := φ) x y J.1)

theorem permAct_apply_coe {S : Set (Subgroup G)} (hS : IsInv φ S) (x : X) (J : S) :
    ((permAct φ S hS x J : S) : Subgroup G) = act φ x J := rfl

theorem ker_permAct {S : Set (Subgroup G)} (hS : IsInv φ S) :
    (permAct φ S hS).ker = fixer φ S := by
  ext x
  rw [MonoidHom.mem_ker, mem_fixer_iff, Equiv.ext_iff]
  constructor
  · intro h J hJ
    have := congrArg Subtype.val (h ⟨J, hJ⟩)
    rwa [permAct_apply_coe] at this
  · intro h J
    refine Subtype.ext ?_
    rw [permAct_apply_coe]
    exact h J J.2

theorem mem_normalizer_of_act_eq {y : X} {J : Subgroup G} (h : act φ y J = J) :
    φ y ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  have h1 : φ y * j * (φ y)⁻¹ ∈ J ↔ j ∈ act φ y⁻¹ J := by
    rw [mem_act_iff]
    simp
  have h2 : act φ y⁻¹ J = J := by
    calc act φ y⁻¹ J = act φ y⁻¹ (act φ y J) := by rw [h]
      _ = J := act_inv_act y J
  rw [h1, h2]

@[expose] noncomputable def actHom (J : Subgroup G) (Y : Subgroup X)
    (h : ∀ y ∈ Y, act φ y J = J) : Y →* MulAut J :=
  (Subgroup.normalizerMonoidHom J).comp
    ((φ.comp Y.subtype).codRestrict (Subgroup.normalizer (J : Set G))
      fun y => mem_normalizer_of_act_eq (h y y.2))

theorem actHom_apply_coe {J : Subgroup G} {Y : Subgroup X} (h : ∀ y ∈ Y, act φ y J = J)
    (y : Y) (j : J) : ((actHom J Y h y j : J) : G) = φ y * j * (φ y)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe J _ j

theorem mem_ker_actHom_iff {J : Subgroup G} {Y : Subgroup X} (h : ∀ y ∈ Y, act φ y J = J)
    {y : Y} : y ∈ (actHom J Y h).ker ↔ ∀ j ∈ J, j * φ y = φ y * j := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hy j hj
    have := congrArg (fun a : MulAut J => ((a ⟨j, hj⟩ : J) : G)) hy
    simp only [actHom_apply_coe, MulAut.one_apply] at this
    calc j * φ y = φ y * j * (φ y)⁻¹ * φ y := by rw [this]
      _ = φ y * j := by group
  · intro hy
    ext j
    simp only [actHom_apply_coe, MulAut.one_apply]
    rw [← hy j j.2]
    group

theorem actHom_mem_range_conj_iff {J : Subgroup G} {Y : Subgroup X}
    (h : ∀ y ∈ Y, act φ y J = J) (y : Y) :
    actHom J Y h y ∈ (MulAut.conj : J →* MulAut J).range ↔
      ∃ k ∈ J, ∀ j ∈ J, φ y * j * (φ y)⁻¹ = k * j * k⁻¹ := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, k.2, fun j hj => ?_⟩
    have := congrArg (fun a : MulAut J => ((a ⟨j, hj⟩ : J) : G)) hk
    simp only [actHom_apply_coe, MulAut.conj_apply] at this
    simpa using this.symm
  · rintro ⟨k, hk, hkj⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    ext j
    simp only [actHom_apply_coe, MulAut.conj_apply]
    simpa using (hkj j j.2).symm

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
