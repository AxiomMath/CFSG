module

public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin

abbrev DualGrp (V : Type*) [CommGroup V] : Type _ := V →* Multiplicative (ZMod 2)

instance dualGrpCommGroup (V : Type*) [CommGroup V] : CommGroup (V →* Multiplicative (ZMod 2)) :=
  MonoidHom.instCommGroup

instance dualGrpFinite (V : Type*) [CommGroup V] [Finite V] : Finite (DualGrp V) :=
  Finite.of_injective (fun f : DualGrp V => (f : V → Multiplicative (ZMod 2))) DFunLike.coe_injective

section Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [CommGroup V]

theorem DualGrp.mul_apply (f g : DualGrp V) (v : V) : (f * g) v = f v * g v := rfl
theorem DualGrp.one_apply (v : V) : (1 : DualGrp V) v = 1 := rfl
theorem DualGrp.inv_apply (f : DualGrp V) (v : V) : f⁻¹ v = (f v)⁻¹ := rfl
theorem DualGrp.ext {f g : DualGrp V} (h : ∀ v, f v = g v) : f = g := DFunLike.ext _ _ h

@[expose] def dualAnn (U : Subgroup V) : Subgroup (DualGrp V) where
  carrier := {f | ∀ u ∈ U, f u = 1}
  one_mem' := fun u _ => rfl
  mul_mem' := fun {f g} hf hg u hu => by
    show f u * g u = 1
    rw [hf u hu, hg u hu, mul_one]
  inv_mem' := fun {f} hf u hu => by
    show (f u)⁻¹ = 1
    rw [hf u hu]
    exact inv_one

theorem mem_dualAnn {U : Subgroup V} {f : DualGrp V} : f ∈ dualAnn U ↔ ∀ u ∈ U, f u = 1 :=
  Iff.rfl

@[expose] def dualCoann (M : Subgroup (DualGrp V)) : Subgroup V where
  carrier := {v | ∀ f ∈ M, f v = 1}
  one_mem' := fun f _ => map_one f
  mul_mem' := fun {a b} ha hb f hf => by
    rw [map_mul, ha f hf, hb f hf, mul_one]
  inv_mem' := fun {a} ha f hf => by
    rw [map_inv, ha f hf]
    exact inv_one

theorem mem_dualCoann {M : Subgroup (DualGrp V)} {v : V} :
    v ∈ dualCoann M ↔ ∀ f ∈ M, f v = 1 := Iff.rfl

@[expose] def F2Vec (V : Type*) [CommGroup V] (_hV : ∀ v : V, v ^ 2 = 1) : Type _ := Additive V

instance (hV : ∀ v : V, v ^ 2 = 1) : AddCommGroup (F2Vec V hV) :=
  inferInstanceAs (AddCommGroup (Additive V))

instance F2Vec.instModule (hV : ∀ v : V, v ^ 2 = 1) : Module (ZMod 2) (F2Vec V hV) :=
  AddCommGroup.zmodModule (G := Additive V) (fun x => by
    have := hV (Additive.toMul x)
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, ← pow_two]
    exact this)

instance [Finite V] (hV : ∀ v : V, v ^ 2 = 1) : Finite (F2Vec V hV) :=
  inferInstanceAs (Finite (Additive V))

variable (hV : ∀ v : V, v ^ 2 = 1)

@[expose] def F2Vec.ofV (v : V) : F2Vec V hV := Additive.ofMul v

@[expose] def F2Vec.toV (w : F2Vec V hV) : V := Additive.toMul w

theorem F2Vec.toV_ofV (v : V) : F2Vec.toV hV (F2Vec.ofV hV v) = v := rfl
theorem F2Vec.ofV_toV (w : F2Vec V hV) : F2Vec.ofV hV (F2Vec.toV hV w) = w := rfl
theorem F2Vec.ofV_mul (a b : V) : F2Vec.ofV hV (a * b) = F2Vec.ofV hV a + F2Vec.ofV hV b := rfl
theorem F2Vec.toV_add (a b : F2Vec V hV) : F2Vec.toV hV (a + b) = F2Vec.toV hV a * F2Vec.toV hV b :=
  rfl
theorem F2Vec.ofV_one : F2Vec.ofV hV (1 : V) = 0 := rfl
theorem F2Vec.toV_zero : F2Vec.toV hV (0 : F2Vec V hV) = 1 := rfl

@[expose] def f2ToLinDual (f : DualGrp V) : Module.Dual (ZMod 2) (F2Vec V hV) where
  toFun w := Multiplicative.toAdd (f (F2Vec.toV hV w))
  map_add' a b := by
    simp only [F2Vec.toV_add, map_mul, toAdd_mul]
  map_smul' c w := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]
      show Multiplicative.toAdd (f (F2Vec.toV hV 0)) = _
      simp [F2Vec.toV_zero]
    · rw [one_smul]; simp

@[expose] def f2OfLinDual (φ : Module.Dual (ZMod 2) (F2Vec V hV)) : DualGrp V where
  toFun v := Multiplicative.ofAdd (φ (F2Vec.ofV hV v))
  map_one' := by
    show Multiplicative.ofAdd (φ (F2Vec.ofV hV 1)) = 1
    rw [F2Vec.ofV_one, map_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (φ (F2Vec.ofV hV (a * b))) =
      Multiplicative.ofAdd (φ (F2Vec.ofV hV a)) * Multiplicative.ofAdd (φ (F2Vec.ofV hV b))
    rw [F2Vec.ofV_mul, map_add]
    rfl

theorem f2OfLinDual_f2ToLinDual (f : DualGrp V) : f2OfLinDual hV (f2ToLinDual hV f) = f := by
  apply DualGrp.ext
  intro v
  rfl

theorem f2ToLinDual_f2OfLinDual (φ : Module.Dual (ZMod 2) (F2Vec V hV)) :
    f2ToLinDual hV (f2OfLinDual hV φ) = φ := by
  apply LinearMap.ext
  intro w
  rfl

@[expose] def f2ToSub (U : Subgroup V) : Submodule (ZMod 2) (F2Vec V hV) where
  carrier := {w | F2Vec.toV hV w ∈ U}
  add_mem' := fun {a b} ha hb => U.mul_mem ha hb
  zero_mem' := U.one_mem
  smul_mem' := fun c w hw => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]; exact U.one_mem
    · rw [one_smul]; exact hw

theorem mem_f2ToSub {U : Subgroup V} {w : F2Vec V hV} : w ∈ f2ToSub hV U ↔ F2Vec.toV hV w ∈ U := Iff.rfl

@[expose] def f2ToSubDual (M : Subgroup (DualGrp V)) : Submodule (ZMod 2) (Module.Dual (ZMod 2) (F2Vec V hV)) where
  carrier := {φ | f2OfLinDual hV φ ∈ M}
  add_mem' := fun {φ ψ} hφ hψ => by
    have : f2OfLinDual hV (φ + ψ) = f2OfLinDual hV φ * f2OfLinDual hV ψ := by
      apply DualGrp.ext
      intro v
      rfl
    show f2OfLinDual hV (φ + ψ) ∈ M
    rw [this]
    exact M.mul_mem hφ hψ
  zero_mem' := by
    have : f2OfLinDual hV 0 = 1 := by
      apply DualGrp.ext
      intro v
      rfl
    show f2OfLinDual hV 0 ∈ M
    rw [this]
    exact M.one_mem
  smul_mem' := fun c φ hφ => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]
      have : f2OfLinDual hV 0 = 1 := by
        apply DualGrp.ext
        intro v
        rfl
      show f2OfLinDual hV 0 ∈ M
      rw [this]
      exact M.one_mem
    · rw [one_smul]; exact hφ

theorem mem_f2ToSubDual {M : Subgroup (DualGrp V)} {φ : Module.Dual (ZMod 2) (F2Vec V hV)} :
    φ ∈ f2ToSubDual hV M ↔ f2OfLinDual hV φ ∈ M := Iff.rfl

theorem f2ToSub_injective : Function.Injective (f2ToSub (V := V) hV) := by
  intro U U' h
  ext v
  have := congrArg (fun S => F2Vec.ofV hV v ∈ S) h
  simpa [mem_f2ToSub, F2Vec.toV_ofV] using this

theorem f2ToSubDual_injective : Function.Injective (f2ToSubDual (V := V) hV) := by
  intro M M' h
  ext f
  have := congrArg (fun S => f2ToLinDual hV f ∈ S) h
  simpa [mem_f2ToSubDual, f2OfLinDual_f2ToLinDual] using this

theorem f2ToSub_dualAnn (U : Subgroup V) :
    f2ToSubDual hV (dualAnn U) = (f2ToSub hV U).dualAnnihilator := by
  ext φ
  rw [mem_f2ToSubDual, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    have h1 : Multiplicative.ofAdd (φ w) = 1 := h (F2Vec.toV hV w) hw
    exact ofAdd_eq_one.mp h1
  · intro h u hu
    have h1 : φ (F2Vec.ofV hV u) = 0 := h _ (by
      show F2Vec.toV hV (F2Vec.ofV hV u) ∈ U
      exact hu)
    show Multiplicative.ofAdd (φ (F2Vec.ofV hV u)) = 1
    rw [h1]
    rfl

theorem f2ToSub_dualCoann (M : Subgroup (DualGrp V)) :
    f2ToSub hV (dualCoann M) = (f2ToSubDual hV M).dualCoannihilator := by
  ext w
  rw [mem_f2ToSub, Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    have h1 : f2OfLinDual hV φ (F2Vec.toV hV w) = 1 := h _ hφ
    exact ofAdd_eq_one.mp h1
  · intro h f hf
    have h1 : f2ToLinDual hV f w = 0 := h (f2ToLinDual hV f) (by
      rw [mem_f2ToSubDual, f2OfLinDual_f2ToLinDual]
      exact hf)
    have h2 : Multiplicative.toAdd (f (F2Vec.toV hV w)) = 0 := h1
    exact toAdd_eq_zero.mp h2

section Finite

variable [Finite V]

include hV

omit [Finite V] in
theorem dualCoann_dualAnn (U : Subgroup V) : dualCoann (dualAnn U) = U := by
  apply f2ToSub_injective hV
  rw [f2ToSub_dualCoann, f2ToSub_dualAnn]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

theorem dualAnn_dualCoann (M : Subgroup (DualGrp V)) :
    dualAnn (dualCoann M) = M := by
  apply f2ToSubDual_injective hV
  rw [f2ToSub_dualAnn, f2ToSub_dualCoann]
  have : Module.Finite (ZMod 2) (F2Vec V hV) := Module.Finite.of_finite
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

theorem dualAnn_card (U : Subgroup V) :
    Nat.card ↥(dualAnn U) * Nat.card ↥U = Nat.card V := by
  have : Module.Finite (ZMod 2) (F2Vec V hV) := Module.Finite.of_finite
  have h1 : Nat.card ↥U = Nat.card ↥(f2ToSub hV U) :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun v => Iff.rfl))
  have h2 : Nat.card ↥(dualAnn U) = Nat.card ↥(f2ToSub hV U).dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv
      ⟨f2ToLinDual hV, f2OfLinDual hV, f2OfLinDual_f2ToLinDual hV, f2ToLinDual_f2OfLinDual hV⟩ (fun f => ?_))
    rw [← f2ToSub_dualAnn, mem_f2ToSubDual]
    show f ∈ dualAnn U ↔ f2OfLinDual hV (f2ToLinDual hV f) ∈ dualAnn U
    rw [f2OfLinDual_f2ToLinDual]
  have h3 : Nat.card V = Nat.card (F2Vec V hV) := Nat.card_congr (Equiv.refl _)
  have hfin := Subspace.finrank_add_finrank_dualAnnihilator_eq (f2ToSub hV U)
  rw [h1, h2, h3, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(f2ToSub hV U)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(f2ToSub hV U).dualAnnihilator),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F2Vec V hV), ← hfin, pow_add, mul_comm]

end Finite

@[expose] noncomputable def dualSub (A : Subgroup (MulAut V)) : Subgroup (MulAut (DualGrp V)) :=
  A.map (dualAct V)

theorem dualAct_apply (a : MulAut V) (f : DualGrp V) (v : V) :
    ((dualAct V a : MulAut (DualGrp V)) f) v = f ((a⁻¹ : MulAut V) v) := rfl

theorem mem_dualSub {A : Subgroup (MulAut V)} {x : MulAut (DualGrp V)} :
    x ∈ dualSub A ↔ ∃ a ∈ A, dualAct V a = x := Iff.rfl

theorem mem_dualAnn_commV {A : Subgroup (MulAut V)} {f : DualGrp V} :
    f ∈ dualAnn (commV A) ↔ ∀ a ∈ A, ∀ v : V, f (a v) = f v := by
  constructor
  · intro h a ha v
    have h1 : f (a v * v⁻¹) = 1 := h _ (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  · intro h u hu
    have hker : commV A ≤ MonoidHom.ker (f : V →* Multiplicative (ZMod 2)) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, ha, v, rfl⟩
      show f (a v * v⁻¹) = 1
      rw [map_mul, map_inv, h a ha v, mul_inv_cancel]
    exact hker hu

theorem fixV_dualSub (A : Subgroup (MulAut V)) : fixV (dualSub A) = dualAnn (commV A) := by
  ext f
  show (∀ x ∈ dualSub A, x f = f) ↔ f ∈ dualAnn (commV A)
  rw [mem_dualAnn_commV]
  constructor
  · intro h a ha v
    have h1 := h (dualAct V a⁻¹) ⟨a⁻¹, A.inv_mem ha, rfl⟩
    have := congrArg (fun g => g v) h1
    have h2 : f ((a⁻¹)⁻¹ v) = f v := this
    simpa using h2
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := hx
    apply DFunLike.ext
    intro v
    show f ((a⁻¹ : MulAut V) v) = f v
    exact h _ (A.inv_mem ha) v

theorem dualCoann_le_dualCoann {M M' : Subgroup (DualGrp V)} (h : M ≤ M') :
    dualCoann M' ≤ dualCoann M := fun _ hv f hf => hv f (h hf)

theorem dualAnn_le_dualAnn {U U' : Subgroup V} (h : U' ≤ U) :
    dualAnn U ≤ dualAnn U' := fun _ hf u hu => hf u (h hu)

section Finite2

variable [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
include hV

omit [Finite V] in
theorem exists_dualChar_ne_one {x : V} (hx : x ≠ 1) : ∃ f : DualGrp V, f x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : x ∈ dualCoann (dualAnn (⊥ : Subgroup V)) := fun f _ => hcon f
  rw [dualCoann_dualAnn hV] at this
  exact hx this

omit [Finite V] in
theorem dualCoann_commV_dualSub (A : Subgroup (MulAut V)) :
    dualCoann (commV (dualSub A)) = fixV A := by
  ext v
  show (∀ f ∈ commV (dualSub A), f v = 1) ↔ ∀ a ∈ A, a v = v
  constructor
  · intro h a ha
    by_contra hne
    have hne' : (a v) * v⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
    obtain ⟨φ, hφ⟩ := exists_dualChar_ne_one hV hne'
    apply hφ
    have h1 := h ((dualAct V a⁻¹ : MulAut (DualGrp V)) φ * φ⁻¹)
      (Subgroup.subset_closure ⟨dualAct V a⁻¹, ⟨a⁻¹, A.inv_mem ha, rfl⟩, φ, rfl⟩)
    have h2 : φ ((a⁻¹)⁻¹ v) * (φ v)⁻¹ = 1 := h1
    simpa [map_mul, map_inv] using h2.symm ▸ h2
  · intro h f hf
    induction hf using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, ⟨a, ha, rfl⟩, φ, rfl⟩ := hg
      show φ ((a⁻¹ : MulAut V) v) * (φ v)⁻¹ = 1
      rw [show (a⁻¹ : MulAut V) v = v from by
        have := h a⁻¹ (A.inv_mem ha); exact this, mul_inv_cancel]
    | one => exact rfl
    | mul a b _ _ ha hb =>
      show a v * b v = 1
      rw [ha, hb, mul_one]
    | inv a _ ha =>
      show (a v)⁻¹ = 1
      rw [ha]
      exact inv_one

omit [Finite V] in
theorem dualAnn_le_dualAnn_iff {U U' : Subgroup V} :
    dualAnn U ≤ dualAnn U' ↔ U' ≤ U := by
  refine ⟨fun h => ?_, dualAnn_le_dualAnn⟩
  have := dualCoann_le_dualCoann h
  rwa [dualCoann_dualAnn hV, dualCoann_dualAnn hV] at this

theorem commV_dualSub (A : Subgroup (MulAut V)) : commV (dualSub A) = dualAnn (fixV A) := by
  rw [← dualCoann_commV_dualSub hV A, dualAnn_dualCoann hV]

theorem isQuadratic_dualSub_iff (A : Subgroup (MulAut V)) :
    IsQuadratic A ↔ IsQuadratic (dualSub A) := by
  unfold IsQuadratic
  rw [commV_dualSub hV, fixV_dualSub, dualAnn_le_dualAnn_iff hV]

omit hV [Finite V] in
theorem dualAnn_bot : dualAnn (⊥ : Subgroup V) = ⊤ := by
  ext f
  constructor
  · intro _; trivial
  · intro _ u hu
    rw [Subgroup.mem_bot.mp hu]
    exact map_one f

theorem card_dualGrp : Nat.card (DualGrp V) = Nat.card V := by
  have h := dualAnn_card hV (⊥ : Subgroup V)
  rw [dualAnn_bot] at h
  simpa using h

omit [Finite V] in
theorem dualAct_injective : Function.Injective (dualAct V) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, a⁻¹ v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hne (by
      ext v
      have h3 := congrArg a (hcon v)
      rw [MulAut.apply_inv_self] at h3
      exact h3.symm)
  obtain ⟨φ, hφ⟩ := exists_dualChar_ne_one hV (x := (a⁻¹ v) * v⁻¹) (fun h => hv (mul_inv_eq_one.mp h))
  apply hφ
  have h1 := congrArg (fun g : MulAut (DualGrp V) => g φ) ha
  have h2 : φ ((a⁻¹ : MulAut V) v) = φ v := by
    have := congrArg (fun g : DualGrp V => g v) h1
    exact this
  rw [map_mul, map_inv, h2, mul_inv_cancel]

omit [Finite V] in
theorem card_dualSub (A : Subgroup (MulAut V)) : Nat.card (dualSub A) = Nat.card A :=
  Subgroup.card_map_of_injective (dualAct_injective hV)

theorem index_fixV_dualSub (A : Subgroup (MulAut V)) :
    (fixV (dualSub A)).index = Nat.card (commV A) := by
  have h1 := dualAnn_card hV (commV A)
  have h2 := Subgroup.card_mul_index (fixV (dualSub A))
  rw [fixV_dualSub, card_dualGrp hV] at h2
  rw [fixV_dualSub]
  have hpos : 0 < Nat.card ↥(dualAnn (commV A)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)

omit [Finite V] hV in
theorem dualAnn_map (a : MulAut V) (U : Subgroup V) :
    dualAnn (U.map a.toMonoidHom) = (dualAnn U).map (dualAct V a).toMonoidHom := by
  ext f
  constructor
  · intro hf
    refine ⟨(dualAct V a⁻¹ : MulAut (DualGrp V)) f, ?_, ?_⟩
    · intro u hu
      show f (((a⁻¹)⁻¹ : MulAut V) u) = 1
      rw [inv_inv]
      exact hf (a u) ⟨u, hu, rfl⟩
    · show (dualAct V a) ((dualAct V a⁻¹) f) = f
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  · rintro ⟨g, hg, rfl⟩ x ⟨u, hu, rfl⟩
    show g ((a⁻¹ : MulAut V) (a u)) = 1
    rw [MulAut.inv_apply_self]
    exact hg u hu

omit [Finite V] in
theorem isPGroup_two_subgroup (S : Subgroup V) : IsPGroup 2 ↥S := fun x => ⟨1, by
  apply Subtype.ext
  have := hV (x : V)
  simpa using this⟩

theorem qOf_dualSub_le_two (A : Subgroup (MulAut V)) (hne : A ≠ ⊥) (hel : IsElemAbelian2 A)
    (hq : IsQuadratic A) (hdim : Nat.card (commV A) ≤ Nat.card A ^ 2) :
    qOf (dualSub A) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hApos : 0 < rk ↥A := IsElemAbelian2.rk_pos hel hne
  have hAdual : IsElemAbelian2 (dualSub A) := by
    obtain ⟨hcomm, hsq⟩ := hel
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      have : dualAct V (a * b) = dualAct V (b * a) := by rw [hcomm a ha b hb]
      exact (map_mul (dualAct V) a b).symm.trans (this.trans (map_mul (dualAct V) b a))
    · rintro x ⟨a, ha, rfl⟩
      exact (map_pow (dualAct V) a 2).symm.trans (by rw [hsq a ha, map_one]; rfl)
  have hdne : dualSub A ≠ ⊥ := by
    intro hbot
    apply hne
    have h1 : Nat.card (dualSub A) = Nat.card A := card_dualSub hV A
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq A h1.symm
  refine qOf_le_iff.mpr ⟨dualSub A, ⟨le_rfl, hdne, hAdual⟩, (isQuadratic_dualSub_iff hV A).mp hq, ?_⟩
  have hidx : rkIdx (fixV (dualSub A)) = padicValNat 2 (Nat.card (commV A)) := by
    unfold rkIdx
    rw [index_fixV_dualSub hV]
  have hrk : rk ↥(dualSub A) = rk ↥A := by
    unfold rk
    rw [card_dualSub hV]
  obtain ⟨m, hm⟩ := (IsElemAbelian2.isPGroup hel).exists_card_eq
  obtain ⟨k, hk⟩ := (isPGroup_two_subgroup hV (commV A)).exists_card_eq
  have hrkA : rk ↥A = m := by unfold rk; rw [hm, padicValNat.prime_pow]
  have hkk : padicValNat 2 (Nat.card (commV A)) = k := by rw [hk, padicValNat.prime_pow]
  have hle : k ≤ 2 * m := by
    have h1 : 2 ^ k ≤ 2 ^ (2 * m) := by
      calc 2 ^ k = Nat.card (commV A) := hk.symm
        _ ≤ Nat.card A ^ 2 := hdim
        _ = 2 ^ (2 * m) := by rw [hm, ← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hmpos : 0 < m := hrkA ▸ hApos
  have hmq : (0 : ℚ) < m := by exact_mod_cast hmpos
  have key : (rkIdx (fixV (dualSub A)) : ℚ) / (rk ↥(dualSub A) : ℚ) ≤ 2 := by
    rw [hidx, hrk, hrkA, hkk, div_le_iff₀ hmq]
    exact_mod_cast (by omega : k ≤ 2 * m)
  exact key

end Finite2

end Dual
end CFSG.Quasithin
