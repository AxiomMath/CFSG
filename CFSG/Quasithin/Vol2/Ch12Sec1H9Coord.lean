module

public import CFSG.Quasithin.Vol2.KGFactSLnTwoHom
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec1H9
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.H9Coord

open CFSG.Open CFSG.Quasithin.SLnTwo CFSG.ComponentClassification.CatalogueBGraphForm
open scoped Matrix

variable {n : ℕ}

abbrev Vec (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

theorem exists_coord {U : Type*} [CommGroup U] [Finite U] (hexp : ∀ u : U, u ^ 2 = 1)
    (hcard : Nat.card U = 2 ^ n) : Nonempty (U ≃* Vec n) := by
  let _ : Module (ZMod 2) (Additive U) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    have h := hexp (Additive.toMul v)
    rw [pow_two] at h
    exact congrArg Additive.ofMul h
  have _ : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
  rw [Nat.card_zmod, show Nat.card (Additive U) = 2 ^ n from hcard] at h
  have hfr : Module.finrank (ZMod 2) (Additive U) =
      Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
    rw [Module.finrank_fin_fun]
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  exact ⟨AddEquiv.toMultiplicativeRight (LinearEquiv.ofFinrankEq _ _ hfr).toAddEquiv⟩

@[expose] def vecAut (A : GL (Fin n) (ZMod 2)) : MulAut (Vec n) where
  toFun x := Multiplicative.ofAdd ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x.toAdd)
  invFun x :=
    Multiplicative.ofAdd (((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      x.toAdd)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem vecAut_apply (A : GL (Fin n) (ZMod 2)) (x : Vec n) :
    vecAut A x = Multiplicative.ofAdd ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x.toAdd) := rfl

@[expose] def vecHom : GL (Fin n) (ZMod 2) →* MulAut (Vec n) where
  toFun := vecAut
  map_one' := MulEquiv.ext fun x => by simp [vecAut_apply]
  map_mul' A B := MulEquiv.ext fun x => by simp [vecAut_apply, Matrix.mulVec_mulVec]

theorem vecAut_one : vecAut (1 : GL (Fin n) (ZMod 2)) = 1 := vecHom.map_one

theorem vecAut_mul (A B : GL (Fin n) (ZMod 2)) : vecAut (A * B) = vecAut A * vecAut B :=
  vecHom.map_mul A B

theorem vecAut_inv (A : GL (Fin n) (ZMod 2)) : vecAut A⁻¹ = (vecAut A)⁻¹ := vecHom.map_inv A

theorem vecAut_mul_apply (A B : GL (Fin n) (ZMod 2)) (x : Vec n) :
    vecAut (A * B) x = vecAut A (vecAut B x) := by
  rw [vecAut_mul, MulAut.mul_apply]

theorem vecHom_injective : Function.Injective (vecHom (n := n)) := by
  intro A B h
  apply Units.ext
  apply matrix_ext_mulVec
  intro x
  have := congrArg (fun f : MulAut (Vec n) => (f (Multiplicative.ofAdd x)).toAdd) h
  simpa [vecHom, vecAut_apply] using this

@[expose] def addOfAut (f : MulAut (Vec n)) : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) where
  toFun x := (f (Multiplicative.ofAdd x)).toAdd
  map_zero' := by simp
  map_add' x y := by simp [ofAdd_add]

theorem addOfAut_apply (f : MulAut (Vec n)) (x : Fin n → ZMod 2) :
    addOfAut f x = (f (Multiplicative.ofAdd x)).toAdd := rfl

theorem vecHom_surjective : Function.Surjective (vecHom (n := n)) := by
  intro f
  have key : ∀ g h : MulAut (Vec n), g * h = 1 →
      matOf (addOfAut g) * matOf (addOfAut h) = 1 := fun g h hgh =>
    matrix_ext_mulVec fun x => by
      rw [← Matrix.mulVec_mulVec, matOf_mulVec, matOf_mulVec, Matrix.one_mulVec, addOfAut_apply,
        addOfAut_apply, ofAdd_toAdd, ← MulAut.mul_apply, hgh, MulAut.one_apply, toAdd_ofAdd]
  refine ⟨⟨matOf (addOfAut f), matOf (addOfAut f⁻¹), key _ _ (mul_inv_cancel f),
    key _ _ (inv_mul_cancel f)⟩, MulEquiv.ext fun x => ?_⟩
  show Multiplicative.ofAdd (matOf (addOfAut f) *ᵥ x.toAdd) = f x
  rw [matOf_mulVec, addOfAut_apply, ofAdd_toAdd, ofAdd_toAdd]

@[expose] noncomputable def vecEquiv : GL (Fin n) (ZMod 2) ≃* MulAut (Vec n) :=
  MulEquiv.ofBijective vecHom ⟨vecHom_injective, vecHom_surjective⟩

theorem vecEquiv_apply (A : GL (Fin n) (ZMod 2)) : vecEquiv A = vecAut A := rfl

theorem vecAut_symm (f : MulAut (Vec n)) : vecAut (vecEquiv.symm f) = f :=
  vecEquiv.apply_symm_apply f

theorem eq_one_of_forall_commute_mulAut {S : Type*} [Group S]
    (hS : ∀ z : S, (∀ g, z * g = g * z) → z = 1) {β : MulAut S}
    (h : ∀ α : MulAut S, β * α = α * β) : β = 1 := by
  ext s
  have key : ∀ y, β (s * y * s⁻¹) = s * β y * s⁻¹ := fun y => by
    have := congrArg (fun f : MulAut S => f y) (h (MulAut.conj s))
    simpa [MulAut.mul_apply, MulAut.conj_apply] using this
  have hz : ∀ g, (s⁻¹ * β s) * g = g * (s⁻¹ * β s) := by
    intro g
    obtain ⟨y, rfl⟩ := β.surjective g
    have h1 := key y
    rw [map_mul, map_mul, map_inv] at h1
    calc s⁻¹ * β s * β y = s⁻¹ * (β s * β y * (β s)⁻¹) * β s := by group
      _ = s⁻¹ * (s * β y * s⁻¹) * β s := by rw [h1]
      _ = β y * (s⁻¹ * β s) := by group
  have h1 := hS _ hz
  rw [MulAut.one_apply]
  calc β s = s * (s⁻¹ * β s) := by group
    _ = s := by rw [h1, mul_one]

@[expose] def resAut {W : Type} [CommGroup W] (U : Subgroup W) : ↥(stabV U) →* MulAut ↥U where
  toFun l :=
    { toFun := fun u => ⟨(l : MulAut W) u, ((l.2 : (l : MulAut W) ∈ stabV U) u).mp u.2⟩
      invFun := fun u => ⟨(l : MulAut W)⁻¹ u,
        (((stabV U).inv_mem l.2 : (l : MulAut W)⁻¹ ∈ stabV U) u).mp u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem resAut_apply {W : Type} [CommGroup W] (U : Subgroup W) (l : ↥(stabV U)) (u : ↥U) :
    ((resAut U l u : ↥U) : W) = (l : MulAut W) u := rfl

variable {W : Type} [CommGroup W] {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}

theorem mul_mem_L (hyp : H9Hyp n M L T W₁ W₂) {a b : MulAut W} (ha : a ∈ M) (hb : b ∈ M)
    (haL : a ∉ L) (hbL : b ∉ L) : a * b ∈ L := by
  have hidx : (L.subgroupOf M).index = 2 := hyp.index
  have h := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥M)) (b := ⟨b, hb⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h.mpr ⟨fun h1 => absurd h1 haL, fun h1 => absurd h1 hbL⟩

theorem conj_mem_L (hyp : H9Hyp n M L T W₁ W₂) {m : MulAut W} (hm : m ∈ M) {l : MulAut W}
    (hl : l ∈ L) : m * l * m⁻¹ ∈ L := by
  have hN : (L.subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hyp.index
  exact Subgroup.mem_subgroupOf.mp
    (hN.conj_mem ⟨l, hyp.le hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨m, hm⟩)

theorem exists_glRep (hyp : H9Hyp n M L T W₁ W₂) (e₁ : ↥W₁ ≃* Vec n) :
    ∃ φ : ↥L ≃* GL (Fin n) (ZMod 2), ∀ l : ↥L, ∀ x : Vec n,
      (l : MulAut W) (e₁.symm x : W) = (e₁.symm (vecAut (φ l) x) : W) := by
  let ψ : ↥L →* GL (Fin n) (ZMod 2) :=
    (vecEquiv.symm.toMonoidHom.comp (MulAut.congr e₁).toMonoidHom).comp
      ((resAut W₁).comp (Subgroup.inclusion hyp.inv₁))
  have hψ : ∀ l : ↥L,
      vecAut (ψ l) = MulAut.congr e₁ (resAut W₁ (Subgroup.inclusion hyp.inv₁ l)) := fun l =>
    vecAut_symm _
  have hact : ∀ l : ↥L, ∀ x,
      (l : MulAut W) (e₁.symm x : W) = (e₁.symm (vecAut (ψ l) x) : W) := by
    intro l x
    rw [hψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    apply Subtype.ext
    apply hyp.faith l l.2
    intro w hw
    have := hact l (e₁ ⟨w, hw⟩)
    rw [hl, vecAut_one, MulAut.one_apply, MulEquiv.symm_apply_apply] at this
    exact this
  have hsurj : Function.Surjective ψ := by
    intro A
    obtain ⟨l, hl, hlf⟩ := hyp.full ((MulAut.congr e₁).symm (vecAut A))
    refine ⟨⟨l, hl⟩, vecHom_injective ?_⟩
    show vecAut (ψ ⟨l, hl⟩) = vecAut A
    have hres : resAut W₁ (Subgroup.inclusion hyp.inv₁ ⟨l, hl⟩) =
        (MulAut.congr e₁).symm (vecAut A) := MulEquiv.ext fun u => Subtype.ext (hlf u)
    rw [hψ, hres, MulEquiv.apply_symm_apply]
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩, hact⟩

@[expose] def tConj (hyp : H9Hyp n M L T W₁ W₂) {t : MulAut W} (htM : t ∈ M) : ↥L ≃* ↥L where
  toFun l := ⟨t⁻¹ * l * t, by simpa using conj_mem_L hyp (M.inv_mem htM) l.2⟩
  invFun l := ⟨t * l * t⁻¹, conj_mem_L hyp htM l.2⟩
  left_inv l := Subtype.ext (by show t * (t⁻¹ * (l : MulAut W) * t) * t⁻¹ = l; group)
  right_inv l := Subtype.ext (by show t⁻¹ * (t * (l : MulAut W) * t⁻¹) * t = l; group)
  map_mul' l l' := Subtype.ext (by
    show t⁻¹ * ((l : MulAut W) * l') * t = (t⁻¹ * l * t) * (t⁻¹ * l' * t)
    group)

theorem coe_tConj (hyp : H9Hyp n M L T W₁ W₂) {t : MulAut W} (htM : t ∈ M) (l : ↥L) :
    ((tConj hyp htM l : ↥L) : MulAut W) = t⁻¹ * l * t := rfl

theorem exists_graph (hyp : H9Hyp n M L T W₁ W₂) (hn : 3 ≤ n) (φ : ↥L ≃* GL (Fin n) (ZMod 2))
    {t : MulAut W} (htM : t ∈ M) (htL : t ∉ L) :
    ∃ c : GL (Fin n) (ZMod 2), ∀ l : ↥L,
      φ (tConj hyp htM l) = c * glGraphAut n (ZMod 2) (φ l) * c⁻¹ := by
  let α : MulAut (GL (Fin n) (ZMod 2)) := φ.symm.trans ((tConj hyp htM).trans φ)
  have hα : ∀ l : ↥L, α (φ l) = φ (tConj hyp htM l) := fun l => by
    show φ (tConj hyp htM (φ.symm (φ l))) = _
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨c, hc | hc⟩ := exists_conj_or_conj_graph_GL hn α
  ·
    exfalso
    set lc := φ.symm c with hlc
    have hcomm : ∀ l : ↥L, (t * (lc : MulAut W)) * l = l * (t * lc) := by
      intro l
      have h1 : tConj hyp htM l = lc * l * lc⁻¹ := by
        apply φ.injective
        rw [← hα, hc, map_mul, map_mul, map_inv, hlc, MulEquiv.apply_symm_apply]
      have h2 : t⁻¹ * (l : MulAut W) * t = lc * l * (lc : MulAut W)⁻¹ := congrArg Subtype.val h1
      calc t * lc * l = t * (lc * l * (lc : MulAut W)⁻¹) * lc := by group
        _ = t * (t⁻¹ * l * t) * lc := by rw [h2]
        _ = l * (t * lc) := by group
    have hxM : t * (lc : MulAut W) ∈ M := M.mul_mem htM (hyp.le lc.2)
    have hxL : t * (lc : MulAut W) ∉ L := fun h => htL (by
      have := L.mul_mem h (L.inv_mem lc.2)
      rwa [mul_inv_cancel_right] at this)
    have hcent : ∀ m ∈ M, (t * (lc : MulAut W)) * m = m * (t * lc) := by
      intro m hm
      by_cases hmL : m ∈ L
      · exact hcomm ⟨m, hmL⟩
      · have h1 : (t * (lc : MulAut W))⁻¹ * m ∈ L := mul_mem_L hyp (M.inv_mem hxM) hm
          (fun h => hxL (by simpa using L.inv_mem h)) hmL
        have h2 : t * (lc : MulAut W) * ((t * lc)⁻¹ * m) = ((t * lc)⁻¹ * m) * (t * lc) :=
          hcomm ⟨_, h1⟩
        calc t * lc * m = t * lc * (t * lc * ((t * lc)⁻¹ * m)) := by group
          _ = t * lc * (((t * lc)⁻¹ * m) * (t * lc)) := by rw [h2]
          _ = m * (t * lc) := by group
    obtain ⟨ψ⟩ := hyp.aut
    have h1 : ψ ⟨t * lc, hxM⟩ = 1 :=
      eq_one_of_forall_commute_mulAut (fun z hz => eq_one_of_forall_commute_SL hz) fun α' => by
        obtain ⟨m, rfl⟩ := ψ.surjective α'
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcent m m.2)
    have h2 : (⟨t * lc, hxM⟩ : ↥M) = 1 := ψ.injective (by rw [h1, map_one])
    exact hxL (by rw [show t * (lc : MulAut W) = 1 from congrArg Subtype.val h2]; exact L.one_mem)
  · exact ⟨c, fun l => by rw [← hα, hc]⟩

theorem phi_sq (hyp : H9Hyp n M L T W₁ W₂) (φ : ↥L ≃* GL (Fin n) (ZMod 2)) {t : MulAut W}
    (htM : t ∈ M) (htL : t ∉ L) {c : GL (Fin n) (ZMod 2)}
    (hc : ∀ l : ↥L, φ (tConj hyp htM l) = c * glGraphAut n (ZMod 2) (φ l) * c⁻¹) :
    φ ⟨t * t, mul_mem_L hyp htM htM htL htL⟩ * c = glGraphAut n (ZMod 2) c⁻¹ := by
  set s : ↥L := ⟨t * t, mul_mem_L hyp htM htM htL htL⟩ with hs
  have h1 : ∀ l : ↥L, tConj hyp htM (tConj hyp htM l) = s⁻¹ * l * s := fun l => Subtype.ext (by
    show t⁻¹ * (t⁻¹ * (l : MulAut W) * t) * t = (t * t)⁻¹ * l * (t * t)
    group)
  have hz : ∀ g, (φ s * c * glGraphAut n (ZMod 2) c) * g =
      g * (φ s * c * glGraphAut n (ZMod 2) c) := by
    intro g
    obtain ⟨l, rfl⟩ := φ.surjective g
    have h2 := hc (tConj hyp htM l)
    rw [hc l, h1] at h2
    have h3 : φ (s⁻¹ * l * s) = (φ s)⁻¹ * φ l * φ s := by rw [map_mul, map_mul, map_inv]
    have h4 : glGraphAut n (ZMod 2) (c * glGraphAut n (ZMod 2) (φ l) * c⁻¹) =
        glGraphAut n (ZMod 2) c * φ l * (glGraphAut n (ZMod 2) c)⁻¹ := by
      rw [map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
    rw [h3, h4] at h2
    calc φ s * c * glGraphAut n (ZMod 2) c * φ l =
        φ s * (c * (glGraphAut n (ZMod 2) c * φ l * (glGraphAut n (ZMod 2) c)⁻¹) * c⁻¹) *
          (c * glGraphAut n (ZMod 2) c) := by group
      _ = φ s * ((φ s)⁻¹ * φ l * φ s) * (c * glGraphAut n (ZMod 2) c) := by rw [← h2]
      _ = φ l * (φ s * c * glGraphAut n (ZMod 2) c) := by group
  have hz1 := eq_one_of_forall_commute_GL hz
  calc φ s * c = φ s * c * glGraphAut n (ZMod 2) c * (glGraphAut n (ZMod 2) c)⁻¹ := by group
    _ = (glGraphAut n (ZMod 2) c)⁻¹ := by rw [hz1, one_mul]
    _ = glGraphAut n (ZMod 2) c⁻¹ := (map_inv _ c).symm

end CFSG.Quasithin.H13.H9Coord
