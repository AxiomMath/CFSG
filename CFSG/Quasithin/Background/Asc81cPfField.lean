module

public import CFSG.Quasithin.Background.Asc81cPfBasic

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W]

section Res

theorem additive_ext {U : Subgroup W} {a b : Additive U}
    (h : ((Additive.toMul a : U) : W) = ((Additive.toMul b : U) : W)) : a = b :=
  Additive.toMul.injective (Subtype.ext h)

@[expose] def resEnd (U : Subgroup W) (g : MulAut W) (hg : ∀ u ∈ U, g u ∈ U) :
    AddMonoid.End (Additive U) where
  toFun a := Additive.ofMul ⟨g (Additive.toMul a : U), hg _ (Additive.toMul a).2⟩
  map_zero' := additive_ext (by simp)
  map_add' a b := additive_ext (by simp)

end Res

section Singer

variable {G X : Subgroup (MulAut W)}

@[expose] def rho (X : Subgroup (MulAut W)) (x : X) :
    AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)) :=
  resEnd _ x fun _ hu => commSub_stable' x.2 hu

theorem rho_mul (x y : X) : rho X (x * y) = rho X x * rho X y := AddMonoidHom.ext fun _ => rfl

theorem rho_one : rho X 1 = 1 := AddMonoidHom.ext fun _ => rfl

theorem rho_comm (h : Hyp101 G X) (x y : X) : rho X x * rho X y = rho X y * rho X x := by
  rw [← rho_mul, ← rho_mul]
  congr 1
  exact Subtype.ext (mul_comm_of_isCyclic h.2.2.1 x.2 y.2)

theorem additive_add_self (hW : ∀ w : W, w ^ 2 = 1) (a : Additive (commSub (⊤ : Subgroup W) X)) :
    a + a = 0 := by
  apply additive_ext
  show ((Additive.toMul a : _) : W) * (Additive.toMul a : _) = 1
  rw [← pow_two, hW]

theorem eq_zero_or_eq_rho (h : Hyp101 G X)
    (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))
    (hf : ∀ x : X, f * rho X x = rho X x * f) : f = 0 ∨ ∃ x : X, f = rho X x := by
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one h
  let u₀ : commSub (⊤ : Subgroup W) X := ⟨w₀, hw₀⟩
  have hrep : ∀ u : commSub (⊤ : Subgroup W) X, (u : W) ≠ 1 →
      ∃ x : X, Additive.ofMul u = rho X x (Additive.ofMul u₀) := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := exists_apply_eq h hw₀ hw₀1 u.2 hu
    exact ⟨⟨x, hx⟩, additive_ext hxu.symm⟩
  have hfu : ∀ x : X, f (rho X x (Additive.ofMul u₀)) = rho X x (f (Additive.ofMul u₀)) :=
    fun x => congrArg (fun φ => φ (Additive.ofMul u₀)) (hf x)
  by_cases hf0 : ((Additive.toMul (f (Additive.ofMul u₀)) : _) : W) = 1
  · left
    have hz : f (Additive.ofMul u₀) = 0 := additive_ext hf0
    refine AddMonoidHom.ext fun a => ?_
    show f a = 0
    by_cases ha : ((Additive.toMul a : _) : W) = 1
    · have : a = 0 := additive_ext ha
      rw [this]
      exact map_zero f
    · obtain ⟨x, hx⟩ := hrep (Additive.toMul a) ha
      have ha' : a = rho X x (Additive.ofMul u₀) := hx
      rw [ha', hfu x, hz]
      exact map_zero _
  · right
    obtain ⟨x₀, hx₀, hx₀c⟩ := exists_apply_eq h hw₀ hw₀1
      (Additive.toMul (f (Additive.ofMul u₀))).2 hf0
    have hc : f (Additive.ofMul u₀) = rho X ⟨x₀, hx₀⟩ (Additive.ofMul u₀) :=
      additive_ext hx₀c.symm
    refine ⟨⟨x₀, hx₀⟩, AddMonoidHom.ext fun a => ?_⟩
    show f a = rho X ⟨x₀, hx₀⟩ a
    by_cases ha : ((Additive.toMul a : _) : W) = 1
    · have : a = 0 := additive_ext ha
      rw [this]
      exact (map_zero f).trans (map_zero _).symm
    · obtain ⟨x, hx⟩ := hrep (Additive.toMul a) ha
      have ha' : a = rho X x (Additive.ofMul u₀) := hx
      rw [ha', hfu x, hc]
      show (rho X x * rho X ⟨x₀, hx₀⟩) (Additive.ofMul u₀) =
        (rho X ⟨x₀, hx₀⟩ * rho X x) (Additive.ofMul u₀)
      rw [rho_comm h]

theorem rho_injective (h : Hyp101 G X) : Function.Injective (rho X) := by
  intro x y hxy
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one h
  have h1 : (x : MulAut W) w₀ = (y : MulAut W) w₀ :=
    congrArg (fun φ : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)) =>
      ((Additive.toMul (φ (Additive.ofMul (⟨w₀, hw₀⟩ : commSub (⊤ : Subgroup W) X))) :
        commSub (⊤ : Subgroup W) X) : W)) hxy
  have h2 : ((y : MulAut W)⁻¹ * x) w₀ = w₀ := by
    rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
  have h3 := eq_one_of_apply_eq h (X.mul_mem (X.inv_mem y.2) x.2) hw₀ hw₀1 h2
  apply Subtype.ext
  have := congrArg (fun z => (y : MulAut W) * z) h3
  simpa using this

theorem rho_ne_zero (h : Hyp101 G X) (x : X) : rho X x ≠ 0 := by
  intro h0
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one h
  have h2 : (x : MulAut W) w₀ = 1 :=
    congrArg (fun φ : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)) =>
      ((Additive.toMul (φ (Additive.ofMul (⟨w₀, hw₀⟩ : commSub (⊤ : Subgroup W) X))) :
        commSub (⊤ : Subgroup W) X) : W)) h0
  apply hw₀1
  have h3 : (x : MulAut W) w₀ = (x : MulAut W) 1 := by rw [map_one]; exact h2
  exact (x : MulAut W).injective h3

theorem comm_of_mem (h : Hyp101 G X) {c : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))}
    (hc : c = 0 ∨ ∃ x : X, c = rho X x) (x : X) : c * rho X x = rho X x * c := by
  rcases hc with rfl | ⟨y, rfl⟩
  · rw [zero_mul, mul_zero]
  · exact rho_comm h y x

@[expose] def singerRing (h : Hyp101 G X) :
    Subring (AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) where
  carrier := {f | f = 0 ∨ ∃ x : X, f = rho X x}
  mul_mem' := by
    rintro a b (rfl | ⟨x, rfl⟩) (rfl | ⟨y, rfl⟩)
    · exact Or.inl (zero_mul _)
    · exact Or.inl (zero_mul _)
    · exact Or.inl (mul_zero _)
    · exact Or.inr ⟨x * y, (rho_mul x y).symm⟩
  one_mem' := Or.inr ⟨1, rho_one.symm⟩
  add_mem' := by
    intro a b ha hb
    exact eq_zero_or_eq_rho h (a + b) fun x => by
      rw [add_mul, mul_add, comm_of_mem h ha x, comm_of_mem h hb x]
  zero_mem' := Or.inl rfl
  neg_mem' := by
    intro a ha
    refine eq_zero_or_eq_rho h (-a) fun x => AddMonoidHom.ext fun b => ?_
    have h1 : a (rho X x b) = rho X x (a b) :=
      congrArg (fun φ : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)) => φ b)
        (comm_of_mem h ha x)
    show -(a (rho X x b)) = rho X x (-(a b))
    rw [map_neg, h1]

theorem mem_singerRing (h : Hyp101 G X)
    {f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))} :
    f ∈ singerRing h ↔ f = 0 ∨ ∃ x : X, f = rho X x := Iff.rfl

theorem rho_mem (h : Hyp101 G X) (x : X) : rho X x ∈ singerRing h := Or.inr ⟨x, rfl⟩

theorem singerRing_mul_comm (h : Hyp101 G X) (a b : singerRing h) : a * b = b * a := by
  apply Subtype.ext
  show (a : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * b = b * a
  rcases (mem_singerRing h).1 a.2 with ha | ⟨x, hx⟩
  · rw [ha, zero_mul, mul_zero]
  · rw [hx]
    exact (comm_of_mem h ((mem_singerRing h).1 b.2) x).symm

theorem isField_singerRing (h : Hyp101 G X) : IsField (singerRing h) where
  exists_pair_ne := ⟨0, 1, fun h0 => rho_ne_zero h 1 (by
    rw [rho_one]
    exact (congrArg Subtype.val h0).symm)⟩
  mul_comm := singerRing_mul_comm h
  mul_inv_cancel := by
    intro a ha
    rcases (mem_singerRing h).1 a.2 with h0 | ⟨x, hx⟩
    · exact absurd (Subtype.ext h0 : a = 0) ha
    · refine ⟨⟨rho X x⁻¹, rho_mem h _⟩, Subtype.ext ?_⟩
      show (a : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * rho X x⁻¹ = 1
      rw [hx, ← rho_mul, mul_inv_cancel, rho_one]

@[expose, instance_reducible] noncomputable def singerField (h : Hyp101 G X) :
    Field (singerRing h) :=
  (isField_singerRing h).toField

theorem one_add_one_singerRing (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X) :
    (1 : singerRing h) + 1 = 0 := by
  apply Subtype.ext
  refine AddMonoidHom.ext fun a => ?_
  show a + a = 0
  exact additive_add_self hW a

theorem normalizer_stable {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    ∀ u ∈ commSub (⊤ : Subgroup W) X, y u ∈ commSub (⊤ : Subgroup W) X := by
  intro u hu
  have hX : X.map (MulAut.conj y).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hy
  have h1 := commSub_map_conj X y
  rw [hX] at h1
  rw [h1]
  exact ⟨u, hu, rfl⟩

@[expose] def resN {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)) :=
  resEnd _ y (normalizer_stable hy)

theorem resN_inv_mul {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    resN (Subgroup.inv_mem _ hy) * resN hy = 1 := by
  refine AddMonoidHom.ext fun a => additive_ext ?_
  show y⁻¹ (y ((Additive.toMul a : commSub (⊤ : Subgroup W) X) : W)) = _
  rw [MulAut.inv_apply_self]
  rfl

theorem resN_mul_inv {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    resN hy * resN (Subgroup.inv_mem _ hy) = 1 := by
  refine AddMonoidHom.ext fun a => additive_ext ?_
  show y (y⁻¹ ((Additive.toMul a : commSub (⊤ : Subgroup W) X) : W)) = _
  rw [MulAut.apply_inv_self]
  rfl

theorem conj_mem {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) (x : X) :
    y * (x : MulAut W) * y⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.1 hy x).1 x.2

theorem resN_conj_rho {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (x : X) : resN hy * rho X x * resN (Subgroup.inv_mem _ hy) = rho X ⟨_, conj_mem hy x⟩ :=
  AddMonoidHom.ext fun _ => rfl

theorem resN_conj_rho' {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (x : X) : resN (Subgroup.inv_mem _ hy) * rho X x * resN hy =
      rho X ⟨y⁻¹ * (x : MulAut W) * y, by simpa using conj_mem (Subgroup.inv_mem _ hy) x⟩ :=
  AddMonoidHom.ext fun _ => rfl

@[expose] def conjRingEquiv (h : Hyp101 G X) {y : MulAut W}
    (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) : singerRing h ≃+* singerRing h where
  toFun f := ⟨resN hy * (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
      resN (Subgroup.inv_mem _ hy), by
    rcases (mem_singerRing h).1 f.2 with hf | ⟨x, hx⟩
    · rw [hf, mul_zero, zero_mul]
      exact (singerRing h).zero_mem
    · rw [hx, resN_conj_rho]
      exact rho_mem h _⟩
  invFun f := ⟨resN (Subgroup.inv_mem _ hy) *
      (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * resN hy, by
    rcases (mem_singerRing h).1 f.2 with hf | ⟨x, hx⟩
    · rw [hf, mul_zero, zero_mul]
      exact (singerRing h).zero_mem
    · rw [hx, resN_conj_rho']
      exact rho_mem h _⟩
  left_inv f := by
    apply Subtype.ext
    show resN (Subgroup.inv_mem _ hy) * (resN hy *
      (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
        resN (Subgroup.inv_mem _ hy)) * resN hy = f
    rw [← mul_assoc, ← mul_assoc, resN_inv_mul, one_mul, mul_assoc, resN_inv_mul, mul_one]
  right_inv f := by
    apply Subtype.ext
    show resN hy * (resN (Subgroup.inv_mem _ hy) *
      (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * resN hy) *
        resN (Subgroup.inv_mem _ hy) = f
    rw [← mul_assoc, ← mul_assoc, resN_mul_inv, one_mul, mul_assoc, resN_mul_inv, mul_one]
  map_mul' f g := by
    apply Subtype.ext
    show resN hy * ((f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * g) *
        resN (Subgroup.inv_mem _ hy) =
      resN hy * f * resN (Subgroup.inv_mem _ hy) * (resN hy * g * resN (Subgroup.inv_mem _ hy))
    calc resN hy * ((f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) * g) *
          resN (Subgroup.inv_mem _ hy)
        = resN hy * (f * (g * resN (Subgroup.inv_mem _ hy))) := by simp only [mul_assoc]
      _ = resN hy * (f * ((resN (Subgroup.inv_mem _ hy) * resN hy) *
            (g * resN (Subgroup.inv_mem _ hy)))) := by rw [resN_inv_mul, one_mul]
      _ = _ := by simp only [mul_assoc]
  map_add' f g := by
    apply Subtype.ext
    show resN hy * ((f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) + g) *
        resN (Subgroup.inv_mem _ hy) =
      resN hy * f * resN (Subgroup.inv_mem _ hy) + resN hy * g * resN (Subgroup.inv_mem _ hy)
    rw [mul_add, add_mul]

theorem conjRingEquiv_apply (h : Hyp101 G X) {y : MulAut W}
    (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) (f : singerRing h) :
    ((conjRingEquiv h hy f : singerRing h) : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))
      = resN hy * f * resN (Subgroup.inv_mem _ hy) := rfl

theorem conjRingEquiv_rho (h : Hyp101 G X) {y : MulAut W}
    (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) (x : X) :
    conjRingEquiv h hy ⟨rho X x, rho_mem h x⟩ = ⟨rho X ⟨_, conj_mem hy x⟩, rho_mem h _⟩ :=
  Subtype.ext ((conjRingEquiv_apply h hy _).trans (resN_conj_rho hy x))

theorem resN_eq_one {y : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (h1 : y = 1) : resN hy = 1 := by
  subst h1
  exact AddMonoidHom.ext fun _ => rfl

theorem resN_mul' {y y' : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hy' : y' ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hyy : y * y' ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    resN hyy = resN hy * resN hy' :=
  AddMonoidHom.ext fun _ => rfl

theorem resN_mul_inv' {y y' : MulAut W} (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hy' : y' ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hyy : (y * y')⁻¹ ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    resN hyy = resN (Subgroup.inv_mem _ hy') * resN (Subgroup.inv_mem _ hy) :=
  AddMonoidHom.ext fun _ => rfl

variable [Finite W]

theorem finite_mulAut : Finite (MulAut W) :=
  Finite.of_injective (fun e : MulAut W => (e : W → W)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem finite_singerRing (h : Hyp101 G X) : Finite (singerRing h) := by
  have : Finite (AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) :=
    FunLike.finite (AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))
  infer_instance

theorem card_singerRing (h : Hyp101 G X) :
    Nat.card (singerRing h) = Nat.card (commSub (⊤ : Subgroup W) X) := by
  have := finite_mulAut (W := W)
  rw [card_commSub h, ← Finite.card_option]
  let e : Option X → singerRing h := fun o => o.elim 0 fun x => ⟨rho X x, rho_mem h x⟩
  have he : Function.Bijective e := by
    constructor
    · rintro (_ | x) (_ | y) hxy
      · rfl
      · exact absurd (congrArg Subtype.val hxy).symm (rho_ne_zero h y)
      · exact absurd (congrArg Subtype.val hxy) (rho_ne_zero h x)
      · exact congrArg some (rho_injective h (congrArg Subtype.val hxy))
    · rintro ⟨f, hf⟩
      rcases (mem_singerRing h).1 hf with hf0 | ⟨x, hx⟩
      · exact ⟨none, Subtype.ext hf0.symm⟩
      · exact ⟨some x, Subtype.ext hx.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective e he)).symm

theorem card_dvd_rk (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X) {Y : Subgroup (MulAut W)}
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hYC : ∀ y ∈ Y, (∀ x ∈ X, y * x = x * y) → y = 1) :
    Nat.card Y ∣ rk (commSub (⊤ : Subgroup W) X) := by
  let _ : Field (singerRing h) := singerField h
  have : Finite (singerRing h) := finite_singerRing h
  have h12 : (2 : singerRing h) = 0 := by
    rw [← one_add_one_eq_two]
    exact one_add_one_singerRing hW h
  have : CharP (singerRing h) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h12
  let _ : Algebra (ZMod 2) (singerRing h) := ZMod.algebra (singerRing h) 2
  have hcomm : ∀ (y : MulAut W) (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
      (r : ZMod 2), conjRingEquiv h hy (algebraMap (ZMod 2) (singerRing h) r) =
        algebraMap (ZMod 2) (singerRing h) r := by
    intro y hy r
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.val, (ZMod.natCast_zmod_val r).symm⟩
    rw [map_natCast]
    exact map_natCast (conjRingEquiv h hy) n
  let σ : Y → Gal(singerRing h/ZMod 2) := fun y => AlgEquiv.ofRingEquiv (hcomm y (hYN y.2))
  let φ : Y →* Gal(singerRing h/ZMod 2) :=
    { toFun := σ
      map_one' := AlgEquiv.ext fun f => Subtype.ext (by
        show resN (hYN (1 : Y).2) * (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
          resN (Subgroup.inv_mem _ (hYN (1 : Y).2)) = f
        rw [resN_eq_one _ rfl, resN_eq_one _ inv_one, one_mul, mul_one])
      map_mul' := fun y y' => AlgEquiv.ext fun f => Subtype.ext (by
        show resN (hYN (y * y').2) * (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
          resN (Subgroup.inv_mem _ (hYN (y * y').2)) =
            resN (hYN y.2) * (resN (hYN y'.2) * f * resN (Subgroup.inv_mem _ (hYN y'.2))) *
              resN (Subgroup.inv_mem _ (hYN y.2))
        rw [resN_mul' (hYN y.2) (hYN y'.2), resN_mul_inv' (hYN y.2) (hYN y'.2)]
        simp only [mul_assoc]) }
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun y hy => ?_
    have hyc : ∀ x ∈ X, (y : MulAut W) * x = x * y := by
      intro x hx
      have h1 := DFunLike.congr_fun hy ⟨rho X ⟨x, hx⟩, rho_mem h _⟩
      have h2 : conjRingEquiv h (hYN y.2) ⟨rho X ⟨x, hx⟩, rho_mem h _⟩ =
          ⟨rho X ⟨x, hx⟩, rho_mem h _⟩ := h1
      rw [conjRingEquiv_rho] at h2
      have h3 : (y : MulAut W) * x * (y : MulAut W)⁻¹ = x :=
        congrArg Subtype.val (rho_injective h (congrArg Subtype.val h2))
      have h4 : (y : MulAut W) * x * (y : MulAut W)⁻¹ * y = x * y := by rw [h3]
      rwa [inv_mul_cancel_right] at h4
    exact Subtype.ext (hYC y y.2 hyc)
  have h1 := Subgroup.card_dvd_of_injective φ hinj
  rw [IsGalois.card_aut_eq_finrank] at h1
  have h2 : Nat.card (singerRing h) = 2 ^ Module.finrank (ZMod 2) (singerRing h) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 : Nat.card (singerRing h) = 2 ^ rk (commSub (⊤ : Subgroup W) X) := by
    rw [card_singerRing h, card_eq_two_pow hW]
  rwa [Nat.pow_right_injective (le_refl 2) (h2.symm.trans h3)] at h1

theorem sq_card_centralizer_le (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X) {y : MulAut W}
    (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W))) (hyX : ∃ x ∈ X, y * x ≠ x * y) :
    (Nat.card ↥(X ⊓ Subgroup.centralizer {y}) + 1) ^ 2 ≤
      Nat.card (commSub (⊤ : Subgroup W) X) := by
  let _ : Field (singerRing h) := singerField h
  have : Finite (singerRing h) := finite_singerRing h
  have h12 : (2 : singerRing h) = 0 := by
    rw [← one_add_one_eq_two]
    exact one_add_one_singerRing hW h
  have : CharP (singerRing h) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h12
  let _ : Algebra (ZMod 2) (singerRing h) := ZMod.algebra (singerRing h) 2
  have hcomm : ∀ r : ZMod 2, conjRingEquiv h hy (algebraMap (ZMod 2) (singerRing h) r) =
      algebraMap (ZMod 2) (singerRing h) r := by
    intro r
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.val, (ZMod.natCast_zmod_val r).symm⟩
    rw [map_natCast]
    exact map_natCast (conjRingEquiv h hy) n
  let σ : Gal(singerRing h/ZMod 2) := AlgEquiv.ofRingEquiv hcomm
  have hσx : ∀ x : X, σ ⟨rho X x, rho_mem h x⟩ = ⟨rho X x, rho_mem h x⟩ ↔
      y * (x : MulAut W) = x * y := by
    intro x
    have e1 : σ ⟨rho X x, rho_mem h x⟩ = ⟨rho X ⟨_, conj_mem hy x⟩, rho_mem h _⟩ :=
      conjRingEquiv_rho h hy x
    rw [e1]
    constructor
    · intro h2
      have h3 : y * (x : MulAut W) * y⁻¹ = x :=
        congrArg Subtype.val (rho_injective h (congrArg Subtype.val h2))
      calc y * (x : MulAut W) = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [h3]
    · intro h2
      have h3 : y * (x : MulAut W) * y⁻¹ = x := by rw [h2, mul_inv_cancel_right]
      exact Subtype.ext (congrArg (rho X) (Subtype.ext h3))
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hx, hyx⟩ := hyX
    intro h1
    apply hyx
    refine (hσx ⟨x, hx⟩).1 ?_
    rw [h1]
    rfl
  let K := IntermediateField.fixedField (Subgroup.zpowers σ)
  have hmemK : ∀ f : singerRing h, f ∈ K ↔ σ f = f := by
    intro f
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro hf
      exact hf σ (Subgroup.mem_zpowers σ)
    · intro hf τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer Gal(singerRing h/ZMod 2) f := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact hf
      have h1 := hle hτ
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h1
  have hfin : Module.finrank K (singerRing h) = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have hord : 2 ≤ orderOf σ := by
    have h1 : 0 < orderOf σ := orderOf_pos σ
    have h2 : orderOf σ ≠ 1 := fun h0 => hσ1 (orderOf_eq_one_iff.1 h0)
    omega
  have hcardF : Nat.card (singerRing h) = Nat.card K ^ Module.finrank K (singerRing h) :=
    Module.natCard_eq_pow_finrank
  have hcen : ∀ x : ↥(X ⊓ Subgroup.centralizer {y}), y * (x : MulAut W) = x * y := fun x =>
    Subgroup.mem_centralizer_iff.1 x.2.2 y (Set.mem_singleton y)
  have hcardK : Nat.card K = Nat.card ↥(X ⊓ Subgroup.centralizer {y}) + 1 := by
    have := finite_mulAut (W := W)
    rw [← Finite.card_option]
    let e : Option ↥(X ⊓ Subgroup.centralizer {y}) → K := fun o => o.elim 0 fun x =>
      ⟨⟨rho X ⟨x, x.2.1⟩, rho_mem h _⟩, (hmemK _).2 ((hσx ⟨x, x.2.1⟩).2 (hcen x))⟩
    have he : Function.Bijective e := by
      constructor
      · rintro (_ | x) (_ | x') hxx
        · rfl
        · exact absurd (congrArg (fun k : K => ((k : singerRing h) :
            AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))) hxx).symm
            (rho_ne_zero h _)
        · exact absurd (congrArg (fun k : K => ((k : singerRing h) :
            AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))) hxx) (rho_ne_zero h _)
        · have h1 := rho_injective h (congrArg (fun k : K => ((k : singerRing h) :
            AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X)))) hxx)
          exact congrArg some (Subtype.ext (congrArg Subtype.val h1 :))
      · rintro ⟨f, hf⟩
        rcases (mem_singerRing h).1 f.2 with hf0 | ⟨x, hx⟩
        · exact ⟨none, Subtype.ext (Subtype.ext hf0.symm)⟩
        · have hfx : f = ⟨rho X x, rho_mem h x⟩ := Subtype.ext hx
          have hyx : y * (x : MulAut W) = x * y := (hσx x).1 (hfx ▸ (hmemK f).1 hf)
          have hxc : (x : MulAut W) ∈ X ⊓ Subgroup.centralizer {y} := by
            refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
            rw [Set.mem_singleton_iff.1 hg]
            exact hyx
          exact ⟨some ⟨x, hxc⟩, Subtype.ext (Subtype.ext hx.symm)⟩
    exact (Nat.card_congr (Equiv.ofBijective e he)).symm
  calc (Nat.card ↥(X ⊓ Subgroup.centralizer {y}) + 1) ^ 2 = Nat.card K ^ 2 := by rw [hcardK]
    _ ≤ Nat.card K ^ orderOf σ := Nat.pow_le_pow_right Nat.card_pos hord
    _ = Nat.card (singerRing h) := by rw [hcardF, hfin]
    _ = Nat.card (commSub (⊤ : Subgroup W) X) := card_singerRing h

end Singer

end Pf

end Asc81c

end CFSG.Quasithin
