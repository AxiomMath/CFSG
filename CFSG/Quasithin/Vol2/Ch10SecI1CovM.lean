module

public import CFSG.Quasithin.Vol2.Ch10SecI1Cov
public import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.Quasithin.Background.B4ModelsApi

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {D : FFModel}

section Rep

variable (hA : D.IsActionModel)

include hA in
theorem act_map_one' (γ : D.Gam) : D.act γ 1 = 1 := by
  have h := hA.act_mul γ 1 1
  rw [mul_one] at h
  exact left_eq_mul.mp h

@[expose] def secHom (γ : D.Gam) : ↥D.sec →* ↥D.sec where
  toFun m := ⟨D.act γ m, hA.sec_inv γ m m.2⟩
  map_one' := Subtype.ext (act_map_one' hA γ)
  map_mul' m m' := Subtype.ext (hA.act_mul γ m m')

@[expose] def secAct (γ : D.Gam) : D.Sec →* D.Sec :=
  QuotientGroup.map _ _ (secHom hA γ) fun m hm => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hA.ker_inv γ m (Subgroup.mem_subgroupOf.mp hm)

theorem secAct_mk (γ : D.Gam) (m : ↥D.sec) :
    secAct hA γ (QuotientGroup.mk m) = QuotientGroup.mk ⟨D.act γ m, hA.sec_inv γ m m.2⟩ :=
  rfl

variable [Module (ZMod 2) (Additive D.Sec)]

@[expose] def secRep : Representation (ZMod 2) D.Gam (Additive D.Sec) where
  toFun γ := (MonoidHom.toAdditive (secAct hA γ)).toZModLinearMap 2
  map_one' := LinearMap.ext fun w => by
    induction w using Additive.rec with | _ q => ?_
    induction q using QuotientGroup.induction_on with | H m => ?_
    change Additive.ofMul (secAct hA 1 (QuotientGroup.mk m)) = Additive.ofMul (QuotientGroup.mk m)
    rw [secAct_mk]
    congr 2
    exact Subtype.ext (hA.act_one m)
  map_mul' γ δ := LinearMap.ext fun w => by
    induction w using Additive.rec with | _ q => ?_
    induction q using QuotientGroup.induction_on with | H m => ?_
    change Additive.ofMul (secAct hA (γ * δ) (QuotientGroup.mk m)) =
      Additive.ofMul (secAct hA γ (secAct hA δ (QuotientGroup.mk m)))
    rw [secAct_mk, secAct_mk, secAct_mk]
    congr 2
    exact Subtype.ext (hA.act_mul_act γ δ m)

theorem secRep_mk (γ : D.Gam) (m : ↥D.sec) :
    secRep hA γ (Additive.ofMul (QuotientGroup.mk m)) =
      Additive.ofMul (QuotientGroup.mk ⟨D.act γ m, hA.sec_inv γ m m.2⟩ : D.Sec) :=
  rfl

theorem secRep_isModel (hks : D.ker ≤ D.sec) : D.IsModel (secRep hA) := by
  refine ⟨MulEquiv.refl _, AddEquiv.refl _, hks, hA.sec_inv, hA.ker_inv, fun γ w m hm hw => ?_⟩
  change w = Additive.ofMul (QuotientGroup.mk m) at hw
  subst hw
  exact secRep_mk hA γ m

end Rep

section SecForm

structure SecPairing (D : FFModel) (b : D.Amb → D.Amb → ZMod 2) : Prop where
  add_left : ∀ x y z, b (x * y) z = b x z + b y z
  add_right : ∀ x y z, b x (y * z) = b x y + b x z
  ker_left : ∀ k ∈ D.ker, ∀ y ∈ D.sec, b k y = 0
  ker_right : ∀ x ∈ D.sec, ∀ k ∈ D.ker, b x k = 0

variable {b : D.Amb → D.Amb → ZMod 2} (hb : SecPairing D b)

include hb in
theorem SecPairing.mk_out (x y : ↥D.sec) :
    b ((QuotientGroup.mk x : D.Sec).out : D.Amb) ((QuotientGroup.mk y : D.Sec).out : D.Amb) =
      b x y := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (D.ker.subgroupOf D.sec) x
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (D.ker.subgroupOf D.sec) y
  have hk : ((h : ↥D.sec) : D.Amb) ∈ D.ker := Subgroup.mem_subgroupOf.mp h.2
  have hk' : ((h' : ↥D.sec) : D.Amb) ∈ D.ker := Subgroup.mem_subgroupOf.mp h'.2
  rw [hh, hh', Subgroup.coe_mul, Subgroup.coe_mul, hb.add_left, hb.add_right, hb.add_right,
    hb.ker_left _ hk _ (h' : ↥D.sec).2, hb.ker_left _ hk _ y.2, hb.ker_right _ x.2 _ hk']
  simp

@[expose] def secVal (q q' : Additive D.Sec) : ZMod 2 :=
  b ((Additive.toMul q).out : D.Amb) ((Additive.toMul q').out : D.Amb)

include hb in
theorem secVal_mk (x y : ↥D.sec) :
    secVal (b := b) (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      b x y :=
  hb.mk_out x y

include hb in
theorem secVal_add_left (q₁ q₂ q : Additive D.Sec) :
    secVal (b := b) (q₁ + q₂) q = secVal (b := b) q₁ q + secVal (b := b) q₂ q := by
  induction q₁ using Additive.rec with | _ q₁ => ?_
  induction q₂ using Additive.rec with | _ q₂ => ?_
  induction q using Additive.rec with | _ q => ?_
  induction q₁ using QuotientGroup.induction_on with | H x₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | H x₂ => ?_
  induction q using QuotientGroup.induction_on with | H x => ?_
  rw [← ofMul_mul, ← QuotientGroup.mk_mul, secVal_mk hb, secVal_mk hb, secVal_mk hb,
    Subgroup.coe_mul, hb.add_left]

include hb in
theorem secVal_add_right (q q₁ q₂ : Additive D.Sec) :
    secVal (b := b) q (q₁ + q₂) = secVal (b := b) q q₁ + secVal (b := b) q q₂ := by
  induction q₁ using Additive.rec with | _ q₁ => ?_
  induction q₂ using Additive.rec with | _ q₂ => ?_
  induction q using Additive.rec with | _ q => ?_
  induction q₁ using QuotientGroup.induction_on with | H x₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | H x₂ => ?_
  induction q using QuotientGroup.induction_on with | H x => ?_
  rw [← ofMul_mul, ← QuotientGroup.mk_mul, secVal_mk hb, secVal_mk hb, secVal_mk hb,
    Subgroup.coe_mul, hb.add_right]

variable [Module (ZMod 2) (Additive D.Sec)]

theorem zmod2_smul_eq {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (c : ZMod 2) (x : N) :
    c • x = if c = 0 then 0 else x := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · simp
  · simp

@[expose] def secForm : LinearMap.BilinForm (ZMod 2) (Additive D.Sec) :=
  LinearMap.mk₂ (ZMod 2) (secVal (b := b)) (secVal_add_left hb)
    (fun c q q' => by
      have h0 : secVal (b := b) 0 q' = 0 := by
        have := secVal_add_left hb 0 0 q'
        rw [add_zero] at this
        exact left_eq_add.mp this
      simp only [zmod2_smul_eq]
      split_ifs <;> simp [h0])
    (secVal_add_right hb)
    (fun c q q' => by
      have h0 : secVal (b := b) q 0 = 0 := by
        have := secVal_add_right hb q 0 0
        rw [add_zero] at this
        exact left_eq_add.mp this
      simp only [zmod2_smul_eq]
      split_ifs <;> simp [h0])

theorem secForm_mk (x y : ↥D.sec) :
    secForm hb (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      b x y :=
  secVal_mk hb x y

end SecForm

section Cover

variable {W : Type} [CommGroup W] [Finite W]

theorem cover_card_le_of_form (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤) [Finite D.Gam]
    (hR : D.Realizes Gm ⊤ Z) (hA : D.IsActionModel) (hD2 : ∀ x : D.Sec, x ^ 2 = 1)
    {b : D.Amb → D.Amb → ZMod 2} (hb : SecPairing D b)
    (hbnd : ∀ x ∈ D.sec, (∀ y ∈ D.sec, b x y = 0) → x ∈ D.ker)
    (hbi : ∀ γ, ∀ x ∈ D.sec, ∀ y ∈ D.sec, b (D.act γ x) (D.act γ y) = b x y) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) D.Gam M), D.IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d := by
  have hks : D.ker ≤ D.sec := hR.choose_spec.2.2.1
  obtain ⟨C, π, -, -, hCk⟩ := H13.VolI.ModelCover.exists_of_realizes hZ hcomm hR
  have h2 : ∀ x : Additive D.Sec, 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hD2, ofMul_one]
  let _ : Module (ZMod 2) (Additive D.Sec) := AddCommGroup.zmodModule h2
  have : Finite (Additive D.Sec) := Finite.of_surjective _ C.surj
  let ρ := secRep hA
  let β : W →* Multiplicative (Additive D.Sec) := C.β
  have hβe : ∀ γ v, Multiplicative.toAdd (β (C.ρ γ v)) = ρ γ (Multiplicative.toAdd (β v)) := by
    intro γ v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (C.β v)
    have h1 := C.equiv γ v m (hA.sec_inv γ m m.2) hm.symm
    change Additive.ofMul (C.β (C.ρ γ v)) = ρ γ (Additive.ofMul (C.β v))
    rw [h1, ← hm]
    rfl
  have hB : (secForm hb).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun q hq => ?_
    induction q using Additive.rec with | _ q => ?_
    induction q using QuotientGroup.induction_on with | H x => ?_
    have hx : (x : D.Amb) ∈ D.ker := hbnd x x.2 fun y hy => by
      have h1 := hq (Additive.ofMul (QuotientGroup.mk ⟨y, hy⟩))
      rwa [secForm_mk] at h1
    have h1 : (QuotientGroup.mk x : D.Sec) = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1]
    rfl
  have hBi : ∀ γ x y, secForm hb (ρ γ x) (ρ γ y) = secForm hb x y := by
    intro γ x y
    induction x using Additive.rec with | _ x => ?_
    induction y using Additive.rec with | _ y => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [secRep_mk, secRep_mk, secForm_mk, secForm_mk]
    exact hbi γ x x.2 y y.2
  have hle := card_le_card_H1_of_form hW2 C.ρ Z
    (fun γ z hz => C.fix γ z ((hCk z).2 hz)) C.gen ρ β C.surj hCk hβe (secForm hb) hB hBi
  have hcard : Nat.card (H1 ρ) ≤ 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) (hH1 ρ (secRep_isModel hA hks))
  exact hle.trans hcard

end Cover

end CFSG.Quasithin.ASInputs.C10KH
