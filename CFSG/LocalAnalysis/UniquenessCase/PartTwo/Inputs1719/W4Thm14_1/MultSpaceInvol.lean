module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceSemisimple
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private structure ComplDecomp (C D : Subgroup W) (x : W) where
  c : W
  d : W
  hc : c ∈ C
  hd : d ∈ D
  hx : c * d = x

private noncomputable def complDecomp (C D : Subgroup W) (hsup : C ⊔ D = ⊤) (x : W) :
    ComplDecomp C D x :=
  let hx : x ∈ C ⊔ D := hsup ▸ Subgroup.mem_top x
  let e := Subgroup.mem_sup.mp hx
  { c := e.choose
    d := e.choose_spec.2.choose
    hc := e.choose_spec.1
    hd := e.choose_spec.2.choose_spec.1
    hx := e.choose_spec.2.choose_spec.2 }

private theorem eq_of_mul_eq_mul_of_inf_eq_bot {C D : Subgroup W} (hCD : C ⊓ D = ⊥)
    {c c' d d' : W} (hc : c ∈ C) (hc' : c' ∈ C) (hd : d ∈ D) (hd' : d' ∈ D)
    (h : c * d = c' * d') : c = c' ∧ d = d' := by
  have h1 : c'⁻¹ * c = d' * d⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : c'⁻¹ * c ∈ C ⊓ D :=
    ⟨C.mul_mem (C.inv_mem hc') hc, h1 ▸ D.mul_mem hd' (D.inv_mem hd)⟩
  rw [hCD, Subgroup.mem_bot, inv_mul_eq_one] at h2
  refine ⟨h2.symm, ?_⟩
  rw [h2] at h
  exact mul_left_cancel h

private noncomputable def projD (C D : Subgroup W) (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = ⊤) :
    W →* ↥D where
  toFun x := ⟨(complDecomp C D hsup x).d, (complDecomp C D hsup x).hd⟩
  map_one' := by
    apply Subtype.ext
    have h := (complDecomp C D hsup 1).hx
    exact (eq_of_mul_eq_mul_of_inf_eq_bot hCD (complDecomp C D hsup 1).hc
      (Subgroup.one_mem C) (complDecomp C D hsup 1).hd (Subgroup.one_mem D)
      (by simpa using h)).2
  map_mul' x y := by
    apply Subtype.ext
    have hx := (complDecomp C D hsup x).hx
    have hy := (complDecomp C D hsup y).hx
    have hxy := (complDecomp C D hsup (x * y)).hx
    have hprod : (complDecomp C D hsup x).c * (complDecomp C D hsup y).c *
        ((complDecomp C D hsup x).d * (complDecomp C D hsup y).d) = x * y := by
      calc (complDecomp C D hsup x).c * (complDecomp C D hsup y).c *
            ((complDecomp C D hsup x).d * (complDecomp C D hsup y).d)
          = ((complDecomp C D hsup x).c * (complDecomp C D hsup x).d) *
            ((complDecomp C D hsup y).c * (complDecomp C D hsup y).d) := by ac_rfl
        _ = x * y := by rw [hx, hy]
    exact (eq_of_mul_eq_mul_of_inf_eq_bot hCD (complDecomp C D hsup (x * y)).hc
      (C.mul_mem (complDecomp C D hsup x).hc (complDecomp C D hsup y).hc)
      (complDecomp C D hsup (x * y)).hd
      (D.mul_mem (complDecomp C D hsup x).hd (complDecomp C D hsup y).hd)
      (hxy.trans hprod.symm)).2

private theorem coe_projD (C D : Subgroup W) (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = ⊤) (x : W) :
    ((projD C D hCD hsup x : ↥D) : W) = (complDecomp C D hsup x).d := rfl

private theorem mul_inv_mem_fixV_zpowers_of_sq (hW : ∀ w : W, w ^ 2 = 1) {b : MulAut W}
    (hb2 : b ^ 2 = 1) (d : W) : b d * d⁻¹ ∈ fixV (Subgroup.zpowers b) := by
  rw [mem_fixV_zpowers_iff_apply]
  have hbb : b (b d) = d := by
    have h : b * b = 1 := by rw [← pow_two, hb2]
    calc b (b d) = (b * b) d := (MulAut.mul_apply W b b d).symm
      _ = d := by rw [h]; rfl
  have hd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hW d)
  have hB : (b d)⁻¹ = b d :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hW (b d))
  calc b (b d * d⁻¹) = b (b d) * b (d⁻¹) := map_mul b _ _
    _ = d * (b d)⁻¹ := by rw [hbb, map_inv]
    _ = b d * d⁻¹ := by rw [hd, hB, mul_comm]

private theorem apply_eq_self_complDecomp_d_of_mem_fixV_zpowers_mul {C D : Subgroup W}
    (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = ⊤) {a b : MulAut W}
    (hbc : ∀ c ∈ C, b c = c) (hCX : StableUnder (Subgroup.zpowers a) C)
    (hDX : StableUnder (Subgroup.zpowers a) D) (hstep : ∀ d : W, b d * d⁻¹ ∈ C)
    {x : W} (hx : x ∈ fixV (Subgroup.zpowers (a * b))) :
    a (complDecomp C D hsup x).d = (complDecomp C D hsup x).d := by
  let p := complDecomp C D hsup x
  have hpC : p.c ∈ C := p.hc
  have hpD : p.d ∈ D := p.hd
  have hpx : p.c * p.d = x := p.hx
  have hbcp : b p.c = p.c := hbc p.c hpC
  have hstepd : b p.d * p.d⁻¹ ∈ C := hstep p.d
  have hCmul : p.c * (b p.d * p.d⁻¹) ∈ C := C.mul_mem hpC hstepd
  have hbx : b x = p.c * (b p.d * p.d⁻¹) * p.d := by
    calc b x = b (p.c * p.d) := congrArg b hpx.symm
      _ = b p.c * b p.d := map_mul b _ _
      _ = p.c * b p.d := by rw [hbcp]
      _ = p.c * (b p.d * p.d⁻¹) * p.d := by rw [mul_assoc, inv_mul_cancel_right]
  have hxF : a (b x) = x := by
    simpa only [MulAut.mul_apply W] using mem_fixV_zpowers_iff_apply.mp hx
  have haC : a (p.c * (b p.d * p.d⁻¹)) ∈ C :=
    hCX a (Subgroup.mem_zpowers a) _ hCmul
  have haD : a p.d ∈ D := hDX a (Subgroup.mem_zpowers a) _ hpD
  have heq : p.c * p.d = (a (p.c * (b p.d * p.d⁻¹))) * (a p.d) := by
    calc p.c * p.d = x := hpx
      _ = a (b x) := hxF.symm
      _ = a (p.c * (b p.d * p.d⁻¹) * p.d) := by rw [hbx]
      _ = a (p.c * (b p.d * p.d⁻¹)) * a p.d := map_mul a _ _
  exact (eq_of_mul_eq_mul_of_inf_eq_bot hCD hpC haC hpD haD heq).2.symm

private theorem mem_inf_fixV_zpowers_of_projD_eq_one {C D : Subgroup W}
    (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = ⊤) {a b : MulAut W}
    (hbc : ∀ c ∈ C, b c = c) {x : W} (hxF : x ∈ fixV (Subgroup.zpowers (a * b)))
    (hx1 : projD C D hCD hsup x = 1) : x ∈ C ⊓ fixV (Subgroup.zpowers a) := by
  let p := complDecomp C D hsup x
  have hd1 : p.d = 1 := by
    have h := congrArg (fun z : ↥D => (z : W)) hx1
    rw [coe_projD] at h
    simpa using h
  have hx_eq : x = p.c := by
    have h : p.c * p.d = x := p.hx
    rw [hd1, mul_one] at h
    exact h.symm
  have hxC : x ∈ C := hx_eq.symm ▸ p.hc
  have hfix : x ∈ fixV (Subgroup.zpowers a) := by
    have hax : a (b x) = x := by
      simpa only [MulAut.mul_apply W] using mem_fixV_zpowers_iff_apply.mp hxF
    rw [hbc x hxC] at hax
    exact mem_fixV_zpowers_iff_apply.mpr hax
  exact ⟨hxC, hfix⟩

private theorem card_le_card_mul_of_range_ker [Finite W] {F D A B : Subgroup W} (ψ : ↥F →* ↥D)
    (hrange : ∀ y : ↥D, y ∈ ψ.range → (y : W) ∈ B)
    (hker : ∀ x : ↥F, x ∈ ψ.ker → (x : W) ∈ A) :
    Nat.card ↥F ≤ Nat.card ↥A * Nat.card ↥B := by
  have hcard_range : Nat.card ↥ψ.range ≤ Nat.card ↥B := by
    refine Nat.card_le_card_of_injective
      (fun r : ↥ψ.range => (⟨((r : ↥D) : W), hrange (r : ↥D) r.2⟩ : ↥B)) ?_
    intro r₁ r₂ hr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥B => (z : W)) hr
  have hcard_ker : Nat.card ↥ψ.ker ≤ Nat.card ↥A := by
    refine Nat.card_le_card_of_injective
      (fun k : ↥ψ.ker => (⟨((k : ↥F) : W), hker (k : ↥F) k.2⟩ : ↥A)) ?_
    intro k₁ k₂ hk
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥A => (z : W)) hk
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, Nat.mul_comm]
  exact Nat.mul_le_mul hcard_ker hcard_range

theorem card_fixV_zpowers_mul_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {a b : MulAut W} (ha : a ∈ L)
    (hb : b ∈ Subgroup.centralizer (L : Set (MulAut W))) (hb2 : b ^ 2 = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (a * b))) ≤ Nat.card ↥(fixV (Subgroup.zpowers a)) := by
  classical
  let C : Subgroup W := fixV (Subgroup.zpowers b)
  let X : Subgroup (MulAut W) := Subgroup.zpowers a
  let F : Subgroup W := fixV (Subgroup.zpowers (a * b))
  have hbc : ∀ c ∈ C, b c = c := fun c hc => mem_fixV_zpowers_iff_apply.mp hc
  have hCL : StableUnder L C := by
    refine CFSG.LocalAnalysis.WeakClosure81.stableUnder_fixV fun l hl k hk => ?_
    have hkL : k ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      (Subgroup.zpowers_le.mpr hb) hk
    rw [Subgroup.mem_centralizer_iff.mp hkL l hl, mul_inv_cancel_right]
    exact hk
  obtain ⟨D, hDL, hCD, hsup⟩ := exists_stableUnder_compl hfix hspan hCL
  have hCX : StableUnder X C := fun x hx => hCL x (Subgroup.zpowers_le.mpr ha hx)
  have hDX : StableUnder X D := fun x hx => hDL x (Subgroup.zpowers_le.mpr ha hx)
  have hstep : ∀ d : W, b d * d⁻¹ ∈ C := fun d => mul_inv_mem_fixV_zpowers_of_sq hW hb2 d
  let ψ : ↥F →* ↥D := (projD C D hCD hsup).comp F.subtype
  have hrange : ∀ y : ↥D, y ∈ ψ.range → (y : W) ∈ D ⊓ fixV X := by
    intro y hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    have hx' : projD C D hCD hsup (x : W) = y := by
      simpa only [ψ, MonoidHom.comp_apply, Subgroup.subtype_apply] using hx
    refine ⟨?_, ?_⟩
    · rw [← hx']
      exact (projD C D hCD hsup (x : W)).2
    · rw [← hx', coe_projD]
      exact mem_fixV_zpowers_iff_apply.mpr
        (apply_eq_self_complDecomp_d_of_mem_fixV_zpowers_mul hCD hsup hbc hCX hDX hstep x.2)
  have hker : ∀ x : ↥F, x ∈ ψ.ker → ((x : W) ∈ C ⊓ fixV X) := by
    intro x hxker
    have hx1 : projD C D hCD hsup (x : W) = 1 := by
      have h := MonoidHom.mem_ker.mp hxker
      simpa only [ψ, MonoidHom.comp_apply, Subgroup.subtype_apply] using h
    exact mem_inf_fixV_zpowers_of_projD_eq_one hCD hsup hbc x.2 hx1
  have hcard : Nat.card ↥F ≤ Nat.card ↥(C ⊓ fixV X) * Nat.card ↥(D ⊓ fixV X) :=
    card_le_card_mul_of_range_ker ψ hrange hker
  calc Nat.card ↥F ≤ Nat.card ↥(C ⊓ fixV X) * Nat.card ↥(D ⊓ fixV X) := hcard
    _ = Nat.card ↥((C ⊔ D) ⊓ fixV X) := (card_inf_fixV_sup hCX hDX hCD).symm
    _ = Nat.card ↥(fixV X) := by rw [hsup, top_inf_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
