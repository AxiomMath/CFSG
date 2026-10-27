module

public import CFSG.Quasithin.Background.L3SmallFin
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.L3Small

open CFSG.Quasithin L3

section Module

variable {W : Type*} [CommGroup W]

@[expose] def fixOf (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    show g (a * b) = a * b
    rw [map_mul, show g a = a from ha, show g b = b from hb]
  inv_mem' := fun {a} ha => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha]

theorem mem_fixOf {g : MulAut W} {w : W} : w ∈ fixOf g ↔ g w = w := Iff.rfl

@[expose] def fixAll (ρ : Γ →* MulAut W) : Subgroup W where
  carrier := {w | ∀ γ, ρ γ w = w}
  one_mem' := fun γ => map_one (ρ γ)
  mul_mem' := fun ha hb γ => by rw [map_mul, ha γ, hb γ]
  inv_mem' := fun ha γ => by rw [map_inv, ha γ]

@[expose] def stabOf (ρ : Γ →* MulAut W) (w : W) : Subgroup Γ where
  carrier := {γ | ρ γ w = w}
  one_mem' := by
    show ρ 1 w = w
    rw [map_one, MulAut.one_apply]
  mul_mem' := fun {x y} hx hy => by
    show ρ (x * y) w = w
    rw [map_mul, MulAut.mul_apply, show ρ y w = w from hy, show ρ x w = w from hx]
  inv_mem' := fun {x} hx => by
    show ρ x⁻¹ w = w
    have h1 : ρ x w = w := hx
    calc ρ x⁻¹ w = ρ x⁻¹ (ρ x w) := by rw [h1]
      _ = w := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

@[expose] def stabSubOf (ρ : Γ →* MulAut W) (U : Subgroup W) : Subgroup Γ where
  carrier := {γ | ∀ u, u ∈ U ↔ ρ γ u ∈ U}
  one_mem' := fun u => by rw [map_one, MulAut.one_apply]
  mul_mem' := fun {x y} hx hy u => by
    rw [map_mul, MulAut.mul_apply]
    exact (hy u).trans (hx _)
  inv_mem' := fun {x} hx u => by
    have h1 := hx (ρ x⁻¹ u)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
    exact h1.symm

theorem injective_of_ne (ρ : Γ →* MulAut W) {γ : Γ} (hγ : ρ γ ≠ 1) : Function.Injective ρ := by
  have : IsSimpleGroup Γ := isSimpleGroup_Γ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h0 | h0
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp h0
  · exfalso
    apply hγ
    have : γ ∈ ρ.ker := h0 ▸ Subgroup.mem_top γ
    exact this

theorem closure_conj (h : Γ) :
    Subgroup.closure ({h * c₀ * h⁻¹, (h * a₀ * h⁻¹) * (h * c₀ * h⁻¹) * (h * a₀ * h⁻¹)} :
      Set Γ) = ⊤ := by
  have e1 : (MulAut.conj h).toMonoidHom c₀ = h * c₀ * h⁻¹ := rfl
  have e2 : (MulAut.conj h).toMonoidHom (a₀ * c₀ * a₀) =
      (h * a₀ * h⁻¹) * (h * c₀ * h⁻¹) * (h * a₀ * h⁻¹) := by
    show h * (a₀ * c₀ * a₀) * h⁻¹ = _
    group
  have e : ({h * c₀ * h⁻¹, (h * a₀ * h⁻¹) * (h * c₀ * h⁻¹) * (h * a₀ * h⁻¹)} : Set Γ) =
      (MulAut.conj h).toMonoidHom '' {c₀, a₀ * c₀ * a₀} := by
    rw [Set.image_pair, e1, e2]
  rw [e, ← MonoidHom.map_closure, closure_c₀]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective

@[expose] def pw (b : W) (t : ZMod 2) : W := if t = 0 then 1 else b

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem pw_add {b : W} (hb : b * b = 1) (s t : ZMod 2) : pw b (s + t) = pw b s * pw b t := by
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
  · simp [pw]
  · simp [pw]
  · simp [pw]
  · have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [h2]
    simp [pw, hb]

@[expose] def coordHom (b : Fin 4 → W) (hb : ∀ i, b i * b i = 1) :
    Multiplicative (Fin 4 → ZMod 2) →* W where
  toFun x := ∏ i, pw (b i) (Multiplicative.toAdd x i)
  map_one' := by simp [pw]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [toAdd_mul, Pi.add_apply, pw_add (hb i)]

theorem coordHom_apply (b : Fin 4 → W) (hb : ∀ i, b i * b i = 1)
    (x : Multiplicative (Fin 4 → ZMod 2)) :
    coordHom b hb x = pw (b 0) (Multiplicative.toAdd x 0) * pw (b 1) (Multiplicative.toAdd x 1) *
      pw (b 2) (Multiplicative.toAdd x 2) * pw (b 3) (Multiplicative.toAdd x 3) := by
  show ∏ i : Fin 4, pw (b i) (Multiplicative.toAdd x i) = _
  rw [Fin.prod_univ_four]

theorem coordHom_single (b : Fin 4 → W) (hb : ∀ i, b i * b i = 1) (j : Fin 4) :
    coordHom b hb (Multiplicative.ofAdd (Pi.single j 1)) = b j := by
  rw [coordHom_apply]
  fin_cases j <;> simp [pw]

variable [Finite W]

omit [Finite W] in
theorem elemAutEquivGL_apply {e : W ≃* Multiplicative (Fin 4 → ZMod 2)} (g : MulAut W)
    (i j : Fin 4) :
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e g : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j =
      Multiplicative.toAdd (e (g (e.symm (Multiplicative.ofAdd (Pi.single j 1))))) i := by
  have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e g
    (e.symm (Multiplicative.ofAdd (Pi.single j 1)))
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, Matrix.mulVec_single_one] at h1
  rw [← h1]
  rfl

theorem false_of_sixteen (hW2 : ∀ w : W, w * w = 1) (ρ : Γ →* MulAut W)
    (hirr : ∀ U : Subgroup W, (∀ γ : Γ, ∀ u ∈ U, ρ γ u ∈ U) → U = ⊥ ∨ U = ⊤) {a c : Γ}
    (ha2 : a * a = 1) (hc3 : c ^ 3 = 1) (h7 : (a * c) ^ 7 = 1)
    (h4 : (a * c * a * c * c) ^ 4 = 1) (hgen : Subgroup.closure ({a, c} : Set Γ) = ⊤)
    (hFF : fixOf (ρ c) ⊓ fixOf (ρ (a * c * a)) = ⊥) {f₁ f₂ : W}
    (hf₁ : f₁ ∈ fixOf (ρ (a * c * a))) (hf₂ : f₂ ∈ fixOf (ρ (a * c * a))) (hf₁1 : f₁ ≠ 1)
    (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₁ ≠ f₂) (h16 : Nat.card W = 16) : False := by
  have hρa2 : ∀ w, ρ a (ρ a w) = w := fun w => by
    rw [← MulAut.mul_apply, ← map_mul, ha2, map_one, MulAut.one_apply]
  have hmapF : ∀ f ∈ fixOf (ρ (a * c * a)), ρ a f ∈ fixOf (ρ c) := by
    intro f hf
    have h1 : ρ a (ρ c (ρ a f)) = f := by
      have := (mem_fixOf.mp hf)
      rwa [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at this
    show ρ c (ρ a f) = ρ a f
    have h2 := congrArg (ρ a) h1
    rwa [hρa2] at h2
  set g₁ := ρ a f₁ with hg₁
  set g₂ := ρ a f₂ with hg₂
  have hg₁F := hmapF f₁ hf₁
  have hg₂F := hmapF f₂ hf₂
  have hg₁1 : g₁ ≠ 1 := fun h0 => hf₁1 (by rw [← hρa2 f₁, ← hg₁, h0, map_one])
  have hg₂1 : g₂ ≠ 1 := fun h0 => hf₂1 (by rw [← hρa2 f₂, ← hg₂, h0, map_one])
  have hg₁₂ : g₁ ≠ g₂ := fun h0 => hf₁₂ (by rw [← hρa2 f₁, ← hρa2 f₂, ← hg₁, ← hg₂, h0])
  let b : Fin 4 → W := ![f₁, f₂, g₁, g₂]
  have hb : ∀ i, b i * b i = 1 := fun i => hW2 _
  set φ := coordHom b hb with hφ
  have hpair : ∀ {x y : W}, x ≠ 1 → y ≠ 1 → x ≠ y → x * x = 1 → ∀ s t : ZMod 2,
      pw x s * pw y t = 1 → s = 0 ∧ t = 0 := by
    intro x y hx hy hxy hxx s t h0
    rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa [pw] using h0) hy
    · exact absurd (by simpa [pw] using h0) hx
    · exfalso
      apply hxy
      have h1 : x * y = 1 := by simpa [pw] using h0
      calc x = x * (x * y) := by rw [h1, mul_one]
        _ = y := by rw [← mul_assoc, hxx, one_mul]
  have hpwF : ∀ (K : Subgroup W) (x : W), x ∈ K → ∀ t : ZMod 2, pw x t ∈ K := by
    intro K x hx t
    unfold pw
    split_ifs
    · exact K.one_mem
    · exact hx
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ, coordHom_apply] at hx
    set p := pw (b 0) (Multiplicative.toAdd x 0) * pw (b 1) (Multiplicative.toAdd x 1)
    set q := pw (b 2) (Multiplicative.toAdd x 2) * pw (b 3) (Multiplicative.toAdd x 3)
    have hpq : p * q = 1 := by
      rw [← hx]
      simp only [p, q, mul_assoc]
    have hpF : p ∈ fixOf (ρ (a * c * a)) :=
      Subgroup.mul_mem _ (hpwF _ _ hf₁ _) (hpwF _ _ hf₂ _)
    have hqF : q ∈ fixOf (ρ c) := Subgroup.mul_mem _ (hpwF _ _ hg₁F _) (hpwF _ _ hg₂F _)
    have hp1 : p = 1 := by
      have : p ∈ fixOf (ρ c) ⊓ fixOf (ρ (a * c * a)) := by
        refine ⟨?_, hpF⟩
        rw [eq_inv_of_mul_eq_one_left hpq]
        exact Subgroup.inv_mem _ hqF
      rw [hFF, Subgroup.mem_bot] at this
      exact this
    have hq1 : q = 1 := by rw [hp1, one_mul] at hpq; exact hpq
    obtain ⟨h0, h1⟩ := hpair hf₁1 hf₂1 hf₁₂ (hW2 f₁) _ _ hp1
    obtain ⟨h2, h3⟩ := hpair hg₁1 hg₂1 hg₁₂ (hW2 g₁) _ _ hq1
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hbij : Function.Bijective φ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [h16, Nat.card_eq_fintype_card]
    rfl
  set e₁ : W ≃* Multiplicative (Fin 4 → ZMod 2) := (MulEquiv.ofBijective φ hbij).symm with he₁
  have he₁b : ∀ j, e₁.symm (Multiplicative.ofAdd (Pi.single j 1)) = b j := by
    intro j
    show φ (Multiplicative.ofAdd (Pi.single j 1)) = b j
    exact coordHom_single b hb j
  have he₁b' : ∀ j, e₁ (b j) = Multiplicative.ofAdd (Pi.single j 1) := by
    intro j
    rw [← he₁b j, MulEquiv.apply_symm_apply]
  set Ma := CFSG.SectionRank.Ccomm.elemAutEquivGL e₁ (ρ a) with hMa
  set Mc := CFSG.SectionRank.Ccomm.elemAutEquivGL e₁ (ρ c) with hMc
  have hcol : ∀ (g : MulAut W) (j k : Fin 4), g (b j) = b k → ∀ i,
      (CFSG.SectionRank.Ccomm.elemAutEquivGL e₁ g : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j =
        (Pi.single k (1 : ZMod 2) : Fin 4 → ZMod 2) i := by
    intro g j k hgk i
    rw [elemAutEquivGL_apply, he₁b, hgk, he₁b', toAdd_ofAdd]
  have hMa_eq : (Ma : Matrix (Fin 4) (Fin 4) (ZMod 2)) = swap4 := by
    have c0 := hcol (ρ a) 0 2 rfl
    have c1 := hcol (ρ a) 1 3 rfl
    have c2 := hcol (ρ a) 2 0 (hρa2 f₁)
    have c3 := hcol (ρ a) 3 1 (hρa2 f₂)
    ext i j
    fin_cases j
    · exact (c0 i).trans (by fin_cases i <;> decide)
    · exact (c1 i).trans (by fin_cases i <;> decide)
    · exact (c2 i).trans (by fin_cases i <;> decide)
    · exact (c3 i).trans (by fin_cases i <;> decide)
  set X : Fin 2 → Fin 2 → ZMod 2 := fun i j =>
    (Mc : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i, by omega⟩ ⟨j, by omega⟩ with hX
  set Y : Fin 2 → Fin 2 → ZMod 2 := fun i j =>
    (Mc : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i + 2, by omega⟩ ⟨j, by omega⟩ with hY
  have hMc_eq : (Mc : Matrix (Fin 4) (Fin 4) (ZMod 2)) = blk X Y := by
    have d2 := hcol (ρ c) 2 2 (mem_fixOf.mp hg₁F)
    have d3 := hcol (ρ c) 3 3 (mem_fixOf.mp hg₂F)
    ext i j
    fin_cases j
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · exact (d2 i).trans (by fin_cases i <;> rfl)
    · exact (d3 i).trans (by fin_cases i <;> rfl)
  have hval : ∀ γ : Γ, γ = 1 →
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e₁ (ρ γ) : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rintro γ rfl
    rw [map_one, map_one, Units.val_one]
  have hrel : relsB (blk X Y) = true := by
    unfold relsB
    rw [← hMc_eq, ← hMa_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := hval _ hc3
      rwa [map_pow, map_pow, Units.val_pow_eq_pow_val] at this
    · have := hval _ h7
      rwa [map_pow, map_pow, map_mul, map_mul, Units.val_pow_eq_pow_val, Units.val_mul] at this
    · have := hval _ h4
      rwa [map_pow, map_pow, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
        map_mul, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mul, Units.val_mul,
        Units.val_mul] at this
  have hred := reducible_blk X Y hrel
  unfold redB at hred
  obtain ⟨v, hv0, hvS⟩ := of_decide_eq_true hred
  unfold invSpanB at hvS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hvS
  obtain ⟨⟨⟨⟨hvmem, hSne⟩, hSadd⟩, hSswap⟩, hSc⟩ := hvS
  set S := closure4 (blk X Y) v with hS
  have hchar : ∀ x : Fin 4 → ZMod 2, x + x = 0 := fun x => by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize x i = t
    revert t
    decide
  have hneg : ∀ x : Fin 4 → ZMod 2, -x = x := fun x => by
    funext i
    simp only [Pi.neg_apply]
    generalize x i = t
    revert t
    decide
  have hS0 : (0 : Fin 4 → ZMod 2) ∈ S := by
    have := hSadd v hvmem v hvmem
    rwa [hchar] at this
  let U : Subgroup W :=
    { carrier := {w | Multiplicative.toAdd (e₁ w) ∈ S}
      one_mem' := by
        show Multiplicative.toAdd (e₁ 1) ∈ S
        rw [map_one, toAdd_one]
        exact hS0
      mul_mem' := fun {x y} hx hy => by
        show Multiplicative.toAdd (e₁ (x * y)) ∈ S
        rw [map_mul, toAdd_mul]
        exact hSadd _ hx _ hy
      inv_mem' := fun {x} hx => by
        show Multiplicative.toAdd (e₁ x⁻¹) ∈ S
        rw [map_inv, toAdd_inv, hneg]
        exact hx }
  have hmemU : ∀ w, w ∈ U ↔ Multiplicative.toAdd (e₁ w) ∈ S := fun w => Iff.rfl
  have hUa : ∀ u ∈ U, ρ a u ∈ U := by
    intro u hu
    rw [hmemU, ← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec, ← hMa, hMa_eq]
    exact hSswap _ hu
  have hUc : ∀ u ∈ U, ρ c u ∈ U := by
    intro u hu
    rw [hmemU, ← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec, ← hMc, hMc_eq]
    exact hSc _ hu
  have hρc3 : ∀ w, ρ c (ρ c (ρ c w)) = w := fun w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, ← pow_three', hc3,
      map_one, MulAut.one_apply]
  have hstab : stabSubOf ρ U = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro γ (rfl | rfl)
    · intro u
      refine ⟨hUa u, fun h0 => ?_⟩
      have := hUa _ h0
      rwa [hρa2] at this
    · intro u
      refine ⟨hUc u, fun h0 => ?_⟩
      have := hUc _ (hUc _ h0)
      rwa [hρc3] at this
  have hinvU : ∀ γ : Γ, ∀ u ∈ U, ρ γ u ∈ U := fun γ u hu =>
    ((show γ ∈ stabSubOf ρ U from hstab ▸ Subgroup.mem_top γ) u).mp hu
  rcases hirr U hinvU with h0 | h0
  · have h1 : e₁.symm (Multiplicative.ofAdd v) ∈ U := by
      rw [hmemU, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hvmem
    rw [h0, Subgroup.mem_bot] at h1
    apply hv0
    have h2 := congrArg (fun w => Multiplicative.toAdd (e₁ w)) h1
    simpa using h2
  · apply hSne
    ext x
    refine ⟨fun _ => Finset.mem_univ x, fun _ => ?_⟩
    have h1 : e₁.symm (Multiplicative.ofAdd x) ∈ U := h0 ▸ Subgroup.mem_top _
    rw [hmemU, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
    exact h1

noncomputable def toGLEquiv : Γ ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

theorem exists_natural (hW2 : ∀ w : W, w * w = 1) (ρ : Γ →* MulAut W)
    (hirr : ∀ U : Subgroup W, (∀ γ : Γ, ∀ u ∈ U, ρ γ u ∈ U) → U = ⊥ ∨ U = ⊤) {c : Γ}
    (hc3 : c ^ 3 = 1) (hcard : Nat.card W = 4 * Nat.card (fixOf (ρ c))) :
    ∃ (α : Γ ≃* Γ) (β : W ≃* Multiplicative Vec), ∀ γ w,
      β (ρ γ w) = Multiplicative.ofAdd (act (α γ) (Multiplicative.toAdd (β w))) := by
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hρc : ρ c ≠ 1 := by
    intro h0
    have h1 : fixOf (ρ c) = ⊤ := by
      ext w
      simp [mem_fixOf, h0]
    rw [h1, Subgroup.card_top] at hcard
    omega
  have hc1 : c ≠ 1 := fun h0 => hρc (by rw [h0, map_one])
  have hinj := injective_of_ne ρ hρc
  have hWp : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one, pow_two]; exact hW2 w⟩
  obtain ⟨h, rfl⟩ := conj_c₀ c hc3 hc1
  set a := h * a₀ * h⁻¹ with ha
  have ha2 : a * a = 1 := by
    calc a * a = h * (a₀ * a₀) * h⁻¹ := by rw [ha]; group
      _ = 1 := by rw [a₀_mul_self]; group
  have h7 : (a * (h * c₀ * h⁻¹)) ^ 7 = 1 := by
    have e : a * (h * c₀ * h⁻¹) = h * (a₀ * c₀) * h⁻¹ := by rw [ha]; group
    rw [e, conj_pow, a₀_mul_c₀_pow]
    group
  have h4 : (a * (h * c₀ * h⁻¹) * a * (h * c₀ * h⁻¹) * (h * c₀ * h⁻¹)) ^ 4 = 1 := by
    have e : a * (h * c₀ * h⁻¹) * a * (h * c₀ * h⁻¹) * (h * c₀ * h⁻¹) =
        h * (a₀ * c₀ * a₀ * c₀ * c₀) * h⁻¹ := by rw [ha]; group
    rw [e, conj_pow, comm_a₀_c₀_pow]
    group
  set c := h * c₀ * h⁻¹ with hcdef
  have hgen1 : Subgroup.closure ({c, a * c * a} : Set Γ) = ⊤ := closure_conj h
  have hgen : Subgroup.closure ({a, c} : Set Γ) = ⊤ := by
    rw [eq_top_iff, ← hgen1, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))) (Subgroup.subset_closure (Or.inl rfl))
  have hfixAll : fixAll ρ = ⊥ := by
    rcases hirr (fixAll ρ) (fun γ u hu δ => by rw [hu γ]; exact hu δ) with h0 | h0
    · exact h0
    · exfalso
      apply hρc
      ext w
      have : w ∈ fixAll ρ := h0 ▸ Subgroup.mem_top w
      exact this c
  have hρa2 : ∀ w, ρ a (ρ a w) = w := fun w => by
    rw [← MulAut.mul_apply, ← map_mul, ha2, map_one, MulAut.one_apply]
  have hmemF' : ∀ w, w ∈ fixOf (ρ (a * c * a)) ↔ ρ a w ∈ fixOf (ρ c) := by
    intro w
    rw [mem_fixOf, mem_fixOf, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro h1
      have h2 := congrArg (ρ a) h1
      rwa [hρa2] at h2
    · intro h1
      rw [h1, hρa2]
  have hcardF' : Nat.card (fixOf (ρ (a * c * a))) = Nat.card (fixOf (ρ c)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨ρ a w, (hmemF' w).mp w.2⟩
        invFun := fun w => ⟨ρ a w, (hmemF' _).mpr (by rw [hρa2]; exact w.2)⟩
        left_inv := fun w => Subtype.ext (hρa2 w)
        right_inv := fun w => Subtype.ext (hρa2 w) }
  have hFF : fixOf (ρ c) ⊓ fixOf (ρ (a * c * a)) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hw'⟩
    have hst : stabOf ρ w = ⊤ := by
      rw [eq_top_iff, ← hgen1, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hw
      · exact hw'
    have h1 : w ∈ fixAll ρ := fun γ => (hst ▸ Subgroup.mem_top γ : γ ∈ stabOf ρ w)
    rw [hfixAll] at h1
    exact h1
  have hle : Nat.card (fixOf (ρ c)) * Nat.card (fixOf (ρ (a * c * a))) ≤ Nat.card W := by
    let μ : ↥(fixOf (ρ c)) × ↥(fixOf (ρ (a * c * a))) → W := fun p => p.1 * p.2
    have hμ : Function.Injective μ := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ h0
      have h1 : (x' : W)⁻¹ * x = y' * (y : W)⁻¹ := by
        have h2 : (x : W) * y = x' * y' := h0
        calc (x' : W)⁻¹ * x = (x' : W)⁻¹ * (x * y) * (y : W)⁻¹ := by group
          _ = (x' : W)⁻¹ * (x' * y') * (y : W)⁻¹ := by rw [h2]
          _ = y' * (y : W)⁻¹ := by group
      have h3 : (x' : W)⁻¹ * x ∈ fixOf (ρ c) ⊓ fixOf (ρ (a * c * a)) :=
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ x'.2) x.2,
          h1 ▸ Subgroup.mul_mem _ y'.2 (Subgroup.inv_mem _ y.2)⟩
      rw [hFF, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (y : W) = y' := by
        rw [← h3] at h1
        rw [inv_mul_cancel, eq_comm, mul_inv_eq_one] at h1
        exact h1.symm
      rw [Prod.mk.injEq]
      exact ⟨Subtype.ext h3.symm, Subtype.ext h4⟩
    have := Nat.card_le_card_of_injective μ hμ
    rwa [Nat.card_prod] at this
  rw [hcardF'] at hle
  have hFpos : 0 < Nat.card (fixOf (ρ c)) := Nat.card_pos
  have hF4 : Nat.card (fixOf (ρ c)) ≤ 4 := by nlinarith
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hWp.to_subgroup (fixOf (ρ c)))
  have hk2 : k ≤ 2 := by
    by_contra h0
    push Not at h0
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h0
    omega
  interval_cases k
  ·
    exfalso
    rw [hk] at hcard
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := W) (p := 2)
      (fun x y => mul_comm x y) (fun w => by rw [pow_two]; exact hW2 w) (n := 2)
      (by rw [hcard]; norm_num)
    have h1 : Nat.card (MulAut W) = 6 := by
      rw [Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv,
        Matrix.card_GL_field, ZMod.card]
      decide
    have h2 := Nat.card_le_card_of_injective ρ hinj
    rw [card_Γ, h1] at h2
    norm_num at h2
  ·
    rw [hk] at hcard
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := W) (p := 2)
      (fun x y => mul_comm x y) (fun w => by rw [pow_two]; exact hW2 w) (n := 3)
      (by rw [hcard]; norm_num)
    set φ : Γ →* GL (Fin 3) (ZMod 2) :=
      (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ with hφ
    set αh : Γ →* Γ := toGLEquiv.symm.toMonoidHom.comp φ with hαh
    have hαinj : Function.Injective αh := by
      intro x y hxy
      apply hinj
      have h1 : φ x = φ y := toGLEquiv.symm.injective hxy
      exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective h1
    refine ⟨MulEquiv.ofBijective αh (Finite.injective_iff_bijective.mp hαinj), e, ?_⟩
    intro γ w
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, ← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec]
    show _ = ((αh γ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec _
    congr 1
    have h1 : toGLEquiv (αh γ) = φ γ := by
      rw [hαh]
      exact toGLEquiv.apply_symm_apply (φ γ)
    rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact (congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      h1).symm
  ·
    exfalso
    rw [hk] at hcard hcardF'
    have hF'4 : Nat.card (fixOf (ρ (a * c * a))) = 4 := hcardF'
    have hne : fixOf (ρ (a * c * a)) ≠ ⊥ := fun h0 => by
      rw [h0, Subgroup.card_bot] at hF'4
      norm_num at hF'4
    obtain ⟨⟨f₁, hf₁⟩, hf₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hf₁1' : f₁ ≠ 1 := fun h0 => hf₁1 (Subtype.ext h0)
    have hz : Subgroup.zpowers f₁ < fixOf (ρ (a * c * a)) := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hf₁) fun h0 => ?_
      have h1 : Nat.card (Subgroup.zpowers f₁) = 2 := by
        rw [Nat.card_zpowers]
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hW2 f₁) hf₁1'
      rw [h0, hF'4] at h1
      norm_num at h1
    obtain ⟨f₂, hf₂, hf₂z⟩ := IsConcreteLE.exists_of_lt hz
    have hf₂1 : f₂ ≠ 1 := fun h0 => hf₂z (h0 ▸ Subgroup.one_mem _)
    have hf₁₂ : f₁ ≠ f₂ := fun h0 => hf₂z (h0 ▸ Subgroup.mem_zpowers f₁)
    exact false_of_sixteen hW2 ρ hirr ha2 hc3 h7 h4 hgen hFF hf₁ hf₂ hf₁1' hf₂1 hf₁₂
      (by rw [hcard]; norm_num)

end Module

end CFSG.Quasithin.L3Small
