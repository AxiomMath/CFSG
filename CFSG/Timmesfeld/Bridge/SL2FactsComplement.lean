module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Defs
public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Quasithin Matrix

namespace NatCompl

section Cocycle

variable {F : Type} [Field F]

theorem cocycle_eq_zero {f : Matrix.SpecialLinearGroup (Fin 2) F → (Fin 2 → F)}
    (hf : f ∈ JonesParshall.Z1A (JonesParshall.mu2 (F := F)))
    {S : Set (Matrix.SpecialLinearGroup (Fin 2) F)} (hS : Subgroup.closure S = ⊤)
    (h0 : ∀ s ∈ S, f s = 0) : f = 0 := by
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | f g = 0}
      mul_mem' := fun {g h} hg hh => by
        change f (g * h) = 0
        rw [hf g h]
        change f g + JonesParshall.mu2 g (f h) = 0
        rw [show f g = 0 from hg, show f h = 0 from hh, map_zero, add_zero]
      one_mem' := JonesParshall.Z1A_one hf
      inv_mem' := fun {g} hg => by
        change f g⁻¹ = 0
        have h := hf g⁻¹ g
        rw [inv_mul_cancel, JonesParshall.Z1A_one hf, show f g = 0 from hg, map_zero,
          add_zero] at h
        exact h.symm }
  have hle : ⊤ ≤ H := hS ▸ (Subgroup.closure_le H).2 h0
  funext g
  exact hle (Subgroup.mem_top g)

theorem coboundaryA_injective :
    Function.Injective (JonesParshall.coboundaryA (JonesParshall.mu2 (F := F))) := by
  refine (injective_iff_map_eq_zero _).2 fun m hm => ?_
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ m = m := fun g => by
    have := congrFun hm g
    rwa [JonesParshall.coboundaryA_apply, JonesParshall.mu2_apply, Pi.zero_apply,
      sub_eq_zero] at this
  have h1 := (ARS.NaturalModule.forall_upperElt_mulVec_eq_iff m).1 fun t => hfix _
  have h0 := (ARS.NaturalModule.forall_lowerElt_mulVec_eq_iff m).1 fun t => hfix _
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem card_fixed_le [Finite F] {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t ≠ 1) :
    Nat.card {v : Fin 2 → F // (t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v} ≤ Nat.card F := by
  set A := (t : Matrix (Fin 2) (Fin 2) F) 0 0
  set B := (t : Matrix (Fin 2) (Fin 2) F) 0 1
  set C := (t : Matrix (Fin 2) (Fin 2) F) 1 0
  set D := (t : Matrix (Fin 2) (Fin 2) F) 1 1
  have hrow : ∀ v : Fin 2 → F, (t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v →
      A * v 0 + B * v 1 = v 0 ∧ C * v 0 + D * v 1 = v 1 := fun v hv =>
    ⟨by rw [← JonesParshall.mulVec_two_zero, hv], by rw [← JonesParshall.mulVec_two_one, hv]⟩
  by_cases hc : A = 1 ∧ C = 0
  · have hBD : B ≠ 0 ∨ D ≠ 1 := by
      by_contra! hBD
      apply ht
      ext i j
      fin_cases i <;> fin_cases j
      · exact hc.1
      · exact hBD.1
      · exact hc.2
      · exact hBD.2
    refine Nat.card_le_card_of_injective (fun v => v.1 0) fun v w hvw => Subtype.ext ?_
    obtain ⟨hv0, hv1⟩ := hrow v.1 v.2
    obtain ⟨hw0, hw1⟩ := hrow w.1 w.2
    have h0 : v.1 0 = w.1 0 := hvw
    have hd : v.1 1 = w.1 1 := by
      rw [hc.1] at hv0 hw0
      rw [hc.2] at hv1 hw1
      rcases hBD with hB | hD
      · have : B * (v.1 1 - w.1 1) = 0 := by linear_combination hv0 - hw0
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hB)
      · have : (D - 1) * (v.1 1 - w.1 1) = 0 := by linear_combination hv1 - hw1
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hD))
    funext i
    fin_cases i
    · exact h0
    · exact hd
  · refine Nat.card_le_card_of_injective (fun v => v.1 1) fun v w hvw => Subtype.ext ?_
    obtain ⟨hv0, hv1⟩ := hrow v.1 v.2
    obtain ⟨hw0, hw1⟩ := hrow w.1 w.2
    have h1 : v.1 1 = w.1 1 := hvw
    have hd : v.1 0 = w.1 0 := by
      by_cases hA : A = 1
      · have hC : C ≠ 0 := fun hC => hc ⟨hA, hC⟩
        have : C * (v.1 0 - w.1 0) = 0 := by linear_combination hv1 - hw1 - D * h1 + h1
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
      · have : (A - 1) * (v.1 0 - w.1 0) = 0 := by linear_combination hv0 - hw0 - B * h1
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hA))
    funext i
    fin_cases i
    · exact hd
    · exact h1

variable [CharP F 2]

theorem cocycle_mulVec_eq {f : Matrix.SpecialLinearGroup (Fin 2) F → (Fin 2 → F)}
    (hf : f ∈ JonesParshall.Z1A (JonesParshall.mu2 (F := F)))
    {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t * t = 1) :
    (t : Matrix (Fin 2) (Fin 2) F) *ᵥ f t = f t := by
  have h := hf t t
  rw [ht, JonesParshall.Z1A_one hf, JonesParshall.mu2_apply] at h
  funext i
  exact (CharTwo.add_eq_zero.1 (congrFun h.symm i)).symm

variable [Fintype F]

theorem card_Z1A (hF : 4 ≤ Fintype.card F) :
    Nat.card (JonesParshall.Z1A (JonesParshall.mu2 (F := F))) = Fintype.card F ^ 3 := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hn1 : 1 < (n : ℕ) := by
    by_contra h
    have : (n : ℕ) ≤ 1 := by omega
    have : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  rw [JonesParshall.card_Z1A_mu2 hn hn1]
  have hB : Nat.card (JonesParshall.B1A (JonesParshall.mu2 (F := F))) = Fintype.card F ^ 2 := by
    change Nat.card ↥(JonesParshall.coboundaryA (JonesParshall.mu2 (F := F))).range = _
    rw [← Nat.card_congr (AddMonoidHom.ofInjective
      (f := JonesParshall.coboundaryA (JonesParshall.mu2 (F := F))) coboundaryA_injective).toEquiv,
      Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]
  rw [hB]
  ring

theorem exists_cocycle_eq (hF : 4 ≤ Fintype.card F)
    {t₁ t₂ t₃ : Matrix.SpecialLinearGroup (Fin 2) F} (h₁ : t₁ * t₁ = 1) (h₂ : t₂ * t₂ = 1)
    (h₃ : t₃ * t₃ = 1) (h₁' : t₁ ≠ 1) (h₂' : t₂ ≠ 1) (h₃' : t₃ ≠ 1)
    (hgen : Subgroup.closure {t₁, t₂, t₃} = ⊤) {v₁ v₂ v₃ : Fin 2 → F}
    (hv₁ : (t₁ : Matrix (Fin 2) (Fin 2) F) *ᵥ v₁ = v₁)
    (hv₂ : (t₂ : Matrix (Fin 2) (Fin 2) F) *ᵥ v₂ = v₂)
    (hv₃ : (t₃ : Matrix (Fin 2) (Fin 2) F) *ᵥ v₃ = v₃) :
    ∃ f ∈ JonesParshall.Z1A (JonesParshall.mu2 (F := F)), f t₁ = v₁ ∧ f t₂ = v₂ ∧ f t₃ = v₃ := by
  let C := fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
    {v : Fin 2 → F // (t : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v}
  let ev : JonesParshall.Z1A (JonesParshall.mu2 (F := F)) → C t₁ × C t₂ × C t₃ := fun f =>
    (⟨f.1 t₁, cocycle_mulVec_eq f.2 h₁⟩, ⟨f.1 t₂, cocycle_mulVec_eq f.2 h₂⟩,
      ⟨f.1 t₃, cocycle_mulVec_eq f.2 h₃⟩)
  have hinj : Function.Injective ev := by
    intro f f' hff'
    have e₁ : f.1 t₁ = f'.1 t₁ := congrArg (fun p : C t₁ × C t₂ × C t₃ => p.1.1) hff'
    have e₂ : f.1 t₂ = f'.1 t₂ := congrArg (fun p : C t₁ × C t₂ × C t₃ => p.2.1.1) hff'
    have e₃ : f.1 t₃ = f'.1 t₃ := congrArg (fun p : C t₁ × C t₂ × C t₃ => p.2.2.1) hff'
    have h0 := cocycle_eq_zero (sub_mem f.2 f'.2) hgen (by
      rintro s (rfl | rfl | rfl)
      · rw [Pi.sub_apply, e₁, sub_self]
      · rw [Pi.sub_apply, e₂, sub_self]
      · rw [Pi.sub_apply, e₃, sub_self])
    exact Subtype.ext (sub_eq_zero.1 h0)
  have hcardC : Nat.card (C t₁ × C t₂ × C t₃) ≤ Fintype.card F ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, pow_succ, pow_two, ← Nat.card_eq_fintype_card, mul_assoc]
    exact Nat.mul_le_mul (card_fixed_le h₁') (Nat.mul_le_mul (card_fixed_le h₂')
      (card_fixed_le h₃'))
  have hbij : Function.Bijective ev := (Nat.bijective_iff_injective_and_card ev).2
    ⟨hinj, le_antisymm (Nat.card_le_card_of_injective ev hinj) (card_Z1A hF ▸ hcardC)⟩
  obtain ⟨f, hf⟩ := hbij.2 (⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩, ⟨v₃, hv₃⟩)
  exact ⟨f.1, f.2, congrArg (fun p : C t₁ × C t₂ × C t₃ => p.1.1) hf,
    congrArg (fun p : C t₁ × C t₂ × C t₃ => p.2.1.1) hf,
    congrArg (fun p : C t₁ × C t₂ × C t₃ => p.2.2.1) hf⟩

end Cocycle

section Group

variable {G : Type*} [Group G] {F : Type} [Field F] {X : Subgroup G}
  {φ : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F} {θ : (Fin 2 → F) → G}

theorem mul_theta (hθ : ARS.IsNaturalModule φ θ) (y : X) (v : Fin 2 → F) :
    (y : G) * θ v = θ ((φ y : Matrix (Fin 2) (Fin 2) F) *ᵥ v) * y := by
  rw [hθ.map_mulVec, inv_mul_cancel_right]

theorem theta_mul_inj (hθ : ARS.IsNaturalModule φ θ) (hVX : ∀ v, θ v ∈ X → v = 0)
    {v v' : Fin 2 → F} {y y' : G} (hy : y ∈ X) (hy' : y' ∈ X) (h : θ v * y = θ v' * y') :
    v = v' ∧ y = y' := by
  have h1 : θ (-v' + v) = y' * y⁻¹ := by
    rw [hθ.map_add, hθ.map_neg, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have hv : -v' + v = 0 := hVX _ (h1 ▸ X.mul_mem hy' (X.inv_mem hy))
  obtain rfl : v = v' := ((neg_add_eq_zero).1 hv).symm
  exact ⟨rfl, mul_left_cancel h⟩

noncomputable def projElt (hG : ∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) (g : G) : X :=
  ⟨(hG g).choose_spec.choose, (hG g).choose_spec.choose_spec.1⟩

omit [Field F] in
theorem projElt_spec (hG : ∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) (g : G) :
    g = θ (hG g).choose * (projElt hG g : G) :=
  (hG g).choose_spec.choose_spec.2

theorem projElt_eq (hθ : ARS.IsNaturalModule φ θ) (hVX : ∀ v, θ v ∈ X → v = 0)
    (hG : ∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) {g : G} {v : Fin 2 → F} {y : G} (hy : y ∈ X)
    (h : g = θ v * y) : projElt hG g = ⟨y, hy⟩ :=
  Subtype.ext (theta_mul_inj hθ hVX (projElt hG g).2 hy ((projElt_spec hG g).symm.trans h)).2

noncomputable def proj (hθ : ARS.IsNaturalModule φ θ) (hVX : ∀ v, θ v ∈ X → v = 0)
    (hG : ∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) : G →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := φ (projElt hG g)
  map_one' := by
    rw [projElt_eq hθ hVX hG X.one_mem (show (1 : G) = θ 0 * 1 by rw [hθ.map_zero, one_mul])]
    exact map_one φ
  map_mul' g h := by
    have hgh : g * h = θ ((hG g).choose + (φ (projElt hG g) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        (hG h).choose) * ((projElt hG g : G) * (projElt hG h : G)) := by
      conv_lhs => rw [projElt_spec hG g, projElt_spec hG h]
      rw [hθ.map_add, mul_assoc (θ _) (projElt hG g : G), ← mul_assoc (projElt hG g : G),
        mul_theta hθ]
      simp only [mul_assoc]
    rw [projElt_eq hθ hVX hG (X.mul_mem (projElt hG g).2 (projElt hG h).2) hgh, ← map_mul]
    rfl

theorem proj_apply (hθ : ARS.IsNaturalModule φ θ) (hVX : ∀ v, θ v ∈ X → v = 0)
    (hG : ∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) {g : G} {v : Fin 2 → F} {y : G} (hy : y ∈ X)
    (h : g = θ v * y) : proj hθ hVX hG g = φ ⟨y, hy⟩ := by
  change φ (projElt hG g) = _
  rw [projElt_eq hθ hVX hG hy h]

noncomputable def splitting (hθ : ARS.IsNaturalModule φ θ)
    {f : Matrix.SpecialLinearGroup (Fin 2) F → (Fin 2 → F)}
    (hf : f ∈ JonesParshall.Z1A (JonesParshall.mu2 (F := F))) : X →* G where
  toFun y := θ (f (φ y)) * y
  map_one' := by
    rw [map_one, JonesParshall.Z1A_one hf, hθ.map_zero, one_mul]
    rfl
  map_mul' y y' := by
    rw [map_mul, hf, JonesParshall.mu2_apply, hθ.map_add, Subgroup.coe_mul,
      mul_assoc (θ _) (y : G), ← mul_assoc (y : G), mul_theta hθ]
    simp only [mul_assoc]

theorem involution_decomp [CharP F 2] (hθ : ARS.IsNaturalModule φ θ)
    (hVX : ∀ v, θ v ∈ X → v = 0) {x : G} {v : Fin 2 → F} {y : G} (hy : y ∈ X)
    (hx : x = θ v * y) (hxx : x * x = 1) (hxV : ∀ w, θ w ≠ x) :
    φ ⟨y, hy⟩ * φ ⟨y, hy⟩ = 1 ∧ φ ⟨y, hy⟩ ≠ 1 ∧
      (φ ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  have hsq : θ (v + (φ ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) * (y * y) = θ 0 * 1 := by
    rw [hθ.map_zero, one_mul, ← hxx, hx, hθ.map_add,
      mul_assoc (θ v) y, ← mul_assoc y, mul_theta hθ ⟨y, hy⟩]
    simp only [mul_assoc]
  obtain ⟨h1, h2⟩ := theta_mul_inj hθ hVX (X.mul_mem hy hy) X.one_mem hsq
  refine ⟨?_, fun h1' => ?_, ?_⟩
  · rw [← map_mul, show (⟨y, hy⟩ * ⟨y, hy⟩ : X) = 1 from Subtype.ext h2, map_one]
  · have : (⟨y, hy⟩ : X) = 1 := φ.injective (h1'.trans (map_one φ).symm)
    apply hxV v
    rw [hx, show y = 1 from congrArg Subtype.val this, mul_one]
  · funext i
    exact (CharTwo.add_eq_zero.1 (congrFun h1 i)).symm

end Group

end NatCompl

open NatCompl in
theorem naturalComplementStmt : NaturalComplementStmt := by
  intro G _ _ F _ _ _ hF X φ θ hθ hVX hG x a b hx ha hb hxV haV hbV hgen v hv
  obtain ⟨vx, yx, hyx, hxd⟩ := hG x
  obtain ⟨va, ya, hya, had⟩ := hG a
  obtain ⟨vb, yb, hyb, hbd⟩ := hG b
  obtain ⟨hx2, hx1, hxv⟩ := involution_decomp hθ hVX hyx hxd hx hxV
  obtain ⟨ha2, ha1, hav⟩ := involution_decomp hθ hVX hya had ha haV
  obtain ⟨hb2, hb1, hbv⟩ := involution_decomp hθ hVX hyb hbd hb hbV
  have hπx := proj_apply hθ hVX hG hyx hxd
  have hπa := proj_apply hθ hVX hG hya had
  have hπb := proj_apply hθ hVX hG hyb hbd
  have hgen' : Subgroup.closure {φ ⟨yx, hyx⟩, φ ⟨ya, hya⟩, φ ⟨yb, hyb⟩} = ⊤ := by
    rw [eq_top_iff]
    intro M _
    obtain ⟨w, k, hk, hgk⟩ := hgen (φ.symm M : G)
    have hM : proj hθ hVX hG (φ.symm M : G) = M := by
      rw [proj_apply hθ hVX hG (φ.symm M).2
        (show (φ.symm M : G) = θ 0 * (φ.symm M : G) by rw [hθ.map_zero, one_mul])]
      exact φ.apply_symm_apply M
    have hθw : proj hθ hVX hG (θ w) = 1 := by
      rw [proj_apply hθ hVX hG X.one_mem (show θ w = θ w * 1 from (mul_one _).symm)]
      exact map_one φ
    rw [← hM, hgk, map_mul, hθw, one_mul]
    have hk' : proj hθ hVX hG k ∈ (Subgroup.closure {x, a, b}).map (proj hθ hVX hG) :=
      ⟨k, hk, rfl⟩
    rwa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      hπx, hπa, hπb] at hk'
  obtain ⟨f, hf, hfx, hfa, hfb⟩ := exists_cocycle_eq hF hx2 ha2 hb2 hx1 ha1 hb1 hgen' hxv hav hbv
  have hle : Subgroup.closure {x, a, b} ≤ (splitting hθ hf).range := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact ⟨⟨yx, hyx⟩, by
        change θ (f (φ ⟨yx, hyx⟩)) * yx = _
        rw [hfx, hxd]⟩
    · exact ⟨⟨ya, hya⟩, by
        change θ (f (φ ⟨ya, hya⟩)) * ya = _
        rw [hfa, had]⟩
    · exact ⟨⟨yb, hyb⟩, by
        change θ (f (φ ⟨yb, hyb⟩)) * yb = _
        rw [hfb, hbd]⟩
  obtain ⟨y, hy⟩ := hle hv
  have hy' : θ (f (φ y)) * (y : G) = θ v * 1 := by
    rw [mul_one]
    exact hy
  obtain ⟨h1, h2⟩ := theta_mul_inj hθ hVX y.2 X.one_mem hy'
  rw [← h1, show y = 1 from Subtype.ext h2, map_one, JonesParshall.Z1A_one hf]

end CFSG.Timmesfeld.Bridge.RootClosure
