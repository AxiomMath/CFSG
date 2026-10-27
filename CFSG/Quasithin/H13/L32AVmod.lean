module

public import CFSG.Quasithin.H13.L32ARuOne

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

namespace L32A

abbrev e₁ : Fin 3 → ZMod 2 := ![1, 0, 0]

abbrev e₂ : Fin 3 → ZMod 2 := ![0, 1, 0]

theorem exists_sl3_pair' : ∀ p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2), p.1 ≠ 0 → p.2 ≠ 0 →
    p.1 ≠ p.2 → ∃ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e₁ = p.1 ∧
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e₂ = p.2 := by
  decide +kernel

theorem exists_sl3_pair (y₁ y₂ : Fin 3 → ZMod 2) (h₁ : y₁ ≠ 0) (h₂ : y₂ ≠ 0) (h : y₁ ≠ y₂) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e₁ = y₁ ∧
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e₂ = y₂ :=
  exists_sl3_pair' (y₁, y₂) h₁ h₂ h

theorem card_SL_three_two' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

variable {G : Type} [Group G]

@[expose] noncomputable def mulAutOfSL {V : Subgroup G} (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2))
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : MulAut ↥V :=
  ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL 3)).symm
    (Matrix.SpecialLinearGroup.toGL A)

theorem mulAutOfSL_apply {V : Subgroup G} (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2))
    (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : ↥V) :
    e (mulAutOfSL e A v) = Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (Multiplicative.toAdd (e v))) := by
  have h1 : Vol2.Ch10.SecA.mulAutPiEquivGL 3 (MulAut.congr e (mulAutOfSL e A)) =
      Matrix.SpecialLinearGroup.toGL A :=
    MulEquiv.apply_symm_apply ((MulAut.congr e).trans (Vol2.Ch10.SecA.mulAutPiEquivGL 3)) _
  have h2 := mulAutPiEquivGL_mulVec 3 (MulAut.congr e (mulAutOfSL e A))
    (Multiplicative.toAdd (e v))
  rw [h1, MulAut.congr_apply] at h2
  simp only [ofAdd_toAdd, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  rw [← ofAdd_toAdd (e (mulAutOfSL e A v)), ← h2]
  rfl

theorem exists_conj_of_autOn_eq_top {L V : Subgroup G} (hA : autOn L V = ⊤) (φ : MulAut ↥V) :
    ∃ l ∈ L, ∀ v : ↥V, l * (v : G) * l⁻¹ = φ v := by
  have hφ : φ ∈ autOn L V := by rw [hA]; exact Subgroup.mem_top _
  obtain ⟨x, hxL, hxφ⟩ := hφ
  refine ⟨(x : G), hxL, fun v => ?_⟩
  have := congrArg (fun ψ : MulAut ↥V => ((ψ v : ↥V) : G)) hxφ
  rw [← this]
  rfl

theorem exists_conj_eq_pair [Finite G] {T L V : Subgroup G} (h : Hyp1281One G T L V 3)
    {v₁ v₂ w₁ w₂ : G} (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (hw₁ : w₁ ∈ V) (hw₂ : w₂ ∈ V)
    (hv₁1 : v₁ ≠ 1) (hv₂1 : v₂ ≠ 1) (hw₁1 : w₁ ≠ 1) (hw₂1 : w₂ ≠ 1) (hv : v₁ ≠ v₂)
    (hw : w₁ ≠ w₂) : ∃ l ∈ L, l * v₁ * l⁻¹ = w₁ ∧ l * v₂ * l⁻¹ = w₂ := by
  obtain ⟨hcard, hsq, hcomm⟩ := h.card_sq
  have hA : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One h
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hne0 : ∀ {u : G} (hu : u ∈ V), u ≠ 1 → Multiplicative.toAdd (e ⟨u, hu⟩) ≠ 0 := by
    intro u hu hu1 h0
    apply hu1
    have h1 : e ⟨u, hu⟩ = 1 := by rw [← ofAdd_toAdd (e ⟨u, hu⟩), h0]; rfl
    have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    simpa using this
  have hne : ∀ {u u' : G} (hu : u ∈ V) (hu' : u' ∈ V), u ≠ u' →
      Multiplicative.toAdd (e ⟨u, hu⟩) ≠ Multiplicative.toAdd (e ⟨u', hu'⟩) := by
    intro u u' hu hu' huu' h0
    apply huu'
    have := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h0))
    simpa using this
  obtain ⟨A, hA₁, hA₂⟩ := exists_sl3_pair _ _ (hne0 hv₁ hv₁1) (hne0 hv₂ hv₂1) (hne hv₁ hv₂ hv)
  obtain ⟨B, hB₁, hB₂⟩ := exists_sl3_pair _ _ (hne0 hw₁ hw₁1) (hne0 hw₂ hw₂1) (hne hw₁ hw₂ hw)
  obtain ⟨l, hl, hlφ⟩ := exists_conj_of_autOn_eq_top hA (mulAutOfSL e (B * A⁻¹))
  have key : ∀ {u u' : G} (hu : u ∈ V) (hu' : u' ∈ V) (x : Fin 3 → ZMod 2),
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x = Multiplicative.toAdd (e ⟨u, hu⟩) →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x = Multiplicative.toAdd (e ⟨u', hu'⟩) →
      l * u * l⁻¹ = u' := by
    intro u u' hu hu' x hAx hBx
    have h1 := hlφ ⟨u, hu⟩
    have h2 := mulAutOfSL_apply e (B * A⁻¹) ⟨u, hu⟩
    have h3 : (((B * A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))).mulVec (Multiplicative.toAdd (e ⟨u, hu⟩)) =
          Multiplicative.toAdd (e ⟨u', hu'⟩) := by
      rw [← hAx, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        ← Matrix.SpecialLinearGroup.coe_mul A⁻¹ A, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hBx]
    rw [h3, ofAdd_toAdd] at h2
    rw [h1, e.injective h2]
  exact ⟨l, hl, key hv₁ hw₁ e₁ hA₁ hB₁, key hv₂ hw₂ e₂ hA₂ hB₂⟩

end L32A

end CFSG.Quasithin.H13
