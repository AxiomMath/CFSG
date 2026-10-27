module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.Coset.Defs

public section

namespace CFSG.ASVolI

@[expose] noncomputable def burnsideC56_cosetEquiv {α : Type*} [Group α] (s : Subgroup α) :
    α ≃ (α ⧸ s) × s where
  toFun a := ((a : α ⧸ s), ⟨((a : α ⧸ s).out)⁻¹ * a,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : α ⧸ s))⟩)
  invFun p := p.1.out * p.2
  left_inv a := by simp
  right_inv p := by
    obtain ⟨q, c⟩ := p
    have h1 : ((q.out * c : α) : α ⧸ s) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ c.2, QuotientGroup.out_eq']
    refine Prod.ext h1 (Subtype.ext ?_)
    simp only
    rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]

@[expose] noncomputable def burnsideC56_rmul (A Y : Type*) [Group A] : A →* Equiv.Perm (A × Y) where
  toFun a := Equiv.prodCongr (Equiv.mulRight a⁻¹) (Equiv.refl Y)
  map_one' := by ext ⟨x, y⟩ <;> simp
  map_mul' a b := by ext ⟨x, y⟩ <;> simp [mul_assoc]

variable {G : Type} [Group G] (H Λ : Subgroup G)

abbrev burnsideC56_CH : Subgroup ↥H := (Λ ⊓ H).subgroupOf H

abbrev burnsideC56_CL : Subgroup ↥Λ := (Λ ⊓ H).subgroupOf Λ

abbrev burnsideC56_Om : Type := (↥H ⧸ burnsideC56_CH H Λ) × (↥Λ ⧸ burnsideC56_CL H Λ) × ↥(Λ ⊓ H)

@[expose] noncomputable def burnsideC56_eCH : ↥(burnsideC56_CH H Λ) ≃ ↥(Λ ⊓ H) :=
  (Subgroup.subgroupOfEquivOfLe (inf_le_right : Λ ⊓ H ≤ H)).toEquiv

@[expose] noncomputable def burnsideC56_eCL : ↥(burnsideC56_CL H Λ) ≃ ↥(Λ ⊓ H) :=
  (Subgroup.subgroupOfEquivOfLe (inf_le_left : Λ ⊓ H ≤ Λ)).toEquiv

@[expose] noncomputable def burnsideC56_eH : ↥H × (↥Λ ⧸ burnsideC56_CL H Λ) ≃ burnsideC56_Om H Λ :=
  ((burnsideC56_cosetEquiv (burnsideC56_CH H Λ)).prodCongr (Equiv.refl _)).trans
    ((Equiv.prodAssoc _ _ _).trans
      ((Equiv.refl _).prodCongr ((Equiv.prodComm _ _).trans
        ((Equiv.refl _).prodCongr (burnsideC56_eCH H Λ)))))

@[expose] noncomputable def burnsideC56_eL : ↥Λ × (↥H ⧸ burnsideC56_CH H Λ) ≃ burnsideC56_Om H Λ :=
  ((burnsideC56_cosetEquiv (burnsideC56_CL H Λ)).prodCongr (Equiv.refl _)).trans
    ((Equiv.prodComm _ _).trans
      ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr (burnsideC56_eCL H Λ))))

@[expose] noncomputable def burnsideC56_iota : ↥H →* Equiv.Perm (burnsideC56_Om H Λ) :=
  (burnsideC56_eH H Λ).permCongrHom.toMonoidHom.comp (burnsideC56_rmul ↥H _)

@[expose] noncomputable def burnsideC56_kappa : ↥Λ →* Equiv.Perm (burnsideC56_Om H Λ) :=
  (burnsideC56_eL H Λ).permCongrHom.toMonoidHom.comp (burnsideC56_rmul ↥Λ _)

theorem burnsideC56_iota_apply (h : ↥H) (ω : burnsideC56_Om H Λ) :
    burnsideC56_iota H Λ h ω =
      burnsideC56_eH H Λ (((burnsideC56_eH H Λ).symm ω).1 * h⁻¹, ((burnsideC56_eH H Λ).symm ω).2) :=
  rfl

theorem burnsideC56_kappa_apply (l : ↥Λ) (ω : burnsideC56_Om H Λ) :
    burnsideC56_kappa H Λ l ω =
      burnsideC56_eL H Λ (((burnsideC56_eL H Λ).symm ω).1 * l⁻¹, ((burnsideC56_eL H Λ).symm ω).2) :=
  rfl

theorem burnsideC56_eH_apply (a : ↥H) (y : ↥Λ ⧸ burnsideC56_CL H Λ) :
    burnsideC56_eH H Λ (a, y) = ((a : ↥H ⧸ burnsideC56_CH H Λ), y,
      ⟨((((a : ↥H ⧸ burnsideC56_CH H Λ).out)⁻¹ * a : ↥H) : G),
        Subgroup.mem_subgroupOf.mp
          (QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : ↥H ⧸ burnsideC56_CH H Λ)))⟩) := rfl

theorem burnsideC56_eH_symm_apply (ω : burnsideC56_Om H Λ) :
    (burnsideC56_eH H Λ).symm ω =
      (ω.1.out * ⟨(ω.2.2 : G), (Subgroup.mem_inf.mp ω.2.2.2).2⟩, ω.2.1) := rfl

theorem burnsideC56_eL_apply (b : ↥Λ) (x : ↥H ⧸ burnsideC56_CH H Λ) :
    burnsideC56_eL H Λ (b, x) = (x, (b : ↥Λ ⧸ burnsideC56_CL H Λ),
      ⟨((((b : ↥Λ ⧸ burnsideC56_CL H Λ).out)⁻¹ * b : ↥Λ) : G),
        Subgroup.mem_subgroupOf.mp
          (QuotientGroup.eq.mp (QuotientGroup.out_eq' (b : ↥Λ ⧸ burnsideC56_CL H Λ)))⟩) := rfl

theorem burnsideC56_eL_symm_apply (ω : burnsideC56_Om H Λ) :
    (burnsideC56_eL H Λ).symm ω =
      (ω.2.1.out * ⟨(ω.2.2 : G), (Subgroup.mem_inf.mp ω.2.2.2).1⟩, ω.1) := rfl

theorem burnsideC56_iota_C (g : G) (hH : g ∈ H) (hΛ : g ∈ Λ) (ω : burnsideC56_Om H Λ) :
    burnsideC56_iota H Λ ⟨g, hH⟩ ω = (ω.1, ω.2.1, ⟨(ω.2.2 : G) * g⁻¹,
      mul_mem ω.2.2.2 (inv_mem (Subgroup.mem_inf.mpr ⟨hΛ, hH⟩))⟩) := by
  obtain ⟨x, y, c⟩ := ω
  rw [burnsideC56_iota_apply, burnsideC56_eH_symm_apply]
  dsimp only
  rw [burnsideC56_eH_apply]
  have hmem : (⟨(c : G), (Subgroup.mem_inf.mp c.2).2⟩ : ↥H) * (⟨g, hH⟩ : ↥H)⁻¹ ∈
      burnsideC56_CH H Λ := by
    rw [Subgroup.mem_subgroupOf]
    exact mul_mem c.2 (inv_mem (Subgroup.mem_inf.mpr ⟨hΛ, hH⟩))
  have h1 : ((x.out * ⟨(c : G), (Subgroup.mem_inf.mp c.2).2⟩ * (⟨g, hH⟩ : ↥H)⁻¹ : ↥H) :
      ↥H ⧸ burnsideC56_CH H Λ) = x := by
    rw [mul_assoc, QuotientGroup.mk_mul_of_mem _ hmem, QuotientGroup.out_eq']
  refine Prod.ext h1 (Prod.ext rfl (Subtype.ext ?_))
  simp only
  rw [h1]
  simp [mul_assoc]

theorem burnsideC56_kappa_C (g : G) (hH : g ∈ H) (hΛ : g ∈ Λ) (ω : burnsideC56_Om H Λ) :
    burnsideC56_kappa H Λ ⟨g, hΛ⟩ ω = (ω.1, ω.2.1, ⟨(ω.2.2 : G) * g⁻¹,
      mul_mem ω.2.2.2 (inv_mem (Subgroup.mem_inf.mpr ⟨hΛ, hH⟩))⟩) := by
  obtain ⟨x, y, c⟩ := ω
  rw [burnsideC56_kappa_apply, burnsideC56_eL_symm_apply]
  dsimp only
  rw [burnsideC56_eL_apply]
  have hmem : (⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ : ↥Λ) * (⟨g, hΛ⟩ : ↥Λ)⁻¹ ∈
      burnsideC56_CL H Λ := by
    rw [Subgroup.mem_subgroupOf]
    exact mul_mem c.2 (inv_mem (Subgroup.mem_inf.mpr ⟨hΛ, hH⟩))
  have h1 : ((y.out * ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ * (⟨g, hΛ⟩ : ↥Λ)⁻¹ : ↥Λ) :
      ↥Λ ⧸ burnsideC56_CL H Λ) = y := by
    rw [mul_assoc, QuotientGroup.mk_mul_of_mem _ hmem, QuotientGroup.out_eq']
  refine Prod.ext rfl (Prod.ext h1 (Subtype.ext ?_))
  simp only
  rw [h1]
  simp [mul_assoc]

theorem burnsideC56_iota_eq_kappa (g : G) (hH : g ∈ H) (hΛ : g ∈ Λ) :
    burnsideC56_iota H Λ ⟨g, hH⟩ = burnsideC56_kappa H Λ ⟨g, hΛ⟩ := by
  refine Equiv.ext fun ω => ?_
  rw [burnsideC56_iota_C H Λ g hH hΛ, burnsideC56_kappa_C H Λ g hH hΛ]

theorem burnsideC56_iota_eH (h a : ↥H) (y : ↥Λ ⧸ burnsideC56_CL H Λ) :
    burnsideC56_iota H Λ h (burnsideC56_eH H Λ (a, y)) = burnsideC56_eH H Λ (a * h⁻¹, y) := by
  rw [burnsideC56_iota_apply, Equiv.symm_apply_apply]

theorem burnsideC56_kappa_eL (l b : ↥Λ) (x : ↥H ⧸ burnsideC56_CH H Λ) :
    burnsideC56_kappa H Λ l (burnsideC56_eL H Λ (b, x)) = burnsideC56_eL H Λ (b * l⁻¹, x) := by
  rw [burnsideC56_kappa_apply, Equiv.symm_apply_apply]

theorem burnsideC56_iota_injective : Function.Injective (burnsideC56_iota H Λ) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have := congrArg (fun p : Equiv.Perm (burnsideC56_Om H Λ) => p (burnsideC56_eH H Λ (1, ((1 : ↥Λ) : ↥Λ ⧸ burnsideC56_CL H Λ)))) hh
  simp only [burnsideC56_iota_eH, Equiv.Perm.coe_one, id_eq] at this
  have h2 := congrArg Prod.fst ((burnsideC56_eH H Λ).injective this)
  simpa using h2

theorem burnsideC56_kappa_injective : Function.Injective (burnsideC56_kappa H Λ) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have := congrArg (fun p : Equiv.Perm (burnsideC56_Om H Λ) => p (burnsideC56_eL H Λ (1, ((1 : ↥H) : ↥H ⧸ burnsideC56_CH H Λ)))) hl
  simp only [burnsideC56_kappa_eL, Equiv.Perm.coe_one, id_eq] at this
  have h2 := congrArg Prod.fst ((burnsideC56_eL H Λ).injective this)
  simpa using h2

theorem burnsideC56_kappa_fst (l : ↥Λ) (ω : burnsideC56_Om H Λ) :
    (burnsideC56_kappa H Λ l ω).1 = ω.1 := by
  rw [burnsideC56_kappa_apply]
  obtain ⟨x, y, c⟩ := ω
  rfl

theorem burnsideC56_iota_eq_kappa_iff (h : ↥H) (l : ↥Λ)
    (hhl : burnsideC56_iota H Λ h = burnsideC56_kappa H Λ l) : (h : G) = l := by
  have e1 := congrArg (fun p : Equiv.Perm (burnsideC56_Om H Λ) =>
    (p (burnsideC56_eH H Λ (1, ((1 : ↥Λ) : ↥Λ ⧸ burnsideC56_CL H Λ)))).1) hhl
  simp only [burnsideC56_iota_eH, burnsideC56_kappa_fst] at e1
  rw [burnsideC56_eH_apply, burnsideC56_eH_apply] at e1
  dsimp only at e1
  have hmem : h⁻¹ ∈ burnsideC56_CH H Λ := by
    have := QuotientGroup.eq.mp e1
    simpa using this
  rw [Subgroup.mem_subgroupOf] at hmem
  have hΛ : (h : G) ∈ Λ := by
    have := (Subgroup.mem_inf.mp hmem).1
    simpa using inv_mem this
  have e2 := burnsideC56_iota_eq_kappa H Λ (h : G) h.2 hΛ
  rw [show (⟨(h : G), h.2⟩ : ↥H) = h from rfl, hhl] at e2
  exact congrArg Subtype.val ((burnsideC56_kappa_injective H Λ) e2).symm

end CFSG.ASVolI
