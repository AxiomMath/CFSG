module

public import CFSG.RankThree.PartTwo.Sec21.IrreducibleTransvection
public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts.KP14 Matrix

variable {G : Type*} [Group G] {A : Subgroup G}

@[expose] noncomputable def glEquiv3 :
    GL (Fin 3) (ZMod 3) ≃* ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 3 → ZMod 3))

theorem glEquiv3_apply (g : GL (Fin 3) (ZMod 3)) (v : Fin 3 → ZMod 3) :
    glEquiv3 g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v := rfl

@[expose] noncomputable def coordLin3 (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    MulAut A →* ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :=
  @Sec12.coordHom G _ A (Fin 3 → ZMod 3) _ (Pi.Function.module _ _ _) f

theorem coordLin3_apply (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (φ : MulAut A)
    (v : Fin 3 → ZMod 3) :
    coordLin3 f φ v = Multiplicative.toAdd (f.symm (φ (f (Multiplicative.ofAdd v)))) := rfl

theorem coordLin3_injective (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    Function.Injective (coordLin3 f) :=
  @Sec12.coordHom_injective G _ A (Fin 3 → ZMod 3) _ (Pi.Function.module _ _ _) f

@[expose] noncomputable def coordGL (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    MulAut A →* GL (Fin 3) (ZMod 3) :=
  glEquiv3.symm.toMonoidHom.comp (coordLin3 f)

theorem coordGL_mulVec (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (φ : MulAut A)
    (v : Fin 3 → ZMod 3) :
    ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
      coordLin3 f φ v := by
  rw [← glEquiv3_apply, coordGL, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem coordGL_injective (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    Function.Injective (coordGL f) :=
  glEquiv3.symm.injective.comp (coordLin3_injective f)

theorem mem_commOf_iff (hA : IsMulCommutative A) (φ : MulAut A) (x : A) :
    x ∈ commOf φ ↔ ∃ a : A, a⁻¹ * φ a = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨1, by rw [map_one, inv_one, one_mul]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      refine ⟨a * b, ?_⟩
      rw [map_mul, _root_.mul_inv_rev]
      have hc := hA.is_comm.comm
      calc b⁻¹ * a⁻¹ * (φ a * φ b) = a⁻¹ * φ a * (b⁻¹ * φ b) := by
            rw [hc b⁻¹ a⁻¹, mul_assoc, ← mul_assoc b⁻¹, hc b⁻¹ (φ a)]
            group
    | inv y _ hy =>
      obtain ⟨a, rfl⟩ := hy
      refine ⟨a⁻¹, ?_⟩
      rw [map_inv, inv_inv, _root_.mul_inv_rev, inv_inv, hA.is_comm.comm]
  · rintro ⟨a, rfl⟩
    exact Subgroup.subset_closure ⟨a, rfl⟩

theorem card_commOf_eq_range (hA : IsMulCommutative A) {V : Type*} [AddCommGroup V]
    [Module (ZMod 3) V] (f : Multiplicative V ≃* A) (φ : MulAut A) :
    Nat.card (commOf φ) = Nat.card (Set.range fun v : V => Sec12.coordHom f φ v - v) := by
  set g : V → A := fun v => f (Multiplicative.ofAdd v)
  have hg : Function.Injective g := fun v w h =>
    Multiplicative.ofAdd.injective (f.injective h)
  have key : ∀ w : V, g (Sec12.coordHom f φ w - w) = (g w)⁻¹ * φ (g w) := by
    intro w
    rw [sub_eq_neg_add, Sec12.coordHom_apply]
    simp only [g, ofAdd_add, ofAdd_neg, map_mul, map_inv, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hset : (commOf φ : Set A) = g '' Set.range fun v : V => Sec12.coordHom f φ v - v := by
    ext x
    rw [SetLike.mem_coe, mem_commOf_iff hA, ← Set.range_comp, Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨Multiplicative.toAdd (f.symm a), ?_⟩
      rw [Function.comp_apply, key]
      simp [g]
    · rintro ⟨w, rfl⟩
      exact ⟨g w, (key w).symm⟩
  rw [← Nat.card_image_of_injective hg, ← hset]
  rfl

theorem card_commOf_eq (hA : IsMulCommutative A) (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (φ : MulAut A) :
    Nat.card (commOf φ) = Nat.card (Set.range fun v : Fin 3 → ZMod 3 =>
      (((coordGL f φ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) *ᵥ v) := by
  refine (@card_commOf_eq_range G _ A hA (Fin 3 → ZMod 3) _ (Pi.Function.module _ _ _) f
    φ).trans ?_
  have h1 : ∀ w : Fin 3 → ZMod 3,
      (((coordGL f φ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) - 1) *ᵥ w =
        coordLin3 f φ w - w := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, coordGL_mulVec]
  simp only [h1]
  rfl

theorem isReflectionOn_iff (hA : IsMulCommutative A) (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (φ : MulAut A) : IsReflectionOn φ ↔ IsReflection (coordGL f φ) := by
  rw [IsReflectionOn, IsReflection, orderOf_injective (coordGL f) (coordGL_injective f) φ,
    card_commOf_eq hA f φ]

theorem not_isTransvectionOn_of_mem_monomial (hA : IsMulCommutative A)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {φ : MulAut A} (hφ : coordGL f φ ∈ monomial) :
    ¬ IsTransvectionOn φ := by
  intro hT
  obtain ⟨v, ψ, h⟩ := @exists_isTransvectionWith_coordHom G _ A hA (Fin 3 → ZMod 3) _
    (Pi.Function.module _ _ _) f φ hT
  exact @not_isTransvectionWith (coordGL f φ) hφ (Fin 3 → ZMod 3) _ (Pi.Function.module _ _ _)
    (@LinearEquiv.refl (ZMod 3) (Fin 3 → ZMod 3) _ _ (Pi.Function.module _ _ _))
    (coordLin3 f φ) (fun x => (coordGL_mulVec f φ x).symm) v ψ h

theorem image_eq_swapRefl_or_eq_monoRefl (hA : IsMulCommutative A)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {G₀ : Subgroup (MulAut A)}
    (hG₀ : G₀.map (coordGL f) ≤ monomial)
    (e : (G₀.map (coordGL f)) ≃* alternatingGroup (Fin 4)) {D : Set (MulAut A)}
    (hD : ∀ d ∈ D, coordGL f d ∈ monomial) (hDr : ∀ d ∈ D, IsReflectionOn d)
    (hinv : ∀ g ∈ G₀, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hst : ∃ s ∈ D, ∃ t ∈ D, s * t ≠ t * s) :
    coordGL f '' D = swapRefl ∨ coordGL f '' D = monoRefl := by
  refine eq_swapRefl_or_eq_monoRefl_of_alternating hG₀ e ?_ ?_ ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact hD d hd
  · rintro _ ⟨d, hd, rfl⟩
    exact (isReflectionOn_iff hA f d).mp (hDr d hd)
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ⟨g * d * g⁻¹, hinv g hg d hd, by rw [map_mul, map_mul, map_inv]⟩
  · obtain ⟨s, hs, t, ht, hst⟩ := hst
    refine ⟨coordGL f s, ⟨s, hs, rfl⟩, coordGL f t, ⟨t, ht, rfl⟩, fun h => hst ?_⟩
    apply coordGL_injective f
    rw [map_mul, map_mul, h]

end CFSG.RankThree.PartTwo.Sec21
