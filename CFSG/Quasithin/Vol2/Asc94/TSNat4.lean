module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.Quasithin.A94.TS

open Subgroup
open scoped Matrix MatrixGroups

variable {G : Type} [Group G]

private theorem card_SL4_galois : Nat.card SL(4, GaloisField 2 1) = 20160 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero]
  decide

private noncomputable def zmodTwoEquivGalois : ZMod 2 ≃+* GaloisField 2 1 := by
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])

private theorem det_eq_one_galois (A : GL (Fin 4) (GaloisField 2 1)) :
    (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)).det = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  have h1 : Nat.card (GaloisField 2 1)ˣ = 1 := by rw [Nat.card_units, hcard]
  have hsub := (Nat.card_eq_one_iff_unique.1 h1).1
  have : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  exact congrArg Units.val this

private theorem isElementaryAbelian_of {E : Subgroup G}
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a) : IsElementaryAbelian 2 ↥E where
  is_comm := ⟨fun a b => Subtype.ext (hEe a a.2 b b.2).2⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simp [pow_two, (hEe g g.2 g g.2).1])

private theorem exists_coords16 [Finite G] {E : Subgroup G} (hE16 : Nat.card ↥E = 16)
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a) :
    Nonempty (Multiplicative (Fin 4 → ZMod 2) ≃* ↥E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isElementaryAbelian_of hEe
  open scoped IsMulCommutative in
  have hfin : Module.finrank (ZMod 2) (Additive ↥E) = 4 := by
    have h := FiniteField.pow_finrank_eq_natCard 2 (Additive ↥E)
    have h' : Nat.card (Additive ↥E) = 2 ^ 4 := hE16
    exact Nat.pow_right_injective le_rfl (h.trans h')
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive ↥E) hfin
  exact ⟨MulEquiv.toAdditiveRight.symm b.equivFun.symm.toAddEquiv⟩

section Coords

variable {E : Subgroup G} (f : Multiplicative (Fin 4 → ZMod 2) ≃* ↥E)

private noncomputable def coordLin16 (σ : MulAut ↥E) :
    (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  (AddEquiv.toMultiplicative.symm ((f.trans σ).trans f.symm)).toLinearEquiv fun c v => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

private theorem coordLin16_apply (σ : MulAut ↥E) (v : Fin 4 → ZMod 2) :
    coordLin16 f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) := rfl

private noncomputable def coordHom16 :
    MulAut ↥E →* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) where
  toFun := coordLin16 f
  map_one' := by ext v; simp [coordLin16_apply]
  map_mul' σ τ := by ext v; simp [coordLin16_apply]

private noncomputable def toGL16 :
    ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) ≃* GL (Fin 4) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

private theorem toGL16_mulVec (g : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (v : Fin 4 → ZMod 2) :
    (toGL16 g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = g v := by
  have h1 : Matrix.GeneralLinearGroup.toLin (toGL16 g) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2)).symm g :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2) =>
    (u : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2)) v) h1
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h2
  exact h2

private noncomputable def actGL16 : ↥(normalizer (E : Set G)) →* GL (Fin 4) (ZMod 2) :=
  toGL16.toMonoidHom.comp ((coordHom16 f).comp E.normalizerMonoidHom)

private theorem actGL16_mulVec (g : ↥(normalizer (E : Set G))) (v : Fin 4 → ZMod 2) :
    ((f (Multiplicative.ofAdd ((actGL16 f g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)) :
      ↥E) : G) =
      (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  rw [actGL16, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    toGL16_mulVec]
  show ((f (Multiplicative.ofAdd (coordLin16 f _ v)) : ↥E) : G) = _
  rw [coordLin16_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rfl

private theorem actGL16_eq_one_iff (g : ↥(normalizer (E : Set G))) :
    actGL16 f g = 1 ↔ ∀ e ∈ E, (g : G) * e = e * g := by
  constructor
  · intro h e he
    have := actGL16_mulVec f g (Multiplicative.toAdd (f.symm ⟨e, he⟩))
    rw [h, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd, MulEquiv.apply_symm_apply] at this
    calc (g : G) * e = ((g : G) * e * (g : G)⁻¹) * g := by group
      _ = e * g := by rw [← this]
  · intro h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    apply (Multiplicative.ofAdd.trans f.toEquiv).injective
    apply Subtype.ext
    show ((f (Multiplicative.ofAdd ((actGL16 f g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)) :
      ↥E) : G) = (f (Multiplicative.ofAdd v) : G)
    rw [actGL16_mulVec]
    have := h _ (f (Multiplicative.ofAdd v)).2
    calc (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ =
        ((f (Multiplicative.ofAdd v) : G) * g) * (g : G)⁻¹ := by rw [this]
      _ = _ := by group

end Coords

theorem naturalSL_of_card_four [Finite G] {E : Subgroup G} (hE16 : Nat.card ↥E = 16)
    (hEe : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a)
    (hC : ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hM : Nat.card ↥(normalizer (E : Set G)) = 322560) :
    CFSG.CGT.Timmesfeld75.NaturalSL E (normalizer (E : Set G)) 4 1 := by
  classical
  obtain ⟨f⟩ := exists_coords16 hE16 hEe
  set σ := zmodTwoEquivGalois with hσ
  set M := normalizer (E : Set G) with hMdef
  let ρ : ↥M →* GL (Fin 4) (ZMod 2) := actGL16 f
  let ρ' : ↥M →* SL(4, GaloisField 2 1) :=
    { toFun := fun m => ⟨(ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ, by
        have := det_eq_one_galois ((Matrix.GeneralLinearGroup.map (σ : ZMod 2 →+* _)) (ρ m))
        simpa [Matrix.GeneralLinearGroup.map] using this⟩
      map_one' := by
        apply Subtype.ext
        simp [Matrix.map_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show (ρ (a * b) : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ =
          (ρ a : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ *
            (ρ b : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ
        rw [map_mul, Units.val_mul]
        exact Matrix.map_mul (f := (σ : ZMod 2 →+* GaloisField 2 1)) }
  have hρ' : ∀ m, ((ρ' m : SL(4, GaloisField 2 1)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) =
      (ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).map σ := fun m => rfl
  have hker : ρ'.ker = E.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ρ m = 1 := by
        apply Units.ext
        have h2 := congrArg (fun A : SL(4, GaloisField 2 1) =>
          ((A : Matrix (Fin 4) (Fin 4) (GaloisField 2 1))).map σ.symm) h
        simp only [hρ', Matrix.map_map] at h2
        have hid : (⇑σ.symm ∘ ⇑σ) = id := funext σ.symm_apply_apply
        rw [hid, Matrix.map_id] at h2
        rw [h2]
        simp
      exact hC m ((actGL16_eq_one_iff f m).1 h1)
    · intro hm
      have h1 : ρ m = 1 := (actGL16_eq_one_iff f m).2 fun e he => (hEe _ hm e he).2
      apply Subtype.ext
      rw [hρ', h1]
      simp
  have hsurj : Function.Surjective ρ' := by
    have h1 := Subgroup.card_mul_index ρ'.ker
    rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : E ≤ M)).toEquiv, hE16, hM] at h1
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [card_SL4_galois]
    omega
  let τ : (Fin 4 → ZMod 2) ≃+ (Fin 4 → GaloisField 2 1) :=
    AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  let φ : ↥E ≃* Multiplicative (Fin 4 → GaloisField 2 1) :=
    f.symm.trans (AddEquiv.toMultiplicative τ)
  have hφ : ∀ t : ↥E, Multiplicative.toAdd (φ t) = σ ∘ Multiplicative.toAdd (f.symm t) :=
    fun t => rfl
  have hN : (E.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  refine ⟨hN, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj), φ, ?_⟩
  intro h t hmem
  have he : ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj)) (QuotientGroup.mk h) = ρ' h := rfl
  rw [he]
  apply Multiplicative.toAdd.injective
  rw [hφ, toAdd_ofAdd, hφ, hρ']
  have hact := actGL16_mulVec f h (Multiplicative.toAdd (f.symm t))
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at hact
  have hfeq : f.symm ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
      Multiplicative.ofAdd ((ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (f.symm t)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hact.symm
  rw [hfeq, toAdd_ofAdd]
  funext i
  exact RingHom.map_mulVec (σ : ZMod 2 →+* GaloisField 2 1) _ _ i

end CFSG.Quasithin.A94.TS
