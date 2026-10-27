module

public import CFSG.Quasithin.Background.SmithB42Sp4Ident
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.B42Sp4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7b CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

theorem exists_antiSp_equiv {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {f : ℕ}
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 2 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* antiSp K) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card_pow hcard
  let e₁ : X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨K, hK, Fintype.ofFinite K, inferInstance, hcard,
    ⟨(e₁.trans e).trans (antiProjEquiv K).symm⟩⟩

section Real

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem binaryNaturalSp4_of_coords {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (θL : ↥L ≃* antiSp K) (i : ℕ)
    (φ : W ≃+ (Fin 4 → K))
    (hφ : ∀ (g : antiSp K) (w : W), φ (binPsi θ ((θL.symm g : ↥L) : MulAut V) w) =
      (glMat (((minorAut K ^ i) g : antiSp K) : GL (Fin 4) K)).mulVec (φ w)) :
    BinaryNaturalSp4 L ⊤ ⊥ f := by
  let ε : StatedSp 2 K ≃* ↥L :=
    ((antiSpEquiv K).symm.trans (minorAut K ^ i).symm).trans θL.symm
  have hε : ∀ γ : StatedSp 2 K,
      (minorAut K ^ i) (θL (ε γ)) = (antiSpEquiv K).symm γ := fun γ => by
    simp [ε]
  let β : V →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd fun j => φ (Multiplicative.toAdd (θ v)) (antiIdx j)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext j
        simp
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        funext j
        simp }
  have hβ : ∀ v, Multiplicative.toAdd (β v) =
      fun j => φ (Multiplicative.toAdd (θ v)) (antiIdx j) := fun v => rfl
  refine ⟨K, inferInstance, inferInstance, hK, ε.toMonoidHom, ?_⟩
  refine G64.realizesVia_nat_of ε.surjective le_top (fun _ _ _ => trivial)
    (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one])
    (β.comp (⊤ : Subgroup V).subtype) ?_ ?_ ?_
  · intro y
    refine ⟨⟨θ.symm (Multiplicative.ofAdd (φ.symm fun a => Multiplicative.toAdd y
      (antiIdx.symm a))), trivial⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext j
    simp [hβ]
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : ∀ j, φ (Multiplicative.toAdd (θ u)) (antiIdx j) = 0 := fun j =>
        congrFun (congrArg Multiplicative.toAdd h1) j
      have h3 : φ (Multiplicative.toAdd (θ u)) = 0 := by
        funext a
        have := h2 (antiIdx.symm a)
        simpa using this
      have h4 : Multiplicative.toAdd (θ u) = 0 := by
        rw [← map_zero φ] at h3
        exact φ.injective h3
      have h5 : θ u = 1 := Multiplicative.toAdd.injective h4
      simpa using congrArg θ.symm h5
    · intro h1
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, h1, map_one]
  · intro γ u hu
    apply Multiplicative.toAdd.injective
    have hθ : Multiplicative.toAdd (θ (((ε γ : ↥L) : MulAut V) (u : V))) =
        binPsi θ (((θL.symm (θL (ε γ))) : ↥L) : MulAut V) (Multiplicative.toAdd (θ u)) := by
      rw [MulEquiv.symm_apply_apply, B42L2.toAdd_binPsi]
    have h1 := hφ (θL (ε γ)) (Multiplicative.toAdd (θ u))
    rw [← hθ, hε] at h1
    show (fun j => φ (Multiplicative.toAdd (θ (((ε γ : ↥L) : MulAut V) (u : V)))) (antiIdx j)) =
      ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (fun j => φ (Multiplicative.toAdd (θ u)) (antiIdx j))
    rw [h1]
    have h2 : ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (glMat (((antiSpEquiv K).symm γ : antiSp K) : GL (Fin 4) K)).submatrix antiIdx antiIdx := by
      rw [← spMat_antiSpEquiv, MulEquiv.apply_symm_apply]
    have h3 : (fun j => φ (Multiplicative.toAdd (θ u)) (antiIdx j)) ∘ antiIdx.symm =
        φ (Multiplicative.toAdd (θ u)) := by
      funext a
      simp
    rw [h2, Matrix.submatrix_mulVec_equiv, h3]
    rfl

theorem binaryNaturalSp4_of_offender_core
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hZ : Subgroup.center ↥L = ⊥) {f : ℕ}
    (hf : 2 ≤ f) (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : BinaryNaturalSp4 L ⊤ ⊥ f := by
  obtain ⟨K, _, _, _, hK, ⟨θL⟩⟩ := exists_antiSp_equiv hZ hmodel
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  set ψ := binPsi θ with hψ
  let πW : antiSp K →* (W ≃ₗ[ZMod 2] W) :=
    ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)
  have hπW : ∀ g, πW g = ψ ((θL.symm g : ↥L) : MulAut V) := fun g => rfl
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2
  have hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, πW g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrV U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (θL ⟨l, hl⟩) u hu
    rwa [hπW, MulEquiv.symm_apply_apply] at h1
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set A₀ := A.map ψ.toMonoidHom with hA₀
  have hnorm : ∀ a ∈ A₀, ∀ x, ∃ y, a * πW x * a⁻¹ = πW y := by
    rintro _ ⟨a, ha, rfl⟩ x
    have hl : a * ((θL.symm x : ↥L) : MulAut V) * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp
        ((hA.1.trans (B42L2.le_normalizer_of_b4HypCore hHyp)) ha) _).mp (θL.symm x).2
    refine ⟨θL ⟨_, hl⟩, ?_⟩
    rw [hπW (θL _), MulEquiv.symm_apply_apply, hπW x]
    change ψ a * ψ ((θL.symm x : ↥L) : MulAut V) * (ψ a)⁻¹ =
      ψ (a * ((θL.symm x : ↥L) : MulAut V) * a⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hA1 : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff_of_injective A ψ.injective]
    exact hA.2.1
  have hoff : Nat.card W ≤ Nat.card A₀ * Nat.card {m : W // ∀ a ∈ A₀, a m = m} := by
    have h1 := weight_map θ A
    have h2 := B42L2.card_le_of_offender hA
    rw [natCard_eq θ] at h2
    calc Nat.card W ≤ Nat.card A * Nat.card (fixV A) := h2
      _ = _ := h1.symm
  obtain ⟨i, φ, hφ⟩ := exists_natural_of_offender hf hK πW
    (fun g g' h => θL.symm.injective (Subtype.ext (ψ.injective h))) hntW hirr A₀ hnorm
    (by rw [hA₀]; exact (isElemAbelian2_iff_map θ A).1 hA.2.2.1) hA1 hoff
  exact binaryNaturalSp4_of_coords θ hK θL i φ hφ

theorem binaryNaturalSp4_of_offender (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥) {f : ℕ}
    (hf : 2 ≤ f) (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : BinaryNaturalSp4 L ⊤ ⊥ f :=
  binaryNaturalSp4_of_offender_core hV hHyp.core hZ hf hmodel hA

end Real

end CFSG.Quasithin.B42Sp4
