module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.KGFactL33Mat

public section

namespace CFSG.Quasithin.ModH

variable {G : Type} [Group G] {L I : Subgroup G}

@[expose] noncomputable def quotConj (g : Subgroup.normalizer (L : Set G)) : MulAut (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (L.normalizerMonoidHom g)
    (Subgroup.map_center_eq _)

theorem quotConj_mk (g : Subgroup.normalizer (L : Set G)) (l : ↥L) :
    quotConj g (QuotientGroup.mk l) = QuotientGroup.mk (L.normalizerMonoidHom g l) := rfl

@[expose] noncomputable def quotConjHom : (Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ Subgroup.center ↥L) where
  toFun := quotConj
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H a =>
      change QuotientGroup.mk (L.normalizerMonoidHom 1 a) = QuotientGroup.mk a
      simp
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H a =>
      change QuotientGroup.mk (L.normalizerMonoidHom (g * h) a) =
        QuotientGroup.mk (L.normalizerMonoidHom g (L.normalizerMonoidHom h a))
      simp

theorem exists_rho (hLI : L ≤ I) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hinn : ∀ α : MulAut (↥L ⧸ Subgroup.center ↥L), ∃ q, MulAut.conj q = α)
    (hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥) :
    ∃ ρ : ↥I →* (↥L ⧸ Subgroup.center ↥L),
      (∀ (i : ↥I) (l : ↥L), ρ i * QuotientGroup.mk l * (ρ i)⁻¹ =
        QuotientGroup.mk (L.normalizerMonoidHom ⟨i, hN i.2⟩ l)) ∧
      (∀ l : ↥L, ρ ⟨l, hLI l.2⟩ = QuotientGroup.mk l) := by
  have hsurj : Function.Surjective (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* _) := fun α => hinn α
  have hinj : Function.Injective (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* _) := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h : a * x * a⁻¹ = b * x * b⁻¹ := by
        have := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ x) hab
        simpa using this
      have h2 : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
        calc (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
          _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [h]
          _ = x := by group
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [hcen, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    MulEquiv.ofBijective (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* _) ⟨hinj, hsurj⟩
  let ρ : ↥I →* (↥L ⧸ Subgroup.center ↥L) :=
    e.symm.toMonoidHom.comp (quotConjHom.comp (Subgroup.inclusion hN))
  have hconj : ∀ i : ↥I, MulAut.conj (ρ i) = quotConj (L := L) ⟨i, hN i.2⟩ := by
    intro i
    have h := e.apply_symm_apply (quotConj (L := L) ⟨i, hN i.2⟩)
    exact h
  refine ⟨ρ, fun i l => ?_, fun l => ?_⟩
  · have := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ (QuotientGroup.mk l)) (hconj i)
    simpa [quotConj_mk] using this
  · apply hinj
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h1 := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ (QuotientGroup.mk a))
        (hconj ⟨l, hLI l.2⟩)
      simp only [quotConj_mk, MulAut.conj_apply] at h1 ⊢
      rw [h1]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp

end CFSG.Quasithin.ModH
