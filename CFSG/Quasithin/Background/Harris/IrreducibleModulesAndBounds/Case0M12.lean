module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12Rep
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12Classify
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12
  CFSG.Blueprint Matrix

namespace Case0M12

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isPermCoreModule_of_rep10
    {L : Subgroup (GLV V)}
    (f : ↥L ≃* G12) (e : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2))
    (he : ∀ (g : G12) (v : V), e (((f.symm g : ↥L) : GLV V) v) = rep10 g *ᵥ e v) :
    IsPermCoreModule L NativeSporadic.M12 := by
  refine ⟨f, e.symm.toLinearMap ∘ₗ (Matrix.mulVecLin m12M ∘ₗ (permCore 12).subtype), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu, hMu⟩ := m12M_surjective (e x)
    refine ⟨⟨u, hu⟩, ?_⟩
    simp [hMu]
  · intro u
    have hsum : ∑ i, (u : Fin 12 → ZMod 2) i = 0 := u.2
    constructor
    · intro h
      have h1 : m12M *ᵥ (u : Fin 12 → ZMod 2) = 0 := by
        have : e.symm (m12M *ᵥ (u : Fin 12 → ZMod 2)) = 0 := h
        exact e.symm.map_eq_zero_iff.1 this
      rcases m12M_ker hsum h1 with h0 | h2
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr ⟨by decide, h2⟩
    · rintro (h0 | ⟨-, h1⟩)
      · rw [h0, map_zero]
      · have : (u : Fin 12 → ZMod 2) = fun _ => 1 := funext h1
        show e.symm (m12M *ᵥ (u : Fin 12 → ZMod 2)) = 0
        rw [this, m12M_ones, map_zero]
  · intro γ u u' hu'
    have hsum : ∑ i, (u : Fin 12 → ZMod 2) i = 0 := u.2
    show e.symm (m12M *ᵥ (u' : Fin 12 → ZMod 2)) = (γ : GLV V) (e.symm (m12M *ᵥ (u : Fin 12 → ZMod 2)))
    rw [hu', equivariant (f γ) hsum]
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    have := he (f γ) (e.symm (m12M *ᵥ (u : Fin 12 → ZMod 2)))
    rw [MulEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem endIsField_one_of_rep10
    [Finite V] {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤)
    (f : ↥L ≃* G12) (e : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2))
    (he : ∀ (g : G12) (v : V), e (((f.symm g : ↥L) : GLV V) v) = rep10 g *ᵥ e v) :
    EndIsField L 1 := by
  have hscalar : ∀ φ ∈ endCommutant L, ∃ c : ZMod 2, φ = c • (1 : Module.End (ZMod 2) V) := by
    intro φ hφ
    let E : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
      e.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap
    have hE : ∀ y, E y = e (φ (e.symm y)) := fun y => rfl
    have hcomm : ∀ g : G12, LinearMap.toMatrix' E * rep10 g = rep10 g * LinearMap.toMatrix' E := by
      intro g
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro y
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
        LinearMap.toMatrix'_mulVec, hE, hE]
      have h1 : e.symm (rep10 g *ᵥ y) = ((f.symm g : ↥L) : GLV V) (e.symm y) := by
        apply e.injective
        rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rw [h1, OrdinaryProofs.endCommutant_apply_comm hφ (f.symm g).2, he]
    obtain ⟨c, hc⟩ := rep10_endo_scalar _ hcomm
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    apply e.injective
    have h1 : E (e v) = c • e v := by
      rw [← LinearMap.toMatrix'_mulVec, hc]
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hE, LinearEquiv.symm_apply_apply] at h1
    rw [h1]
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (endCommutant L)) := by
    intro φ
    obtain ⟨c, hc⟩ := hscalar φ.1 φ.2
    refine ⟨c, Subtype.ext ?_⟩
    rw [hc]
    simp [Algebra.algebraMap_eq_smul_one]
  have hle : Nat.card (endCommutant L) ≤ 2 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_zmod] at this
  have := OrdinaryProofs.endCommutant_nontrivial hirr
  obtain ⟨e', ⟨ε⟩⟩ := OrdinaryProofs.exists_endIsField hirr (V := V)
  have : Finite (endCommutant L) := Finite.of_surjective _ hsurj
  have hge : 2 ≤ Nat.card (endCommutant L) := Finite.one_lt_card
  have hcard : Nat.card (GaloisField 2 e') = 2 ^ 1 := by
    rw [← Nat.card_congr ε.toEquiv]
    omega
  exact ⟨ε.trans (GaloisField.algEquivGaloisField 2 1 hcard)⟩

end Case0M12

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem m12_data
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M12)) :
    m = 4 ∧ Module.finrank (ZMod 2) V = 10 ∧
      ∃ (f : ↥L ≃* CFSG.Quasithin.B45Mat.M12.G12) (e : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)),
        ∀ (g : CFSG.Quasithin.B45Mat.M12.G12) (v : V),
          e (((f.symm g : ↥L) : GLV V) v) = rep10 g *ᵥ e v := by
  obtain ⟨eq⟩ := hM
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover h.L_comp.2.2 h.H_irr eq m12_cover
  have hm : m ≤ 4 := m_le_of_autRank h f m12_autRank
  have hb := h.bound
  obtain ⟨e, he⟩ := Case0M12.m12_classify h.H_irr f (by omega)
  have hd : Module.finrank (ZMod 2) V = 10 := by
    rw [e.finrank_eq]
    simp
  exact ⟨by omega, hd, f, e, he⟩

theorem case0_M12
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M12)) :
    G93Case0 L m := by
  obtain ⟨hm, hd, f, e, he⟩ := m12_data h hM
  have hperm := Case0M12.isPermCoreModule_of_rep10 f e he
  exact ⟨⟨hm, hd, hperm⟩, Case0M12.endIsField_one_of_rep10 h.H_irr f e he,
    Case0M12.selfDual_of_isPermCoreModule (by decide) hperm⟩

theorem case0_M12_concl
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M12)) :
    G93Concl Γ L m :=
  Or.inl (case0_M12 h hM)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
