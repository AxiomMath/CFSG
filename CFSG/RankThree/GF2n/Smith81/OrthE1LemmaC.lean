module

public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCForms
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCSplit

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.Open Module

theorem lcData_of_acts {K : Type} [Field K] [CharP K 2] (S : QSpace K)
    (V : Submodule K S.E) (Xg : Subgroup (S.E ≃ₗ[K] S.E)) (hXO : Xg ≤ S.O) (hts : S.IsTS V)
    (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V) (hV : Module.finrank K V = 4)
    (hE : Module.finrank K S.E = 8) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ↥V ≃ₗ[K] (ι → K)) (f : (ι → K) → K) (P : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K)
    (hP : IsPolarOf f P) (hnd : ∀ x, (∀ y, P x y = 0) → x = 0)
    (hirr : ∀ A : Matrix ι ι K, (∀ g ∈ StatedOmega f,
        A * (g : Matrix ι ι K) = (g : Matrix ι ι K) * A) → ∃ k : K, A = k • (1 : Matrix ι ι K))
    (hact : ActsAsNatural S V Xg c f) : Nonempty (LCData S V Xg) := by
  obtain ⟨hX, h1, h2, -⟩ := hact
  let act : ↥Xg → V →ₗ[K] V := fun g => ((g : S.E ≃ₗ[K] S.E) : S.E →ₗ[K] S.E).restrict (hX g g.2)
  have hc : ∀ g : ↥Xg, ∃ A ∈ StatedOmega f, ∀ v : V, c (act g v) = (A : Matrix ι ι K) *ᵥ c v := by
    intro g
    obtain ⟨A, hA, hAe⟩ := h1 g g.2
    exact ⟨A, hA, fun v => hAe v v.2⟩
  refine ⟨
    { O_le := hXO
      ts := hts
      perp := hperp
      dimV := hV
      dimE := hE
      act := act
      act_coe := fun _ _ => rfl
      pf := P.compl₁₂ c.toLinearMap c.toLinearMap
      pf_nondeg := fun v hv => by
        apply c.injective
        rw [map_zero]
        apply hnd
        intro y
        have := hv (c.symm y)
        simpa [LinearMap.compl₁₂_apply] using this
      pf_alt := fun v => hP.alt (c v)
      pf_inv := fun g v w => by
        obtain ⟨A, hA, hAe⟩ := hc g
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
        rw [hAe v, hAe w]
        exact hP.map_apply (Matrix.mulVecLin A) (fun x => statedOmega_isometry f hA x) (c v) (c w)
      schur := fun a ha => by
        let L : (ι → K) →ₗ[K] (ι → K) := c.toLinearMap ∘ₗ a ∘ₗ c.symm.toLinearMap
        let M : Matrix ι ι K := LinearMap.toMatrix' L
        have hM : ∀ x, M *ᵥ x = L x := fun x => LinearMap.toMatrix'_mulVec L x
        obtain ⟨k, hk⟩ := hirr M (by
          intro A hA
          obtain ⟨g, hg, hgA⟩ := h2 A hA
          refine Matrix.ext_iff_mulVec.2 fun x => ?_
          have key : ∀ v : V, c (act ⟨g, hg⟩ v) = (A : Matrix ι ι K) *ᵥ c v :=
            fun v => hgA v v.2
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
          obtain ⟨v, rfl⟩ := c.surjective x
          simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
          rw [← key v, LinearEquiv.symm_apply_apply, ha ⟨g, hg⟩ v, key (a v)])
        refine ⟨k, fun v => ?_⟩
        apply c.injective
        have := hM (c v)
        rw [hk, Matrix.smul_mulVec, Matrix.one_mulVec] at this
        simpa [L, map_smul] using this.symm }⟩

theorem lcData_of (hKF1 : ParabolicStatement) (hKF2 : NatIrredStatement) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ (S : QSpace K), Module.finrank K S.E = 8 → S.IsHyp →
    ∀ (V : Submodule K S.E), S.IsTS V → Module.finrank K V = 4 →
    ∀ (Xg : Subgroup (S.E ≃ₗ[K] S.E)), Xg ≤ S.O →
      (∀ c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K), ActsAsNatural S V Xg c (StatedQuadPlus 2 K) →
        Nonempty (LCData S V Xg)) ∧
      (∀ (b c' : K), (∀ s : K, s ^ 2 + b * s + c' ≠ 0) →
        ∀ c : ↥V ≃ₗ[K] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
          ActsAsNatural S V Xg c (StatedQuadMinus 2 K b c') → Nonempty (LCData S V Xg)) := by
  intro K _ _ _ hK S h8 hyp V hTS hV Xg hXO
  have hperp := (hKF1 K hK S h8 hyp V hTS hV).1
  obtain ⟨hirrP, hirrM⟩ := hKF2 K hK
  refine ⟨fun c hc => ?_, fun b c' hb c hc => ?_⟩
  · obtain ⟨hirr1, -⟩ := hirrP
    exact lcData_of_acts S V Xg hXO hTS hperp hV h8 c (StatedQuadPlus 2 K)
      (plusPolar 2 K) plusPolar_isPolar plusPolar_nondeg hirr1 hc
  · obtain ⟨hirr1, -⟩ := hirrM b c' hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      obtain ⟨s, hs⟩ := isSquare_of_charTwo' c'
      apply hb s
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hs + s ^ 2 * h2
    exact lcData_of_acts S V Xg hXO hTS hperp hV h8 c (StatedQuadMinus 2 K b c')
      (minusPolar (2 - 1) K b) (minusPolar_isPolar c') (minusPolar_nondeg hb0) hirr1 hc

theorem lemmaC_of (hKF1 : ParabolicStatement) (hKF2 : NatIrredStatement) : LemmaCStatement := by
  intro K _ _ _ hK S h8 hyp V hTS hV Xg hXO
  obtain ⟨hP, hM⟩ := lcData_of hKF1 hKF2 K hK S h8 hyp V hTS hV Xg hXO
  exact ⟨fun c hc => (hP c hc).elim fun D => D.conclusion,
    fun b c' hb c hc => (hM b c' hb c hc).elim fun D => D.conclusion⟩

end CFSG.RankThree.GF2n.Smith81.Smith23E1
