module

public import CFSG.GroupTheory.AutomorphismFixedSubgroupSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldDiag
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Chevalley.G2Rank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.Exceptional
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.E6Descent
open CFSG.RankThree.Chevalley.SteinbergBT


theorem isSimpleGroup_adjoint_odd {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : 3 ≤ Nat.card K) : IsSimpleGroup (adjointGroup τ K) := by
  rcases hτ with rfl | hE
  · exact CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 hK
  · have hq : CFSG.IsQuasisimple (adjointGroup τ K) := by
      rcases hE with rfl | rfl | rfl | rfl
      · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K
      · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K
      · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K
      · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K
    exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field τ K)).trans
        QuotientGroup.quotientBot).symm

theorem fieldAutOdd_adjoint_of_conjugate {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hr : r.Prime) (σ : K ≃+* K) (hσ : orderOf σ = r)
    (θ δ : MulAut (adjointGroup τ K)) (hδ : δ * θ * δ⁻¹ = entrywiseAdjointAut τ σ) :
    r ∣ f ∧ ∃ Y : Subgroup (adjointGroup τ K), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hrf, hcard⟩ := card_fixSubfield hp hf hK σ
  rw [hσ] at hrf hcard
  let k := fixSubfield σ
  have he : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hk : 3 ≤ Nat.card k := by
    rw [hcard]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have : IsSimpleGroup (adjointGroup τ k) := isSimpleGroup_adjoint_odd hτ hk
  have : CharP k p := CFSG.SectionRank.charP_of_natCard_eq_pow hcard
  have hrank : 2 ≤ CFSG.pRank p (adjointGroup τ k) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    rcases hτ with rfl | hτ
    · have h := three_mul_le_pRank_G2 hcard
      omega
    · have h := four_mul_le_pRank hτ hcard
      omega
  let ι := δ.symm.toMonoidHom.comp (fixedFieldInclusion (τ := τ) σ)
  have hι : Function.Injective ι := δ.symm.injective.comp (fixedFieldInclusion_injective σ)
  have hθ : θ = δ⁻¹ * entrywiseAdjointAut τ σ * δ := by
    rw [← hδ]
    group
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    change θ (δ.symm (fixedFieldInclusion σ y)) = δ.symm (fixedFieldInclusion σ y)
    simp only [hθ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    exact congrArg δ.symm (CFSG.StandardType.entrywise_fixedFieldInclusion σ y)
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

theorem fieldAutOdd_adjointG2 {K : Type} [Field K] [Finite K] {p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut (adjointGroup .G2 K))
    (hθ : orderOf θ = r) (hout : θ ∉ (MulAut.conj : adjointGroup .G2 K →*
      MulAut (adjointGroup .G2 K)).range) :
    r ∣ f ∧ ∃ Y : Subgroup (adjointGroup .G2 K), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.charP_of_natCard_eq_pow hK
  obtain ⟨x, σ, hσ, hform⟩ : ∃ (x : adjointGroup .G2 K) (σ : K ≃+* K),
      orderOf σ = r ∧ θ = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    by_cases hp3 : p = 3
    · subst p
      exact G2_form_three hf K hK hr (by omega) θ hθ hout
    · exact G2_form_odd hp hp2 hp3 hf K hK hr θ hθ hout
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form .G2 hp hf K hK hr θ hθ
    x σ hσ hform
  exact fieldAutOdd_adjoint_of_conjugate (Or.inl rfl) hp hp2 hf hK hr σ hσ θ δ hδ

theorem fieldAutOdd_adjointE {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (θ : MulAut (adjointGroup τ K))
    (hθ : orderOf θ = r) (hout : θ ∉ (MulAut.conj : adjointGroup τ K →*
      MulAut (adjointGroup τ K)).range) :
    r ∣ f ∧ ∃ Y : Subgroup (adjointGroup τ K), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.charP_of_natCard_eq_pow hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨σ, δ, hσ, hδ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.exists_conj_entrywise_exc_of_diag hτ hK2
      hr (by omega) (fun _ => Or.inl (by omega)) (hθ ▸ pow_orderOf_eq_one θ) hout
  exact fieldAutOdd_adjoint_of_conjugate (Or.inr hτ) hp hp2 hf hK hr σ hσ θ δ hδ

theorem fieldAutOdd_untwisted {X : Type} [Group X] [Finite X] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hX : UntwistedChevalleyModel X τ (p ^ f)) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r) (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := hX
  let e := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field τ K)).trans QuotientGroup.quotientBot)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun α : MulAut (adjointGroup τ K) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  obtain ⟨hrf, Y, hY, hs, hrank⟩ :
      r ∣ f ∧ ∃ Y : Subgroup (adjointGroup τ K),
        Y ≤ signalizerFixedSubgroup (MulAut.congr e θ) ∧ IsSimpleGroup Y ∧
          2 ≤ CFSG.pRank p Y := by
    rcases hτ with rfl | hτ
    · exact fieldAutOdd_adjointG2 hp hp2 hf hK hr hr5 (MulAut.congr e θ) hθ' hout'
    · exact fieldAutOdd_adjointE hτ hp hp2 hf hK hr hr5 (MulAut.congr e θ) hθ' hout'
  have : IsSimpleGroup Y := hs
  let ι := e.symm.toMonoidHom.comp Y.subtype
  have hι : Function.Injective ι := e.symm.injective.comp Y.subtype_injective
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    apply e.injective
    have hy : (MulAut.congr e θ) y = y := hY y.2
    simpa [ι, MulAut.congr_apply] using hy
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
