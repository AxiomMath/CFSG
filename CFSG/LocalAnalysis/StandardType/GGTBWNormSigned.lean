module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Pi

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusWNormSC_of_outdiagPrime {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I)
    (h : GGTorusWNormSC p R (Set.range (MulAut.conj : R →* MulAut R))) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI
  refine h L' ψ hψ hker hperf A hA ?_
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  have hφp : φ ^ p = 1 := TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hφ p) (by
    intro l
    rw [hA.2 a ha]
    rfl)
  exact ⟨φ, hI φ hφI hφp, hφ⟩

theorem ggWNormConcl_of_signed {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y]
    [Finite Y] {A : Subgroup Y} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    {ψ' : MulAut ↥A} {k : ℕ} (hk : 3 ≤ k) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    {w : MulAut ↥A} (hwin : ggLin (p := p) ι w ∈ ggHL ι φ h α)
    (hws : IsSignedPerm ⇑((MulAut.congr Θ).symm w)) {c : ℕ} (hc : ∀ a, ψ' a = (w a) ^ c) :
    GGWNormConcl ι φ h α ψ' := by
  have hscalar : ∀ v : V, ggLin (p := p) ι ψ' v = (c : ZMod p) • ggLin (p := p) ι w v := by
    intro v
    obtain ⟨a, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
    change ggLin (p := p) ι ψ' (ι (Additive.ofMul a)) =
      (c : ZMod p) • ggLin (p := p) ι w (ι (Additive.ofMul a))
    rw [ggLin_apply_ofMul, hc, ofMul_pow, map_nsmul, ggLin_apply_ofMul,
      Nat.cast_smul_eq_nsmul (ZMod p)]
  let ξ : Additive (Fin k → Multiplicative (ZMod p)) ≃+ (Fin k → ZMod p) :=
    (MulEquiv.toAdditive (MulEquiv.piMultiplicative (fun _ : Fin k => ZMod p)).symm).trans
      (AddEquiv.additiveMultiplicative (Fin k → ZMod p))
  let η : (Fin k → ZMod p) ≃+ V :=
    ξ.symm.trans ((MulEquiv.toAdditive Θ).trans ι)
  let T : (Fin k → ZMod p) ≃ₗ[ZMod p] V :=
    LinearEquiv.ofBijective (η.toAddMonoidHom.toZModLinearMap p) η.bijective
  let b : Module.Basis (Fin k) (ZMod p) V := (Pi.basisFun (ZMod p) (Fin k)).map T
  have hb (i : Fin k) : b i = ι (Additive.ofMul (Θ (Pi.mulSingle i (ofAdd 1)))) := by
    change T ((Pi.basisFun (ZMod p) (Fin k)) i) = _
    rw [Pi.basisFun_apply]
    change η (Pi.single i 1) = _
    apply congrArg ι
    apply congrArg Additive.ofMul
    apply congrArg Θ
    ext j
    change (Pi.single i (1 : ZMod p) : Fin k → ZMod p) j =
      toAdd ((Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin k → Multiplicative (ZMod p)) j)
    simp [Pi.single_apply, toAdd_mulSingle, eq_comm]
  have hb0 : b (⟨0, by omega⟩ : Fin k) ≠ 0 := b.ne_zero _
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro hcz
    have hzero := hscalar ((ggLin (p := p) ι w).symm (b ⟨0, by omega⟩))
    rw [hcz, zero_smul] at hzero
    have hx : (ggLin (p := p) ι w).symm (b ⟨0, by omega⟩) = 0 :=
      (ggLin (p := p) ι ψ').injective (hzero.trans (map_zero _).symm)
    have hz := congrArg (ggLin (p := p) ι w) hx
    rw [LinearEquiv.apply_symm_apply, map_zero] at hz
    exact hb0 hz
  refine ⟨⟨Units.mk0 (c : ZMod p) hc0, ggLin (p := p) ι w, hwin, hscalar⟩, fun href => ?_⟩
  have : Finite V := Finite.of_equiv ↥A (Additive.ofMul.trans ι.toEquiv)
  obtain ⟨π, ε, hε, hrel⟩ := hws
  have hwc : (MulAut.congr Θ).symm w =
      permAut π * diagAut ε (fun i => coord_sign_mul_self (hε i)) := by
    apply MulEquiv.ext
    intro f
    apply eq_of_toAdd_perm_eq π
    intro i
    rw [hrel, MulAut.mul_apply, permAut_apply]
    simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, diagAut_apply,
      toAdd_ofAdd]
  have hwb (i : Fin k) : ggLin (p := p) ι w (b i) = ε i • b (π i) := by
    rw [hb, ggLin_apply_ofMul]
    have hwa : w (Θ (Pi.mulSingle i (ofAdd 1))) =
        Θ (Pi.mulSingle (π i) (ofAdd (ε i))) := by
      have h := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod p)) =>
        u (Pi.mulSingle i (ofAdd 1))) hwc
      rw [MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle] at h
      simpa only [mul_one, MulAut.congr_symm_apply, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using congrArg Θ h
    rw [hwa]
    have ht : T (ε i • (Pi.basisFun (ZMod p) (Fin k)) (π i)) =
        ι (Additive.ofMul (Θ (Pi.mulSingle (π i) (ofAdd (ε i))))) := by
      rw [Pi.basisFun_apply]
      change η (ε i • Pi.single (π i) 1) = _
      apply congrArg ι
      apply congrArg Additive.ofMul
      apply congrArg Θ
      ext j
      change (ε i • (Pi.single (π i) (1 : ZMod p) : Fin k → ZMod p)) j =
        toAdd ((Pi.mulSingle (π i) (ofAdd (ε i)) : Fin k → Multiplicative (ZMod p)) j)
      simp [Pi.single_apply, toAdd_mulSingle, smul_eq_mul]
    rw [← ht, map_smul]
    rfl
  have hsign : (c : ZMod p) = 1 ∨ (c : ZMod p) = -1 :=
    ggRC_scalar_eq_one_or_neg_one_of_monomial_refl hp2 hk b (ggLin (p := p) ι ψ')
      ((ggIsReflection_iff_ggLinRefl hp2 ι ψ').mp href) (c : ZMod p) hc0 π ε hε
      (fun i => by rw [hscalar, hwb, smul_smul])
  rcases hsign with hpos | hneg
  · have heq : ggLin (p := p) ι ψ' = ggLin (p := p) ι w := by
      ext v
      simpa [hpos] using hscalar v
    exact heq ▸ hwin
  · have hn : LinearEquiv.neg (ZMod p) ∈ ggHL ι φ h α :=
      Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))
    have heq : ggLin (p := p) ι ψ' = LinearEquiv.neg (ZMod p) * ggLin (p := p) ι w := by
      ext v
      simpa only [hneg, LinearEquiv.mul_apply, LinearEquiv.neg_apply,
        neg_one_smul (ZMod p)] using hscalar v
    exact heq ▸ (Subgroup.mul_mem _ hn hwin)

theorem ggTorusWNormSC_of_signedNormalizer {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp2 : p ≠ 2)
    (hN : ∀ {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
      {φ : MulAut ↥A}, Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
      commutator L' = ⊤ → IsElemAbelian p A → (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A → φ ∈ Subgroup.normalizer
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A)) →
      ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (w : MulAut ↥A),
        3 ≤ k ∧ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
          IsSignedPerm ⇑((MulAut.congr Θ).symm w) ∧ ∃ c : ℕ, ∀ a, φ a = (w a) ^ c) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    _hM _hC _hpair _hlin hgen ψ' hψ'
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  have hn := mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal
    (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A) hψ'
  obtain ⟨k, Θ, w, hk, hw, hws, c, hc⟩ := hN hψ hker hperf hA hAI h3 hsc hn
  have hwin : ggLin (p := p) ι w ∈ ggHL ι φ h α := by
    have hclosure : Subgroup.closure (Set.range φ) ≤
        (ggHL ι φ h α).comap (ggLin (p := p) ι) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (Or.inl (Or.inl (Set.mem_range_self i)))
    exact hclosure (hgen ▸ hw)
  exact ggWNormConcl_of_signed hp2 ι φ h α hk Θ hwin hws hc

theorem ggTorusWNormSC_of_signedEltSC {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (hT : GGTorusSignedEltSC p R) : GGTorusWNormSC p R I :=
  ggTorusWNormSC_of_signedNormalizer hp2 fun hψ hker hperf hA hAI h3 hsc hφ =>
    exists_signedModelSC_normalizer hp hp2 hI hZ hcp hT hψ hker hperf hA hAI h3 hsc hφ

end CFSG.StandardType
