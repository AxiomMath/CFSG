module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly UCoord

theorem ggTorusWNormSC_of_permEltSC {p d : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d) (hpd : ¬ p ∣ d)
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (hT : GGTorusPermEltSC p d R) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    _hM _hC _hpair _hlin hgen s hs
  let W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  obtain ⟨Θ, -, hP, hN⟩ := exists_permModel hp hZ hIp hcp hT hψ hker hperf hA hAI h3 hsc
  have hWin (σ : Equiv.Perm (Fin d)) : MulAut.congr Θ (permAutV σ) ∈ W := by
    obtain ⟨n, hn, he⟩ := hP σ
    rw [← he]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hWperm : ∀ w ∈ W, ∃ σ : Equiv.Perm (Fin d), w = MulAut.congr Θ (permAutV σ) := by
    intro w hw
    obtain ⟨c, ⟨n, rfl⟩, hn, he⟩ := mem_ggAutomizer_iff.mp hw
    obtain ⟨σ, hσ⟩ := hN n hn
    exact ⟨σ, (MulEquiv.ext fun a => Subtype.ext (he a)).trans hσ⟩
  let ρ : Equiv.Perm (Fin d) →* W :=
    ((MulAut.congr Θ).toMonoidHom.comp (permAutVHom d p)).codRestrict W hWin
  have hρ : Function.Bijective ρ := by
    constructor
    · intro σ τ he
      apply permAutV_injective hp hp2
      apply (MulAut.congr Θ).injective
      exact congrArg Subtype.val he
    · intro w
      obtain ⟨σ, hσ⟩ := hWperm w w.2
      exact ⟨σ, Subtype.ext hσ.symm⟩
  have hZW : Subgroup.center ↥W = ⊥ := by
    let e : Equiv.Perm (Fin d) ≃* W := MulEquiv.ofBijective ρ hρ
    have hz := center_perm_eq_bot_of_three_le_card (α := Fin d) (by simpa using (show 3 ≤ d by omega))
    rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
  have hNI : NormInducesInner W :=
    ggTorusWeylNormInnerSC_of_permElt hp hp2 hd hZ hIp hcp hT
      L' ψ hψ hker hperf A hA hAI h3 hsc
  have hscalar : ∀ f : MulAut ↥A, (∀ w ∈ W, f * w = w * f) →
      ∃ c : ZMod p, ∀ v, ggLin (p := p) ι f v = c • v := by
    intro f hf
    let F : ↥(sumZero d p) →* ↥(sumZero d p) :=
      ((MulAut.congr Θ).symm f).toMonoidHom
    have hF : ∀ (σ : Equiv.Perm (Fin d)) (v : ↥(sumZero d p)),
        F (permAutV σ v) = permAutV σ (F v) := by
      intro σ v
      apply Θ.injective
      have he := congrArg (fun g : MulAut ↥A => g (Θ v)) (hf _ (hWin σ))
      simpa [F, MulAut.mul_apply, MulAut.congr_apply, MulAut.congr_symm_apply] using he
    obtain ⟨c, hc⟩ := exists_pow_of_commute_permAutV hp hp2 (by omega) hpd F hF
    refine ⟨(c : ZMod p), fun v => ?_⟩
    obtain ⟨a, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
    obtain ⟨u, rfl⟩ := Θ.surjective a
    have he : f (Θ u) = Θ u ^ c := by
      have he := congrArg Θ (hc u)
      simpa [F, map_pow, MulAut.congr_symm_apply] using he
    change ggLin (p := p) ι f (ι (Additive.ofMul (Θ u))) =
      (c : ZMod p) • ι (Additive.ofMul (Θ u))
    rw [ggLin_apply_ofMul, he, ofMul_pow, map_nsmul, Nat.cast_smul_eq_nsmul (ZMod p)]
  have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by simpa using (Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt)) h3)
  have : Nontrivial V := ι.injective.nontrivial
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  exact ggWNormConcl_of_centerless ι φ h α hgen hZW hNI hscalar
    (mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal hs)

end CFSG.StandardType
