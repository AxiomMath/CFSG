module

public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGKGTwModelDiag
public import CFSG.LocalAnalysis.StandardType.GGKGTwConj
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgTwFrame_core {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : Nat.card A = 3 ^ 5) (hsc : GGTorusSelfCent 3 A) :
    ∃ (v : WeylGroup TwistTag.E6.tag) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (κ : A →* Multiplicative (Fin 6 → ZMod 3))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K),
      KGTwFrame n σ (MulEquiv.refl _) Fr ζ hζ ψ₀ A v g κ t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_surjective ψ₀ hψ₀
  obtain ⟨g₀, hg₀, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := n) hn hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0)
  have hL : IsLang Fr g₀ := ⟨hg₀, hgn⟩
  obtain ⟨D, hD⟩ := exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  have hgood : D.Good :=
    { center := tFrame_center hn hK σ hσ
      faithful := tFrame_faithful hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      shape := tFrame_shape hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      torus := tFrame_torus hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      cent := tFrame_cent hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      inner := tFrame_inner hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      weyl := tFrame_weyl hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      modules := tFrame_modules hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      norm := tFrame_norm hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      aut := tFrame_aut hn hK σ hσ Fr hFr h3 hL hζ hζo hD }
  have hZ : ψ₀.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ₀ hker hgood.center
  let ρ : MulAut L' →* MulAut ↥(twistedE6RootGroup K σ) := BstarDesc.descAut hψ₀ hZ
  have hρ : ∀ a l, ρ a (ψ₀ l) = ψ₀ (a l) := fun a l => BstarDesc.descAut_apply hψ₀ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ₀ hZ hperf
  have hAH' : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφH, hφ⟩ := hAH a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ₀ r
      rw [hρ, hφ]
    rw [hρφ, hD.H_eq]
    exact hφH
  obtain ⟨γ, hγH, hγ⟩ := exists_align D hgood.shape hρinj hA h5.ge hAH'
  let ψ' : L' →* ↥(twistedE6RootGroup K σ) := γ.toMonoidHom.comp ψ₀
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ₀
  have hkerEq : ψ'.ker = ψ₀.ker := by
    ext l
    change γ (ψ₀ l) = 1 ↔ ψ₀ l = 1
    exact ⟨fun h => γ.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  let ρ' : MulAut L' →* MulAut ↥(twistedE6RootGroup K σ) :=
    (MulAut.conj γ).toMonoidHom.comp ρ
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := by
    intro a l
    change (MulAut.conj γ (ρ a)) (γ (ψ₀ l)) = γ (ψ₀ (a l))
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hρ a l]
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := fun a => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hρ'inj : Function.Injective ρ' := (MulAut.conj γ).injective.comp hρinj
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := by
    intro a ha
    rw [hρ'eq a]
    exact hγ a ha
  obtain ⟨Φ, hΦ, T, w, hbody⟩ :=
    modelDiag_of_good_cover ggAbelianLift D hgood (coverOdd_T hn hK σ hσ h3) hψ' hker' hperf
      hρ' hρ'inj hA hsc hal
  obtain ⟨hinj, hrange, -, -, -, -, -, hrefl, -, hinnaut, -, -⟩ := hbody
  obtain ⟨g, t, hLg, ht, hconj⟩ :=
    kgTw_conj_of_tspec hn hK σ hσ Fr hFr hL hζ hD hγH
  refine ⟨CFSG.HardMathSupport.Lang.E6Descent.twE6W0, g, Φ, t, ?_⟩
  refine ⟨hFr, ?_, hLg.1, ?_, ?_, ht, ?_⟩
  ·
    intro δ
    have h := CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul
      (permLattice CFSG.RankThree.E6.e6Rho δ)
    exact h.trans (congrArg Neg.neg (TwistedDiag.permLattice_permLattice' δ))
  ·
    exact inv_mul_eq_iff_eq_mul.mp hLg.2
  ·
    refine ⟨h5, hinj, kgFrame_range_eq_hyp hinj hrange h5, ?_, ?_⟩
    · exact hinnaut
    · intro i
      haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [h5]; norm_num)
      refine ⟨w i, kgFrame_conj_mem_normalizer (w i)
        (fun a => (hrefl i a).imp fun b hb => hb.1), ?_⟩
      intro a b hb
      obtain ⟨b', hb', hΦb'⟩ := hrefl i a
      have hbb' : b = b' := Subtype.ext (hb.trans hb')
      rw [hbb']
      exact hΦb'
  ·
    intro a l
    have hconj' : γ⁻¹ * ρ' a * γ = ρ a := by
      rw [hρ'eq a]; group
    have key : (γ⁻¹ * D.diag (Φ a) * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l) := by
      rw [hΦ a, hconj']
      exact hρ a l
    have h2 := hconj (Multiplicative.toAdd (Φ a)) (ψ₀ l)
    rw [show D.ad (Multiplicative.toAdd (Φ a)) = D.diag (Φ a) from rfl] at h2
    change ((ψ₀ ((a : MulAut L') l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      t (Multiplicative.toAdd (Φ a)) *
        ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (Φ a)))⁻¹
    exact (congrArg Subtype.val key).symm.trans h2

end CFSG.StandardType.KGL

end
