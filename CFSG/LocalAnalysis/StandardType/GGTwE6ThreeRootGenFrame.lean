module

public import CFSG.LocalAnalysis.StandardType.GGKGTwFrameCore

public section

namespace CFSG.StandardType.TwE6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_lang_frame
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) :
    ∃ (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (D : FrameData ↥(twistedE6RootGroup K σ)),
      IsLang Fr g₀ ∧ TSpec hn hK σ hσ Fr hFr g₀ hζ D ∧ D.Good := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
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
  exact ⟨g₀, D, hL, hD, hgood⟩

theorem align_data
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {L' : Type} [Group L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (D : FrameData ↥(twistedE6RootGroup K σ))
    (hH_eq : D.H = (RecipeExcLang.twConj K σ).range) (hgood : D.Good) :
    ∃ (γ : MulAut ↥(twistedE6RootGroup K σ))
      (ψ' : L' →* ↥(twistedE6RootGroup K σ))
      (ρ' : MulAut L' →* MulAut ↥(twistedE6RootGroup K σ)),
      γ ∈ D.H ∧ Function.Surjective ψ' ∧ ψ'.ker = ψ₀.ker ∧
      ψ'.ker ≤ Subgroup.center L' ∧ Function.Injective ρ' ∧
      (∀ a l, ρ' a (ψ' l) = ψ' (a l)) ∧
      (∀ a ∈ A, ρ' a ∈ D.diag.range) ∧
      (∀ (a : A) (l : L'), (γ⁻¹ * ρ' a * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l)) := by
  classical
  have hZ : ψ₀.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ₀ hker hgood.center
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
    rw [hρφ, hH_eq]
    exact hφH
  obtain ⟨γ, hγH, hγ⟩ := exists_align D hgood.shape hρinj hA h5 hAH'
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
  refine ⟨γ, ψ', ρ', hγH, hψ', hkerEq, hker', hρ'inj, hρ', hal, ?_⟩
  intro a l
  have h1 : γ⁻¹ * ρ' a * γ = ρ a := by
    rw [hρ'eq a]
    group
  rw [h1]
  exact hρ a l

theorem model_data
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)}
    {ψ' : L' →* ↥(twistedE6RootGroup K σ)} (hψ' : Function.Surjective ψ')
    (hkerEq : ψ'.ker = ψ₀.ker) (hker' : ψ'.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (D : FrameData ↥(twistedE6RootGroup K σ)) (hgood : D.Good)
    {ρ' : MulAut L' →* MulAut ↥(twistedE6RootGroup K σ)}
    (hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l)) (hρinj : Function.Injective ρ')
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ' a ∈ D.diag.range) :
    ∃ (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L'),
      (∀ a : A, D.diag (κ a) = ρ' a) ∧ Function.Injective κ ∧
      (κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
      (∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T) ∧
      (∀ a ∈ A, ∀ t ∈ T, a t = t) ∧
      (∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
        MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x) ∧
      ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ u : WeylGroup .E6, ∀ a b : A,
          (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
            Multiplicative.toAdd (κ b) = adAct .E6 3 u (Multiplicative.toAdd (κ a)) := by
  classical
  obtain ⟨Φ, hΦ, T, w, hbody⟩ :=
    CFSG.StandardType.KGL.modelDiag_of_good_cover ggAbelianLift D hgood
      (coverOdd_T hn hK σ hσ h3) hψ' hker' hperf hρ' hρinj hA hsc hal
  obtain ⟨hinj, hrange, -, hTodd, hTfix, -, -, -, hHyp, hinner, -, -⟩ := hbody
  have hTodd' : ∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T := by
    intro z hz hodd
    have hz' : z ∈ ψ'.ker := by rwa [hkerEq]
    exact hTodd z hz' hodd
  exact ⟨Φ, T, w, hΦ, hinj, hrange, hTodd', hTfix, hHyp, hinner⟩

private theorem matrix_data
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {L' : Type} [Group L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} {A : Subgroup (MulAut L')}
    (D : FrameData ↥(twistedE6RootGroup K σ))
    {g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hL : IsLang Fr g₀) (hD : TSpec hn hK σ hσ Fr hFr g₀ hζ D)
    {γ : MulAut ↥(twistedE6RootGroup K σ)} (hγH : γ ∈ D.H)
    (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    {ρ' : MulAut L' →* MulAut ↥(twistedE6RootGroup K σ)}
    (hΦ : ∀ a : A, D.diag (κ a) = ρ' a)
    (hkey : ∀ (a : A) (l : L'), (γ⁻¹ * ρ' a * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l)) :
    ∃ (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
        g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
      (∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
        g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) ∧
      (∀ (a : A) (l : L'),
        ((ψ₀ ((a : MulAut L') l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          t (Multiplicative.toAdd (κ a)) *
            ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
              (t (Multiplicative.toAdd (κ a)))⁻¹) := by
  classical
  obtain ⟨g, t, hLg, ht, hconj⟩ :=
    CFSG.StandardType.KGL.kgTw_conj_of_tspec hn hK σ hσ Fr hFr hL hζ hD hγH
  let g' : ModGL TwistTag.E6.tag (AlgebraicClosure K) := g
  have hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g' =
      g' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 :=
    inv_mul_eq_iff_eq_mul.mp hLg.2
  refine ⟨g', t, ?_, hgF, fun x => (ht x).2, ?_⟩
  · exact hLg.1
  intro a l
  have key : (γ⁻¹ * D.diag (κ a) * γ) (ψ₀ l) = ψ₀ ((a : MulAut L') l) := by
    rw [hΦ a]
    exact hkey a l
  have h2 := hconj (Multiplicative.toAdd (κ a)) (ψ₀ l)
  rw [show D.ad (Multiplicative.toAdd (κ a)) = D.diag (κ a) from rfl] at h2
  change ((ψ₀ ((a : MulAut L') l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
    t (Multiplicative.toAdd (κ a)) *
      ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        (t (Multiplicative.toAdd (κ a)))⁻¹
  exact (congrArg Subtype.val key).symm.trans h2

theorem exists_frame_torus
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ∃ (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (κ : A →* Multiplicative (Fin 6 → ZMod 3))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K) (T : Subgroup L'),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
        g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
      Function.Injective κ ∧
      (κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) ∧
      (∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
        g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) ∧
      (∀ (a : A) (l : L'),
        ((ψ₀ ((a : MulAut L') l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          t (Multiplicative.toAdd (κ a)) *
            ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
              (t (Multiplicative.toAdd (κ a)))⁻¹) ∧
      (∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T) ∧
      (∀ a ∈ A, ∀ y ∈ T, a y = y) ∧
      (∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
        MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x) ∧
      ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ u : WeylGroup .E6, ∀ a b : A,
          (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
            Multiplicative.toAdd (κ b) = adAct .E6 3 u (Multiplicative.toAdd (κ a)) := by
  classical
  obtain ⟨g₀, D, hL, hD, hgood⟩ :=
    exists_lang_frame hn hK σ hσ h3 hFr hζ hζo
  obtain ⟨γ, ψ', ρ', hγH, hψ', hkerEq, hker', hρinj, hρ', hal, hkey⟩ :=
    align_data (K := K) (σ := σ) hψ₀ hker hperf hA hAH h5 D hD.H_eq hgood
  obtain ⟨κ, T, w, hΦ, hκinj, hκrange, hTodd, hTfix, hHyp, hinner⟩ :=
    model_data hn hK σ hσ h3 hψ' hkerEq hker' hperf D hgood hρ' hρinj hA hsc hal
  obtain ⟨g, t, hg, hgF, ht, hconj⟩ :=
    matrix_data hn hK σ hσ hFr hζ D hL hD hγH κ hΦ hkey
  exact ⟨g, κ, t, T, hg, hgF, hκinj, hκrange, ht, hconj, hTodd, hTfix, hHyp, hinner⟩

end CFSG.StandardType.TwE6ThreeRootGen

end
