module

public import CFSG.Mathlib.LinearAlgebra.Matrix.SingerSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE6ThreeLines
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem _root_.CFSG.LieType.SeitzGeneration.SylowTorus.exists_conj_eq_of_selfCent {G : Type*}
    [Group G] {p m : ℕ} (hS : SylowTorus G p m) (hp : p.Prime) {V : Subgroup G}
    (hV : IsElemAbelian p V) (hVcard : Nat.card V = p ^ m) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ c : G, (∀ x ∈ V, c * x * c⁻¹ ∈ E) ∧ ∀ x ∈ E, c⁻¹ * x * c ∈ V := by
  classical
  obtain ⟨T, E₀, hTc, hconj, hE₀T, hTtors, hE₀ab, hE₀card⟩ := hS.exists_torus
  have hfin : Finite E₀ :=
    Nat.finite_of_card_ne_zero (by rw [hE₀card]; exact (pow_pos hp.pos m).ne')
  have hcp : ∀ (a b : G) (i : ℕ), (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := fun a b i => by
    simpa using conj_pow (a := a⁻¹) (b := b) (i := i)
  have hinto : ∀ {Q : Subgroup G}, IsElemAbelian p Q → ∃ c : G, ∀ x ∈ Q, c⁻¹ * x * c ∈ E₀ := by
    intro Q hQ
    obtain ⟨c, hc⟩ := hconj Q (CFSG.LieType.SeitzGeneration.isPGroup_of_isElemAbelian hQ)
    refine ⟨c, fun x hx => ?_⟩
    obtain ⟨t, ht, htx⟩ := hc hx
    have htx' : c⁻¹ * x * c = t := by
      rw [← htx]
      show c⁻¹ * (c * t * c⁻¹) * c = t
      group
    rw [htx']
    refine hTtors t ht ?_
    rw [← htx', hcp, hQ.2 x hx]
    group
  obtain ⟨g, hEg⟩ := hinto hE
  have hE₀E : ∀ s ∈ E₀, g * s * g⁻¹ ∈ E := by
    intro s hs
    apply hsc
    · intro e he
      have h1 : s * (g⁻¹ * e * g) = (g⁻¹ * e * g) * s := by
        have := hTc
        exact setLike_mul_comm (hE₀T hs) (hE₀T (hEg e he))
      calc g * s * g⁻¹ * e = g * (s * (g⁻¹ * e * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * e * g) * s) * g⁻¹ := by rw [h1]
        _ = e * (g * s * g⁻¹) := by group
    · rw [conj_pow, hE₀ab.2 s hs]
      group
  obtain ⟨h, hVh⟩ := hinto hV
  let ch : G →* G := (MulAut.conj h⁻¹).toMonoidHom
  have hch : ∀ x, ch x = h⁻¹ * x * h := fun x => by
    show h⁻¹ * x * h⁻¹⁻¹ = h⁻¹ * x * h
    rw [inv_inv]
  have hVeq : V.map ch = E₀ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [hch]
      exact hVh x hx
    · rw [Subgroup.card_map_of_injective (f := ch) (MulAut.conj h⁻¹).injective, hVcard, hE₀card]
  have hE₀V : ∀ s ∈ E₀, h * s * h⁻¹ ∈ V := by
    intro s hs
    rw [← hVeq] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    rw [hch, show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
    exact hx
  refine ⟨g * h⁻¹, fun x hx => ?_, fun x hx => ?_⟩
  · have := hE₀E _ (hVh x hx)
    rw [show g * h⁻¹ * x * (g * h⁻¹)⁻¹ = g * (h⁻¹ * x * h) * g⁻¹ by group]
    exact this
  · have := hE₀V _ (hEg x hx)
    rw [show (g * h⁻¹)⁻¹ * x * (g * h⁻¹) = h * (g⁻¹ * x * g) * h⁻¹ by group]
    exact this

@[expose] def diagWeight (p Q : ℕ) : Fin 3 → ZMod p := fun i => if i = 0 then (Q : ZMod p) else 1

theorem ggTorusWNormSC_of_reference {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R) {G : Type*} [Group G] (ε : R ≃* G) (hS : SylowTorus G p 3)
    {t : Multiplicative (Fin 3 → ZMod p) →* G} (htinj : Function.Injective t) {x : G} {Q : ℕ}
    (hx : ∀ v, x * t v * x⁻¹ =
      t (Multiplicative.ofAdd fun i => diagWeight p Q i * Multiplicative.toAdd v i))
    (hQ0 : ((Q : ℕ) : ZMod p) ≠ 0) (hQ : ((Q : ℕ) : ZMod p) ^ 2 ≠ 1) :
    GGTorusWNormSC p R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α _ hC hpair hlin hgen
    _ _
  exfalso
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hw0 : diagWeight p Q 0 = (Q : ZMod p) := if_pos rfl
  have hw1 : diagWeight p Q 1 = 1 := if_neg (by decide)
  have hw2 : diagWeight p Q 2 = 1 := if_neg (by decide)
  have hwne : ∀ i, diagWeight p Q i ≠ 0 := by
    intro i
    fin_cases i
    · change diagWeight p Q 0 ≠ 0
      rw [hw0]
      exact hQ0
    · change diagWeight p Q 1 ≠ 0
      rw [hw1]
      exact one_ne_zero
    · change diagWeight p Q 2 ≠ 0
      rw [hw2]
      exact one_ne_zero
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, -, hEsc⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  have hV0 : IsElemAbelian p t.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨w, hw⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hw, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨u, rfl⟩ := hy
      rw [← map_pow]
      convert map_one t
      apply Multiplicative.toAdd.injective
      funext i
      simp
  have hV0card : Nat.card t.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective htinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod p) ≃ (Fin 3 → ZMod p))]
    simp [Nat.card_fun, Nat.card_zmod]
  obtain ⟨c, hcV, hcE⟩ := hS.exists_conj_eq_of_selfCent hp hV0 hV0card hEg hEgs
  let Φ : G →* MulAut L' := Λ₀.comp ε.symm.toMonoidHom
  let f0 : Multiplicative (Fin 3 → ZMod p) →* MulAut L' :=
    Φ.comp ((MulAut.conj c).toMonoidHom.comp t)
  have hf0 : ∀ v, f0 v = Φ (c * t v * c⁻¹) := fun _ => rfl
  have hf0A : ∀ v, f0 v ∈ A := by
    intro v
    obtain ⟨e, he, he'⟩ := hcV (t v) ⟨v, rfl⟩
    have he2 : ε e = c * t v * c⁻¹ := he'
    change Λ₀ (ε.symm (c * t v * c⁻¹)) ∈ A
    rw [← he2, MulEquiv.symm_apply_apply]
    exact he
  let κ0 : Multiplicative (Fin 3 → ZMod p) →* ↥A := f0.codRestrict A hf0A
  have hκ0 : ∀ v, (κ0 v : MulAut L') = f0 v := fun _ => rfl
  have hκinj : Function.Injective κ0 := by
    intro v w hvw
    have h1 : Λ₀ (ε.symm (c * t v * c⁻¹)) = Λ₀ (ε.symm (c * t w * c⁻¹)) :=
      congrArg Subtype.val hvw
    exact htinj (mul_left_cancel (mul_right_cancel (ε.symm.injective (hΛinj h1))))
  have hκsurj : Function.Surjective κ0 := by
    rintro ⟨a, ha⟩
    obtain ⟨e, he⟩ := hAΛ a ha
    have heE : ε e ∈ E := ⟨e, show Λ₀ e ∈ A by rw [he]; exact ha, rfl⟩
    obtain ⟨v, hv⟩ := hcE _ heE
    refine ⟨v, Subtype.ext ?_⟩
    change Λ₀ (ε.symm (c * t v * c⁻¹)) = a
    rw [hv, show c * (c⁻¹ * ε e * c) * c⁻¹ = ε e by group, MulEquiv.symm_apply_apply, he]
  obtain ⟨l, hl⟩ := hψ (ε.symm (c * x * c⁻¹))
  have hΛl : Φ (c * x * c⁻¹) = MulAut.conj l := hΛeq hl
  have hact : ∀ v, MulAut.conj l * f0 v * (MulAut.conj l)⁻¹ =
      f0 (Multiplicative.ofAdd fun i =>
        diagWeight p Q i * Multiplicative.toAdd v i) := by
    intro v
    rw [hf0 (Multiplicative.ofAdd _), ← hx v, ← hΛl, hf0, ← map_inv Φ, ← map_mul Φ, ← map_mul Φ]
    congr 1
    group
  have hgN : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨v, hv⟩ := hκsurj ⟨a, ha⟩
      have hv' : f0 v = a := congrArg Subtype.val hv
      rw [← hv', hact]
      exact hf0A _
    · intro ha
      obtain ⟨v, hv⟩ := hκsurj ⟨_, ha⟩
      have hv' : f0 v = MulAut.conj l * a * (MulAut.conj l)⁻¹ := congrArg Subtype.val hv
      have hw : (Multiplicative.ofAdd fun i => diagWeight p Q i *
          Multiplicative.toAdd (Multiplicative.ofAdd fun j =>
            (diagWeight p Q j)⁻¹ * Multiplicative.toAdd v j) i) = v := by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_ofAdd]
        exact mul_inv_cancel_left₀ (hwne i) _
      have h1 := hact (Multiplicative.ofAdd fun j =>
        (diagWeight p Q j)⁻¹ * Multiplicative.toAdd v j)
      rw [hw, hv'] at h1
      rw [← mul_left_cancel (mul_right_cancel h1)]
      exact hf0A _
  let s : MulAut ↥A := ggConjAut A hgN
  have hsW : s ∈ Subgroup.closure (Set.range φ) := by
    rw [← hgen]
    exact Subgroup.subset_closure
      (ggConjAut_mem_ggInduced (H := (MulAut.conj : L' →* MulAut L').range) ⟨l, rfl⟩ hgN)
  let β0 : (Fin 3 → ZMod p) →+ V :=
    { toFun := fun v => ι (Additive.ofMul (κ0 (Multiplicative.ofAdd v)))
      map_zero' := by simp
      map_add' := fun v w => by simp only [ofAdd_add, map_mul, ofMul_mul, map_add] }
  have hκbij : Function.Bijective κ0 := ⟨hκinj, hκsurj⟩
  have hβbij : Function.Bijective β0 :=
    ι.bijective.comp (Additive.ofMul.bijective.comp (hκbij.comp Multiplicative.ofAdd.bijective))
  let β : (Fin 3 → ZMod p) ≃ₗ[ZMod p] V := LinearEquiv.ofBijective (β0.toZModLinearMap p) hβbij
  have hβ : ∀ v, β v = ι (Additive.ofMul (κ0 (Multiplicative.ofAdd v))) := fun _ => rfl
  have hsβ : ∀ v, ggLin (p := p) ι s (β v) = β (fun i => diagWeight p Q i * v i) := by
    intro v
    rw [hβ, hβ, ggLin_apply_ofMul]
    congr 2
    apply Subtype.ext
    rw [ggConjAut_apply, hκ0, hκ0, hact]
    rfl
  have hdet : LinearMap.det (ggLin (p := p) ι s : V →ₗ[ZMod p] V) = (Q : ZMod p) := by
    have heq : (ggLin (p := p) ι s : V →ₗ[ZMod p] V) =
        (β : (Fin 3 → ZMod p) →ₗ[ZMod p] V) ∘ₗ
          Matrix.toLin' (Matrix.diagonal (diagWeight p Q)) ∘ₗ
          (β.symm : V →ₗ[ZMod p] (Fin 3 → ZMod p)) := by
      apply LinearMap.ext
      intro y
      obtain ⟨v, rfl⟩ := β.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Matrix.toLin'_apply]
      rw [hsβ]
      congr 1
      funext i
      rw [Matrix.mulVec_diagonal]
    rw [heq, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three,
      hw0, hw1, hw2, mul_one, mul_one]
  have h2 : ∀ i, α i (h i) = 2 := fun i => by
    rw [hpair, hC.1 i]
    simp
  have hsq := ggLin_det_sq_eq_one_of_mem_closure_refl ι φ h α h2 hlin hsW
  have hsq' : (LinearMap.det (ggLin (p := p) ι s : V →ₗ[ZMod p] V)) ^ 2 = 1 := by
    have e := congrArg Units.val hsq
    rw [Units.val_pow_eq_pow_val, LinearEquiv.coe_det, Units.val_one] at e
    exact e
  rw [hdet] at hsq'
  exact hQ hsq'


namespace E6PhiThree


theorem frame_root_cases {L : Type} [Field L] {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ) {x y : Fin Tag.E6.rank → ℤ}
    (h01 : σ 0 1 = x) (h12 : σ 1 2 = y) {i j : Fin 3} (hij : i ≠ j) :
    σ i j = x ∨ σ i j = y ∨ σ i j = x + y ∨ σ i j = -x ∨ σ i j = -y ∨ σ i j = -(x + y) := by
  obtain ⟨h02, h10, h21, h20⟩ := e6ThreeLine_sigma h h01 h12
  fin_cases i <;> fin_cases j <;> simp_all

theorem orth_of_six {x y x' y' : Fin Tag.E6.rank → ℤ}
    (h1 : x ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ x') = 0)
    (h2 : x ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y') = 0)
    (h3 : y ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ x') = 0)
    (h4 : y ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y') = 0)
    {a b : Fin Tag.E6.rank → ℤ}
    (ha : a = x ∨ a = y ∨ a = x + y ∨ a = -x ∨ a = -y ∨ a = -(x + y))
    (hb : b = x' ∨ b = y' ∨ b = x' + y' ∨ b = -x' ∨ b = -y' ∨ b = -(x' + y')) :
    a ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ b) = 0 := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Matrix.mulVec_add, Matrix.mulVec_neg, h1, h2, h3, h4]

theorem e6ThreeLine_orth_0_7 :
    e6ThreeLineX 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 7) = 0 ∧
    e6ThreeLineX 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 7) = 0 ∧
    e6ThreeLineY 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 7) = 0 ∧
    e6ThreeLineY 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 7) = 0 := by
  decide +kernel

theorem e6ThreeLine_orth_0_11 :
    e6ThreeLineX 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 11) = 0 ∧
    e6ThreeLineX 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 11) = 0 ∧
    e6ThreeLineY 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 11) = 0 ∧
    e6ThreeLineY 0 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 11) = 0 := by
  decide +kernel

theorem e6ThreeLine_orth_7_11 :
    e6ThreeLineX 7 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 11) = 0 ∧
    e6ThreeLineX 7 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 11) = 0 ∧
    e6ThreeLineY 7 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineX 11) = 0 ∧
    e6ThreeLineY 7 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6ThreeLineY 11) = 0 := by
  decide +kernel

theorem frame_commute {K : Type} [Field K] {ρ ρ' : SL(3, K) →* ModGL Tag.E6 K}
    {σ σ' : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ) (h' : IsSLFrame ρ' σ')
    {x y x' y' : Fin Tag.E6.rank → ℤ} (h01 : σ 0 1 = x) (h12 : σ 1 2 = y) (h01' : σ' 0 1 = x')
    (h12' : σ' 1 2 = y')
    (horth : x ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ x') = 0 ∧
      x ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y') = 0 ∧ y ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ x') = 0 ∧
      y ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y') = 0) (g g' : SL(3, K)) :
    Commute (ρ g) (ρ' g') := by
  have hg : ρ g ∈ rootSpan Tag.E6 K (frameRoots σ) := by
    rw [← h.range]
    exact ⟨g, rfl⟩
  have hg' : ρ' g' ∈ rootSpan Tag.E6 K (frameRoots σ') := by
    rw [← h'.range]
    exact ⟨g', rfl⟩
  exact rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
    (fun r hr => by
      obtain ⟨i, j, hij, rfl⟩ := hr
      exact h.isRoot i j hij)
    (fun r hr => by
      obtain ⟨i, j, hij, rfl⟩ := hr
      exact h'.isRoot i j hij)
    (fun a ha b hb => by
      obtain ⟨i, j, hij, rfl⟩ := ha
      obtain ⟨i', j', hij', rfl⟩ := hb
      exact orth_of_six horth.1 horth.2.1 horth.2.2.1 horth.2.2.2 (frame_root_cases h h01 h12 hij)
        (frame_root_cases h' h01' h12' hij'))
    _ hg _ hg'

theorem frame_mem {K : Type} [Field K] {ρ : SL(3, K) →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (h : IsSLFrame ρ σ) (g : SL(3, K)) :
    ρ g ∈ adjointGroup Tag.E6 K := by
  apply CFSG.LieType.Chevalley.rootSpan_le_adjointGroup K (frameRoots σ)
  rw [← h.range]
  exact ⟨g, rfl⟩

theorem pow_three_eq_one_of_commute {K : Type} [Field K] {G : Type*} [Group G]
    {ρ : SL(3, K) →* G} (hρ : Function.Injective ρ) {g : SL(3, K)}
    (hg : ∀ X : SL(3, K), Commute (ρ g) (ρ X)) : g ^ 3 = 1 := by
  apply CFSG.Singer.pow_card_eq_one_of_mem_center
  rw [Subgroup.mem_center_iff]
  intro X
  apply hρ
  rw [map_mul, map_mul]
  exact ((hg X).eq).symm

theorem mul_rearrange {G : Type*} [Group G] {a b c d e f : G} (hbc : Commute b c)
    (hbe : Commute b e) (hde : Commute d e) :
    a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
  calc a * b * (c * d) * (e * f) = a * (b * c) * d * e * f := by simp only [mul_assoc]
    _ = a * (c * b) * d * e * f := by rw [hbc.eq]
    _ = a * c * (b * (d * e)) * f := by simp only [mul_assoc]
    _ = a * c * (b * (e * d)) * f := by rw [hde.eq]
    _ = a * c * ((b * e) * d) * f := by simp only [mul_assoc]
    _ = a * c * ((e * b) * d) * f := by rw [hbe.eq]
    _ = a * c * e * (b * d * f) := by simp only [mul_assoc]

theorem exists_reference {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ (t : Multiplicative (Fin 3 → ZMod p) →* adjointGroup Tag.E6 K) (x : adjointGroup Tag.E6 K),
      Function.Injective t ∧ ∀ v, x * t v * x⁻¹ =
        t (Multiplicative.ofAdd fun i =>
          diagWeight p (Nat.card K) i * Multiplicative.toAdd v i) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  have hdiv : (Nat.card K ^ 3 - 1) / (Nat.card K - 1) = Nat.card K ^ 2 + Nat.card K + 1 := by
    apply Nat.div_eq_of_eq_mul_left (by omega)
    obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    ring_nf
    omega
  obtain ⟨τ, σ, hτ, hστ⟩ := CFSG.Singer.exists_singer_sl (K := K) (ℓ := 2) 3 (p := p)
    (by rw [hdiv]; exact hpq)
  obtain ⟨ρ0, σ0, hf0, hi0, h01_0, h12_0⟩ := e6ThreeLine_frame (L := K) 0
  obtain ⟨ρ1, σ1, hf1, hi1, h01_1, h12_1⟩ := e6ThreeLine_frame (L := K) 7
  obtain ⟨ρ2, σ2, hf2, hi2, h01_2, h12_2⟩ := e6ThreeLine_frame (L := K) 11
  have c01 := frame_commute hf0 hf1 h01_0 h12_0 h01_1 h12_1 e6ThreeLine_orth_0_7
  have c02 := frame_commute hf0 hf2 h01_0 h12_0 h01_2 h12_2 e6ThreeLine_orth_0_11
  have c12 := frame_commute hf1 hf2 h01_1 h12_1 h01_2 h12_2 e6ThreeLine_orth_7_11
  have hmod : ∀ m : ℕ, τ ^ (m % p) = τ ^ m := fun m => by
    rw [← hτ]
    exact pow_mod_orderOf τ m
  let u : Multiplicative (ZMod p) →* SL(3, K) :=
    { toFun := fun a => τ ^ (Multiplicative.toAdd a).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, ZMod.val_add, hmod, pow_add] }
  have hu : ∀ a, u a = τ ^ (Multiplicative.toAdd a).val := fun _ => rfl
  let tL : Multiplicative (Fin 3 → ZMod p) →* ModGL Tag.E6 K :=
    { toFun := fun v => ρ0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
        ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
        ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul]
        exact mul_rearrange (c01 _ _) (c02 _ _) (c12 _ _) }
  have htL : ∀ v, tL v = ρ0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
      ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
      ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))) := fun _ => rfl
  have htmem : ∀ v, tL v ∈ adjointGroup Tag.E6 K := fun v =>
    mul_mem (mul_mem (frame_mem hf0 _) (frame_mem hf1 _)) (frame_mem hf2 _)
  let t := tL.codRestrict (adjointGroup Tag.E6 K) htmem
  have hzero : ∀ a : ZMod p, (u (Multiplicative.ofAdd a)) ^ 3 = 1 → a = 0 := by
    intro a ha
    rw [hu, toAdd_ofAdd, ← pow_mul] at ha
    have hdvd := orderOf_dvd_of_pow_eq_one ha
    rw [hτ] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt a))
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3) hp3
  have hinj : Function.Injective t := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : tL v = 1 := congrArg Subtype.val hv
    rw [htL] at hv'
    set a0 := u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))
    set a1 := u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))
    set a2 := u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))
    have e0 : ρ0 a0 = (ρ1 a1 * ρ2 a2)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hv')
    have hc0 : ∀ X, Commute (ρ0 a0) (ρ0 X) := fun X => by
      rw [e0]
      exact (((c01 X a1).symm.mul_left (c02 X a2).symm)).inv_left
    have hv0 : Multiplicative.toAdd v 0 = 0 := hzero _ (pow_three_eq_one_of_commute hi0 hc0)
    have ha0 : a0 = 1 := by
      simp only [a0, hv0, ofAdd_zero, map_one]
    rw [ha0, map_one, one_mul] at hv'
    have e1 : ρ1 a1 = (ρ2 a2)⁻¹ := eq_inv_of_mul_eq_one_left hv'
    have hc1 : ∀ X, Commute (ρ1 a1) (ρ1 X) := fun X => by
      rw [e1]
      exact (c12 X a2).symm.inv_left
    have hv1 : Multiplicative.toAdd v 1 = 0 := hzero _ (pow_three_eq_one_of_commute hi1 hc1)
    have ha1 : a1 = 1 := by
      simp only [a1, hv1, ofAdd_zero, map_one]
    rw [ha1, map_one, one_mul] at hv'
    have ha2 : a2 = 1 := hi2 (by rw [hv', map_one])
    have hv2 : Multiplicative.toAdd v 2 = 0 := by
      apply hzero
      show a2 ^ 3 = 1
      rw [ha2, one_pow]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
  let x : adjointGroup Tag.E6 K := ⟨ρ0 σ, frame_mem hf0 σ⟩
  refine ⟨t, x, hinj, fun v => ?_⟩
  apply Subtype.ext
  change ρ0 σ * tL v * (ρ0 σ)⁻¹ = tL _
  rw [htL, htL]
  have hw1 : diagWeight p (Nat.card K) 1 = 1 := if_neg (by decide)
  have hw2 : diagWeight p (Nat.card K) 2 = 1 := if_neg (by decide)
  have hw0 : diagWeight p (Nat.card K) 0 = (Nat.card K : ZMod p) := if_pos rfl
  simp only [toAdd_ofAdd, hw0, hw1, hw2, one_mul]
  have hσu : ∀ a : ZMod p, σ * u (Multiplicative.ofAdd a) * σ⁻¹ =
      u (Multiplicative.ofAdd ((Nat.card K : ZMod p) * a)) := by
    intro a
    rw [hu, hu, toAdd_ofAdd, toAdd_ofAdd]
    calc σ * τ ^ a.val * σ⁻¹ = (σ * τ * σ⁻¹) ^ a.val := conj_pow.symm
      _ = τ ^ (Nat.card K * a.val) := by rw [hστ, ← pow_mul]
      _ = τ ^ ((Nat.card K * a.val) % p) := (hmod _).symm
      _ = τ ^ ((Nat.card K % p * a.val) % p) := by rw [Nat.mod_mul_mod]
      _ = τ ^ (((Nat.card K : ZMod p) * a).val) := by rw [ZMod.val_mul, ZMod.val_natCast]
  have e : ρ0 σ * (ρ0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
      ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
      ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))) * (ρ0 σ)⁻¹ =
      ρ0 (σ * u (Multiplicative.ofAdd (Multiplicative.toAdd v 0)) * σ⁻¹) *
      ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
      ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))) := by
    rw [map_mul, map_mul, map_inv]
    have h1 := (c01 σ (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1)))).eq
    have h2 := (c02 σ (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))).eq
    calc _ = ρ0 σ * ρ0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) *
          (ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
          (ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2))) * (ρ0 σ)⁻¹)) := by
            simp only [mul_assoc]
      _ = ρ0 σ * ρ0 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 0))) * (ρ0 σ)⁻¹ *
          (ρ1 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 1))) *
          ρ2 (u (Multiplicative.ofAdd (Multiplicative.toAdd v 2)))) := by
            rw [← (c02 σ _).inv_left.eq, ← mul_assoc (ρ1 _), ← (c01 σ _).inv_left.eq]
            simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  rw [e, hσu]

theorem ggTorusWNormSC_recipe_E6_phi3 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hp3 : p ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpq
  push_cast at h0
  have hq3 : ((Nat.card K : ℕ) : ZMod p) ^ 3 = 1 := by
    have e : ((Nat.card K : ℕ) : ZMod p) ^ 3 - 1 =
        ((Nat.card K : ZMod p) - 1) * ((Nat.card K : ZMod p) ^ 2 + Nat.card K + 1) := by ring
    rw [h0, mul_zero, sub_eq_zero] at e
    exact e
  have hq1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    rw [h1] at h0
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      rw [← h0]
      push_cast
      ring
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hq3 hq1
  have hQ0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num)] at hq3
    exact zero_ne_one hq3
  have hQ : ((Nat.card K : ℕ) : ZMod p) ^ 2 ≠ 1 := by
    intro h2
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [he] at hd
    norm_num at hd
  obtain ⟨t, x, htinj, hx⟩ := exists_reference (K := K) (p := p) hp3 (by exact hpq)
  have hS : SylowTorus (adjointGroup Tag.E6 K) p 3 := by
    have hS' : SylowTorus (adjointGroup Tag.E6 K) p ([3, 3, 3].count 3) :=
      PRankBounds.sylowTorus_of_blocks_of_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp (by omega)
        (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3] e6Three_charpoly e6Three_pow he
        (by norm_num) (by decide) (by decide) (by decide)
    exact hS'
  exact ggTorusWNormSC_of_reference hp (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (TableBExc.ggOutdiagPrime_E6 (K := K) hp hp3) (ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3)
    (TableBExc.recipeEquiv .E6 K) hS htinj hx hQ0 hQ

theorem largeEvenLabelAll_wnorm_E6_phi3 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .E6) (hpq : p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E6_phi3 hp hp7 (by rw [hK]; exact hpq)

end E6PhiThree

end CFSG.StandardType

end
