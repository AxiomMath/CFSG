module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux3
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux5
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux4Pin

public section

namespace CFSG.StandardType.RCKRP

attribute [local instance] ZMod.algebra

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

theorem rckTw_cover_E78_of_field
    {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ CoeffField p₀) {a : Fin τ.rank → CoeffFieldˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ (φ : twistedE6Group 2 h →* ModGL τ CoeffField) (σ : CoeffField ≃+* CoeffField) (z : ModGL τ CoeffField)
        (γ : Fin τ.rank → ℤ),
        φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (twistedE6Group 2 h) ∧
        (∀ c, σ c = c ^ 2 ^ h) ∧ z ∈ rootSpan τ CoeffField (componentRoots (rootCharHom a) i) ∧
        φ.range ≤ rootSpan τ CoeffField (componentRoots (rootCharHom a) i) ∧ IsRoot τ γ ∧
        γ ∈ componentRoots (rootCharHom a) i ∧ -γ ∈ componentRoots (rootCharHom a) i ∧
        (∀ g ∈ rootSpan τ CoeffField ({γ, -γ} : Set (Fin τ.rank → ℤ)),
          S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
        ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
            (MulAut.conj z).toMonoidHom ∧
        ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) (-γ)).map
            (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  classical
  have hτ : M27Ok τ := ‹M27Ok τ›
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
    rckTw78_hρ (p₀ := p₀) S hT i v hΨ
  have hΦ' := rckTw78_frob S hq
  haveI : CharP CoeffField 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) CoeffField).injective 2
  set nv := canonicalRep (coxeterSystem τ) CoeffField v with hnv
  set nw := canonicalRep (coxeterSystem τ) CoeffField w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (e6Nodes τ), IsRoot τ α := fun α hα => hα.1
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ' : Ψ = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := hΨ
  have hmodel : rootSpan τ CoeffField Ψ ⊓ S.D.model = rootSpan τ CoeffField Ψ ⊓
      twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup CoeffField _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ']
      exact hxF
  have htrans := rootSpan_inf_twistedFixedPoints_smul (iterateFrobenius CoeffField 2 h) v nw hroots
  have hnvM := canonicalRep_mem_monomialSubgroup CoeffField v
  have hnwM := canonicalRep_mem_monomialSubgroup CoeffField w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ CoeffField :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  obtain ⟨u, hu, hact⟩ := rckTw78_hπρ S hT i v hΨ hout hn nv nw hnv hnw hn'M hρ
  obtain ⟨q, n₁, hL, hq0, hn₁, hh', hnq, hgen, hlangpt⟩ :=
    rckTw78_lang_pt (τ := τ) (L := CoeffField) (ℓ := 2) (f := h) (by omega) hn'M
      (fun i hi => rhoτ_mem hi) (fun i hi => rhoτ_symm_mem hi) hu hact
  have hstd : StdTwist6 n₁ (rhoτ τ) := ⟨Or.inr rfl, hgen⟩
  have hrange : stdLayer τ 2 h n₁ = (psi2 τ CoeffField 2 h).range :=
    hstd.stdLayer_eq_range_of_rho rfl
  have hconj := rckTw78_hconj h nv nw hL n₁ hh' hlangpt
  have hP : rootSpan τ CoeffField Ψ ⊓ S.D.model =
      (rootSpan τ CoeffField (parabolicRoots τ (e6Nodes τ)) ⊓
        twistedFixedPoints (nv⁻¹ * nw * nv)
          (Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)))).map (MulAut.conj nv).toMonoidHom := by
    rw [hmodel, hΨ']
    exact htrans
  have hrangeφ0 := rckTw78_phi_range h hh nv hL _ _ hP (hconj.trans hrange)
  have hqsP := rckTw78_phi_quasisimple h hh (nv * hL⁻¹) _ hrangeφ0
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = rootSpan τ CoeffField Ψ ⊓ S.D.model :=
    rationalComponent_eq_of_layer S i hρ hqsP
  have hfin : Ψ.Finite :=
    (root_character_kernel_orthogonal_central_product τ CoeffField (rootCharHom a)).1.subset
      (fun α hα => by
        have hα' := hα
        simp only [hΨdef, componentRoots, Set.mem_setOf_eq] at hα'
        exact hα'.choose)
  have horbit : componentOrbitLength S.ρ Ψ = 1 := componentOrbitLength_eq_one hfin hρ
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := CoeffField) 2 h
  have hσc : ∀ c, σ c = c ^ 2 ^ h := by
    intro c
    change σ.toRingHom c = c ^ 2 ^ h
    rw [hσ, iterateFrobenius_def]
  set e₁ : Fin τ.rank → ℤ := Pi.single (e6Idx 1) 1 with he₁
  set γ : Fin τ.rank → ℤ := v • e₁ with hγ
  have hγroot : IsRoot τ γ := IsRoot.smul (isRoot_single τ (e6Idx 1)) v
  have hγmem : γ ∈ componentRoots (rootCharHom a) i := by
    rw [← hΨdef, hΨ']
    exact ⟨e₁, single_mem_parabolicRoots_e6 (e6Idx 1)
      (by have h := e6Set_lt (τ := τ) (e6Idx_mem_e6Set (τ := τ) 1)
          have hr : Tag.E6.rank = 6 := rfl
          omega), rfl⟩
  have hnegmem : -γ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem γ hγmem
  set z : ModGL τ CoeffField := nv * hL⁻¹ * nv⁻¹ with hz
  have hh_adj : hL ∈ adjointGroup τ CoeffField := by
    rw [subsystemGroup_eq_rootSpan] at hh'
    exact rootSpan_le_adjointGroup CoeffField _ hh'
  have hzadj : z ∈ adjointGroup τ CoeffField :=
    mul_mem (mul_mem (monomialSubgroup_le_adjointGroup' hnvM) (inv_mem hh_adj))
      (inv_mem (monomialSubgroup_le_adjointGroup' hnvM))
  have hn₁fix := rckTw78_n1fix n₁ hgen
  have hhP : hL⁻¹ ∈ rootSpan τ CoeffField (parabolicRoots τ (e6Nodes τ)) := by
    have h1 := inv_mem hh'
    rwa [subsystemGroup_eq_rootSpan, ← e6Nodes_eq_e6Set] at h1
  have hzspan : z ∈ rootSpan τ CoeffField Ψ := by
    have h1 : z ∈ (rootSpan τ CoeffField (parabolicRoots τ (e6Nodes τ))).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) CoeffField v)).toMonoidHom := ⟨hL⁻¹, hhP, rfl⟩
    rw [CFSG.RankThree.PartOne.KE.map_conj_rootSpan v hroots] at h1
    rwa [← hΨ'] at h1
  have hφspan : (rckTw78_phi h hh (nv * hL⁻¹)).range ≤ rootSpan τ CoeffField Ψ :=
    hrangeφ0.le.trans inf_le_left
  refine ⟨horbit, rckTw78_phi h hh (nv * hL⁻¹), σ, z, γ, hrangeφ0.trans hR.symm,
    rckTw78_phi_ker h hh (nv * hL⁻¹), hσc, hzspan, hφspan, hγroot, hγmem, hnegmem, ?_, ?_, ?_⟩
  · exact rckTw78_untwist S v nv nw hL n₁ σ hnv hn hΦ' hlangpt hn₁fix hσc
  · exact rckTw78_pin_core h hh σ hσ v nv hL _ z hnv hz rfl
  · have h' := rckTw78_pin_core_neg h hh σ hσ v nv hL _ z hnv hz rfl
    rw [smul_neg] at h'
    exact h'

theorem rckTw_cover_E78
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ (φ : twistedE6Group 2 h →* ModGL τ GGL) (σ : GGL ≃+* GGL) (z : ModGL τ GGL)
        (γ : Fin τ.rank → ℤ),
        φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (twistedE6Group 2 h) ∧
        (∀ c, σ c = c ^ 2 ^ h) ∧ z ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) ∧
        φ.range ≤ rootSpan τ GGL (componentRoots (rootCharHom a) i) ∧ IsRoot τ γ ∧
        γ ∈ componentRoots (rootCharHom a) i ∧ -γ ∈ componentRoots (rootCharHom a) i ∧
        (∀ g ∈ rootSpan τ GGL ({γ, -γ} : Set (Fin τ.rank → ℤ)),
          S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
        ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
            (MulAut.conj z).toMonoidHom ∧
        ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) (-γ)).map
            (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  exact rckTw_cover_E78_of_field S hT i v hΨ hout hh hq

end CFSG.StandardType.RCKRP

end
