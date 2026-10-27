module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSL
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogD
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLabelledD

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped MatrixGroups


theorem rckSpin_cover_of_tree {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ}
    (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {n : ℕ} (hn : 4 ≤ n) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hroots : componentRoots (rootCharHom a) i = rootsOfFam β (Set.range l))
    (hgram : ∀ c d : Fin n, c ≠ d → ¬ edgeD n c d → ¬ edgeD n d c →
      iform (β (l c)) (β (l d)) = 0)
    (hframe : ∀ {F : Type} [Field F] (c d : Fin n), edgeD n c d →
      ∃ θ : SL(3, F) →* ModGL τ F,
        θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l c)) ∧
          θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l d)))
    {h : ℕ} (hq : S.D.q = 2 ^ h) :
    ∃ φ : (ggU .POmegaPlus n
        (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).K →* ModGL τ GGL,
      φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (ggU .POmegaPlus n
          (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).K := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hes : 0 < h * s := Nat.mul_pos (carrierSL_exp_pos S hq) hs0
  obtain ⟨σ, hfin, hcardσ, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  have hcard : Nat.card ↥(fixSubfield σ) = 2 ^ (h * s) := by
    rw [hcardσ, hq, ← pow_mul]
  have hcomp : componentRootSpan ↥(fixSubfield σ) (rootCharHom a) i =
      rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l)) := by
    show rootSpan τ ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram
    (hframe (F := ↥(fixSubfield σ)))
  obtain ⟨e⟩ := @carrierSL_fieldEquiv ↥(fixSubfield σ) inferInstance hfin (h * s) hes hcard
  let φ₂ : SL(2, GaloisField 2 (h * s)) →* SL(2, ↥(fixSubfield σ)) :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let φ₃ : SL(3, GaloisField 2 (h * s)) →* SL(3, ↥(fixSubfield σ)) :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B hAB => by
    have h' := congrArg (Matrix.SpecialLinearGroup.map e.symm.toRingHom) hAB
    simp only [φ₂] at h'
    rwa [map_map_symm e, map_map_symm e] at h'
  have hφ₂surj : Function.Surjective φ₂ := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom A, by
      simpa [φ₂] using map_symm_map e A⟩
  let ρ' : Fin n → SL(2, GaloisField 2 (h * s)) →*
      ↥(rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l))) :=
    fun k => (ρ k).comp φ₂
  have hρ' : ∀ k, Function.Injective (ρ' k) ∧ (ρ' k).range = U k := by
    intro k
    refine ⟨(hρ k).1.comp hφ₂inj, ?_⟩
    rw [← (hρ k).2]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨φ₂ y, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  have hψ' : ∀ i j : Fin n, edgeD n i j →
      ∃ ψ' : SL(3, GaloisField 2 (h * s)) →*
        ↥(rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l))),
        ψ'.comp (blk (GaloisField 2 (h * s)) 0) = ρ' i ∧
          ψ'.comp (blk (GaloisField 2 (h * s)) 1) = ρ' j := by
    intro i j hij
    obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
    refine ⟨ψ.comp φ₃, ?_, ?_⟩
    · apply MonoidHom.ext
      intro A
      change ψ (φ₃ (blk (GaloisField 2 (h * s)) 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.toRingHom 0 A)
    · apply MonoidHom.ext
      intro A
      change ψ (φ₃ (blk (GaloisField 2 (h * s)) 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.toRingHom 1 A)
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaPlus n 2 (h * s) :=
    ⟨Nat.prime_two, hes, hn⟩
  obtain ⟨Ψ, hsurj, hkerΨ, hqs, hcent, -⟩ :=
    weakCT_spinPlus_of_frame hadm (by omega) (GaloisField.card 2 (h * s) (by omega))
      U hgen hcomm hρ' hψ'
  rw [← hcomp] at hqs
  let m : ↥(rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l))) →*
      ↥(componentRootSpan ↥(fixSubfield σ) (rootCharHom a) i) :=
    (MulEquiv.subgroupCongr hcomp).symm.toMonoidHom
  let φ : spinGroup (Spin.quadPlus n (GaloisField 2 (h * s))) →* ModGL τ GGL :=
    f.comp (m.comp Ψ)
  have hm_inj : Function.Injective m := fun a b h => by
    have := congrArg (MulEquiv.subgroupCongr hcomp) h
    simpa [m] using this
  have hm_surj : Function.Surjective m := fun x =>
    ⟨(MulEquiv.subgroupCongr hcomp) x, by simp [m]⟩
  have hrange : φ.range = f.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨m (Ψ x), rfl⟩
    · rintro _ ⟨c, rfl⟩
      obtain ⟨x', hx'⟩ := hm_surj c
      obtain ⟨x, rfl⟩ := hsurj x'
      exact ⟨x, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hx']⟩
  have hCperf : Group.IsPerfect ↥(componentRootSpan ↥(fixSubfield σ)
      (rootCharHom a) i) := hqs.1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hCperf)) hf1
  rw [ggU_pOmegaPlus (by omega)]
  refine ⟨φ, ?_, ?_⟩
  · rw [hrange, hRf]
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hyC : m (Ψ x) ∈ Subgroup.center
        ↥(componentRootSpan ↥(fixSubfield σ) (rootCharHom a) i) := by
      apply hker
      rw [MonoidHom.mem_ker]
      simpa [φ] using hx
    have hyX : Ψ x ∈ Subgroup.center
        ↥(rootSpan τ ↥(fixSubfield σ) (rootsOfFam β (Set.range l))) := by
      rw [Subgroup.mem_center_iff] at hyC ⊢
      intro a
      apply hm_inj
      rw [map_mul, map_mul]
      exact hyC (m a)
    have hycent : Ψ x ∈ (Subgroup.center
        (spinGroup (Spin.quadPlus n (GaloisField 2 (h * s))))).map Ψ := by
      rw [← hcent]
      exact hyX
    obtain ⟨z, hz, hzy⟩ := hycent
    have hmem : z⁻¹ * x ∈ Ψ.ker := by
      rw [MonoidHom.mem_ker]
      change Ψ (z⁻¹ * x) = 1
      rw [map_mul, map_inv, hzy]
      simp
    have hzx : z⁻¹ * x ∈ Subgroup.center
        (spinGroup (Spin.quadPlus n (GaloisField 2 (h * s)))) := hkerΨ hmem
    have hxcenter : x ∈ Subgroup.center
        (spinGroup (Spin.quadPlus n (GaloisField 2 (h * s)))) := by
      have hprod : z * (z⁻¹ * x) = x := by group
      rw [← hprod]
      exact Subgroup.mul_mem _ hz hzx
    exact hxcenter

theorem rckSpin_cover
    {τ : Tag} {p₀ : ℕ}
    (S : LangSetup τ GGL p₀) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hap : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {h : ℕ} (hq : S.D.q = 2 ^ h) :
    ∃ φ : (ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i))
        (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).K →* ModGL τ GGL,
      φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i))
          (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))).K := by
  obtain ⟨n, β, l, hnr, hβ, hroots, hgram, hframe⟩ :=
    rckD_labelled hτ S hp (carrierSL_natCast_ne_zero hp hp2) hap i h4 hn
  rw [← hnr]
  exact rckSpin_cover_of_tree hτ S hT i hinner (by rw [hnr]; exact h4) β hβ l hroots hgram
    hframe hq

end CFSG.StandardType.RCKRP

end
