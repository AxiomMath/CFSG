module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerBorel
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.PartBAssembly
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace PsiDiag.Adj


theorem torus_le_scalarSub {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan (adjDatum F K).isFiniteType
      (adjDatum F K).divisible)}
    (hE : ChevalleyExtras (adjDatum F K) K (xPar F) C O) (i : Fin τ.rank) :
    ⨆ j, torus (τ := τ) K j ≤ scalarSub (D := adjDatum F K) (xPar F) (Pi.single i 1) := by
  refine iSup_le fun j t ht => ?_
  obtain ⟨s, rfl⟩ := ht
  have htor : torusHom K j s = torusElt (D := adjDatum F K) (xPar F) j s := by
    have e1 : torusElt (D := adjDatum F K) (xPar F) j s =
        CFSG.LieType.Steinberg.weylElement (xPar F) j s *
          (CFSG.LieType.Steinberg.weylElement (xPar F) j 1)⁻¹ := rfl
    rw [e1, weylElement_xPar, ← weylElement_eq_xPar F j, mul_inv_cancel_right]
    rfl
  rw [htor]
  exact torusElt_mem_scalarSub hE j s (single_mem_roots (D := adjDatum F K) i)

theorem exists_mem_centralizer {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]
    [Finite K] [CharP K 2] {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan (adjDatum F K).isFiniteType
      (adjDatum F K).divisible)}
    (hE : ChevalleyExtras (adjDatum F K) K (xPar F) C O) {nW : Fin τ.rank → adjointGroup τ K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix (adjDatum F K).isFiniteType).toCoxeterSystem
      (weylAction (adjDatum F K).isFiniteType) (adjDatum F K).roots (adjDatum F K).rootGroup nW
      (torus (τ := τ) K))
    (hext : SteinbergExtras (adjDatum F K) nW (torus (τ := τ) K)) {a : ℕ}
    (hdet : τ.cartan.det = 2 ^ a) {G : Type*} [Group G] (ψ : adjointGroup τ K →* G)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup τ K)) {c : G}
    (hc : GGPsiInnerDiag (adjDatum F K) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) :=
  exists_mem_centralizer_of_ggPsiInnerDiag hE rfl hct.iSup_eq_top hdet
    (fun i _ hh => ggTorus_conj_single hct hext hE.param i (torus_le_scalarSub hE i) hh) ψ hker hc

end PsiDiag.Adj

section Genuine

theorem PsiDiag.Adj.exists_mem_centralizer_F4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] (ψ : adjointGroup .F4 K →* G)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K)) {c : G}
    (hc : GGPsiInnerDiag (f4Datum K) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  exact PsiDiag.Adj.exists_mem_centralizer (f4_chevalleyExtras K O C hC) (f4_isCTGroupDatum K)
    (f4_steinbergExtras K) (a := 0) (by rw [pow_zero]; exact det_cartan_F4) ψ hker hc

theorem PsiDiag.Adj.exists_mem_centralizer_E8 {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] (ψ : adjointGroup .E8 K →* G)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .E8 K)) {c : G}
    (hc : GGPsiInnerDiag (e8Datum K) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e8Datum K).isFiniteType
    (Dv := (e8Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  exact PsiDiag.Adj.exists_mem_centralizer (e8_chevalleyExtras K O C hC) (e8_isCTGroupDatum K)
    (e8_steinbergExtras K) (a := 0) (by rw [pow_zero]; exact det_cartan_E8) ψ hker hc

theorem ggPsiDiagInner_F4 :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU .F4 n f).D .F4 n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU .F4 n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f ψ G₀ hpres c _ hc
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker hc

theorem ggPsiDiagInner_E8 :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .E8 n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU .E8 n f).D .E8 n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU .E8 n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f ψ G₀ hpres c _ hc
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker hc

end Genuine

end CFSG.StandardType
