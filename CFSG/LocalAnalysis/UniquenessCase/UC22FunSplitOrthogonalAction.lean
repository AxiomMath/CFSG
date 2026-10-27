module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalBlocks
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Kernel
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockFixOfNormalW
import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
import CFSG.ClassicalInvolution.Asc77.AscR10E23
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameToral
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.AS81.Sec2
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section PairAction

variable {G ι : Type} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]

omit [Finite G] in
theorem exists_twoKernel_quotient_perm_of_faithful_pair_action
    (φ : G →* Equiv.Perm (ι × Bool)) (hinj : Function.Injective φ)
    (hblock : ∀ g : G, φ g ∈ blockStab ι)
    (hfull : ∀ σ : Equiv.Perm ι, ∃ g : G, ∀ x : ι × Bool, (φ g x).1 = σ x.1) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 N ∧
      Nonempty (G ⧸ N ≃* Equiv.Perm ι) := by
  let ψ : G →* blockStab ι := φ.codRestrict (blockStab ι) hblock
  let β : G →* Equiv.Perm ι := blockMapHom.comp ψ
  have hβ : Function.Surjective β := by
    intro σ
    obtain ⟨g, hg⟩ := hfull σ
    refine ⟨g, Equiv.ext fun i => ?_⟩
    exact (blockMapHom_apply (ψ g) (i, false)).trans (hg (i, false))
  have hker : IsPGroup 2 β.ker := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hinj
    have hβg : β g = 1 := g.2
    have hfix : φ g ∈ blockFix ι :=
      mem_blockFix_of_blockMap_eq_one (hblock g) hβg
    change φ ((g : G) ^ (2 ^ 1)) = φ 1
    rw [map_pow, map_one, pow_one, pow_two]
    exact blockFix_sq hfix
  exact ⟨β.ker, inferInstance, hker, ⟨QuotientGroup.quotientKerEquivOfSurjective β hβ⟩⟩

omit [Finite G] in
theorem exists_twoKernel_quotient_perm_of_paired_conjPermHom
    {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}
    (e : ι × Bool ≃ Δ)
    (hblock : ∀ g : conjSetStab Δ,
      e.symm.permCongrHom (conjPermHom (le_refl (conjSetStab Δ)) g) ∈ blockStab ι)
    (hfull : ∀ σ : Equiv.Perm ι, ∃ g : conjSetStab Δ, ∀ x : ι × Bool,
      (e.symm (conjPermHom (le_refl (conjSetStab Δ)) g (e x))).1 = σ x.1) :
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    ∃ (N : Subgroup ρ.range) (_ : N.Normal), IsPGroup 2 N ∧
      Nonempty (ρ.range ⧸ N ≃* Equiv.Perm ι) := by
  let ρ := conjPermHom (le_refl (conjSetStab Δ))
  let φ : ρ.range →* Equiv.Perm (ι × Bool) :=
    e.symm.permCongrHom.toMonoidHom.comp ρ.range.subtype
  apply exists_twoKernel_quotient_perm_of_faithful_pair_action φ
    (e.symm.permCongrHom.injective.comp ρ.range.subtype_injective)
  · rintro ⟨g, x, rfl⟩
    exact hblock x
  · intro σ
    obtain ⟨g, hg⟩ := hfull σ
    refine ⟨⟨ρ g, g, rfl⟩, ?_⟩
    intro x
    exact hg x

end PairAction

section Conjugations


theorem mem_conjSetStab_of_paired_conjugation
    {X ι : Type} [Group X] [Finite ι] (L : ι × Bool → Subgroup X)
    (σ : Equiv.Perm ι) (g : X)
    (h : ∀ i,
      ({(L (i, false)).map (MulAut.conj g).toMonoidHom,
        (L (i, true)).map (MulAut.conj g).toMonoidHom} : Set (Subgroup X)) =
        {L (σ i, false), L (σ i, true)}) :
    g ∈ conjSetStab (Set.range L) := by
  classical
  let Δ := Set.range L
  have hm : Set.MapsTo (Subgroup.map (MulAut.conj g).toMonoidHom) Δ Δ := by
    rintro H ⟨⟨i, b⟩, rfl⟩
    have hx : (L (i, b)).map (MulAut.conj g).toMonoidHom ∈
        ({L (σ i, false), L (σ i, true)} : Set (Subgroup X)) := by
      rw [← h i]
      cases b <;> simp
    rcases hx with hx | hx
    · exact ⟨(σ i, false), hx.symm⟩
    · exact ⟨(σ i, true), hx.symm⟩
  let f : Δ → Δ := fun H => ⟨H.1.map (MulAut.conj g).toMonoidHom, hm H.2⟩
  have hf : Function.Injective f := by
    intro H J heq
    apply Subtype.ext
    exact Subgroup.map_injective (MulAut.conj g).injective (congrArg Subtype.val heq)
  have hs : Function.Surjective f := Finite.surjective_of_injective hf
  apply (inv_mem_iff (H := conjSetStab Δ)).mp
  rw [mem_conjSetStab]
  intro H
  simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
  constructor
  · exact fun hH => hm hH
  · intro hH
    obtain ⟨J, hJ⟩ := hs ⟨H.map (MulAut.conj g).toMonoidHom, hH⟩
    have heq : J.1 = H :=
      Subgroup.map_injective (MulAut.conj g).injective (congrArg Subtype.val hJ)
    exact heq ▸ J.2

theorem paired_conjPermHom_fst
    {X ι : Type} [Group X] [Finite ι] (L : ι × Bool → Subgroup X)
    (e : ι × Bool ≃ Set.range L) (he : ∀ k, (e k : Subgroup X) = L k)
    (σ : Equiv.Perm ι) (g : X)
    (h : ∀ i,
      ({(L (i, false)).map (MulAut.conj g).toMonoidHom,
        (L (i, true)).map (MulAut.conj g).toMonoidHom} : Set (Subgroup X)) =
        {L (σ i, false), L (σ i, true)}) :
    ∀ x : ι × Bool,
      (e.symm (conjPermHom (le_refl (conjSetStab (Set.range L)))
        ⟨g, mem_conjSetStab_of_paired_conjugation L σ g h⟩ (e x))).1 = σ x.1 := by
  rintro ⟨i, b⟩
  let y := conjPermHom (le_refl (conjSetStab (Set.range L)))
    ⟨g, mem_conjSetStab_of_paired_conjugation L σ g h⟩ (e (i, b))
  have hy : (y : Subgroup X) = (L (i, b)).map (MulAut.conj g).toMonoidHom := by
    rw [conjPermHom_apply, he]
    simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
  have hpair : (y : Subgroup X) ∈ ({L (σ i, false), L (σ i, true)} : Set (Subgroup X)) := by
    rw [hy, ← h i]
    cases b <;> simp
  have hinj : Function.Injective L := by
    intro k l hkl
    apply e.injective
    apply Subtype.ext
    rw [he, he, hkl]
  have hey : L (e.symm y) = (y : Subgroup X) := by
    rw [← he, e.apply_symm_apply]
  rcases hpair with hpair | hpair
  · exact congrArg Prod.fst (hinj (hey.trans hpair))
  · exact congrArg Prod.fst (hinj (hey.trans hpair))

end Conjugations

section SpinPermutations

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

omit [Finite F] [FiniteDimensional F V] in
private theorem frame_pair_eq_of_span_eq (h2 : (2 : F) ≠ 0)
    (H A : OFrame Q) (hs : H.span = A.span) :
    ({H.La.range, H.swap.La.range} : Set (Subgroup (V ≃ₗ[F] V))) =
      {A.La.range, A.swap.La.range} := by
  have he := Frame.La_neg_one_eq_of_span_eq (F := A) hs
  have hs' : H.swap.span = A.span := H.span_eq_swap_span.trans hs
  have he' := Frame.La_neg_one_eq_of_span_eq (F := A) hs'
  have h0 := Frame.La_range_eq_or_eq_swap h2 he
  have h1 := Frame.La_range_eq_or_eq_swap h2 he'
  have hne : H.La.range ≠ H.swap.La.range := H.La_range_ne_swap_La_range
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact (hne (h0.trans h1.symm)).elim
  · rw [h0, h1]
  · rw [h0, h1]
    exact Set.pair_comm _ _
  · exact (hne (h0.trans h1.symm)).elim

omit [Finite F] [FiniteDimensional F V] in
private theorem frame_map_span_eq_of_preserves
    (A : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hp : ∀ x ∈ A.span, g x ∈ A.span) : (A.map hg).span = A.span := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨Y, rfl⟩
    rw [Frame.map_incl]
    exact hp _ ⟨Y, rfl⟩
  · rw [Frame.finrank_span, Frame.finrank_span]

omit [Finite F] [FiniteDimensional F V] in
private theorem frame_map_span_eq_of_fixes
    (A : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hp : ∀ x ∈ A.span, g x = x) : (A.map hg).span = A.span :=
  frame_map_span_eq_of_preserves A hg (fun x hx => by rw [hp x hx]; exact hx)

theorem exists_spin_permutation_frame_pairs
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 0 < m) (A : Fin m → OFrame Q)
    (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) (σ : Equiv.Perm (Fin m)) :
    ∃ x : spinGroup Q, ∀ i,
      ({(A i).La.range.map (MulAut.conj (spinAction Q x)).toMonoidHom,
        (A i).swap.La.range.map (MulAut.conj (spinAction Q x)).toMonoidHom} :
          Set (Subgroup (V ≃ₗ[F] V))) =
        {(A (σ i)).La.range, (A (σ i)).swap.La.range} := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  let : Invertible (2 : F) := invertibleOfNonzero h2
  let k : Fin m := ⟨0, hm⟩
  have : Nontrivial V := ⟨⟨(A k).e₁, 0, (A k).P.e_ne_zero⟩⟩
  let η : Fin m × Bool ≃ Fin (m * 2) :=
    (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans (finProdFinEquiv)
  let v := CFSG.LieType.SeitzGeneration.ExcHigh.frameFam A η
  let v' := CFSG.LieType.SeitzGeneration.ExcHigh.frameFam (fun i => A (σ i)) η
  have hv : CFSG.ClassicalInvolution.ModelFacts.OrthAut.IsHypFam Q v :=
    CFSG.LieType.SeitzGeneration.ExcHigh.isHypFam_frameFam A η
      (fun i j hij x hx y hy => (ho i j hij).polar_zero hx hy)
  have hv' : CFSG.ClassicalInvolution.ModelFacts.OrthAut.IsHypFam Q v' :=
    CFSG.LieType.SeitzGeneration.ExcHigh.isHypFam_frameFam (fun i => A (σ i)) η
      (fun i j hij x hx y hy => (ho _ _ (σ.injective.ne hij)).polar_zero hx hy)
  have hP : (Q.restrict (A k).span).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (A k).polarNondegOn_span)
  obtain ⟨x, h, hh, hp, hfix, hvec⟩ :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.exists_spin_normalization_isometry hodd
      (QuadraticMap.nondegenerate_polar_iff.mp hQ) hv hv' hP (by rw [Frame.finrank_span]; omega)
  let g := spinAction Q x
  have hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun z => map_spinAction Q x z
  have hvec' : ∀ i b s, CFSG.LieType.SeitzGeneration.ExcHigh.pairVec (A (σ i)) b s =
      g (h (CFSG.LieType.SeitzGeneration.ExcHigh.pairVec (A i) b s)) := by
    intro i b s
    simpa [v, v', CFSG.LieType.SeitzGeneration.ExcHigh.frameFam] using hvec (η (i, b)) s
  have hframe : ∀ i, ((A i).map hh).map hg = A (σ i) := by
    intro i
    apply CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec
    · exact (hvec' i false true).symm
    · exact (hvec' i false false).symm
    · exact (hvec' i true true).symm
    · exact (hvec' i true false).symm
  have hspan : ∀ i, ((A i).map hh).span = (A i).span := by
    intro i
    by_cases hik : i = k
    · subst i
      exact frame_map_span_eq_of_preserves (A k) hh hp
    · apply frame_map_span_eq_of_fixes (A i) hh
      intro z hz
      apply hfix
      intro y hy
      exact (ho k i (Ne.symm hik)).polar_zero hy hz
  refine ⟨x, fun i => ?_⟩
  have hpair := frame_pair_eq_of_span_eq h2 ((A i).map hh) (A i) (hspan i)
  have himage := congrArg (Set.image (Subgroup.map (MulAut.conj g).toMonoidHom)) hpair
  have map_group : ∀ B : OFrame Q,
      B.La.range.map (MulAut.conj g).toMonoidHom = (B.map hg).La.range := by
    intro B
    ext z
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨M, rfl⟩, rfl⟩
      exact ⟨M, B.map_La hg M⟩
    · rintro ⟨M, rfl⟩
      exact ⟨B.La M, ⟨M, rfl⟩, (B.map_La hg M).symm⟩
  have hswap : ∀ B : OFrame Q, (B.map hg).swap = B.swap.map hg := fun B => by
    cases B with
    | mk P P' h => cases P'; rfl
  simp only [Set.image_pair, map_group, ← hswap, hframe] at himage
  change ({(A i).La.range.map (MulAut.conj g).toMonoidHom,
    (A i).swap.La.range.map (MulAut.conj g).toMonoidHom} : Set (Subgroup (V ≃ₗ[F] V))) = _
  simpa only [map_group, ← hswap] using himage.symm

end SpinPermutations

section ModelPermutations


variable {p n e m : ℕ} [hp : Fact p.Prime] {t : StatedLieTag}
  {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem model_frame_pair_conjugation_of_geometric
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin m → OFrame Q)
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (u : (modelUniv t n p e hp.out).K) (σ : Equiv.Perm (Fin m))
    (hperm : ∀ i,
      ({(A i).La.range.map (MulAut.conj (π u)).toMonoidHom,
        (A i).swap.La.range.map (MulAut.conj (π u)).toMonoidHom} :
          Set (Subgroup (V ≃ₗ[F] V))) =
        {(A (σ i)).La.range, (A (σ i)).swap.La.range}) :
    ∀ i,
      ({(R (i, false)).map (MulAut.conj u).toMonoidHom,
        (R (i, true)).map (MulAut.conj u).toMonoidHom} :
          Set (Subgroup (modelUniv t n p e hp.out).K)) =
        {R (σ i, false), R (σ i, true)} := by
  intro i
  have hmapF : (R (i, false)).map π = (A i).La.range := by simpa using (hR (i, false)).2
  have hmapT : (R (i, true)).map π = (A i).swap.La.range := by simpa using (hR (i, true)).2
  have hσF : (R (σ i, false)).map π = (A (σ i)).La.range := by simpa using (hR (σ i, false)).2
  have hσT : (R (σ i, true)).map π = (A (σ i)).swap.La.range := by simpa using (hR (σ i, true)).2
  have himage : Subgroup.map π ''
      ({(R (i, false)).map (MulAut.conj u).toMonoidHom,
        (R (i, true)).map (MulAut.conj u).toMonoidHom} :
          Set (Subgroup (modelUniv t n p e hp.out).K)) =
      Subgroup.map π '' ({R (σ i, false), R (σ i, true)} :
        Set (Subgroup (modelUniv t n p e hp.out).K)) := by
    simp only [Set.image_pair, CFSG.ClassicalInvolution.ModelFacts.map_conj_map,
      hmapF, hmapT, hσF, hσT]
    exact hperm i
  have hmem : ∀ {S}, S ∈
      ({(R (i, false)).map (MulAut.conj u).toMonoidHom,
        (R (i, true)).map (MulAut.conj u).toMonoidHom} :
          Set (Subgroup (modelUniv t n p e hp.out).K)) →
      S ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D := by
    rintro S (rfl | rfl)
    · exact conjSub_mem_fundamentalSubgroups (hR (i, false)).1 u
    · exact conjSub_mem_fundamentalSubgroups (hR (i, true)).1 u
  have hσmem : ∀ {S}, S ∈ ({R (σ i, false), R (σ i, true)} :
      Set (Subgroup (modelUniv t n p e hp.out).K)) →
      S ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D := by
    rintro S (rfl | rfl)
    · exact (hR (σ i, false)).1
    · exact (hR (σ i, true)).1
  ext S
  constructor
  · intro hS
    have hSm : S.map π ∈ Subgroup.map π '' ({R (σ i, false), R (σ i, true)} :
        Set (Subgroup (modelUniv t n p e hp.out).K)) := himage ▸ ⟨S, hS, rfl⟩
    obtain ⟨T, hT, heq⟩ := hSm
    have hST := eq_modelFund_of_map_eq hp2 hfund hadm π hπker (hmem hS) (hσmem hT) heq.symm
    exact hST.symm ▸ hT
  · intro hS
    have hSm : S.map π ∈ Subgroup.map π ''
        ({(R (i, false)).map (MulAut.conj u).toMonoidHom,
          (R (i, true)).map (MulAut.conj u).toMonoidHom} :
            Set (Subgroup (modelUniv t n p e hp.out).K)) := himage.symm ▸ ⟨S, hS, rfl⟩
    obtain ⟨T, hT, heq⟩ := hSm
    have hST := eq_modelFund_of_map_eq hp2 hfund hadm π hπker (hσmem hS) (hmem hT) heq.symm
    exact hST.symm ▸ hT

theorem exists_paired_conjPermHom_of_model_frame_permutations
    {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin m → OFrame Q)
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (ψ : (modelUniv t n p e hp.out).K →* X)
    (ePair : Fin m × Bool ≃ Δ)
    (hePair : ∀ k, (ePair k : Subgroup X) = (R k).map ψ)
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ u : (modelUniv t n p e hp.out).K, ∀ i,
      ({(A i).La.range.map (MulAut.conj (π u)).toMonoidHom,
        (A i).swap.La.range.map (MulAut.conj (π u)).toMonoidHom} :
          Set (Subgroup (V ≃ₗ[F] V))) =
        {(A (σ i)).La.range, (A (σ i)).swap.La.range}) :
    ∀ σ : Equiv.Perm (Fin m), ∃ g : conjSetStab Δ,
      ∀ x : Fin m × Bool,
        (ePair.symm (conjPermHom (le_refl (conjSetStab Δ))
          g (ePair x))).1 = σ x.1 := by
  have hΔ : Δ = Set.range (fun k => (R k).map ψ) := by
    ext L
    constructor
    · intro hL
      obtain ⟨k, hk⟩ := ePair.surjective ⟨L, hL⟩
      exact ⟨k, (hePair k).symm.trans (congrArg Subtype.val hk)⟩
    · rintro ⟨k, rfl⟩
      change (R k).map ψ ∈ Δ
      rw [← hePair k]
      exact (ePair k).2
  subst Δ
  intro σ
  obtain ⟨u, hu⟩ := hperm σ
  have hmodel := model_frame_pair_conjugation_of_geometric hp2 hfund hadm π hπker A R hR u σ hu
  have hψmodel : ∀ i,
      ({((R (i, false)).map ψ).map (MulAut.conj (ψ u)).toMonoidHom,
        ((R (i, true)).map ψ).map (MulAut.conj (ψ u)).toMonoidHom} : Set (Subgroup X)) =
        {(R (σ i, false)).map ψ, (R (σ i, true)).map ψ} := by
    intro i
    have hh := congrArg (Set.image (Subgroup.map ψ)) (hmodel i)
    simpa only [Set.image_pair, CFSG.ClassicalInvolution.ModelFacts.map_conj_map] using hh
  exact ⟨⟨ψ u, mem_conjSetStab_of_paired_conjugation (fun k => (R k).map ψ) σ (ψ u) hψmodel⟩,
    paired_conjPermHom_fst (fun k => (R k).map ψ) ePair hePair σ (ψ u) hψmodel⟩

end ModelPermutations

section ModelFamily


variable {p n e m : ℕ} [hp : Fact p.Prime] {t : StatedLieTag}
  {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem injective_map_paired_model_family
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (A : Fin m → OFrame Q) (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    {X : Type} [Group X] (ψ : (modelUniv t n p e hp.out).K →* X)
    (hker : ψ.ker ≤ center (modelUniv t n p e hp.out).K) :
    Function.Injective (fun k => (R k).map ψ) := by
  intro i j heq
  by_contra hij
  have hc : Commutes (R i) (R j) := by
    apply commutes_modelFund_of_commutes_map hp2 hfund hadm π hπker (hR i).1
    rw [(hR i).2, (hR j).2]
    exact commutes_paired_frames A ho hij
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm (hR i).1 with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
  all_goals exact F14.map_ne_of_commuting_of_equiv_sl2 ψ hker eR hc heq


theorem exists_equiv_paired_model_funSet
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hX : LieModel X t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2)) (hm : 0 < m)
    (π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[F] V))
    (hπker : π.ker ≤ center (modelUniv t n p e hp.out).K)
    (hπmap : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
      ∃ H : OFrame Q, R.map π = H.La.range)
    (A : Fin m → OFrame Q) (ho : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False)
    (R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K)
    (hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
      (R k).map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range)
    (h2 : (2 : F) ≠ 0) (ψ : (modelUniv t n p e hp.out).K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center (modelUniv t n p e hp.out).K)
    (P : Sylow 2 X) :
    ∃ (c : X) (ePair : Fin m × Bool ≃ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)),
      ∀ k, (ePair k : Subgroup X) =
        (R k).map ((MulAut.conj c).toMonoidHom.comp ψ) := by
  classical
  obtain ⟨c, hc⟩ := exists_full_paired_model_frame_funSet hp2 hfund hadm hX hA1 hm
    π hπker hπmap A ho hfull R hR h2 ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center (modelUniv t n p e hp.out).K := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hinj := injective_map_paired_model_family hp2 hfund hadm π hπker A ho R hR ψc hkerC
  let f : Fin m × Bool → F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) :=
    fun k => ⟨(R k).map ψc, hc.symm ▸ ⟨k, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hinj (congrArg Subtype.val hij)
    · rintro ⟨L, hL⟩
      rw [hc] at hL
      obtain ⟨k, hk⟩ := hL
      exact ⟨k, Subtype.ext hk⟩
  exact ⟨c, Equiv.ofBijective f hf, fun k => rfl⟩

end ModelFamily

section OrthogonalModels


structure PairedOrthogonalModel (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime] where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (GaloisField p e) V]
  [finiteDimensional : FiniteDimensional (GaloisField p e) V]
  Q : QuadraticForm (GaloisField p e) V
  m : ℕ
  hm : 0 < m
  η : (modelUniv t n p e hp.out).K ≃* spinGroup Q
  π : (modelUniv t n p e hp.out).K →* (V ≃ₗ[GaloisField p e] V)
  hπ : π = (spinAction Q).comp η.toMonoidHom
  hker : π.ker ≤ center (modelUniv t n p e hp.out).K
  hscalar : ∀ z ∈ center (modelUniv t n p e hp.out).K,
    π z ∈ scalars (GaloisField p e) V
  hQ : (polarBilin Q).Nondegenerate
  A : Fin m → OFrame Q
  horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)
  hfull : ∀ H : OFrame Q, (∀ i, SpanOrth H (A i)) → False
  R : Fin m × Bool → Subgroup (modelUniv t n p e hp.out).K
  hR : ∀ k, R k ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D ∧
    (R k).map π =
      if k.2 then (A k.1).swap.La.range else (A k.1).La.range
  hmap : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D,
    ∃ H : OFrame Q, R.map π = H.La.range

attribute [instance] PairedOrthogonalModel.addCommGroup PairedOrthogonalModel.module
  PairedOrthogonalModel.finiteDimensional

theorem exists_paired_orthogonal_model
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) :
    Nonempty (PairedOrthogonalModel t n p e) := by
  classical
  let F := GaloisField p e
  have hodd : Odd (Nat.card F) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  rcases ht with rfl | rfl | rfl
  · have hn3 : 3 ≤ n := hadm.2.2.1
    let Q := quadOdd n F
    have hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F) :=
      CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n p e
        hp.out trivial hadm (by decide) (by decide)
    obtain ⟨R, hR⟩ := exists_paired_frame_modelFund_pOmegaOdd hp2 hadm
    refine ⟨{
      V := Fin n ⊕ Fin n ⊕ Unit → F
      Q := Q
      m := n / 2
      hm := by omega
      η := MulEquiv.refl _
      π := spinAction Q
      hπ := by ext x; rfl
      hker := ker_spinAction_le_center Q
      hscalar := fun z hz => Gaps.spinAction_center_mem_scalars_odd h2 hn3 hz
      hQ := nondegenerate_polarBilin_quadOdd n F h2
      A := oddOrthogonalPairFrame F n
      horth := fun i j hij => spanOrth_oddOrthogonalPairFrame F n hij
      hfull := fun H h => not_spanOrth_all_oddOrthogonalPairFrame F n H h
      R := R
      hR := hR
      hmap := ?_ }⟩
    intro R hR
    obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet_odd hn3 hsc hR
    exact ⟨H, hH⟩
  · have hn4 : 4 ≤ n := hadm.2.2
    have hn3 : 3 ≤ n := by omega
    let Q := quadPlus n F
    obtain ⟨η, hη⟩ := plus_model_data (p := p) (e := e) hn3
    let π := (spinAction Q).comp η.toMonoidHom
    have hπker : π.ker ≤ center (modelUniv .POmegaPlus n p e hp.out).K := by
      intro x hx
      have hy : η x ∈ center (spinGroup Q) :=
        ker_spinAction_le_center Q (by simpa only [MonoidHom.mem_ker, π, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom] using hx)
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro y
      apply η.injective
      simpa only [map_mul] using hy (η y)
    have hsc : FundamentalSingleClass .POmegaPlus (plusDatum n F hn3) := by
      have hm := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus n p e
        hp.out trivial hadm (by decide) (by decide)
      have he := CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (p := p) (f := e) hn3
      change FundamentalSingleClass .POmegaPlus
        (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp.out).D at hm
      rw [he] at hm
      exact hm
    let A := plusOrthogonalPairFrame F n hn3
    have hex : ∀ k : Fin (n / 2) × Bool,
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D,
          R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
      intro k
      have hg : (if k.2 then (A k.1).swap.La.range else (A k.1).La.range) ∈ Gaps.fundSet Q := by
        cases k.2
        · exact ⟨_, IsFundamental.of_frame _⟩
        · exact ⟨_, IsFundamental.of_frame_swap _⟩
      obtain ⟨S, hS, hmap⟩ := Gaps.exists_map_eq hn3 hodd hg
      let R := S.map η.symm.toMonoidHom
      have hRmap : R.map η.toMonoidHom = S := by simp [R, Subgroup.map_map]
      refine ⟨R, (hη R).mpr (hRmap.symm ▸ hS), ?_⟩
      change R.map ((spinAction Q).comp η.toMonoidHom) = _
      rw [← Subgroup.map_map, hRmap]
      exact hmap
    choose R hR hmap using hex
    refine ⟨{
      V := Fin n ⊕ Fin n → F
      Q := Q
      m := n / 2
      hm := by omega
      η := η
      π := π
      hπ := rfl
      hker := hπker
      hscalar := ?_
      hQ := nondegenerate_polarBilin_quadPlus n F
      A := A
      horth := fun i j hij => spanOrth_plusOrthogonalPairFrame F n hn3 hij
      hfull := fun H h => not_spanOrth_all_plusOrthogonalPairFrame F n hn3 H h
      R := R
      hR := fun k => ⟨hR k, hmap k⟩
      hmap := ?_ }⟩
    · intro z hz
      apply Gaps.spinAction_center_mem_scalars hn3
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨x, rfl⟩ := η.surjective y
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg η (hz x)
    · intro R hR
      obtain ⟨i, H, hH, _⟩ := Gaps.map_mem_fundSet hn3 hsc ((hη R).mp hR)
      exact ⟨H, by simpa only [Subgroup.map_map] using hH⟩
  · have hn4 : 4 ≤ n := hadm.2.2
    let b := (CFSG.LieType.Universal.minusCoeffs p e).1
    let c := (CFSG.LieType.Universal.minusCoeffs p e).2
    let Q := quadMinus n F b c
    let π : (modelUniv .POmegaMinus n p e hp.out).K →* (_ ≃ₗ[F] _) := spinAction Q
    have hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := CFSG.LieType.Universal.minusCoeffs_irr p e
    have hcorr :
        (∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
          R.map π ∈ Gaps.fundSet Q) ∧
        ∀ L ∈ Gaps.fundSet Q,
          ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
            R.map π = L := by
      by_cases hq : 5 ≤ p ^ e
      · exact Exotic.fundCorr_minus hp2 hq hadm
      · have hq3 := (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
          hp.out hp2 hadm.2.1).resolve_right hq
        exact Exotic.fundCorr_minus3 hq3 hadm
    let A := minusOrthogonalPairFrame F n b c
    have hex : ∀ k : Fin ((n - 1) / 2) × Bool,
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
          R.map π = if k.2 then (A k.1).swap.La.range else (A k.1).La.range := by
      intro k
      apply hcorr.2
      cases k.2
      · exact ⟨_, IsFundamental.of_frame _⟩
      · exact ⟨_, IsFundamental.of_frame_swap _⟩
    choose R hR hmap using hex
    refine ⟨{
      V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F
      Q := Q
      m := (n - 1) / 2
      hm := by omega
      η := MulEquiv.refl _
      π := π
      hπ := by ext x; rfl
      hker := ker_spinAction_le_center Q
      hscalar := fun z hz => Exotic.spinAction_center_mem_scalars_minus hn4 hirr hz
      hQ := nondegenerate_polarBilin_quadMinus_of_finite n F hirr
      A := A
      horth := fun i j hij => spanOrth_minusOrthogonalPairFrame F n b c hij
      hfull := fun H h => not_spanOrth_all_minusOrthogonalPairFrame F n (by omega) hirr hodd H h
      R := R
      hR := fun k => ⟨hR k, hmap k⟩
      hmap := ?_ }⟩
    intro R hR
    obtain ⟨i, H, hH, _⟩ := hcorr.1 R hR
    exact ⟨H, hH⟩

end OrthogonalModels

section OrthogonalFamily


variable {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime]

theorem exists_equiv_paired_funSet_of_orthogonal_model
    (D : PairedOrthogonalModel t n p e)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hX : LieModel X t n p e) (hA1 : ¬ (t = .PSL ∧ n = 2)) (P : Sylow 2 X) :
    ∃ (ψ : (modelUniv t n p e hp.out).K →* X)
      (ePair : Fin D.m × Bool ≃ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)),
      Function.Surjective ψ ∧ ψ.ker ≤ center (modelUniv t n p e hp.out).K ∧
        ∀ k, (ePair k : Subgroup X) = (D.R k).map ψ := by
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨c, ePair, hePair⟩ := exists_equiv_paired_model_funSet hp2 hfund hadm hX hA1 D.hm
    D.π D.hker D.hmap D.A D.horth D.hfull D.R D.hR h2 ψ hψ hker P
  let ψc := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (modelUniv t n p e hp.out).K := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  exact ⟨ψc, ePair, hψc, hkerC, hePair⟩

theorem finrank_ne_eight_of_large_paired_family
    (D : PairedOrthogonalModel t n p e)
    {X : Type} [Group X] {Δ : Set (Subgroup X)} (ePair : Fin D.m × Bool ≃ Δ)
    (hlarge : 4 < Δ.ncard) : Module.finrank (GaloisField p e) D.V ≠ 8 := by
  classical
  have hcard : Δ.ncard = D.m * 2 := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr ePair]
    simp only [Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have hb := CFSG.ClassicalInvolution.ModelFacts.E8D8.sum_finrank_le_of_orth
    (fun i => (D.A i).span) (fun i => (D.A i).polarNondegOn_span)
    (fun i j hij x hx y hy => (D.horth i j hij).polar_zero hx hy)
  have hb' : 4 * D.m ≤ Module.finrank (GaloisField p e) D.V := by
    simpa only [Frame.finrank_span, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm] using hb
  rw [hcard] at hlarge
  omega

theorem exists_paired_conjPermHom_of_orthogonal_model
    (D : PairedOrthogonalModel t n p e)
    (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}
    (ψ : (modelUniv t n p e hp.out).K →* X) (ePair : Fin D.m × Bool ≃ Δ)
    (hePair : ∀ k, (ePair k : Subgroup X) = (D.R k).map ψ) :
    ∀ σ : Equiv.Perm (Fin D.m), ∃ g : conjSetStab Δ, ∀ x : Fin D.m × Bool,
      (ePair.symm (conjPermHom (le_refl (conjSetStab Δ)) g (ePair x))).1 = σ x.1 := by
  apply exists_paired_conjPermHom_of_model_frame_permutations hp2 hfund hadm
    D.π D.hker D.A D.R D.hR ψ ePair hePair
  intro σ
  have hodd : Odd (Nat.card (GaloisField p e)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  obtain ⟨x, hx⟩ := exists_spin_permutation_frame_pairs hodd D.hQ D.hm D.A D.horth σ
  refine ⟨D.η.symm x, ?_⟩
  have hπ : D.π (D.η.symm x) = spinAction D.Q x := by
    rw [D.hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, D.η.apply_symm_apply]
  simpa only [hπ] using hx

theorem funSet_action_twoKernel_quotient_of_four_lt_orthogonal
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htOrth : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (_hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    (hnotTwo : ¬ FunTwoType t n)
    (hlarge : 4 < (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    (∃ (m : ℕ) (N : Subgroup ρ.range) (_ : N.Normal),
      IsPGroup 2 N ∧ Nonempty (ρ.range ⧸ N ≃* Equiv.Perm (Fin m))) ∨
      (∃ (N : Subgroup ρ.range) (_ : N.Normal),
        IsPGroup 2 N ∧ IsSimpleGroup (ρ.range ⧸ N) ∧ Nat.card (ρ.range ⧸ N) = 168) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hfund : IsFundTag t := by rcases htOrth with rfl | rfl | rfl <;> trivial
  obtain ⟨D⟩ := exists_paired_orthogonal_model hp2 htOrth hadm
  obtain ⟨ψ, ePair, hψ, hker, hePair⟩ :=
    exists_equiv_paired_funSet_of_orthogonal_model D hp2 hfund hadm hX hA1 P
  have hodd : Odd (Nat.card (GaloisField p e)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 hadm.2.1
  have hdim := finrank_ne_eight_of_large_paired_family D ePair hlarge
  have hblock := conjPermHom_mem_blockStab_of_paired_model_frames hp2 hfund hadm hA1 D.hm
    hodd hdim D.π D.hker D.hscalar D.A D.horth D.R D.hR ψ hψ hker
    (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) ePair hePair
  obtain ⟨N, hN, h2N, hquot⟩ := exists_twoKernel_quotient_perm_of_paired_conjPermHom ePair hblock
    (exists_paired_conjPermHom_of_orthogonal_model D hp2 hfund hadm ψ ePair hePair)
  exact Or.inl ⟨D.m, N, hN, h2N, hquot⟩

end OrthogonalFamily

end CFSG.LocalAnalysis.UniquenessCase.UC22
