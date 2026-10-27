module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAut
import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksExt
import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero2
import CFSG.LocalAnalysis.StandardType.GGQ2OrthType
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.F2
import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import Certificates.Certificate41501

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

theorem finrank_commSpace_eq_of_sub_one_eq {g : V ≃ₗ[K] V} {h : W ≃ₗ[K] W} (f : W →ₗ[K] V)
    (p : V →ₗ[K] W) (hpf : p ∘ₗ f = LinearMap.id)
    (hg : (g : V →ₗ[K] V) - 1 = f ∘ₗ ((h : W →ₗ[K] W) - 1) ∘ₗ p) :
    finrank K (commSpace g) = finrank K (commSpace h) := by
  have hpf' : Function.LeftInverse p f := fun w => LinearMap.congr_fun hpf w
  have hc : commSpace g = (commSpace h).map f := by
    rw [commSpace, hg, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hpf'.surjective, Submodule.map_top]
  rw [hc]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hpf'.injective _)).symm

end CFSG.RankThree.OrthogonalInvolutions

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal (SmallFixedException)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (IsF2)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem otah_ne_zero_of_four_le {t : ℕ} {e : PlaneRaw.V t}
    (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) : e ≠ 0 := by
  rintro rfl
  have h0 : PlaneRaw.Code.extSupport (0 : PlaneRaw.V t) = ∅ := by
    ext i
    simp
  rw [h0, Finset.card_empty] at he
  omega

theorem orthExtTorusAut_holds : OrthExtTorusAut := by
  intro K _ _ _ ζ t δ hK hζ _ e he
  apply Set.Subset.antisymm
  · exact (oTorusAut_mono (Subgroup.commutator_le_self _)).trans
      (oTorusAut_oBlockGroup_extension_subset hK hζ (coe_planeQForm K t δ)
        nondegenerate_planeQForm e)
  · exact twistedPermGroupOn_subset_oTorusAut_oYcode hK hζ e he
      (oYcode_extension_map_eq ζ t δ hK hζ e ⟨otah_ne_zero_of_four_le he, he⟩).ge


theorem mem_orthDerived_of_sub_one_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : QuadraticForm K V} {R : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (hR : (polarBilin R).Nondegenerate)
    (h3 : 3 ≤ finrank K W) (hne : ¬ SmallFixedException R)
    (f : W →ₗ[K] V) (p : V →ₗ[K] W) (hpf : p ∘ₗ f = LinearMap.id)
    {A : W ≃ₗ[K] W} {B : V ≃ₗ[K] V}
    (hAB : (B : V →ₗ[K] V) - 1 = f ∘ₗ ((A : W →ₗ[K] W) - 1) ∘ₗ p)
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup R)
    (hB : B ∈ CFSG.RankThree.Classical2.orthDerived Q) :
    A ∈ CFSG.RankThree.Classical2.orthDerived R := by
  have hBΩ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hB
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d.omegaGroup_le_orthDerived_of_listed
    R hR h3 hne ⟨hA, ?_⟩
  rw [← CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_eq_of_sub_one_eq f p hpf hAB]
  exact hBΩ.2

theorem mem_statedOmega_of_sub_one_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Q : QuadraticForm K (κ → K)} {R : QuadraticForm K (ι → K)} {Q₀ : (κ → K) → K}
    {R₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) (hR₀ : ⇑R = R₀)
    (hQ : (polarBilin Q).Nondegenerate) (hR : (polarBilin R).Nondegenerate)
    (h3 : 3 ≤ Fintype.card ι) (hne : ¬ SmallFixedException R)
    (f : (ι → K) →ₗ[K] (κ → K)) (p : (κ → K) →ₗ[K] (ι → K)) (hpf : p ∘ₗ f = LinearMap.id)
    {A : GL ι K} {B : GL κ K}
    (hAB : ∀ v, (B : Matrix κ κ K) *ᵥ v - v = f ((A : Matrix ι ι K) *ᵥ p v - p v))
    (hA : A ∈ CFSG.Assembly.LargeEvenOrthGroup R₀) (hB : B ∈ CFSG.Open.StatedOmega Q₀) :
    A ∈ CFSG.Open.StatedOmega R₀ := by
  rw [statedOmega_eq_comap hQ₀, Subgroup.mem_comap] at hB
  rw [statedOmega_eq_comap hR₀, Subgroup.mem_comap]
  rw [CFSG.Assembly.largeEvenOrthGroup_def, closure_isometries_eq_comap hR₀,
    Subgroup.mem_comap] at hA
  refine mem_orthDerived_of_sub_one_eq hQ hR (by rwa [finrank_fintype_fun_eq_card]) hne f p hpf
    (LinearMap.ext fun v => ?_) hA hB
  simpa using hAB v

theorem not_smallFixedException_planeQForm {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {s : ℕ} {δ : Fin 2}
    (hs : (Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val)) :
    ¬ SmallFixedException (planeQForm K s δ) := by
  have hdim : finrank K (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) = 2 * (s + δ.val) := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  rintro (⟨h3, -⟩ | ⟨⟨h4, T, hT, hTs⟩, -⟩)
  · omega
  · have hod : Odd s := by
      rcases hs with ⟨-, h3'⟩ | ⟨hod, -⟩
      · omega
      · exact hod
    have hirr : ∀ x : K, x ^ 2 + 1 * x + 1 ≠ 0 := by
      have : IsF2 K := IsF2.of_natCard_eq_two hK
      intro x
      rcases IsF2.eq_zero_or_one x with rfl | rfl
      · simp
      · rw [one_pow, one_mul, IsF2.one_add_one, zero_add]
        exact one_ne_zero
    obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) s δ hod
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := s + δ.val) (by omega) hirr
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr e).mp ⟨T, by omega, hTs⟩)


section ZeroKeys

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {δ : Fin 2}

theorem oBlockGroup_zero_le_oYcode_of (hK : Nat.card K = 2) {S : Finset (Fin t)}
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S))
    (ext : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K →*
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
    (f : (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K) →ₗ[K]
      (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K))
    (p : (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) →ₗ[K]
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K))
    (hpf : p ∘ₗ f = LinearMap.id)
    (hext : ∀ A v, ((ext A : GL _ K) : Matrix _ _ K) *ᵥ v - v =
      f ((A : Matrix _ _ K) *ᵥ p v - p v))
    (hblock : ∀ y ∈ oBlockGroup ζ t δ (.zero S),
      ∃ A ∈ CFSG.Assembly.LargeEvenOrthGroup (planeQ (K := K) S.card δ),
        (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) = ext A)
    (hmap : (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype =
      (omegaQ (K := K) S.card δ).map ext) :
    oBlockGroup ζ t δ (.zero S) ≤ oYcode ζ t δ (.zero S) := by
  intro y hy
  obtain ⟨A, hA, hyA⟩ := hblock y hy
  have hS' : (Even S.card ∧ 3 ≤ S.card + δ.val) ∨ (Odd S.card ∧ 2 ≤ S.card + δ.val) := hS
  have h3 : 3 ≤ Fintype.card (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hB : ext A ∈ CFSG.Open.StatedOmega (planeQ (K := K) t δ) := hyA ▸ y.2
  have hAΩ : A ∈ omegaQ (K := K) S.card δ :=
    mem_statedOmega_of_sub_one_eq (coe_planeQForm K t δ) (coe_planeQForm K S.card δ)
      nondegenerate_planeQForm nondegenerate_planeQForm h3
      (not_smallFixedException_planeQForm hK hS') f p hpf (hext A) hA hB
  have hmem : (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
      (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype := by
    rw [hmap]
    exact ⟨A, hAΩ, hyA.symm⟩
  obtain ⟨y', hy', hyy'⟩ := hmem
  rwa [Subtype.ext hyy'] at hy'

theorem orthZeroTorusAut_of_le
    (hle : ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
      Nat.card K = 2 → Function.Injective ζ → ∀ S : Finset (Fin t),
        PlaneRaw.admissible (.orthogonal δ) (.zero S) →
        oBlockGroup ζ t δ (.zero S) ≤ oYcode ζ t δ (.zero S)) :
    OrthZeroTorusAut := by
  intro K _ _ _ ζ t δ hK hζ ht S hS
  apply Set.Subset.antisymm
  · exact (oTorusAut_mono (Subgroup.commutator_le_self _)).trans
      (oTorusAut_oBlockGroup_zero_subset hK hζ (coe_planeQForm K t δ)
        nondegenerate_planeQForm S)
  · exact (normalizerOf_zero_subset_oTorusAut_oBlockGroup hK hζ (by omega)
      (coe_planeQForm K t δ) nondegenerate_planeQForm (omegaQ_le_statedSp t δ) S).trans
      (oTorusAut_mono (hle ζ t δ hK hζ S hS))

end ZeroKeys

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spIncl spIncl_transpose_mul spEmbedMat)

private theorem orthExt_mulVec_sub {K : Type} [Field K] (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K)
    (v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    ((orthExt t δ S A : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) : Matrix _ _ K) *ᵥ v - v =
      spIncl (K := K) (emb t δ S) *ᵥ ((A : Matrix _ _ K) *ᵥ ((spIncl (K := K) (emb t δ S))ᵀ *ᵥ v) -
        (spIncl (K := K) (emb t δ S))ᵀ *ᵥ v) := by
  change spEmbedMat (emb t δ S) (A : Matrix _ _ K) *ᵥ v - v = _
  rw [spEmbedMat, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem orthZeroTorusAut_holds : OrthZeroTorusAut :=
  orthZeroTorusAut_of_le fun ζ t δ hK _ S hS =>
    oBlockGroup_zero_le_oYcode_of hK hS (orthExt t δ S)
      (Matrix.mulVecLin (spIncl (emb t δ S))) (Matrix.mulVecLin ((spIncl (emb t δ S))ᵀ))
      (by rw [← Matrix.mulVecLin_mul, spIncl_transpose_mul (emb_injective t δ S),
        Matrix.mulVecLin_one])
      (fun A v => by simpa only [Matrix.mulVecLin_apply] using orthExt_mulVec_sub t δ S A v)
      (fun _ hy => by
        obtain ⟨A, hA, hyA⟩ := orthBlockGroupLeExt ζ t δ S hy
        exact ⟨A, hA, hyA.symm⟩)
      (oYcode_map_eq_orthExt ζ hK t δ S hS)

theorem orthComponentTorusAut_holds : OrthComponentTorusAut :=
  orthComponentTorusAut_of_parts orthZeroTorusAut_holds orthExtTorusAut_holds

end CFSG.StandardType.GGQ2Frame.OrthBlocks
