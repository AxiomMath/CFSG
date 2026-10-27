module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection
public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedTwoReflection
public import CFSG.LieType.AlgebraicGroups.RootSpanConnected
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealizationGroups
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.LieType.Chevalley.ParabolicGradedAction
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2
open scoped CFSG.ConvolutionPoints

theorem map_baseChangeGL_parabolicSubgroup_le {τ : Tag} {K L : Type} [Field K] [Field L]
    (ι : K →+* L) (J : Set (Fin τ.rank)) :
    (parabolicSubgroup τ K J).map (baseChangeGL ι) ≤ parabolicSubgroup τ L J := by
  rw [parabolicSubgroup, Subgroup.map_sup, MonoidHom.map_closure]
  refine sup_le ?_ ?_
  · rw [borelGroup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (le_trans (show torusGroup τ L ≤ borelGroup τ L from le_sup_left)
        (show borelGroup τ L ≤ parabolicSubgroup τ L J from le_sup_left))
        (baseChangeGL_mem_torusGroup ι hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact (le_trans (show posUnipotent τ L ≤ borelGroup τ L from le_sup_right)
        (show borelGroup τ L ≤ parabolicSubgroup τ L J from le_sup_left))
        (by simpa only [posUnipotent] using baseChangeGL_mem_rootSpan ι hx)
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [baseChangeGL_weylElt_one]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)

end CFSG.LieType.AlgebraicGroups

namespace CFSG.StandardType.SCFourCover

open scoped CFSG.ConvolutionPoints

open Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.EvenOddRadical
  CFSG.RankThree.Classical2

variable {Ω : Type} [Field Ω]

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
  [Algebra K Ω] [IsAlgClosure K Ω]
  (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  {A : Subgroup (MulAut L')}

theorem exists_actual_connected_unipotent_radical_of_ne_one
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    {φ : MulAut A}
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ) (m : ℕ) (hgm : g ^ 2 ^ m = 1)
    (hg0ne : (recipeMatrixHom σ ε (ψ := ψ) g : ModGL Tag.E6 Ω) ≠ 1)
    (H : Subgroup (ModGL Tag.E6 Ω))
    (hH : H = rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype))) :
    let _ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    ∃ M : Subgroup (ModGL Tag.E6 Ω),
      M ≤ adjointGroup Tag.E6 Ω ∧
      IsPointClosed Ω
        (transportPoints (modGLPoint Tag.E6 Ω)
          (M : Set (ModGL Tag.E6 Ω))) ∧
      IsConnectedAlgebraicSubgroup Ω
        (M.map (modGLPoint Tag.E6 Ω).toMonoidHom) ∧
      Algebra.Smooth Ω (MatrixComponents.coordinateHopf M) ∧
      IsPGroup 2 M ∧
      recipeMatrixHom σ ε (ψ := ψ) g ∈ M ∧
      H ≤ Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)) := by
  classical
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hcharK : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  letI : CharP K 2 := hcharK
  letI : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  obtain ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, he_k, hj_k, hconj, hinj⟩ :=
    exists_finite_actor_descent (K := K) (L' := L') (ψ := ψ) (A := A)
      hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  letI : Finite k := hkfin
  letI : CharP k 2 := hchar
  let n0 : actorNormalizer A := ⟨g, hg⟩
  let R : Subgroup (ModGL Tag.E6 k) := Subgroup.zpowers (j_k n0).val
  have hRG : R ≤ adjointGroup Tag.E6 k := Subgroup.zpowers_le.mpr (j_k n0).2
  have hR2 : IsPGroup 2 R := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn0 : n0 ^ 2 ^ m = 1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hgm
    have hpow : (j_k n0).val ^ 2 ^ m = 1 := by
      calc
        (j_k n0).val ^ 2 ^ m = ((j_k n0) ^ 2 ^ m).val := by simp
        _ = (j_k (n0 ^ 2 ^ m)).val := by rw [map_pow]
        _ = 1 := by rw [hn0, map_one]; rfl
    exact CFSG.GroupTheory.WielandtProduct.isPGroup_zpowers_of_pow_eq_one hpow
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hxR : (j_k n0).val ∈ R := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    rw [hbot] at hxR
    have hx1 : (j_k n0).val = 1 := by simpa using hxR
    have htj : baseChangeGL ι (j_k n0).val = recipeMatrixHom σ ε (ψ := ψ) g := by
      simpa only [actorMatrixModel, MonoidHom.comp_apply, Subgroup.coe_subtype] using hj_k n0
    have ht1 : (recipeMatrixHom σ ε (ψ := ψ) g : ModGL Tag.E6 Ω) = 1 := by
      rw [← htj, hx1, map_one]
    exact hg0ne ht1
  obtain ⟨z_k, hzkG, J, hP, hQ⟩ :=
    exists_optimal_radical_ordinary (τ := Tag.E6) (K := k) hRG hR2 hRne
  let F : Subgroup A := φ.toMonoidHom.eqLocus (MonoidHom.id A)
  have hHnorm_k : ∀ a ∈ F, (e_k a).val ∈
      Subgroup.normalizer (R : Set (ModGL Tag.E6 k)) := by
    intro a ha
    have hfix : φ a = a := ha
    have hact : actorNormalizerAction A n0 a = a := by
      rw [actorNormalizerAction_eq_ggConjAut,
        show actorNormalizerMem (A := A) n0 = hg from rfl, hgφ]
      exact hfix
    have hconj_a := hconj n0 a
    rw [hact] at hconj_a
    have hcomm : Commute (e_k a) (j_k n0) := by
      show (e_k a) * (j_k n0) = (j_k n0) * (e_k a)
      calc
        (e_k a) * (j_k n0) = (j_k n0 * e_k a * (j_k n0)⁻¹) * (j_k n0) := by
          nth_rewrite 1 [hconj_a]; rfl
        _ = (j_k n0) * (e_k a) := by group
    have hcomm_val : Commute (e_k a).val (j_k n0).val :=
      congrArg Subtype.val hcomm
    have hmapR : R.map (MulAut.conj (e_k a).val).toMonoidHom = R := by
      dsimp only [R]
      rw [MonoidHom.map_zpowers]
      congr 1
      change (MulAut.conj (e_k a).val) (j_k n0).val = (j_k n0).val
      rw [MulAut.conj_apply, hcomm_val.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmapR
  have hPk : ∀ a ∈ F, z_k⁻¹ * (e_k a).val * z_k ∈
      parabolicSubgroup Tag.E6 k J :=
    fun a ha => hP (e_k a).val (e_k a).2 (hHnorm_k a ha)
  have hQk : z_k⁻¹ * (j_k n0).val * z_k ∈ parabolicRadical Tag.E6 k J :=
    hQ (j_k n0).val (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  let z : ModGL Tag.E6 Ω := baseChangeGL ι z_k
  have hzG : z ∈ adjointGroup Tag.E6 Ω :=
    baseChangeGL_mem_adjointGroup ι hzkG
  let Q : Subgroup (ModGL Tag.E6 Ω) :=
    parabolicRadical Tag.E6 Ω J
  have hQG : Q ≤ adjointGroup Tag.E6 Ω :=
    (parabolicRadical_le_posUnipotent J).trans
      (posUnipotent_le_adjointGroup (τ := Tag.E6) (K := Ω))
  have hQconn : IsConnectedAlgebraicSubgroup Ω
      (Q.map (modGLPoint Tag.E6 Ω).toMonoidHom) := by
    change IsConnectedAlgebraicSubgroup Ω
      ((rootSpan Tag.E6 Ω (parabolicRadicalRoots Tag.E6 J)).map
        (modGLPoint Tag.E6 Ω).toMonoidHom)
    exact isConnectedAlgebraicSubgroup_rootSpan (S := parabolicRadicalRoots Tag.E6 J)
  have hQpc : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (Q : Set (ModGL Tag.E6 Ω))) := by
    rw [← subgroupPoints_map]
    exact hQconn.isPointClosed
  have hQirr : IsPointIrreducible Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (Q : Set (ModGL Tag.E6 Ω))) := by
    rw [← subgroupPoints_map]
    exact (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime).2 hQconn.isPrime
  have hQ2 : IsPGroup 2 Q := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isPGroup_of_le_posFiltration (pos := Label.position) (τ := Tag.E6)
      (K := Ω) (N := Fintype.card (Label Tag.E6)) 2
      Label.position_lt_card
      ((parabolicRadical_le_posUnipotent J).trans
        (posUnipotent_le_posFiltration (τ := Tag.E6) (R := Ω)))
  have hHeq : rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ (F.map A.subtype)) =
        F.map ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
          (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom) :=
    rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  have hHzP : H.map (MulAut.conj z⁻¹).toMonoidHom ≤
      parabolicSubgroup Tag.E6 Ω J := by
    intro y hy
    rw [hH] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    rw [hHeq] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    have hbase : baseChangeGL ι (e_k a).val =
        ((recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a :
          rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) :
            ModGL Tag.E6 Ω) :=
      he_k a
    have hPggl : baseChangeGL ι (z_k⁻¹ * (e_k a).val * z_k) ∈
        parabolicSubgroup Tag.E6 Ω J :=
      map_baseChangeGL_parabolicSubgroup_le ι J (Subgroup.mem_map_of_mem _ (hPk a ha))
    have hbc : baseChangeGL ι (z_k⁻¹ * (e_k a).val * z_k) =
        z⁻¹ * baseChangeGL ι (e_k a).val * z := by
      simp only [z, map_mul, map_inv]
    rw [hbc, hbase] at hPggl
    exact hPggl
  have htQ : z⁻¹ * recipeMatrixHom σ ε (ψ := ψ) g * z ∈ Q := by
    have htj : baseChangeGL ι (j_k n0).val = recipeMatrixHom σ ε (ψ := ψ) g := by
      simpa only [actorMatrixModel, MonoidHom.comp_apply, Subgroup.coe_subtype] using hj_k n0
    have hQggl : baseChangeGL ι (z_k⁻¹ * (j_k n0).val * z_k) ∈ Q := by
      dsimp only [Q]
      exact baseChangeGL_mem_rootSpan ι hQk
    have hbc : baseChangeGL ι (z_k⁻¹ * (j_k n0).val * z_k) =
        z⁻¹ * baseChangeGL ι (j_k n0).val * z := by
      simp only [z, map_mul, map_inv]
    rw [hbc, htj] at hQggl
    exact hQggl
  let M : Subgroup (ModGL Tag.E6 Ω) := Q.map (MulAut.conj z).toMonoidHom
  have hMle : M ≤ adjointGroup Tag.E6 Ω := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hzG (hQG hq)) (inv_mem hzG)
  have hMpc : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (M : Set (ModGL Tag.E6 Ω))) :=
    isPointClosed_map_conj hQpc z
  have hMirr : IsPointIrreducible Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (M : Set (ModGL Tag.E6 Ω))) :=
    isPointIrreducible_map_conj hQirr z
  have hMconn : IsConnectedAlgebraicSubgroup Ω
      (M.map (modGLPoint Tag.E6 Ω).toMonoidHom) :=
    (isConnectedAlgebraicSubgroup_map (modGLPoint Tag.E6 Ω) M
      hMpc.isPointConstructible hMirr).2.1
  have hMsmooth : Algebra.Smooth Ω (MatrixComponents.coordinateHopf M) :=
    hMconn.smooth.1
  have hM2 : IsPGroup 2 M := by
    simpa only [M] using IsPGroup.map hQ2 (MulAut.conj z).toMonoidHom
  have htM : recipeMatrixHom σ ε (ψ := ψ) g ∈ M := by
    have hmem : (MulAut.conj z).toMonoidHom
        (z⁻¹ * recipeMatrixHom σ ε (ψ := ψ) g * z) ∈ M :=
      Subgroup.mem_map_of_mem _ htQ
    have hcancel : (MulAut.conj z).toMonoidHom
        (z⁻¹ * recipeMatrixHom σ ε (ψ := ψ) g * z) =
          recipeMatrixHom σ ε (ψ := ψ) g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hcancel] at hmem
  have hHnormM : H ≤ Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)) := by
    have hHnormQ : H.map (MulAut.conj z⁻¹).toMonoidHom ≤
        Subgroup.normalizer (Q : Set (ModGL Tag.E6 Ω)) :=
      hHzP.trans (parabolicSubgroup_le_normalizer_parabolicRadical J)
    have hmap := Subgroup.map_mono (f := (MulAut.conj z).toMonoidHom) hHnormQ
    have hHcomp : (H.map (MulAut.conj z⁻¹).toMonoidHom).map
        (MulAut.conj z).toMonoidHom = H := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj z).toMonoidHom.comp (MulAut.conj z⁻¹).toMonoidHom =
          MonoidHom.id (ModGL Tag.E6 Ω) := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply,
          MulAut.conj_apply]
        group
      rw [hcomp, Subgroup.map_id]
    have hNcomp : (Subgroup.normalizer (Q : Set (ModGL Tag.E6 Ω))).map
        (MulAut.conj z).toMonoidHom =
          Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)) := by
      rw [Subgroup.map_equiv_normalizer_eq]
    rw [hHcomp, hNcomp] at hmap
    exact hmap
  exact ⟨M, hMle, hMpc, hMconn, hMsmooth, hM2, htM, hHnormM⟩

theorem recipeMatrixHom_mem_connected_fixed_subgroup_of_two_pow
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    (hA : CFSG.Open.IsElemAbelian 3 A)
    {φ : MulAut A}
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ) (m : ℕ) (hgm : g ^ 2 ^ m = 1) :
    recipeMatrixHom σ ε (ψ := ψ) g ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer
            (rgrpModel hn hK σ hσ Fr hFr ε
              (TypeA.inducedSub ψ
                ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) :
              Set (ModGL Tag.E6 Ω))) := by
  classical
  by_cases ht1 : (recipeMatrixHom σ ε (ψ := ψ) g : ModGL Tag.E6 Ω) = 1
  · rw [ht1]
    exact Subgroup.one_mem _
  haveI : Finite A := Subtype.finite
  have hcharK : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  letI : CharP K 2 := hcharK
  letI : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let H : Subgroup (ModGL Tag.E6 Ω) :=
    rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype))
  obtain ⟨M, hMle, hMpc, hMconn, hMsmooth, hM2, htM, hHM⟩ :=
    exists_actual_connected_unipotent_radical_of_ne_one hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI hg hgφ m hgm ht1 H rfl
  let E : Subgroup (ModGL Tag.E6 Ω) :=
    rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  have hEfin : Finite E := Finite.of_equiv A γ
  have hHeq : H = (φ.toMonoidHom.eqLocus (MonoidHom.id A)).map
      (E.subtype.comp γ.toMonoidHom) :=
    rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  have hHE : H ≤ E := by
    rw [hHeq]
    rintro _ ⟨a, ha, rfl⟩
    exact (γ a).2
  have hHfin : Finite H :=
    Finite.of_injective (Subgroup.inclusion hHE) (Subgroup.inclusion_injective hHE)
  have hE3 : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.isElemAbelian_inducedSub hψ hA)
  have hH3 : CFSG.Open.IsElemAbelian 3 H := hE3.mono hHE
  have h3 : (3 : Ω) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime Ω Nat.prime_three (by decide)
  have htC : recipeMatrixHom σ ε (ψ := ψ) g ∈
      Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hHeq] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    have hfix : ggConjAut A hg a = a := by
      rw [hgφ]
      exact ha
    have hconj :=
      recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hg a
    rw [hfix] at hconj
    change (γ a : ModGL Tag.E6 Ω) * recipeMatrixHom σ ε (ψ := ψ) g =
      recipeMatrixHom σ ε (ψ := ψ) g * (γ a : ModGL Tag.E6 Ω)
    nth_rewrite 1 [hconj]
    rw [mul_assoc (recipeMatrixHom σ ε (ψ := ψ) g *
      (γ a : ModGL Tag.E6 Ω))
      (recipeMatrixHom σ ε (ψ := ψ) g)⁻¹
      (recipeMatrixHom σ ε (ψ := ψ) g)]
    rw [inv_mul_cancel, mul_one]
  have htK : recipeMatrixHom σ ε (ψ := ψ) g ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))) := by
    letI : Finite H := hHfin
    letI : Algebra.Smooth Ω (MatrixComponents.coordinateHopf M) := hMsmooth
    letI : ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf M)) :=
      hMconn.connectedSpace
    exact le_closedIdentityComponent_inf_centralizer_of_finite_elemAbelian_three
      M H hMpc hM2 hH3 hHM hMle h3 ⟨htM, htC⟩
  exact htK

theorem given_two_realizer_mem_connected_hyperplane
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    (hA : CFSG.Open.IsElemAbelian 3 A)
    {φ : MulAut A} (_hφ : GGIsReflection 3 φ)
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ) (m : ℕ) (hgm : g ^ 2 ^ m = 1) :
    recipeMatrixHom σ ε (ψ := ψ) g ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer
            (rgrpModel hn hK σ hσ Fr hFr ε
              (TypeA.inducedSub ψ
                ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) :
              Set (ModGL Tag.E6 Ω))) :=
  recipeMatrixHom_mem_connected_fixed_subgroup_of_two_pow hn hK σ hσ Fr hFr ε hε
    hψ hker hperf hAI hA hg hgφ m hgm

theorem exists_connected_two_realizer_of_reflection
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    (hA : CFSG.Open.IsElemAbelian 3 A)
    {φ : MulAut A} (hφ : GGIsReflection 3 φ)
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ) :
    ∃ (g2 : L') (hg2 : MulAut.conj g2 ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (m : ℕ),
      g2 ^ 2 ^ m = 1 ∧ ggConjAut A hg2 = φ ∧
      recipeMatrixHom σ ε (ψ := ψ) g2 ∈
        closedIdentityComponent
          (adjointGroup Tag.E6 Ω ⊓
            Subgroup.centralizer
              (rgrpModel hn hK σ hσ Fr hFr ε
                (TypeA.inducedSub ψ
                  ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) :
                Set (ModGL Tag.E6 Ω))) := by
  obtain ⟨g2, hg2, m, hgm, hg2φ⟩ :=
    exists_two_element_lift_of_reflection hφ hg hgφ
  exact ⟨g2, hg2, m, hgm, hg2φ,
    given_two_realizer_mem_connected_hyperplane hn hK σ hσ Fr hFr ε hε
      hψ hker hperf hAI hA hφ hg2 hg2φ m hgm⟩

theorem negative_recipe_actor_mem_connected_hyperplane_of_reflection
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    (hA : CFSG.Open.IsElemAbelian 3 A)
    {φ : MulAut A} (hφ : GGIsReflection 3 φ)
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ)
    {e : A} (hφe : φ e = e⁻¹) :
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI e :
        ModGL Tag.E6 Ω) ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer
            (rgrpModel hn hK σ hσ Fr hFr ε
              (TypeA.inducedSub ψ
                ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) :
              Set (ModGL Tag.E6 Ω))) := by
  classical
  haveI : Finite A := Subtype.finite
  have hcharK : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  letI : CharP K 2 := hcharK
  letI : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let H : Subgroup (ModGL Tag.E6 Ω) :=
    rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype))
  let E : Subgroup (ModGL Tag.E6 Ω) :=
    rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  have hHeq : H = (φ.toMonoidHom.eqLocus (MonoidHom.id A)).map
      (E.subtype.comp γ.toMonoidHom) :=
    rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  have hHE : H ≤ E := by
    rw [hHeq]
    rintro _ ⟨a, ha, rfl⟩
    exact (γ a).2
  have hEG : E ≤ adjointGroup Tag.E6 Ω := fun x hx =>
    ((TwistedDiag.mem_Rgrp _).mp
      (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ hx)).1
  obtain ⟨g2, hg2, m, hgm, hg2φ, hg2K⟩ :=
    exists_connected_two_realizer_of_reflection hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
      hA hφ hg hgφ
  have heC : (γ e : ModGL Tag.E6 Ω) ∈
      Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hHeq] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    have hcommA : a * e = e * a := hA.1.is_comm.comm a e
    have hγcommE : γ a * γ e = γ e * γ a := by
      calc
        γ a * γ e = γ (a * e) := (map_mul γ a e).symm
        _ = γ (e * a) := by rw [hcommA]
        _ = γ e * γ a := map_mul γ e a
    exact congrArg (fun x : E => (x : ModGL Tag.E6 Ω)) hγcommE
  have he3 : (γ e : ModGL Tag.E6 Ω) ^ 3 = 1 := by
    have h := congrArg (fun x : A => (γ x : ModGL Tag.E6 Ω))
      (Subtype.ext (hA.2 e e.2) : e ^ 3 = 1)
    simpa only [map_pow, map_one, coe_pow, coe_one] using h
  have hinv : recipeMatrixHom σ ε (ψ := ψ) g2 * (γ e : ModGL Tag.E6 Ω) *
      (recipeMatrixHom σ ε (ψ := ψ) g2)⁻¹ =
        (γ e : ModGL Tag.E6 Ω)⁻¹ := by
    have hconj :=
      recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hg2 e
    rw [hg2φ, hφe] at hconj
    simpa only [map_inv, coe_inv] using hconj.symm
  have heZ : (γ e : ModGL Tag.E6 Ω) ∈
      adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω)) :=
    Subgroup.mem_inf.mpr ⟨hEG (γ e).2, heC⟩
  exact mem_closedIdentityComponent_of_order_three_of_inverted
    (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω)))
    (recipeMatrixHom σ ε (ψ := ψ) g2) (γ e) hg2K heZ he3 hinv

theorem negative_mem_full_connected_centralizer_of_actual_reflection_of_connected
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {φ : MulAut A} (hgφ : ggConjAut A hg = φ) (hφ : GGIsReflection 3 φ)
    {e : A} (he : e ≠ 1) (hφe : φ e = e⁻¹) :
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
        hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 e : ModGL Tag.E6 Ω) ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer
            (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) :
              Set (ModGL Tag.E6 Ω))) := by
  classical
  have heK := negative_recipe_actor_mem_connected_hyperplane_of_reflection
    hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hTB.2.2.2.1 hφ hg hgφ hφe
  exact negative_mem_full_connected_centralizer_of_actual_reflection
    hn hK σ hσ Fr hFr ε hε hTB hnt hg hgφ hφ he hφe heK

theorem reflection_difference_mem_full_connected_centralizer
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {φ : MulAut A} (hgφ : ggConjAut A hg = φ) (hφ : GGIsReflection 3 φ) :
    ∀ a : A,
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
          hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 (φ a) :
            ModGL Tag.E6 Ω) *
        ((recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
            hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 a :
              ModGL Tag.E6 Ω))⁻¹ ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer
            (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) :
              Set (ModGL Tag.E6 Ω))) := by
  classical
  intro a
  let E : Subgroup (ModGL Tag.E6 Ω) :=
    rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
  let δ : A := φ a * a⁻¹
  have hδinv : φ δ = δ⁻¹ := by
    dsimp [δ]
    have hφ2 : φ (φ a) = a := by
      have h := congrArg (fun f : MulAut A => f a) hφ.1
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
    rw [map_mul, map_inv, hφ2]
    group
  have hδeqE : γ δ = γ (φ a) * (γ a)⁻¹ := by
    simp only [δ, map_mul, map_inv]
  have hδeq : (γ δ : ModGL Tag.E6 Ω) =
      (γ (φ a) : ModGL Tag.E6 Ω) *
        ((γ a : ModGL Tag.E6 Ω))⁻¹ :=
    congrArg (fun x : E => (x : ModGL Tag.E6 Ω)) hδeqE
  by_cases hδ1 : δ = 1
  · have hzero : (γ δ : ModGL Tag.E6 Ω) = 1 := by
      rw [hδ1, map_one]
      rfl
    rw [← hδeq, hzero]
    exact Subgroup.one_mem _
  · have hmem := negative_mem_full_connected_centralizer_of_actual_reflection_of_connected
      hn hK σ hσ Fr hFr ε hε hTB hnt hg hgφ hφ hδ1 hδinv
    rwa [hδeq] at hmem

end CFSG.StandardType.SCFourCover
