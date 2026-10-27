module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PairStabilizerNativePart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
open CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups WithConv
open scoped CFSG.ConvolutionPoints
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.StandardType.RootCentExc
open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.PositiveNo117
open CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117
open scoped Pointwise
variable {K : Type} [Field K]

theorem f4_map_conj_longest_parabolicRadical_le
    {w₀ : WeylGroup Tag.F4}
    {δ : Fin Tag.F4.rank → Fin Tag.F4.rank} (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = -Pi.single (δ i) 1)
    (hsq : w₀ * w₀ = 1) (h₀ : ReversesSigns w₀) (J : Set (Fin Tag.F4.rank)) :
    (parabolicRadical Tag.F4 K (δ '' J)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K w₀)⁻¹).toMonoidHom ≤
      EvenOddRadical.oppRadical Tag.F4 K J := by
  have hT := (canonical_weyl_root_transport Tag.F4 K).1 w₀
    (EvenOddRadical.oppRadicalRoots Tag.F4 J)
    fun α hα => EvenOddRadical.isRoot_of_mem_oppRadicalRoots hα
  have hle : parabolicRadical Tag.F4 K (δ '' J) ≤
      (EvenOddRadical.oppRadical Tag.F4 K J).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K w₀)).toMonoidHom := by
    rw [EvenOddRadical.oppRadical, hT]
    exact rootSpan_mono (EvenOddRadical.parabolicRadicalRoots_subset_longest hinj hδ hsq h₀ J)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hle hy
  have e : (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K w₀)⁻¹).toMonoidHom
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K w₀)).toMonoidHom z) = z := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hz

private theorem f4_eq_highRoot_of_height_le :
    ∀ α ∈ rootFinset Tag.F4, height (highRoot Tag.F4) ≤ height α → α = highRoot Tag.F4 := by
  decide +kernel

private theorem f4_Qθ_inf_Pneg_of_conj
    {n : ModGL Tag.F4 K} (hnC : n ∈ adjointGroup Tag.F4 K)
    (hnU : conjSub n (Uθ Tag.F4 K) = CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K)
    (hle : (Qθ Tag.F4 K).map (MulAut.conj n⁻¹).toMonoidHom ≤
      EvenOddRadical.oppRadical Tag.F4 K (Jθ Tag.F4)) :
    Qθ Tag.F4 K ⊓ Pneg Tag.F4 K = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, hgP⟩ := hg
  obtain ⟨hgC, hgN⟩ : g ∈ adjointGroup Tag.F4 K ∧
      g ∈ Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K)) := hgP
  have hhC : n⁻¹ * g * n ∈ adjointGroup Tag.F4 K := mul_mem (mul_mem (inv_mem hnC) hgC) hnC
  have hgU : conjSub g (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K) = CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K := map_conj_eq_of_mem_normalizer hgN
  have hhU : conjSub (n⁻¹ * g * n) (Uθ Tag.F4 K) = Uθ Tag.F4 K := by
    rw [conjSub_mul, conjSub_mul, hnU, hgU, ← hnU, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hhP : n⁻¹ * g * n ∈ Pθ Tag.F4 K :=
    f4_mem_Pθ_of_conj_le hhC (le_of_eq hhU)
  have hhQ : n⁻¹ * g * n ∈ EvenOddRadical.oppRadical Tag.F4 K (Jθ Tag.F4) := by
    simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hgQ)
  have h1 : n⁻¹ * g * n ∈
      parabolicSubgroup Tag.F4 K (Jθ Tag.F4) ⊓
        EvenOddRadical.oppRadical Tag.F4 K (Jθ Tag.F4) := ⟨hhP, hhQ⟩
  rw [EvenOddRadical.parabolicSubgroup_inf_oppRadical, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem f4_Qθ_inf_Pneg :
    Qθ Tag.F4 K ⊓ Pneg Tag.F4 K = ⊥ := by
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := EvenOddRadical.exists_longest Tag.F4
  have hht : ∀ v : Fin Tag.F4.rank → ℤ, height (w₀ • v) = -height v := fun v => by
    simpa [parabolicDegree, height] using EvenOddRadical.parabolicDegree_longest hinj hδ ∅ v
  have hθ : w₀ • highRoot Tag.F4 = -highRoot Tag.F4 :=
    neg_eq_iff_eq_neg.1 (f4_eq_highRoot_of_height_le _
      (mem_rootFinset.2 (IsRoot.neg (IsRoot.smul (isRoot_highRoot Tag.F4) w₀)))
      (le_of_eq (by rw [height_neg, hht, neg_neg])))
  have hflip : ∀ v : Fin Tag.F4.rank → ℤ, (w₀ • v) (iθ Tag.F4) = -v (iθ Tag.F4) := fun v => by
    have h1 := iform_smul w₀ (highRoot Tag.F4) v
    rw [hθ, ← neg_one_smul ℤ (highRoot Tag.F4), iform_smul_left, iform_highRoot_apply,
      iform_highRoot_apply] at h1
    exact mul_left_cancel₀ (cθ_ne_zero Tag.F4) (by linear_combination (-1 : ℤ) * h1)
  have hδiθ : δ (iθ Tag.F4) = iθ Tag.F4 := by
    have h := hflip (Pi.single (iθ Tag.F4) 1)
    rw [hδ] at h
    by_contra hne
    simp [Ne.symm hne] at h
  have hδJ : δ '' Jθ Tag.F4 = Jθ Tag.F4 := by
    have hsurj : Function.Surjective δ := Finite.injective_iff_surjective.1 hinj
    ext k
    constructor
    · rintro ⟨i, hi, rfl⟩ h
      exact hi (hinj (h.trans hδiθ.symm))
    · intro hk
      obtain ⟨i, rfl⟩ := hsurj k
      exact ⟨i, fun h => hk (by rw [h]; exact hδiθ), rfl⟩
  obtain ⟨-, hRS, -⟩ := canonical_weyl_root_transport Tag.F4 K
  have hle := f4_map_conj_longest_parabolicRadical_le (K := K) hinj hδ hsq h₀ (Jθ Tag.F4)
  rw [hδJ] at hle
  refine f4_Qθ_inf_Pneg_of_conj (canonicalRep_mem_adjointGroup _ K w₀) ?_ hle
  show (rootSubgroup Tag.F4 K (highRoot Tag.F4)).map _ = _
  rw [hRS w₀ _ (isRoot_highRoot Tag.F4), hθ]

def S_J : Set (Fin Tag.F4.rank → ℤ) :=
  {β | ∃ j ∈ Jθ Tag.F4, β = Pi.single j 1 ∨ β = -Pi.single j 1}

theorem f4_Lθ_eq_torus_sup_rootSpan :
    Lθ Tag.F4 K = torusGroup Tag.F4 K ⊔ rootSpan Tag.F4 K S_J := by
  refine le_antisymm ?_ (sup_le (torusGroup_le_parabolicLevi (Jθ Tag.F4)) ?_)
  · refine sup_le le_sup_left ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan (S := S_J) ⟨j, hj, Or.inl rfl⟩ c)
    · rw [← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan (S := S_J) ⟨j, hj, Or.inr rfl⟩ c)
  · refine iSup₂_le fun β hβ => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hβ
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_single]
      exact xUnit_mem_parabolicLevi hj c
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hj c

theorem f4_Lθ_le_Pneg :
    Lθ Tag.F4 K ≤ Pneg Tag.F4 K :=
  le_inf (parabolicLevi_le_adjointGroup Tag.F4 K (Jθ Tag.F4))
    (f4_Lθ_le_normalizer_Uneg (K := K))

theorem f4_Pθ_inf_Pneg_le_Lθ
    {g : ModGL Tag.F4 K} (hP : g ∈ Pθ Tag.F4 K)
    (hN : g ∈ Pneg Tag.F4 K) : g ∈ Lθ Tag.F4 K := by
  obtain ⟨q, hq, l, hl, hgql⟩ := f4_exists_factor_parabolicSubgroup (Jθ Tag.F4) (K := K) hP
  have hlN : l ∈ Pneg Tag.F4 K := f4_Lθ_le_Pneg (K := K) hl
  have hqN : q ∈ Pneg Tag.F4 K := by
    have : q = g * l⁻¹ := by rw [hgql]; group
    rw [this]
    exact mul_mem hN (inv_mem hlN)
  have hq1 : q ∈ Qθ Tag.F4 K ⊓ Pneg Tag.F4 K := ⟨hq, hqN⟩
  rw [f4_Qθ_inf_Pneg, Subgroup.mem_bot] at hq1
  rw [hgql, hq1, one_mul]
  exact hl

theorem f4_pair_stabilizer_eq_Lθ :
    adjointGroup Tag.F4 K ⊓ Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) ⊓
        Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K)) = Lθ Tag.F4 K := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgP, hgNneg⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgA, hgNθ⟩ := Subgroup.mem_inf.1 hgP
    have hP : g ∈ Pθ Tag.F4 K := by
      rw [f4_Pθ_eq_inf_normalizer]
      exact ⟨hgA, hgNθ⟩
    exact f4_Pθ_inf_Pneg_le_Lθ hP ⟨hgA, hgNneg⟩
  · intro g hg
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact parabolicLevi_le_adjointGroup Tag.F4 K (Jθ Tag.F4) hg
    · exact f4_Pθ_le_normalizer_Uθ ((parabolicLevi_le_parabolicSubgroup (Jθ Tag.F4)) hg)
    · exact f4_Lθ_le_normalizer_Uneg (K := K) hg

theorem f4_isConnectedAlgebraicSubgroup_pairStabilizer
    [IsAlgClosed K] :
    IsConnectedAlgebraicSubgroup K
      ((adjointGroup Tag.F4 K ⊓ Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) ⊓
        Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K))).map
          (modGLPoint Tag.F4 K).toMonoidHom) := by
  rw [f4_pair_stabilizer_eq_Lθ, f4_Lθ_eq_torus_sup_rootSpan]
  exact ConnectedJoint.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117
    (τ := Tag.F4) (k := K) S_J

theorem f4_map_entrywiseFrobGL_Lθ_le
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (e : ℕ) :
    (Lθ Tag.F4 K).map (entrywiseFrobGL Tag.F4 K p e) ≤ Lθ Tag.F4 K := by
  rw [f4_Lθ_eq_torus_sup_rootSpan, Subgroup.map_sup, map_entrywiseFrobGL_torusGroup p e]
  refine sup_le le_sup_left ?_
  have hroot : ∀ α ∈ S_J,
      (rootSubgroup Tag.F4 K α).map (entrywiseFrobGL Tag.F4 K p e) ≤
        rootSubgroup Tag.F4 K α := by
    intro α _
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    change entrywiseFrobGL Tag.F4 K p e (pinnedX Tag.F4 K α c) ∈
      rootSubgroup Tag.F4 K α
    rw [CFSG.StandardType.F4ExplicitPos.LangPosition.entrywiseFrobGL_pinnedX_no117]
    exact Subgroup.subset_closure ⟨iterateFrobenius K p e c, rfl⟩
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  exact le_trans (hroot α hα)
    (le_trans (le_iSup₂_of_le α hα le_rfl) le_sup_right)

theorem f4_frobTwistGL_one_mem_pairStabilizer
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (e : ℕ) {g : ModGL Tag.F4 K}
    (hg : g ∈ adjointGroup Tag.F4 K ⊓
        Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) ⊓
        Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K))) :
    frobTwistGL Tag.F4 K p e 1 g ∈ adjointGroup Tag.F4 K ⊓
        Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) ⊓
        Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K)) := by
  rw [f4_pair_stabilizer_eq_Lθ] at hg ⊢
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  exact f4_map_entrywiseFrobGL_Lθ_le (K := K) p e ⟨g, hg, rfl⟩

end CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

end

end
