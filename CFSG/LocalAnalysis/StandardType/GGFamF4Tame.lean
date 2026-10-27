module

public import CFSG.LocalAnalysis.StandardType.GGFamTameInner
public import CFSG.LocalAnalysis.StandardType.GGFamTameSuN
public import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KF4 CFSG.SeitzReduction.F4Pilot CFSG.RankThree.E6
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.F4ExplicitPos.SelectedLiteral
open scoped MatrixGroups commutatorElement

private theorem l10lH5_compRank_parabolicRoots_of_two
    {J : Set (Fin Tag.F4.rank)} {C : Finset (Option (Fin Tag.F4.rank))}
    (hnone : none ∉ C) (hCJ : ∀ j, some j ∈ C ↔ j ∈ J) (hcard : C.card = 2) :
    compRank (parabolicRoots Tag.F4 J) = 2 := by
  have hroots := rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  calc compRank (parabolicRoots Tag.F4 J)
      = compRank (kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank)))) := by rw [← hroots]
    _ = C.card := compRank_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = 2 := hcard

private theorem l10lH5_compRank_f4LongSupport :
    compRank (parabolicRoots Tag.F4 f4LongSupport) = 2 := by
  refine l10lH5_compRank_parabolicRoots_of_two
    (C := ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [mem_f4LongSupport]
    revert j
    decide
  · decide

private theorem l10lH5_compRank_f4ShortSupport :
    compRank (parabolicRoots Tag.F4 f4ShortSupport) = 2 := by
  refine l10lH5_compRank_parabolicRoots_of_two
    (C := ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [mem_f4ShortSupport]
    revert j
    decide
  · decide

private theorem l10lH5_compRank_b2LeviRoots :
    compRank (CFSG.SeitzReduction.F4Pilot.b2LeviRoots) = 2 := by
  rw [CFSG.SeitzReduction.F4Pilot.b2LeviRoots]
  refine l10lH5_compRank_parabolicRoots_of_two
    (C := ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [mem_nodesTU]
    revert j
    decide
  · decide

private theorem l10lH5_ncard_f4LongSupport :
    (parabolicRoots Tag.F4 f4LongSupport).ncard = 6 := by
  have hnone : none ∉ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4LongSupport := by
    intro j
    rw [mem_f4LongSupport]
    revert j
    decide +kernel
  have hroots : kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4LongSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LongSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4LongSupport).ncard
      = (kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

private theorem l10lH5_ncard_f4ShortSupport :
    (parabolicRoots Tag.F4 f4ShortSupport).ncard = 6 := by
  have hnone : none ∉ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4ShortSupport := by
    intro j
    rw [mem_f4ShortSupport]
    revert j
    decide +kernel
  have hroots : kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4ShortSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4ShortSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4ShortSupport).ncard
      = (kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

private theorem l10lH5_ncard_b2LeviRoots :
    (CFSG.SeitzReduction.F4Pilot.b2LeviRoots).ncard = 8 := by
  rw [CFSG.SeitzReduction.F4Pilot.b2LeviRoots]
  have hnone : none ∉ ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ nodesTU := by
    intro j
    rw [mem_nodesTU]
    revert j
    decide +kernel
  have hroots : kacF4.rootsOf (↑({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 nodesTU :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := nodesTU) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 nodesTU).ncard
      = (kacF4.rootsOf (↑({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 8 := by decide +kernel

theorem famF4_longA2Shape_rankCard
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : FamF4LongA2Shape Ψ) : compRank Ψ = 2 ∧ Ψ.ncard = 6 := by
  obtain ⟨w, rfl⟩ := h
  rw [compRank_image, ncard_image_smul]
  exact ⟨l10lH5_compRank_f4LongSupport, l10lH5_ncard_f4LongSupport⟩

theorem famF4_shortA2Shape_rankCard
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : FamF4ShortA2Shape Ψ) : compRank Ψ = 2 ∧ Ψ.ncard = 6 := by
  obtain ⟨w, rfl⟩ := h
  rw [compRank_image, ncard_image_smul]
  exact ⟨l10lH5_compRank_f4ShortSupport, l10lH5_ncard_f4ShortSupport⟩

theorem famF4_b2Shape_rankCard
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : FamF4B2Shape Ψ) : compRank Ψ = 2 ∧ Ψ.ncard = 8 := by
  obtain ⟨w, rfl⟩ := h
  rw [compRank_image, ncard_image_smul]
  exact ⟨l10lH5_compRank_b2LeviRoots, l10lH5_ncard_b2LeviRoots⟩

theorem famF4_b3Shape_rankCard
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : FamF4B3Shape Ψ) : compRank Ψ = 3 ∧ Ψ.ncard = 18 := by
  obtain ⟨w, rfl⟩ := h
  rw [compRank_image, ncard_image_smul]
  exact ⟨compRank_parabolicRoots_f4LeviB3, ncard_parabolicRoots_f4LeviB3⟩

theorem famF4_c3Shape_rankCard
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (h : FamF4C3Shape Ψ) : compRank Ψ = 3 ∧ Ψ.ncard = 18 := by
  obtain ⟨w, rfl⟩ := h
  rw [compRank_image, ncard_image_smul]
  exact ⟨compRank_parabolicRoots_f4LeviC3, ncard_parabolicRoots_f4LeviC3⟩

private theorem l10lH5_exc_rank {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (hk : twistKindM ρ χ i = .exc) :
    compRank (componentRoots χ i) = 6 ∨ compRank (componentRoots χ i) = 4 := by
  unfold twistKindM at hk
  split_ifs at hk with h1 h2
  rcases h2 with ⟨hr, -⟩ | ⟨hr, -⟩
  · exact Or.inl hr
  · exact Or.inr hr

private theorem l10lH5_suN_rank_ncard {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (h : twistKindM ρ χ i = .suN) :
    2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
  unfold twistKindM at h
  split_ifs at h with h1 h2 h3 h4
  exact h4

private theorem l10lH5_famF4_shape_rank_le_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a)) :
    compRank (componentRoots (famCharHom a) i) ≤ 3 := by
  rcases famF4_shape S hp hp2 hT hap h1 i with hP | hL | hS | hB2 | hB3 | hC3
  · obtain ⟨hr, -⟩ := famF4_pairShape_rankCard hP
    omega
  · obtain ⟨hr, -⟩ := famF4_longA2Shape_rankCard hL
    omega
  · obtain ⟨hr, -⟩ := famF4_shortA2Shape_rankCard hS
    omega
  · obtain ⟨hr, -⟩ := famF4_b2Shape_rankCard hB2
    omega
  · obtain ⟨hr, -⟩ := famF4_b3Shape_rankCard hB3
    omega
  · obtain ⟨hr, -⟩ := famF4_c3Shape_rankCard hC3
    omega

theorem famF4_suN_frame
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.F4 L) (σ : Fin ν → Fin ν → Fin Tag.F4.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧
      (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
      componentRoots (famCharHom a) i = frameRoots σ := by
  obtain ⟨h2r, hnc⟩ := l10lH5_suN_rank_ncard S.ρ hk
  rcases famF4_shape S hp hp2 hT hap h1 i with hP | hL | hS | hB2 | hB3 | hC3
  · obtain ⟨hr, -⟩ := famF4_pairShape_rankCard hP
    omega
  · obtain ⟨w, hw⟩ := hL
    refine ⟨3, (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L w)).toMonoidHom.comp
        (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_actual (K := L)),
      fun i j => w • chainRoot f4chainLong i j, 2, by norm_num, ?_, by norm_num, ?_, ?_⟩
    · exact isSLFrame_long_actual_transport w
    · intro a b hab
      rw [iform_smul]
      exact (f4_long12_isRoot a b hab).2.2
    · rw [frameRoots_f4chainLong_smul, hw]
  · obtain ⟨w, hw⟩ := hS
    refine ⟨3, (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L w)).toMonoidHom.comp
        (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_actual (K := L)),
      fun i j => w • f4ShortSigma i j, 1, by norm_num, ?_, by norm_num, ?_, ?_⟩
    · exact isSLFrame_short_actual_transport w
    · intro a b hab
      rw [iform_smul]
      exact (f4_short_isRoot a b hab).2.2
    · rw [frameRoots_f4ShortSigma_smul, hw]
  · obtain ⟨hr, hn⟩ := famF4_b2Shape_rankCard hB2
    rw [hn] at hnc
    rw [hr] at hnc
    norm_num at hnc
  · obtain ⟨hr, hn⟩ := famF4_b3Shape_rankCard hB3
    rw [hn] at hnc
    rw [hr] at hnc
    norm_num at hnc
  · obtain ⟨hr, hn⟩ := famF4_c3Shape_rankCard hC3
    rw [hn] at hnc
    rw [hr] at hnc
    norm_num at hnc

private theorem l10lH5_langFamTame_suN_F4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    famF4_suN_frame S hp hp2 hT hap h1 i hk
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots (famCharHom a) i) with hsdef
  have hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKindM at hk
    rw [if_pos h] at hk
    exact absurd hk (by decide)
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (famCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] '' componentRoots (famCharHom a) i :=
      ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin Tag.F4.rank → ℤ),
      (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] (-γ) =
        -(S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      rw [hπ x y hxy, hwσ]
  · obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    have : Fact r.Prime := ⟨hr⟩
    have : CharP L r := hchar
    obtain ⟨σQ, hσQ, f, hf1, hfker, hf2⟩ :=
      fam_two_suN_exists_hom S hρ i hν hψ hΨ π hπ hr hchar he hq
    obtain ⟨-, hqsC, hcardC⟩ :=
      stdUnitary_fixSubgroup hr (Nat.mul_pos he hs0) σQ hσQ hν
    have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
    by_cases hQ32 : (ν, S.D.q ^ s) = (3, 2)
    · refine Or.inr
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_dvd_216 ?_)
      rw [hQ] at hQ32
      have h216 := hcardC hQ32
      rw [← h216]
      exact (Subgroup.card_dvd_of_le hf1).trans (Subgroup.card_range_dvd f)
    · refine Or.inl ?_
      have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
        intro h
        exact hQ32 (by rw [hQ]; exact h)
      have hQS := hqsC hne
      rw [le_antisymm hf1 (hf2 hQS.1)]
      exact isQuasisimple_range_of_ker_le_center hQS f hfker

theorem langFamTame_F4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  cases hk : twistKindM S.ρ (famCharHom a) i with
  | inner =>
    refine langFamTame_inner_of_hp5 S hp ?_ hT hap h1 i hk
    intro hG
    exact absurd hG (by decide)
  | suN => exact l10lH5_langFamTame_suN_F4 S hp hp2 hT hap h1 i hk
  | twoD =>
    obtain ⟨-, h4, -⟩ := twistKindM_twoD_unpack S.ρ hk
    have hle := l10lH5_famF4_shape_rank_le_three S hp hp2 hT hap h1 i
    omega
  | exc =>
    rcases l10lH5_exc_rank S.ρ hk with hr | hr
    · have hle := l10lH5_famF4_shape_rank_le_three S hp hp2 hT hap h1 i
      omega
    · have hle := l10lH5_famF4_shape_rank_le_three S hp hp2 hT hap h1 i
      omega

end CFSG.StandardType.TableCRes
