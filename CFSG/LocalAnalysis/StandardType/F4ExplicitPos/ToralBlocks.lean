module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllBasic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart4
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllDef

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ToralBlocks

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.F4Weyl CFSG.RankThree.E6 CFSG.RankThree.PartOne.KF4

open CFSG.StandardType.F4ExplicitPos.A2Actual

theorem coe_xPar_eq_pinnedX_F4
    {K : Type} [Field K] {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) (c : K) :
    ((xPar (rootOperatorFamily Tag.F4) γ c : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      pinnedX Tag.F4 K γ (((rootOperatorFamily Tag.F4).pinnedFamilySign γ : ℤ) * c) := by
  have h := (rootOperatorFamily Tag.F4).pinnedX_eq_eltUnit K hγ
    (((rootOperatorFamily Tag.F4).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (rootOperatorFamily Tag.F4).pinnedFamilySign_mul_self K γ, one_mul] at h
  rw [xPar_of_isRoot_without117 (rootOperatorFamily Tag.F4) hγ c, h]
  rfl

theorem pinnedX_commute_of_strOrth_F4
    {K : Type} [Field K]
    {γ δ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hδ : IsRoot Tag.F4 δ)
    (h0 : iform γ δ = 0) (hn : ¬ IsRoot Tag.F4 (γ + δ)) (c d : K) :
    Commute (pinnedX Tag.F4 K γ c) (pinnedX Tag.F4 K δ d) := by
  have hne : γ + δ ≠ 0 := by
    intro hzero
    have hδ' : δ = -γ := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hzero)
    have hneg : iform γ δ = -iform γ γ := by rw [hδ', iform_neg_right]
    rw [h0] at hneg
    have hpos := iform_self_pos_of_isRoot hγ
    linarith
  set sγ : K := ((rootOperatorFamily Tag.F4).pinnedFamilySign γ : K) with hsγ
  set sδ : K := ((rootOperatorFamily Tag.F4).pinnedFamilySign δ : K) with hsδ
  have hc := commute_xPar_without117 (rootOperatorFamily Tag.F4)
    DataValid.f4Data_valid_without117 noG2_F4 hγ hδ hne hn (sγ * c) (sδ * d)
  have e1 : pinnedX Tag.F4 K γ c =
      ((xPar (rootOperatorFamily Tag.F4) γ (sγ * c) : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) := by
    rw [coe_xPar_eq_pinnedX_F4 hγ (sγ * c)]
    congr 1
    rw [← mul_assoc, (rootOperatorFamily Tag.F4).pinnedFamilySign_mul_self K γ, one_mul]
  have e2 : pinnedX Tag.F4 K δ d =
      ((xPar (rootOperatorFamily Tag.F4) δ (sδ * d) : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) := by
    rw [coe_xPar_eq_pinnedX_F4 hδ (sδ * d)]
    congr 1
    rw [← mul_assoc, (rootOperatorFamily Tag.F4).pinnedFamilySign_mul_self K δ, one_mul]
  show pinnedX Tag.F4 K γ c * pinnedX Tag.F4 K δ d =
    pinnedX Tag.F4 K δ d * pinnedX Tag.F4 K γ c
  rw [e1, e2]
  exact congrArg (Subgroup.subtype (adjointGroup Tag.F4 K)) hc.eq

theorem commute_rootSpan_of_strOrth_F4
    {L : Type} [Field L] {S T : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot Tag.F4 γ) (hT : ∀ δ ∈ T, IsRoot Tag.F4 δ)
    (h : ∀ γ ∈ S, ∀ δ ∈ T, StrOrth γ δ) :
    ∀ x ∈ rootSpan Tag.F4 L S, ∀ y ∈ rootSpan Tag.F4 L T, x * y = y * x := by
  have h1 : ∀ γ ∈ S, rootSpan Tag.F4 L T ≤
      Subgroup.centralizer (rootSubgroup Tag.F4 L γ : Set (ModGL Tag.F4 L)) := by
    intro γ hγ
    refine iSup₂_le fun δ hδ => fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    exact pinnedX_commute_of_strOrth_F4 (hS γ hγ) (hT δ hδ) (h γ hγ δ hδ).1
      (h γ hγ δ hδ).2.1 c d
  have h2 : rootSpan Tag.F4 L S ≤
      Subgroup.centralizer (rootSpan Tag.F4 L T : Set (ModGL Tag.F4 L)) :=
    iSup₂_le fun γ hγ => Subgroup.le_centralizer_iff.2 (h1 γ hγ)
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hx)) y hy).symm

theorem a2BlockToral_F4 :
    A2BlockToral Tag.F4 := by
  intro L _ _ hL α β hpair
  obtain ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := f4_a2Pair_orbit hpair
  · have hfr := (f4Long_frame_actual (K := L)).transport v
    have key := a2BlockAt_of_frame hL hfr
    have e1 : v • chainRoot f4chainLong 0 1 = α := by rw [(f4chainLong_values).1]; exact h1
    have e2 : v • chainRoot f4chainLong 1 2 = β := by rw [(f4chainLong_values).2.1]; exact h2
    simp only [e1, e2] at key
    exact key
  · have hfr := (f4Short_frame_actual (K := L)).transport v
    have key := a2BlockAt_of_frame hL hfr
    have e1 : v • f4ShortSigma 0 1 = α := by rw [(f4ShortSigma_values).2.2.1]; exact h1
    have e2 : v • f4ShortSigma 1 2 = β := by rw [(f4ShortSigma_values).2.2.2]; exact h2
    simp only [e1, e2] at key
    exact key

theorem exists_conj_mem_torusGroup_of_blocks_F4
    (hblk : A2BlockToral Tag.F4) {L : Type}
    [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3) :
    ∀ B : List ((Fin Tag.F4.rank → ℤ) × (Fin Tag.F4.rank → ℤ)),
      (∀ p ∈ B, IsA2Pair p.1 p.2) → B.Pairwise PairsStrOrth →
      ∀ (n : ModGL Tag.F4 L) (hn : n ∈ monomialSubgroup Tag.F4 L),
        weylQuotientHom Tag.F4 L ⟨n, hn⟩ = (B.map pairRefl).prod →
        ∃ g ∈ Subgroup.closure
            (⋃ p ∈ B, (rootSpan Tag.F4 L (a2Roots p.1 p.2) : Set (ModGL Tag.F4 L))),
          g * n * g⁻¹ ∈ torusGroup Tag.F4 L := by
  intro B
  induction B with
  | nil =>
    intro _ _ n hn hπ
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_torusGroup_of_weylQuotientHom_eq_one hn (by simpa using hπ)
  | cons p B' ih =>
    intro hA2 hpair n hn hπ
    have hp := hA2 p List.mem_cons_self
    obtain ⟨m, hmS, hmN, hmρ, hmt⟩ := hblk L hL p.1 p.2 hp
    set n' := m⁻¹ * n with hn'def
    have hn' : n' ∈ monomialSubgroup Tag.F4 L := mul_mem (inv_mem hmN) hn
    have hπ' : weylQuotientHom Tag.F4 L ⟨n', hn'⟩ = (B'.map pairRefl).prod := by
      have e : (⟨n', hn'⟩ : monomialSubgroup Tag.F4 L) = (⟨m, hmN⟩)⁻¹ * ⟨n, hn⟩ := rfl
      rw [e, map_mul, map_inv, hmρ, hπ, List.map_cons, List.prod_cons, ← pairRefl,
        inv_mul_cancel_left]
    obtain ⟨g', hg', hg'n⟩ := ih (fun q hq => hA2 q (List.mem_cons_of_mem _ hq))
      (List.Pairwise.of_cons hpair) n' hn' hπ'
    have hcomm : g' * m = m * g' := by
      have hall : ∀ x ∈ (⋃ q ∈ B', (rootSpan Tag.F4 L (a2Roots q.1 q.2) : Set (ModGL Tag.F4 L))),
          ∀ y ∈ ((rootSpan Tag.F4 L (a2Roots p.1 p.2) : Subgroup (ModGL Tag.F4 L)) :
            Set (ModGL Tag.F4 L)), x * y = y * x := by
        intro x hx y hy
        simp only [Set.mem_iUnion] at hx
        obtain ⟨q, hq, hx⟩ := hx
        have hpq := List.rel_of_pairwise_cons hpair hq
        exact (commute_rootSpan_of_strOrth_F4 (a2Roots_isRoot hp)
          (a2Roots_isRoot (hA2 q (List.mem_cons_of_mem _ hq))) hpq y hy x hx).symm
      have := closure_commute hall g' hg' m (Subgroup.subset_closure hmS)
      exact this
    obtain ⟨y, hy, hyt⟩ := hmt _ hg'n
    refine ⟨y * g', mul_mem (Subgroup.subset_closure (Set.mem_biUnion List.mem_cons_self hy))
      (Subgroup.closure_mono (Set.biUnion_subset_biUnion_left fun q hq =>
        List.mem_cons_of_mem _ hq) hg'), ?_⟩
    have e : y * g' * n * (y * g')⁻¹ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by
      have hn : n = m * n' := by rw [hn'def]; group
      calc y * g' * n * (y * g')⁻¹ = y * (g' * m) * n' * g'⁻¹ * y⁻¹ := by rw [hn]; group
        _ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by rw [hcomm]; group
    rw [e]
    exact hyt

theorem exists_conj_mem_torusGroup_of_kernelWeylGroup_F4
    (hblk : A2BlockToral Tag.F4) {L : Type}
    [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M} {n : ModGL Tag.F4 L}
    (hn : n ∈ monomialSubgroup Tag.F4 L)
    (hw : weylQuotientHom Tag.F4 L ⟨n, hn⟩ ∈ kernelWeylGroup χ)
    (h3 : weylQuotientHom Tag.F4 L ⟨n, hn⟩ ^ 3 = 1) :
    ∃ g ∈ rootSpan Tag.F4 L (kernelRoots χ), g * n * g⁻¹ ∈ torusGroup Tag.F4 L := by
  obtain ⟨B, hB, hpair, hprod⟩ := exists_a2Blocks hw h3
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_blocks_F4 hblk hL B
    (fun p hp => (hB p hp).1) hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  refine (Subgroup.closure_le _).2 ?_ hg
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  exact iSup₂_le (fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ kernelRoots χ) =>
    rootSubgroup Tag.F4 L δ) γ ((hB p hp).2 hγ) le_rfl) hx

theorem monomialToralAt_three_of_block_F4
    (hblk : A2BlockToral Tag.F4) :
    MonomialToralAt Tag.F4 3 :=
  fun _ _ _ hL _ _ _ _ hn hw h3 => exists_conj_mem_torusGroup_of_kernelWeylGroup_F4 hblk hL hn hw h3

end CFSG.StandardType.F4ExplicitPos.ToralBlocks

end

end
