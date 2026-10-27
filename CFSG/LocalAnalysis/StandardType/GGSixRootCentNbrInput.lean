module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbr
public import CFSG.LocalAnalysis.StandardType.GGSixSLSUFourTwoVacuous
public import CFSG.LocalAnalysis.StandardType.GGSixD4SmallVacuous
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.LieType.Universal.Spin

section Inputs

private theorem ggRCSStructNbrConcl_of_layerNbr {G : Type} [Group G] [Finite G]
    {G₀ M Bs E : Subgroup G} {r : G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) (hlayer : GGRCSLayerNbr 3 G₀ M r)
    (hB : Bs ≤ G₀) (hEB : E ≤ Bs) (hE : IsElemAbelian 3 E)
    (hE9 : 9 ≤ Nat.card E) (hEr : E ≤ Subgroup.centralizer {r})
    (hEM : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer {e} ≤ M) :
    GGRCSStructNbrConcl 3 G₀ M r := by
  rcases hlayer with h | ⟨-, Q, S, T, hST⟩
  · exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) h
  · exact hST.structNbrConcl hG₀M hM hE hE9 (le_inf (hEB.trans hB) hEr) hEM

private theorem ggBstar_le_range_PSp {G : Type} [Group G] [Finite G] {n f : ℕ}
    {Bs : Subgroup G} {ψ : (ggU .PSp n f).K →* G} (hn : 2 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSp n f).D ψ b) :
    Bs ≤ ψ.range :=
  CoordSpNs.le_range_of_innerDiag hn ψ hker hC hdiag

private theorem ggBstar_le_range_POmegaPlus {G : Type} [Group G] [Finite G] {n f : ℕ}
    {Bs : Subgroup G} {ψ : (ggU .POmegaPlus n f).K →* G} (hn : 3 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ b) :
    Bs ≤ ψ.range := by
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hC hdiag b hb
  obtain ⟨g, hg, hbg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hdiag b hb)
  rw [hC, Subgroup.mem_bot] at hbg
  rw [eq_inv_of_mul_eq_one_left hbg]
  exact ψ.range.inv_mem hg

private theorem ggBstar_le_range_POmegaMinus {G : Type} [Group G] [Finite G] {n f : ℕ}
    {Bs : Subgroup G} {ψ : (ggU .POmegaMinus n f).K →* G} (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ b) :
    Bs ≤ ψ.range := by
  revert ψ
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hker hC hdiag b hb
  obtain ⟨g, hg, hbg⟩ := PsiDiag.SpinM.exists_mem_centralizer (minusCoeffs_irr 2 f) hn ψ hker
    (hdiag b hb)
  rw [hC, Subgroup.mem_bot] at hbg
  rw [eq_inv_of_mul_eq_one_left hbg]
  exact ψ.range.inv_mem hg

theorem ggRootCentSummandStructNbrInput_of_tags (hstr : GGRootCentSummandStructInput)
    (hPSL : GGRootCentDerivedQTag .PSL) (hPSU : GGRootCentDerivedQTag .PSU)
    (hSp : GGRootCentLayerNbrTag .PSp) (hPlus : GGRootCentLayerNbrTag .POmegaPlus)
    (hMinus : GGRootCentLayerNbrTag .POmegaMinus) (hF4 : GGRootCentDerivedQTag .F4)
    (hE6 : GGRootCentDerivedQTag .E6) (hE7 : GGRootCentDerivedQTag .E7)
    (hE8 : GGRootCentDerivedQTag .E8) (hTwE6 : GGRootCentDerivedQTag .twistedE6) :
    GGRootCentSummandStructNbrInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨-, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, -⟩ := hctx.2
    have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact s1.1
    have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM 3 B x L D J := by
      intro d hd hd1 g hg
      refine s1.2.1.mem_of_conj_mem hd hd1 ?_
      have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have : g⁻¹ * d * g = d := by
        rw [mul_assoc, ← hgd, inv_mul_cancel_left]
      rw [this]
      exact s1.2.1.1 hd
    have h4 : GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G)) := by
      rw [hrange]
      exact hctx.twoLocalRankFour h9iii
    have hEM : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer {e} ≤ ggM 3 B x L D J := by
      intro d hd hd1 g hg
      refine hch.2.2.2.1.mem_of_conj_mem hd hd1 ?_
      have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have : g⁻¹ * d * g = d := by
        rw [mul_assoc, ← hgd, inv_mul_cancel_left]
      rw [this]
      exact hch.2.2.2.1.1 hd
    have hn4 : (t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus) → n = 4 → f ≠ 1 := by
      rintro (ht | ht | ht) rfl rfl
      · subst ht
        exact (ggSix_false_of_slFourTwo hctx s1).elim
      · subst ht
        exact (ggSix_false_of_suFourTwo hctx s1).elim
      · subst ht
        exact (ggSix_false_of_plusFour hctx s1 (by norm_num)).elim
    cases t with
    | PSL =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hPSL G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | PSU =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hPSU G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | PSp =>
      have hBψ : Bs ≤ ψ.range :=
        ggBstar_le_range_PSp hadm.2.2.1 hker hC
          (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb)
      have hlayer := hSp G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution
      rw [hrange] at hlayer
      exact ggRCSStructNbrConcl_of_layerNbr Subgroup.le_normalizer le_rfl hlayer
        (hrange ▸ hBψ) hch.1 hch.2.1 (by rw [hch.2.2.1]; norm_num) hch.le_centralizer hEM
    | POmegaOdd =>
      exact absurd rfl hadm.2.2.2
    | POmegaPlus =>
      have hn : 3 ≤ n := by
        have h4n : 4 ≤ n := hadm.2.2
        omega
      have hBψ : Bs ≤ ψ.range :=
        ggBstar_le_range_POmegaPlus hn hker hC
          (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb)
      have hlayer := hPlus G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution
      rw [hrange] at hlayer
      exact ggRCSStructNbrConcl_of_layerNbr Subgroup.le_normalizer le_rfl hlayer
        (hrange ▸ hBψ) hch.1 hch.2.1 (by rw [hch.2.2.1]; norm_num) hch.le_centralizer hEM
    | POmegaMinus =>
      have hn : 4 ≤ n := hadm.2.2
      have hBψ : Bs ≤ ψ.range :=
        ggBstar_le_range_POmegaMinus hn hker hC
          (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb)
      have hlayer := hMinus G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution
      rw [hrange] at hlayer
      exact ggRCSStructNbrConcl_of_layerNbr Subgroup.le_normalizer le_rfl hlayer
        (hrange ▸ hBψ) hch.1 hch.2.1 (by rw [hch.2.2.1]; norm_num) hch.le_centralizer hEM
    | F4 =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hF4 G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | E6 =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hE6 G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | E7 =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hE7 G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | E8 =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hE8 G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | twistedE6 =>
      have hq := ggRCSLayerQ_of_derivedAtQ Nat.prime_three (by norm_num)
        Subgroup.le_normalizer le_rfl
        (hTwE6 G n f ψ hadm hrank hker hC h4 hn4 r hch.rootInvolution)
      rw [hrange] at hq
      exact ggRCSStructNbrConcl_of_layerQ Nat.prime_three (by norm_num) hq
    | G2 =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
    | trialityD4 =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
    | twistedB2 =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
    | twistedG2 =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
    | twistedF4 =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
    | Tits =>
      exact absurd hrank (show ¬ 2 ≤ 0 by omega)
  · exact ggRCSStructNbrConcl_of_concl
      (hstr G p B Bs x L D J t n f ψ hctx s1 s2 E r hch) (fun h => absurd h hp3)

end Inputs

end CFSG.StandardType
