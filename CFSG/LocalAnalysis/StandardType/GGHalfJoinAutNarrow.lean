module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDStab
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinNorm
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinRows
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSL
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import TauCeti.GroupTheory.ExponentPrime
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.LieType.Universal.SpecialLinear Matrix

private theorem hjan_row_A (m : ℕ) (hm : 3 ≤ m) (X : LargeEvenLabel)
    (h : GGTablePRow 3 ⟨.A, m, 1⟩ X) :
    X = ⟨.A, m + 2, 1⟩ ∨ (m = 5 ∧ X = ⟨.E6, 0, 1⟩) := by
  unfold GGTablePRow at h
  rcases X with ⟨t, r, n⟩
  cases t <;>
    simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
      and_true, and_false, or_false, false_or, true_or, or_true] at h
  · rcases h with h | h | h | h | h | h
    · obtain ⟨h3, -⟩ := h; norm_num at h3
    · obtain ⟨-, -, rfl, rfl⟩ := h; exact Or.inl rfl
    · obtain ⟨⟨h2, h13⟩, -⟩ := h; norm_num at h13
    · obtain ⟨⟨h2, h14⟩, -⟩ := h; norm_num at h14
    · obtain ⟨-, h37, -⟩ := h; norm_num at h37
    · obtain ⟨-, h37, -⟩ := h; norm_num at h37
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rcases h with h | h
    · obtain ⟨h3, -⟩ := h; norm_num at h3
    · obtain ⟨-, -, hm5, rfl, rfl⟩ := h
      exact Or.inr ⟨hm5, rfl⟩
  · norm_num at h
  · norm_num at h

private theorem hjan_row_D3 (X : LargeEvenLabel) (h : GGTablePRow 3 ⟨.D, 3, 1⟩ X) :
    X = ⟨.twD, 4, 1⟩ := by
  unfold GGTablePRow at h
  rcases X with ⟨t, r, n⟩
  cases t <;>
    simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
      and_true, and_false, or_false, false_or, true_or, or_true] at h
  · norm_num at h
  · obtain ⟨-, rfl, rfl⟩ := h; rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem GGHalfJoin.rows_narrow (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hRig : GGLabelRigidInput) {m : ℕ} (hm : 3 ≤ m)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y' : G}
    {K' : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagAll 3 B Bs x L D J)
    (hnbr' : GGNbr 3 B x D J y' K')
    (hlabJ : GGHasLabel ⟨.A, m, 1⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel ⟨.A, m + 2, 1⟩ (↥K' ⧸ Subgroup.center ↥K') ∨
      (m = 3 ∧ GGHasLabel ⟨.twD, 4, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) ∨
      (m = 5 ∧ GGHasLabel ⟨.E6, 0, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) := by
  have hΛJ : LargeEvenInLambda2 ⟨.A, m, 1⟩ := by
    dsimp only [LargeEvenInLambda2]; omega
  have hinnK : GGInnerDiagOn Bs K' := hinn.2 y' K' hnbr'
  obtain ⟨labK, hΛK, hhasK, -⟩ := largeEvenMarking_exists_hasLabel hinnK
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
    hTP G 3 B Bs x L D J y' K' hcfg hinn.1 hinnK hnbr' ⟨.A, m, 1⟩ labK hΛJ hΛK
      ⟨rfl, rfl, rfl, hm⟩ hlabJ hhasK
  have hcases := ggLabelIso_typeA_cases hRig (r := m) (f := 1) (by omega) hΛJ' hΛJ hhasJ' hlabJ
  rcases hcases with hA | ⟨hm3, hD⟩
  · rw [hA] at hrow
    rcases hjan_row_A m hm labK' hrow with h1 | ⟨hm5, h1⟩
    · rw [h1] at hhasK'
      exact Or.inl hhasK'
    · rw [h1] at hhasK'
      exact Or.inr (Or.inr ⟨hm5, hhasK'⟩)
  · rw [hD] at hrow
    have h1 := hjan_row_D3 labK' hrow
    rw [h1] at hhasK'
    exact Or.inr (Or.inl ⟨hm3, hhasK'⟩)

theorem GGHalfJoin.main_false_narrow (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hRig : GGLabelRigidInput)
    (hRows : GGHalfRowDataInput) (h7 : GGHalfFusionOmega8Input) (h8 : GGHalfFusionE6Input)
    (hsub : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m : ℕ} {y : G} {K : Subgroup G}
    (hctx : GGHalfWeylCtx 3 B Bs x L D J m y K) (hNoTr : GGNoTransvection 3 Bs)
    (hAut : GGHalfAutWithin Bs L K) {y' : G} {K' : Subgroup G} (hnbr' : GGNbr 3 B x D J y' K')
    (hy'x : y' ∉ Subgroup.zpowers x) (hy'y : y' ∉ Subgroup.zpowers y) : False := by
  obtain ⟨TJ, hTJBs, hTJJ, hTJcard, hBscard, hZJ, hlabJ⟩ := GGHalfJoin.leviData hsub hctx hNoTr
  have hm : 3 ≤ m := by have := hctx.nbr.2.2.1; omega
  have hJK' : J ≤ K' := hsub G 3 B x L D J hctx.cfg.1 hctx.cfg.2.2 y' K' hnbr'
  have hinn' : GGInnerDiagOn Bs K' := hctx.inn.2 y' K' hnbr'
  have hq : CFSG.Assembly.IsQuasisimple ↥K' := isQuasisimple_of_largeEvenMarking hinn'
  have hBs : IsElemAbelian 3 Bs := hctx.cfg.2.1.2.1
  have hnormBs : Bs ≤ Subgroup.normalizer (K' : Set G) := hinn'.le_normalizer
  have hrows := GGHalfJoin.rows_narrow hTP hRig hm hctx.cfg hctx.inn hnbr' hlabJ
  have hdata : Subgroup.center ↥K' = ⊥ ∧
      ∀ b ∈ Bs, ∃ c ∈ K', ∀ l ∈ K', b * l * b⁻¹ = c * l * c⁻¹ := by
    rcases hrows with hA | ⟨-, hD4⟩ | ⟨-, hE6⟩
    · exact GGHalfJoin.typeA_data hm hBs hinn' hnormBs hA
    · exact hRows G Bs K' hinn' (Or.inl hD4)
    · exact hRows G Bs K' hinn' (Or.inr hE6)
  have hk : 1 ≤ (m + 3) / 2 := by omega
  have hTJcard' : Nat.card TJ = 3 ^ ((m + 3) / 2 - 1) := by
    have : (m + 3) / 2 - 1 = (m + 1) / 2 := by omega
    rw [this]
    exact hTJcard
  obtain ⟨τ, kx, hP⟩ := GGHalfJoin.innerPart (k := (m + 3) / 2) hctx.cfg hnbr' hJK' hdata.1
    hnormBs hdata.2 hk hBscard (le_inf hTJBs hTJJ) hTJcard' hZJ
  have hTJel : IsElemAbelian 3 TJ := hBs.mono hTJBs
  have hfus : ∃ n' ∈ K', n' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G) ∧
      n' * kx * n'⁻¹ ∈ TJ ∧ n' * kx * n'⁻¹ ≠ 1 := by
    rcases hrows with hA | ⟨rfl, hD4⟩ | ⟨rfl, hE6⟩
    · exact GGHalfJoin.fusion_SL m hm G K' J TJ kx hq hdata.1 hA hP.kx_order hP.kx_mem hP.J_comp
        hZJ hlabJ hTJJ hTJel hTJcard
    · exact h7 G K' J TJ kx hq hdata.1 hD4 hP.kx_order hP.kx_mem hP.J_comp hZJ hlabJ hTJJ hTJel
        hTJcard
    · exact h8 G K' J TJ kx hq hdata.1 hE6 hP.kx_order hP.kx_mem hP.J_comp hZJ hlabJ hTJJ hTJel
        hTJcard
  obtain ⟨n', hn'K', hn'norm, hn'T, hn'ne⟩ := hfus
  have hy'Bs : y' ∈ Bs := hctx.cfg.2.1.1 hnbr'.1.2.1
  have hxBs : x ∈ Bs := hctx.cfg.2.1.1 (hctx.cfg.2.2.1.1 hctx.cfg.2.2.1.2.2.2.1)
  have hD : D = Subgroup.closure {x, y'} := hnbr'.2.1
  have hy'D : y' ∈ D := hD ▸ Subgroup.subset_closure (by simp)
  have hstab : ∀ φ ∈ ggInduced ⊤ Bs, ((φ ⟨y', hy'Bs⟩ : ↥Bs) : G) = y' →
      ∀ b : ↥Bs, (b : G) ∈ D → ((φ b : ↥Bs) : G) ∈ D := fun φ hφ hfix =>
    hctx.joinDStab hAut hy'D hy'Bs hy'x hy'y hφ hfix
  have hmem := GGHalfJoin.normalizes_kx hD (hBs.comm hxBs hy'Bs) hxBs hy'Bs hnbr'.1.2.2.2.1 hP
    hstab hn'K' hn'norm
  exact hn'ne (Subgroup.disjoint_def.mp hP.disj hmem hn'T)

theorem ggTypeAHalfJoinAutInput_of_tableP_narrow (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hL : GGLBalanceInput)
    (hsub : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) (hRows : GGHalfRowDataInput)
    (h7 : GGHalfFusionOmega8Input) (h8 : GGHalfFusionE6Input) : GGTypeAHalfJoinAutInput := by
  intro G _ _ p B Bs x L D J n y K hcfg _ hInn hNoTr hN hAut y' K' hnbr' _
  have hN' := hN
  obtain ⟨-, rfl, hn5, -, hnbr, -, -⟩ := hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have hJK : J ≤ K := hsub G 3 B x L D J hcfg.1 hcfg.2.2 y K hnbr
  have hctx : GGHalfWeylCtx 3 B Bs x L D J m y K := ⟨hcfg, hInn, hN', hJK⟩
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hy'Bs : y' ∈ Bs := hcfg.2.1.1 hnbr'.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnbr.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 (hcfg.2.2.1.1 hcfg.2.2.1.2.2.2.1)
  have hy'1 : y' ≠ 1 := hnbr'.1.2.2.1
  by_cases hyy : y' ∈ Subgroup.zpowers y
  · obtain ⟨TJ, -, hTJJ, hTJcard, -, -, -⟩ := GGHalfJoin.leviData hsub hctx hNoTr
    have hpJ : 3 ∣ Nat.card J := by
      have h1 : 3 ∣ Nat.card TJ := by
        rw [hTJcard]
        exact dvd_pow_self 3 (by omega)
      exact h1.trans (Subgroup.card_dvd_of_le hTJJ)
    have hzp : Subgroup.zpowers y = Subgroup.zpowers y' :=
      (TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three (hBs.2 y hyBs) hy'1 hyy).symm
    rw [← ggNbr_unique hL hcfg.1 hcfg.2.2 hpJ hnbr hnbr' hzp]
    exact le_sup_right
  · exfalso
    by_cases hyx : y' ∈ Subgroup.zpowers x
    · have hzpx : Subgroup.zpowers y' = Subgroup.zpowers x :=
        TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three (hBs.2 x hxBs) hy'1 hyx
      apply hnbr'.2.2.2
      have hbot : ⁅K', Subgroup.zpowers x⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro k hk
        refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        rw [SetLike.mem_coe, ← hzpx] at hz
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hk' : y' * k = k * y' :=
          Subgroup.mem_centralizer_iff.mp (hnbr'.1.2.2.2.1 hk) y' (Set.mem_singleton y')
        exact (Commute.zpow_left (show Commute y' k from hk') i).eq
      rw [hbot]
      exact bot_le
    · exact GGHalfJoin.main_false_narrow hTP hRig hRows h7 h8 hsub hctx hNoTr hAut hnbr' hyx hyy

end CFSG.StandardType

end
