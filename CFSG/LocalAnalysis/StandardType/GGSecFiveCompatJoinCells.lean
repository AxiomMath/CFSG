module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHC
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanRankOneSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Cells

open PsiDiag PsiDiagChar RankOneXfer in
theorem ggSecFiveCompat_of_sl2Embedding {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    {K : Subgroup G} (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K)
    {t' : StatedLieTag} {n' f' : ℕ} {ψ' : (ggU t' n' f').K →* G}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    (hker' : ψ'.ker ≤ Subgroup.center (ggU t' n' f').K) (hrange : ψ'.range = K)
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {γ : Fin (ggU t n f).D.rank → ℤ} {δ : Fin (ggU t' n' f').D.rank → ℤ}
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* (ggU t n f).K)
    (hphi : Function.Injective phi) (hγ : γ ∈ (ggU t n f).D.roots)
    (hupper : (sl2UpperUniSub k).map phi = (ggU t n f).D.rootGroup γ)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (ggU t n f).D)
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ) (u₀ : (ggU t n f).K)
    (hS : ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp phi).range =
      (ψ'.comp model'.phi).range) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨u, hm⟩ := SelectedRoot.rootMatch_of_sl2Range_eq phi hphi hupper hdiag model' ψ ψ'
    hpres.2.1.2 hker' u₀ hS
  exact ⟨t, n, f, ψ, hpres, K, hK, t', n', f', ψ', hadm, hrk, hker', hrange, δ, model'.root_mem, γ,
    hγ, u, hm⟩

theorem ggSecFiveCompat_of_selectedSL2 {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    {K : Subgroup G} (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K)
    {t' : StatedLieTag} {n' f' : ℕ} {ψ' : (ggU t' n' f').K →* G}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    (hker' : ψ'.ker ≤ Subgroup.center (ggU t' n' f').K) (hrange : ψ'.range = K)
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {γ : Fin (ggU t n f).D.rank → ℤ} {δ : Fin (ggU t' n' f').D.rank → ℤ}
    (model : SelectedRoot.SelectedSL2Model (ggU t n f).D k γ)
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ) (u₀ : (ggU t n f).K)
    (hS : ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
      (ψ'.comp model'.phi).range) :
    GGSecFiveCompat p B x L D J := by
  exact ggSecFiveCompat_of_sl2Embedding hpres hK hadm hrk hker' hrange
    model.phi model.injective model.root_mem model.upper_eq model.diag_mem model' u₀ hS

@[expose] def GGSecFiveCompatQTwoCellResNInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          GGSecFiveQTwoCell p B Bs x L D J → GGSecFiveCompat p B x L D J

@[expose] def GGSecFiveCompatOrderSixResNInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ → GGSecFiveCompat p B x L D J

@[expose] def GGSecFiveCompatOrderSixQTwoResNInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e → p = 3 → GGInnerDiagOnLabel GGLabQTwo p Bs L →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ → GGSecFiveCompat p B x L D J

theorem ggSecFive_qTwo_of_orderSix (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hsix : GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e) :
    p = 3 ∧ GGInnerDiagOnLabel GGLabQTwo p Bs L := by
  obtain ⟨hpres, hM, r, hrA, hrC, hr6⟩ := hsix
  have hMAE : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M := by
    rcases hM with ⟨m, σ, hm, hMeq⟩ | hD | hE
    · exact Or.inl (Or.inl ⟨m, σ, by omega, hMeq⟩)
    · exact Or.inl (Or.inr hD)
    · exact Or.inr hE
  have hns : ¬ GGSplitLie p L := ggSecFive_not_split_of_not_tier1 hcfg hReg hpres hMAE
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    hMAE.elim (fun h => GGIsWeylMatrixAD.le_three h) (fun h => GGIsWeylMatrixE.le_three h)
  have hp3 : p = 3 :=
    (ggSecFivePhanRankOne_of_card_six hRk1 hcfg hns hpres hle3 (Or.inl rfl) hrA hrC hr6).1
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, -, -, hlabF⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 L (Or.inl rfl) r hrA hrC
  let : Field F := hF
  have : Finite F := hFfin
  have hcardSL : Nat.card (ggRankOneIn L Bs r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  rw [hcardSL, ggSL2_card F] at hr6
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h9 : 9 ≤ Nat.card F ^ 2 := by simpa using Nat.pow_le_pow_left h3 2
    have h24 : 3 * 8 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have hn : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → GGLabQTwo p lab := by
    intro lab hΛ hlab
    have h2 : 2 ^ lab.n ≤ 2 := hF2 ▸ hlabF lab hΛ hlab
    show lab.n < 2
    by_contra hge
    have h4 : 4 ≤ 2 ^ lab.n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨hp3, ?_⟩
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hcfg.1.2.2.1.1
  have hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  exact ⟨hperf, lab, hΛ, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hsimp, hna, θ, hθ⟩ =>
    ⟨hsimp, hna, θ, hn lab hΛ hlab, hθ⟩) hraw⟩

theorem ggSecFiveCompatOrderSixResNInput_of_qTwo (hRk1 : GGSecFiveRk1PhanInput)
    (h : GGSecFiveCompatOrderSixQTwoResNInput) : GGSecFiveCompatOrderSixResNInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hsix t n f ψ hpres
  obtain ⟨hp3, hq⟩ := ggSecFive_qTwo_of_orderSix hRk1 hcfg hReg hsix
  exact h G p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hsix hp3 hq t n f ψ hpres

@[expose] def GGSecFiveCompatOrderSixQTwoADResNInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∨
          GGIsWeylMatrixD M) →
        p = 3 → GGInnerDiagOnLabel GGLabQTwo p Bs L →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ → GGSecFiveCompat p B x L D J

@[expose] def GGSecFiveCompatJoinResNAt (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M → ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
            ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K → GGSecFiveCompat p B x L D J

theorem ggSecFiveCompatRestWResNJoinInput_of_cells (hT : GGTBFixInput)
    (hSmall : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
          (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
            False)
    (hQ : GGSecFiveCompatQTwoCellResNInput) (hSix : GGSecFiveCompatOrderSixResNInput)
    (hB : GGSecFiveCompatJoinResNAt GGIsWeylMatrixB) (hD : GGSecFiveCompatJoinResNAt GGIsWeylMatrixD)
    (hE : GGSecFiveCompatJoinResNAt GGIsWeylMatrixE) (hF : GGSecFiveCompatJoinResNAt GGIsWeylMatrixF4) :
    GGSecFiveCompatRestWResNJoinInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow t n f ψ hpres hprem
  by_cases hQc : GGSecFiveQTwoCell p B Bs x L D J
  · exact hQ G p B Bs x L D J 𝒦 hcfg hReg hrow t n f ψ hpres hQc
  rcases hprem with hQc' | hHC | ⟨ι, M, e, hsix⟩
  · exact (hQc hQc').elim
  ·
    have hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
      (eq_of_le_of_card_centralQuotient_le (ggJoin_le_ggG0 (Bs := Bs) hcfg.2.2.2.1) hpres.2.2.1
        hHC.ge).symm
    obtain ⟨ι, M, hMw, e, hrefl⟩ := hcfg.2.2.2.2.1
    have hpres' : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := ⟨hMw, hrefl⟩
    by_cases hsix : GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e
    · exact hSix G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hsix t n f ψ hpres
    have hM := hpres'.1
    rcases hM with ⟨m, e', hm, hM | ⟨hm2, hM⟩ | ⟨hm4, hM⟩⟩ | ⟨e', hM⟩ | ⟨e', hM⟩ |
      ⟨e', hM⟩ | ⟨e', hM⟩ | ⟨e', hM⟩
    ·
      have : Fintype ι := Fintype.ofEquiv (Fin m) e'
      have hcard : Fintype.card ι = m := by rw [Fintype.card_congr e'.symm, Fintype.card_fin]
      have hm3 : 3 ≤ m := hcard ▸ ggSecFive_three_le_card_of_tbfix hT hcfg hpres'
      have hns : ¬ GGSplitLie p L :=
        ggSecFive_not_split_of_not_tier1 hcfg hReg hpres' (Or.inl (Or.inl ⟨m, e', hm3, hM⟩))
      by_cases hm5 : 5 ≤ m
      · have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
            Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
          fun r hr hrc h6 => hsix ⟨hpres', Or.inl ⟨m, e', hm5, hM⟩, r, hr, hrc, h6⟩
        exact (hrow ⟨𝒦, hcfg, hns, ι, M, e, hpres', ⟨m, e', hm5, hM⟩, hguard⟩).elim
      · exact (hSmall G p B Bs x L D J 𝒦 hcfg hReg hns ι M e hpres' ⟨m, e', by omega, hM⟩).elim
    · exact hB G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' ⟨m, e', hm2, hM⟩ hsix t n f ψ hpres
        hG0
    · exact hD G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' ⟨m, e', hm4, hM⟩ hsix t n f ψ hpres
        hG0
    · exact hE G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' (Or.inl ⟨e', hM⟩) hsix t n f ψ
        hpres hG0
    · exact hE G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' (Or.inr (Or.inl ⟨e', hM⟩)) hsix t n
        f ψ hpres hG0
    · exact hE G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' (Or.inr (Or.inr ⟨e', hM⟩)) hsix t n
        f ψ hpres hG0
    · exact hF G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hpres' ⟨e', hM⟩ hsix t n f ψ hpres hG0
    ·
      have : Fintype ι := Fintype.ofEquiv (Fin 2) e'
      have hcard : Fintype.card ι = 2 := by rw [Fintype.card_congr e'.symm, Fintype.card_fin]
      have h3 := ggSecFive_three_le_card_of_tbfix hT hcfg hpres'
      exfalso
      omega
  · exact hSix G p B Bs x L D J 𝒦 hcfg hReg hrow hQc ι M e hsix t n f ψ hpres

end Cells

end CFSG.StandardType

end
