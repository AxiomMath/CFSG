module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinDNodePlus
public import CFSG.LocalAnalysis.StandardType.PhanDNativeNodeMinus
public import CFSG.LocalAnalysis.StandardType.GGPhanOneNodePosition
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan.PhanE


@[expose] def GGSecFiveJoinMemberAt (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → T M → ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
            ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
            ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
              ∃ (K : Subgroup G), (K = L ∨ ∃ y : G, GGNbr p B x D J y K) ∧
              ∃ (t' : StatedLieTag) (n' f' : ℕ) (ψ' : (ggU t' n' f').K →* G),
                StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
                ψ'.ker ≤ Subgroup.center (ggU t' n' f').K ∧ ψ'.range = K ∧
                ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' 2)
                  (δ : Fin (ggU t' n' f').D.rank → ℤ)
                  (model : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ),
                  (ψ'.comp model.phi).range = ggRankOnePerf Bs r₀

theorem ggSecFiveCompatJoinResNAt_D_of_member (hL1 : GGSecFiveL1PhanInput)
    (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hMem : GGSecFiveJoinMemberAt GGIsWeylMatrixD) :
    GGSecFiveCompatJoinResNAt GGIsWeylMatrixD := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hpres hT hSix t n f ψ hψ hJ
  obtain ⟨r₀, -, hr₀, K, hK, t', n', f', ψ', hadm, hrk, hker', hrange', k', _, _, _, δ, model',
    hmember⟩ := hMem G p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hpres hT hSix t n f ψ hψ hJ
  obtain ⟨m, σ, hm, hM⟩ := hT
  obtain ⟨q, hq4, -, hmk⟩ :=
    ggSecFiveJoinD_markedPres hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hReg hpres hm σ hM hSix hJ
  have hq1 : 1 ≤ q := by
    rcases Nat.lt_or_ge q 1 with h | h
    · interval_cases q
      norm_num at hq4
    · exact h
  have hF : Nat.card (GaloisField 2 (2 * q)) = (2 ^ q) ^ 2 := card_galoisField_two_mul 2 q hq1
  have hMsl : GGSimplyLacedConnected M :=
    ggSimplyLacedConnected_of_weyl (Or.inl ⟨m, σ, by omega, Or.inr (Or.inr ⟨hm, hM⟩)⟩)
      (fun i j hij => GGIsWeylMatrixAD.le_three (Or.inr ⟨m, σ, hm, hM⟩) i j hij)
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs := by
    rw [hJ]
    exact ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨T, hTu, k₀, γ, phi, hphi, hγ, hup, hdiag, v, hv⟩ :=
      JoinDNodePlus.exists_nativeNode_POmegaPlus hm he hq4 (GaloisField 2 (2 * q)) hF
    obtain ⟨ψ₀, hψ₀, hnodes⟩ := hmk (GaloisField 2 (2 * q)) hF .POmegaPlus (Or.inl ⟨rfl, he⟩) T hTu
    exact ggSecFiveCompat_of_phan_node hψ₀ e hMsl hA hr₀ (σ k₀) _ (hnodes k₀) hK hadm
      hrk hker' hrange' phi hphi hγ hup hdiag v hv model' hmember
  · obtain ⟨T, hTu, k₀, γ, phi, hphi, hγ, hup, hdiag, v, hv⟩ :=
      PhanDNative.exists_nativeNode_POmegaMinus hm ho hq4 (GaloisField 2 (2 * q)) hF
    obtain ⟨ψ₀, hψ₀, hnodes⟩ :=
      hmk (GaloisField 2 (2 * q)) hF .POmegaMinus (Or.inr ⟨rfl, ho⟩) T hTu
    exact ggSecFiveCompat_of_phan_node hψ₀ e hMsl hA hr₀ (σ k₀) _ (hnodes k₀) hK hadm
      hrk hker' hrange' phi hphi hγ hup hdiag v hv model' hmember

end CFSG.StandardType
