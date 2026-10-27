module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4BstarRankInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

section Main

theorem bstar_le_ggG0_D4_of_someCompat (hMp : GGInnerDiagMpInput)
    (hMk : GGInnerDiagMarkingInput) (h5 : GGCompatNbrSomeInput) (hdet : ∀ t, GGRootDetect t)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hOp : GGOpAutTrivial 3 Bs)
    (hInn : GGInnerDiagAll 3 B Bs x L D J) {f : ℕ} {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) :
    Bs ≤ ggG0 3 B x L D J := by
  obtain ⟨t₀, n₀, f₀, ψ₀, hpres₀, K, hK, hcomp⟩ :=
    h5 G 3 B Bs x L D J hcfg hOp hInn .POmegaPlus 4 f ψ hpres
  obtain ⟨γ, hγ, u, hall⟩ := ggTorusOnRoot_of_compatNbr hMp hInn hpres₀.2.1.1 hK hcomp
  intro b hb
  have hbN₀ := mem_normalizer_range_of_bstar hpres₀.2.1.1 hBsN hb
  have hbp₀ := pow_mem_centralizer_range_of_bstar hcfg ψ₀ hb
  have h₀ : GGPsiInnerDiag (ggU t₀ n₀ f₀).D ψ₀ b := by
    by_cases hD : t₀ = .POmegaPlus ∧ n₀ = 4
    · obtain ⟨rfl, rfl⟩ := hD
      exact ggPsiInnerDiag_D4_of_semilinear hpres₀.2.1.2 Nat.prime_three (by norm_num) hbN₀
        hbp₀ hγ (hall b hb) (D4Bstar.semilinear_of_torusOnRoot hcfg hpres₀ hBsN hγ hall b hb)
    · exact hdet t₀ G n₀ f₀ ψ₀ hpres₀.1.1 hpres₀.1.2 hpres₀.2.1.2 3 Nat.prime_three
        (by norm_num) (fun h => hD ⟨h.1, h.2.1⟩) b hbN₀ hbp₀ γ hγ u (hall b hb)
  exact D4Bstar.mem_ggG0_of_psiInnerDiag hcfg hpres hBsN hb
    (ggPsiInnerDiag_of_presents_two hMp hMk hpres hpres₀ (hBsN hb) h₀)

theorem ggHypSixD4BstarRankInput_of_someCompat (hMp : GGInnerDiagMpInput)
    (hMk : GGInnerDiagMarkingInput) (h5 : GGCompatNbrSomeInput) (hdet : ∀ t, GGRootDetect t) :
    GGHypSixD4BstarRankInput := by
  intro G _ _ B Bs x L D J hcfg hOp hInn f ψ hpres hBsN
  have hle := bstar_le_ggG0_D4_of_someCompat hMp hMk h5 hdet hcfg hOp hInn hpres hBsN
  obtain ⟨-, -, -, -, h81⟩ := hcfg.tableB_facts
  rw [inf_eq_left.mpr hle]
  calc 27 ≤ 3 ^ 4 := by norm_num
    _ ≤ Nat.card Bs := h81

theorem ggHypSixD4SemilinearInput_of_someCompat (hMp : GGInnerDiagMpInput)
    (hMk : GGInnerDiagMarkingInput) (h5 : GGCompatNbrSomeInput) (hdet : ∀ t, GGRootDetect t) :
    GGHypSixD4SemilinearInput :=
  ggHypSixD4SemilinearInput_of_bstarRank (ggHypSixD4BstarRankInput_of_someCompat hMp hMk h5 hdet)

theorem ggHypSixV2Input_of_someCompat_d4 (hMp : GGInnerDiagMpInput)
    (hMk : GGInnerDiagMarkingInput) (h5 : GGCompatNbrSomeInput) (hdet : ∀ t, GGRootDetect t) :
    GGHypSixV2Input :=
  ggHypSixV2Input_of_someCompat hMp hMk h5 hdet
    (ggHypSixD4SemilinearInput_of_someCompat hMp hMk h5 hdet)

end Main

end CFSG.StandardType
