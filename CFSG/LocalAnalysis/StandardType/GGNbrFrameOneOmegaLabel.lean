module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp


theorem largeEvenLabelAll_frame_omegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ :=
      OrthExc.recipeOmegaMinus_weylInputsSC ggOrthSignedTorusInput_holds hp hn (Or.inl hpn)
        (by omega) hQ
    have := charP_two_of_card hK
    have hm : 3 ≤ l - 1 := by omega
    have hpK : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ'.1, ?_⟩
    refine ⟨l - 1, ggTorusLift_omegaMinus hp hp2 hpK hm b c, ?_⟩
    intro L' _ _ ψ A hA
    exact ggTorusFrame_of_frameEltSC hp hp2 hZ (fun φ hφ _ => hφ) hcp
      (ggTorusFrameEltSC_of_signedEltSC hp
        (ggOrthSignedTorusInput_holds.2 K (l - 1) p b c hm hbc hp (Or.inl hpK)))
      L' ψ A hA

end CFSG.StandardType

end
