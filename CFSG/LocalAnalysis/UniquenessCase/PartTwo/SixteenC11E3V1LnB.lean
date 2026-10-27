module

public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.F918D4
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1611e3_sl3F2_smul_fix_eq_zero :
    ∀ a : Fin 3 → ZMod 2, (∀ γ : FFC.SL3F2, γ • a = a) → a = 0 := by
  decide +kernel

theorem s1611e3_v1_ln3_comm_rank {J : Type} [CommGroup J]
    [Finite J] (hJ2 : ∀ x : J, x ^ 2 = 1) {L₀ : Subgroup (MulAut J)} {Z : Subgroup J}
    (hN : BinaryNaturalSL L₀ ⊤ Z 3 1) (hZ : Z ≤ fixV L₀) (hcomm : commSub (⊤ : Subgroup J) L₀ = ⊤)
    (hZne : Z ≠ ⊥) {s : MulAut J} (hs : s ∈ L₀) (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    2 ≤ rk ↥(commSub (⊤ : Subgroup J) (Subgroup.zpowers s)) := by
  obtain ⟨D⟩ := FFC.exists_natQuot3 hN
  have hfix : fixV L₀ = Z := by
    refine le_antisymm ?_ hZ
    intro v hv
    have hfixθ : ∀ γ : FFC.SL3F2,
        γ • Multiplicative.toAdd (D.θ ⟨v, Subgroup.mem_top v⟩) =
          Multiplicative.toAdd (D.θ ⟨v, Subgroup.mem_top v⟩) := by
      intro γ
      have hthis := D.equiv γ ⟨v, Subgroup.mem_top v⟩
      have hcong : D.θ ⟨(D.ρ γ : MulAut J) v, D.inv γ v (Subgroup.mem_top v)⟩ =
          D.θ ⟨v, Subgroup.mem_top v⟩ := by
        congr 1
        exact Subtype.ext (hv (D.ρ γ) (D.ρ γ).2)
      rw [hthis] at hcong
      simpa using congrArg Multiplicative.toAdd hcong
    have hzero := s1611e3_sl3F2_smul_fix_eq_zero _ hfixθ
    have hθ1 : D.θ ⟨v, Subgroup.mem_top v⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hzero]
      rfl
    exact (D.θ_ker ⟨v, Subgroup.mem_top v⟩).1 hθ1
  have hcommX : XMod.commOf ↥L₀ (⊤ : Subgroup J) = ⊤ := by
    rw [commOf_eq_commSub, hcomm]
  have hleZ : Nat.card ↥Z ≤ 2 := by
    have h := card_fixV_le_two_of_natural3 hJ2 L₀ ⊤ (fun _ _ _ _ => Subgroup.mem_top _)
      hcommX (by rw [top_inf_eq, hfix]; exact hN)
    rwa [top_inf_eq, hfix] at h
  have hZcard : Nat.card ↥Z = 2 := by
    have h1 : 1 < Nat.card ↥Z := (Subgroup.one_lt_card_iff_ne_bot Z).2 hZne
    omega
  have hcover := cover_commSub_involution hJ2 L₀ ⊤ (fun _ _ _ _ => Subgroup.mem_top _)
    hcommX (by rw [top_inf_eq, hfix]; exact hN) (by rw [top_inf_eq, hfix]; exact hZcard)
    s hs hs1 (by rw [pow_two]; exact hs2)
  have hrk : rk ↥(commSub (⊤ : Subgroup J) (Subgroup.zpowers s)) = 2 := by
    unfold rk
    rw [hcover.1, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  exact hrk.ge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
