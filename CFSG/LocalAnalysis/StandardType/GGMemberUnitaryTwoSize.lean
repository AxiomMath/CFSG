module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTwA5TwoMemberSize
import CFSG.LocalAnalysis.StandardType.GGNsq2Strict
import CFSG.LocalAnalysis.StandardType.GGNsq2Rank
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggMember_three_pow_six_of_card_automizer
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hTB : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hBB : B = Bs) {X : Subgroup G} (hX : X ∈ 𝒦)
    (h5 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X) :
    720 ≤ Nat.card ↥(ggAutomizer X Bs) → 3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥ := by
  have hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs X := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) h5
    obtain ⟨⟨hrow, hn1, hr5⟩, hN', hBsI⟩ := hP
    refine ⟨⟨?_, hr5, hn1⟩, hN', hBsI⟩
    rcases hrow.1 with ⟨htw, -⟩ | ⟨-, hr3⟩
    · exact htw
    · omega
  have hW : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs) :=
    (nsQ2U62_member_weyl hRig hLB hP hcfg hBB hX hlab).1
  have h720 : Nat.card ↥(ggAutomizer X Bs) = 720 := by
    obtain ⟨eA, -⟩ := hW
    obtain ⟨eP, -⟩ := ggCoxeterA_mulEquivPerm 5
    rw [← Nat.card_congr eA.toEquiv, Nat.card_congr eP.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  exact fun _ => GGSecFiveRouteCfg.three_pow_six_le_card_or_center_eq_bot_of_twA5_member
    hTB hcfg hpres hle3 hBB hX hlab h720

theorem ggL_three_pow_six_of_card_automizer
    (hTB : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M)
    (h5 : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L) :
    720 ≤ Nat.card ↥(ggAutomizer L Bs) → 3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥L = ⊥ := by
  intro h720
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  rcases hAD with hA | hD
  · obtain ⟨m, σ, -, hM⟩ := hA
    have hlt := ggPhanStrict_card_lt_join_of_wA hWA hcfg
    have hJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = (m + 1).factorial := by
      rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, l05nK3a_card_coxeterA]
    have hm7 : 7 ≤ m + 1 := by
      by_contra hlt7
      have h1 : (m + 1).factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
      have h6 : Nat.factorial 6 = 720 := by decide
      rw [hJoin] at hlt
      omega
    have h7dvd : 7 ∣ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
      rw [hJoin]
      exact Nat.dvd_factorial (by norm_num) hm7
    exact Or.inl (three_pow_six_le_card_of_seven_dvd hconf.2.1.2.1 h7dvd)
  · have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
        (b : G) ∈ Subgroup.zpowers x := by
      intro b hfixed
      obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
      have hrefl : GGReflGenerated 3 (ggAutomizer K' Bs) := hcfg.2.1 y K' hN
      exact hTB G 3 B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN hrefl
        (Or.inr hcfg.2.1) b hfixed
    have hcard := nsQ2U62_card_D hcfg hFix h5 hpres hD
    exact Or.inl (le_of_eq hcard.1.symm)

end CFSG.StandardType

end
