module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SpAmbient
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusOneData
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinRed

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem six_le_rank_of_tableB_sp_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {a r : ℕ} (ha : 3 ≤ a) (hF : Nat.card F = 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSpGroup F a)}
    {I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup F a)))}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj (LargeEvenSpGroup F a)) I L' ψ A)
    (hcard : 3 ^ 6 ≤ Nat.card A) : 6 ≤ a := by
  haveI : NeZero a := ⟨by omega⟩
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, -⟩ := hTB
  have hAI' : ∀ α ∈ A, ∃ β : MulAut (LargeEvenProj (LargeEvenSpGroup F a)),
      ∀ l, β (ψ l) = ψ (α l) := by
    intro α hα
    obtain ⟨β, -, hβ⟩ := hAI α hα
    exact ⟨β, hβ⟩
  have hC := TypeA.card_inducedSub hψ hker hperf hAI'
  have hE := TypeA.isElemAbelian_inducedSub hψ hA
  obtain ⟨E, hEE, hEC⟩ := TableBSymp.exists_of_subset_inn
    (TableBSymp.center_spProj_eq_bot (K := F) (m := a))
    (fun α _ => TwoThree.mem_range_conj_sp hF ha α) hE
  have hb := TwoThree.card_le_pow_half hEE (TwoThree.card_sq_le_sp hF hEE)
  rw [show 2 * a / 2 = a by omega, hEC, hC] at hb
  by_contra h6
  have ha5 : a ≤ 5 := by omega
  have hle : (3 : ℕ) ^ 6 ≤ 3 ^ 5 :=
    hcard.trans (hb.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 3) ha5))
  norm_num at hle

theorem native_sp_equiv_of_tableB
    {F : Type} [Field F] [Finite F] [CharP F 2] {a r : ℕ} [NeZero a]
    (ha : 3 ≤ a) (hF : Nat.card F = 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSpGroup F a)}
    {I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup F a)))}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj (LargeEvenSpGroup F a)) I L' ψ A)
    (hcard : 3 ^ 6 ≤ Nat.card A) :
    ∃ e : L' ≃* StatedSp a F,
      ∀ l, e l = TableBSymp.spProjEquivSp (K := F) (m := a) (ψ l) := by
  have ha6 := six_le_rank_of_tableB_sp_two ha hF hTB hcard
  have hk := SpFin.ker_eq_bot hF (by omega) ψ hTB.1 hTB.2.1 hTB.2.2.1
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk
  let e : L' ≃* StatedSp a F := (MulEquiv.ofBijective ψ ⟨hinj, hTB.1⟩).trans
    (TableBSymp.spProjEquivSp (K := F) (m := a))
  exact ⟨e, fun _ => rfl⟩


theorem sp_two_data_of_innerDiagOnLabel {G : Type} [Group G]
    {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G}
    (hS : ∀ lab, S 3 lab → (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSpGroup F a)),
      3 ≤ a ∧ Nat.card F = 2 ∧ commutator K = ⊤ ∧
        ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
          Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup F a) →* _) := by
  have hpred : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.n = 1 := by
    intro lab hLambda hs
    obtain ⟨hBC, hn⟩ := hS lab hs
    have hr : 3 ≤ lab.rank := by
      rcases hBC with htag | htag <;> simp only [LargeEvenInLambda2, htag] at hLambda <;> omega
    exact ⟨hBC, hr, by rw [hn]; norm_num, hn⟩
  obtain ⟨hperf, lab, hLambda, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => S 3 lab)
    (fun lab hLambda hs => nbrC_labelAll_guard (SympMinus.labelAll_one (hpred lab hLambda hs)))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, a, F', _, _, _, e, ha, hF, -, hI⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  refine ⟨a, F', inferInstance, inferInstance, inferInstance, hBsN, θ.trans e, ha, hF, hperf,
    fun b hb => ?_⟩
  obtain ⟨g, hg⟩ := hI (hBsI b hb)
  refine ⟨e g, ?_⟩
  rw [ggLAut_congr K θ (θ.trans e) ⟨b, hBsN hb⟩, ← hg]
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem native_sp_equiv_of_innerDiagOnLabel
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (e : K ≃* StatedSp a F), 6 ≤ a ∧ Nat.card F = 2 ∧ a + 1 = n := by
  obtain ⟨a, F, hfield, hfin, hchar, hNs, θ, ha, hF, hperf, hinner⟩ :=
    sp_two_data_of_innerDiagOnLabel hS hK
  letI : Field F := hfield
  letI : Finite F := hfin
  letI : CharP F 2 := hchar
  letI : NeZero a := ⟨by omega⟩
  have hAr := P9_Wa_card_range hBs hcard hz hz1 hN hker
  have hTB : GGTorusTBGroup 3 (n - 1) (LargeEvenProj (LargeEvenSpGroup F a))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup F a) →* _)) K
      (ggQuotHom θ) (ggGamma K hN).range := by
    refine ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
      (fun b hb => ?_) (by rw [hAr]) ?_
    · simpa only using hinner b hb
    · rw [hAr]
      exact Nat.pow_le_pow_right (by norm_num) (by rcases hn with rfl | rfl <;> norm_num)
  have hA6 : 3 ^ 6 ≤ Nat.card (ggGamma K hN).range := by
    rw [hAr]
    exact Nat.pow_le_pow_right (by norm_num) (by rcases hn with rfl | rfl <;> norm_num)
  have ha6 := six_le_rank_of_tableB_sp_two ha hF hTB hA6
  obtain ⟨e, he⟩ := native_sp_equiv_of_tableB ha hF hTB hA6
  refine ⟨a, F, hfield, hfin, hchar, e, ha6, hF, ?_⟩
  exact native_sp_rank_eq_of_card_bstar ha hF e hBs hcard hz hz1 hN hker hBstar


end CFSG.StandardType.FrameRoute

end
