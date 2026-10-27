module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineFinal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggTablePRow_line_of_config
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L)
    (hKi : GGInnerDiagOn Bs K) (hn : GGNbr p B x D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) (hpJ : p ∣ Nat.card J)
    (hLB : GGLBalanceInput) {labJ labK : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛK : LargeEvenInLambda2 labK) (hr : GGRegimeLine p (Nat.card Bs) labJ labK)
    (hhJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hhK : GGHasLabel labK (K ⧸ Subgroup.center K)) :
    ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
      GGTablePRow p labJ' labK' ∧
      GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K) := by
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hN, hx, hBasic⟩ := ggTPNBasicB_of_config hc hL hKi hn hJK hpJ hLB
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hI1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    obtain ⟨hp3, -, T, hTJ⟩ := hr
    exact ⟨fun hp7 _ => absurd (hp3.symm.trans hp7) (by norm_num),
      fun _ _ _ => ggTPNRankJ_of_line ggLabelRigidInput_holds hΛJ hTJ hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    ggTablePKnownRK_line_of_B3 GGK0ExcB3Prod.ggK0ExcB3_holds p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD hker labJ labK hΛJ hΛK hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

end CFSG.StandardType

namespace CFSG.StandardType.QTwo

open CFSG CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

theorem qtwoDU5_tablePRow_twA3 {labJ labK : LargeEvenLabel}
    (hJ : labJ = ⟨.twA, 3, 1⟩ ∨ labJ = ⟨.twD, 3, 1⟩) (h : GGTablePRow 3 labJ labK) :
    labK = ⟨.twA, 4, 1⟩ ∨ labK = ⟨.twA, 5, 1⟩ ∨ labK = ⟨.C, 4, 1⟩ ∨ labK = ⟨.D, 4, 1⟩ ∨
      labK = ⟨.D, 5, 1⟩ := by
  rcases hJ with rfl | rfl <;> simp [GGTablePRow] at h
  · have h3 : ¬ Even 3 := by decide
    rcases h with h | h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h3', -⟩ | ⟨h3', -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact absurd h3' h3
    · exact absurd h3' h3
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem qtwoDU5_nbr_tableP
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hc : GGConfig 3 B Bs x L D J) (hL : GGInnerDiagOn Bs L) (hKi : GGInnerDiagOn Bs K)
    (hn : GGNbr 3 B x D J y K) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K)
    (hpJ : 3 ∣ Nat.card J) (hLB : GGLBalanceInput) (hcard : Nat.card Bs = 3 ^ 5)
    (hJlab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ labK : LargeEvenLabel, LargeEvenInLambda2 labK ∧ GGHasLabel labK (K ⧸ Subgroup.center K) ∧
      (labK = ⟨.twA, 4, 1⟩ ∨ labK = ⟨.twA, 5, 1⟩ ∨ labK = ⟨.C, 4, 1⟩ ∨ labK = ⟨.D, 4, 1⟩ ∨
        labK = ⟨.D, 5, 1⟩) := by
  obtain ⟨lab₀, hΛ₀, hh₀, -⟩ := largeEvenMarking_exists_hasLabel hKi
  have hΛJ : LargeEvenInLambda2 ⟨.twA, 3, 1⟩ := by
    unfold LargeEvenInLambda2
    simp
  have hr : GGRegimeLine 3 (Nat.card Bs) ⟨.twA, 3, 1⟩ lab₀ :=
    ⟨rfl, hcard.le, .A3, Or.inr ⟨Or.inl rfl, rfl, by norm_num⟩⟩
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hJ', hK'⟩ :=
    ggTablePRow_line_of_config hc hL hKi hn hI1 hJK hpJ hLB hΛJ hΛ₀ hr hJlab hh₀
  have hiso := ggLabelRigidInput_holds _ _ _ hΛJ hΛJ' hJlab hJ'
  have hJ'' : labJ' = ⟨.twA, 3, 1⟩ ∨ labJ' = ⟨.twD, 3, 1⟩ := by
    unfold GGLabelIso at hiso
    rcases labJ' with ⟨t, r, n⟩
    cases t <;> simp at hiso ⊢ <;> omega
  exact ⟨labK', hΛK', hK', qtwoDU5_tablePRow_twA3 hJ'' hrow⟩

theorem qtwoDU5_nbr_marking
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {y : G} {K : Subgroup G} (hn : GGNbr 3 B x D J y K)
    (hA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) (hpJ : 3 ∣ Nat.card J)
    (hLB : GGLBalanceInput) (hcard : Nat.card Bs = 3 ^ 5)
    (hJlab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.D, 4, 1⟩) 3 Bs K := by
  have hc : GGConfig 3 B Bs x L D J := hroute.1.1
  have hL : GGInnerDiagOn Bs L := hroute.1.2.2.1.1
  have hKi : GGInnerDiagOn Bs K := hroute.1.2.2.1.2 y K hn
  obtain ⟨labK, hΛK, hhK, hlist⟩ := qtwoDU5_nbr_tableP hc hL hKi hn hI1 hJK hpJ hLB hcard hJlab
  have hfield : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → lab.n = 1 := by
    intro lab hΛ hhas
    have hiso := ggLabelRigidInput_holds _ _ _ hΛ hΛK hhas hhK
    unfold GGLabelIso at hiso
    clear hhas hΛ
    revert hiso
    rcases lab with ⟨t, r, n⟩
    rcases hlist with rfl | rfl | rfl | rfl | rfl <;> cases t <;> simp +contextual
  have hns : ¬ GGSplitLie 3 K := qtwoDNbr_nonSplit hfield
  have hEnn := ggX_ennola_of_nonSplit hroute hpres hle3 (Or.inr ⟨⟨y, hn⟩, hA⟩) hns
  refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ hhas hrow => ?_) hEnn
  have hiso := ggLabelRigidInput_holds _ _ _ hΛ hΛK hhas hhK
  unfold GGLabelIso at hiso
  simp only [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
    ggRowP_EE7, ggRowP_EE8, ggRowP_NF4] at hrow
  clear hEnn hhas hhK hΛ hΛK
  revert hiso hrow
  rcases lab with ⟨t, r, n⟩
  rcases hlist with rfl | rfl | rfl | rfl | rfl <;> cases t <;>
    simp +contextual [Nat.even_iff, Nat.odd_iff]

end CFSG.StandardType.QTwo

end
