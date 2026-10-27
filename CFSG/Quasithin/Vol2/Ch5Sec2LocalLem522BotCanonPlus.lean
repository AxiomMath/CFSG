module

public import CFSG.Quasithin.H13.F112PlusDefs
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotCanon
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.EmptyFaithful.S1422Setting
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522Bot
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem center_ne_bot_of_p5 (hF : L2TorusFact) (h516 : Stmt5_1_6) {G : Type} [Group G] [Finite G]
    {T M L V H B D L₂ Dp : Subgroup G} {n : ℕ} (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n 5) :
    centerOf (L₂ ⊔ sec52S M H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  have hD := hyp.notation59.2.1
  obtain ⟨-, hcase⟩ := h516 G T M L V H D n h hyp.ch5Module hH hD hyp.pCore_D
  obtain ⟨-, hcard⟩ := h.isCyclic_card_of_isHall hF hD
  have h5 : 5 ∣ 2 ^ n - 1 := by
    rw [← hcard, ← hyp.card_Dp]
    exact Subgroup.card_dvd_of_le hyp.Dp_le
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZH : ⁅Z, H⁆ = ⊥ := by
    rcases hcase with ⟨-, -, hZ⟩ | ⟨-, -, hZ⟩ | ⟨h2, -⟩ | ⟨-, -, hZ, -⟩
    · exact hZ
    · exact hZ
    · subst h2
      norm_num at h5
    · exact hZ
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := h.isSylowTwoOf hTH
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply hH.1.2
    have := F7.isSylowTwoOf_pCoreOf_le hTsyl
    rw [hT] at this
    exact le_bot_iff.mp this
  have hZT : Z ≤ T := (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
  have hZ2 : IsPGroup 2 Z := h.sylow.1.to_le hZT
  have hZ1 : Z ≠ ⊥ := CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1 hT1
  have hZC : Z ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
  have hSH : sec52S M H ≤ H := (Subgroup.map_subtype_le _).trans inf_le_right
  have hL₂H : L₂ ≤ H := by
    obtain ⟨K₁, hK₁, -, hc⟩ := hyp.choice
    rcases hc with ⟨-, rfl⟩ | ⟨-, -, P, hP, hL₂P⟩
    · exact A3.subnormal_le hK₁.2.2.1
    · exact (A3.subnormal_le hL₂P.2.2.1).trans (hP.1.trans (oTwoUpper_le H))
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hZS : Z ≤ sec52S M H :=
    RonanD33.le_pCoreOf_of_le_normalizer (le_inf (hZT.trans h.T_le) (hZT.trans hTH))
      (inf_le_right.trans hHZ) hZ2
  have hle : Z ≤ centerOf (L₂ ⊔ sec52S M H) :=
    le_inf (hZS.trans le_sup_right) (hZC.trans (Subgroup.centralizer_le (sup_le hL₂H hSH)))
  intro hbot
  exact hZ1 (le_bot_iff.mp (hle.trans hbot.le))

theorem stmt5_2_2_bot_of_correctedPlus (hF : L2TorusFact) (h311 : Theorem311Stmt)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2)
    (hLie : Stmt5_2_L2Lie) (hDSB : DSBStatementPlus) (hDSC : DSCStatementPlus)
    (h516 : Stmt5_1_6) (hlist : Stmt5_2_2_bot_listC) :
    Stmt5_2_2_bot := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hhyp, hborQ⟩ := hyp.hyp111 hF h311 h510 h331 hR hL2 hLie hO
  obtain ⟨-, -, h3, h5⟩ := hyp.SDp_facts hF h311 h510 h331 hR hO
  have hqt : IsQuasithinSub (L₂ ⊔ (Dp ⊔ S) ⊔ S) := isQuasithinSub_of_qtke h.qtke _
  have hnorm : (S.subgroupOf (S ⊔ borelOf (Dp ⊔ S) S)).Normal := by
    rw [hborQ, sup_idem, Subgroup.subgroupOf_self]
    infer_instance
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  rcases hyp.p_cases with hp | hp
  · subst hp
    have hS3 := h3 rfl
    obtain ⟨L1', L2', hsw, hcen, hlistB, hsec⟩ :=
      hDSB G L₂ (Dp ⊔ S) S hhyp hqt (Or.inr hnorm) hL₂ns hS3 le_sup_right
    have hhyp' : Hyp111 L1' L2' S := by
      rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hhyp
      · exact hhyp.symm
    exact hlist G T M L V H B D L₂ Dp n hyp hO hS3 L1' L2' hsw hhyp' hcen hlistB hsec
  · subst hp
    have hc : centerOf (L₂ ⊔ S ⊔ borelOf (Dp ⊔ S) S) ≠ ⊥ := by
      rw [hborQ, sup_assoc, sup_idem]
      exact center_ne_bot_of_p5 hF h516 hyp
    exact hDSC G L₂ (Dp ⊔ S) S hhyp hqt (Or.inr hnorm) hL₂ns hc le_sup_right (h5 rfl)

end CFSG.Quasithin.H13
