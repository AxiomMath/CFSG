module

public import CFSG.Quasithin.Vol2.Ch7Lem7710
public import CFSG.Quasithin.Vol2.Ch7Sec77G2
public import CFSG.Quasithin.Vol2.Ch7Sec77Sp4
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem a318Exclusion_sp4_four (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (hq : CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :
    A318Exclusion ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := by
  obtain ⟨hz, -, hno⟩ := hE.1 F 2 le_rfl (hF.trans (by norm_num))
  have hs : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := by
    have := hq.2.1
    exact ((QuotientGroup.quotientBot (G := ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hz.symm)).isSimpleGroup
  refine ⟨hs, FFC.threeRank2_statedSp.pRank_two_le, ?_⟩
  intro Y _ s p k _ _ hY _ f hf
  exact (hno Y s p k hY).1 f hf

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_c27Sp4 (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hSp4 : Sp4PlaneFixFact) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (h4 : CFSG.Quasithin.IsSp4Block K) : False := by
  obtain ⟨r, b, hr, hyb⟩ := exists_threePart θ
  obtain ⟨-, F, hFf, hFt, hF4, α, hαs, hαk, -⟩ := id h4
  have eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hFc : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
  have hX := a318Exclusion_sp4_four hE hFc (CFSG.LocalCores.isQuasisimple_of_mulEquiv eX hKq)
  exact C.false_of_sp4Block hSp4 hF hK h4 hr (C.threePart_mem hA h36 h38 hK hKq eX hX hyb) hyb

theorem false_of_c27G2
    (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hG2 : CFSG.Quasithin.IsG2Block K) :
    False := by
  obtain ⟨r, b, hr, hyb⟩ := exists_threePart θ
  have hX : A318Exclusion (↥K ⧸ CFSG.pCore 2 ↥K) :=
    a318Exclusion_u33 (fun _ _ _ h => two_le_pRank_of_isPSU_three_three1515e h) hG2.2.1
  exact C.false_of_g2Block hF hK hG2 hr
    (C.threePart_mem hA h36 h38 hK hKq (MulEquiv.refl _) hX hyb) hyb

theorem c27Cases_rest4
    (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA : A318Facts) (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hSp4 : Sp4PlaneFixFact)
    (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L) :
    (C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
          (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
          Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
            (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∨
      C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) := by
  rcases C.c27Cases_rest3 hC27 h443 hC24a hC24b h36 h38 hA hF hK hKq hKM with h | h | h | h
  · exact (C.false_of_c27Sp4 hA h36 h38 hE hSp4 hF hK hKq h.1).elim
  · exact (C.false_of_c27G2 hA h36 h38 hF hK hKq h.1).elim
  · exact Or.inl h
  · exact Or.inr h

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
