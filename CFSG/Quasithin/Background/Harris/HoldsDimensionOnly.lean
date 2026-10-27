module

public import CFSG.Quasithin.Background.G9StmtsDimensionOnly
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.RouteTits
public import CFSG.Quasithin.Background.Harris.Alt6.Final
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddWrappers
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Final
public import CFSG.Quasithin.Background.Harris.G2.Final
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Route3D4
public import CFSG.Quasithin.Background.Harris.L3.Final
public import CFSG.Quasithin.Background.Harris.Ln2.Final4
public import CFSG.Quasithin.Background.Harris.Ln2.Final5
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.Quasithin.Background.Harris.Routing.A7M12
public import CFSG.Quasithin.Background.Harris.Routing.Exclusions
public import CFSG.Quasithin.Background.Harris.Routing.IMBCases
public import CFSG.Quasithin.Background.Harris.Routing.LieExclusions
public import CFSG.Quasithin.Background.Harris.Routing.Small
public import CFSG.Quasithin.Background.Harris.Sp4.Final

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
open CFSG.Quasithin.Background.Harris.OrdinaryProofs

@[expose] def OneCompForDimensionOnly (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V)) (m : ℕ),
    OneCompSetting Γ A L m → P ↥L → G93ConclDimensionOnly Γ L m

theorem OneCompFor.toDimensionOnly {P : ∀ (X : Type) [Group X], Prop} (h : OneCompFor P) :
    OneCompForDimensionOnly P :=
  fun V _ _ _ Γ A L m hs hP => (h V Γ A L m hs hP).toDimensionOnly

theorem oneCompForDimensionOnly_famSpor_M24 :
    OneCompForDimensionOnly (FamSpor .M24) := by
  rintro V _ _ _ Γ A L m hs ⟨hsimp, ⟨e⟩⟩
  obtain ⟨e'⟩ := nonempty_quotCenterEquiv hs.L_comp hsimp
  exact Or.inr (Or.inl
    (CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case1_M24_core_dimensionOnly
      (OneCompSetting.toG93Hyp hs) ⟨e'.trans e⟩))

theorem oneCompForDimensionOnly_famSpor_M22 :
    OneCompForDimensionOnly (FamSpor .M22) := by
  rintro V _ _ _ Γ A L m hs ⟨hsimp, ⟨e⟩⟩
  obtain ⟨e'⟩ := nonempty_quotCenterEquiv hs.L_comp hsimp
  exact Or.inr (Or.inl
    (CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case1_M22_case_dimensionOnly
      (OneCompSetting.toG93Hyp hs) (center_eq_bot_of_simple_component hs.L_comp hsimp)
      ⟨e'.trans e⟩))

theorem oneCompForDimensionOnly_compType
    (h5 : OneCompFor (FamAlt 5)) (h6 : OneCompFor (FamAlt 6)) (h7 : OneCompFor (FamAlt 7))
    (h8 : OneCompFor (FamAlt 8)) (hOL2 : OneCompFor FamOddL2) (hOL3 : OneCompFor FamOddL3)
    (hOU3 : OneCompFor FamOddU3) (hL2 : OneCompFor FamL2) (hL3 : OneCompFor FamL3)
    (hU3 : OneCompFor FamU3) (hSp4 : OneCompFor FamSp4) (hG2 : OneCompFor FamG2)
    (h3D4 : OneCompFor Fam3D4) (h2F4 : OneCompFor Fam2F4) (hSz : OneCompFor FamSz)
    (hTits : OneCompFor FamTits) (hL4 : OneCompFor (FamLn2 4)) (hL5 : OneCompFor (FamLn2 5))
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
        OneCompForDimensionOnly (FamSpor s))
    (hCSL3 : OneCompFor FamCoverSL3) (hA6 : OneCompFor (FamHat (alternatingGroup (Fin 6))))
    (hA7 : OneCompFor (FamHat (alternatingGroup (Fin 7))))
    (hM22 : OneCompFor (FamHat (NativeSporadic.Carrier .M22))) :
    OneCompForDimensionOnly CompType := by
  intro V _ _ _ Γ A L m hs hL
  rcases hL with ⟨hsimp, hlist⟩ | ⟨hz, hlist⟩
  · rcases hlist with ⟨n, hn5, hn8, he⟩ | ⟨p, hp, hp2, (⟨f, hf, hm⟩ | hm | hm)⟩ |
      (⟨f, (⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hfo, hf, hm⟩ |
        ⟨hfo, hf, hm⟩)⟩ | hm) | ⟨n, hn, hm⟩ | ⟨s, hs', he⟩
    · interval_cases n
      · exact (h5 V Γ A L m hs ⟨hsimp, he⟩).toDimensionOnly
      · exact (h6 V Γ A L m hs ⟨hsimp, he⟩).toDimensionOnly
      · exact (h7 V Γ A L m hs ⟨hsimp, he⟩).toDimensionOnly
      · exact (h8 V Γ A L m hs ⟨hsimp, he⟩).toDimensionOnly
    · exact (hOL2 V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, hm⟩).toDimensionOnly
    · exact (hOL3 V Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩).toDimensionOnly
    · exact (hOU3 V Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩).toDimensionOnly
    · exact (hL2 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (hL3 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (hU3 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (hSp4 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (hG2 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (h3D4 V Γ A L m hs ⟨hsimp, f, hf, hm⟩).toDimensionOnly
    · exact (h2F4 V Γ A L m hs ⟨hsimp, f, hfo, hf, hm⟩).toDimensionOnly
    · exact (hSz V Γ A L m hs ⟨hsimp, f, hfo, hf, hm⟩).toDimensionOnly
    · exact (hTits V Γ A L m hs ⟨hsimp, hm⟩).toDimensionOnly
    · rcases hn with rfl | rfl
      · exact (hL4 V Γ A L m hs ⟨hsimp, hm⟩).toDimensionOnly
      · exact (hL5 V Γ A L m hs ⟨hsimp, hm⟩).toDimensionOnly
    · exact hSpor s hs' V Γ A L m hs ⟨hsimp, he⟩
  · rcases hlist with ⟨s, p, e, hp, he, hpe, hm⟩ | hm | hm | hm
    · exact (hCSL3 V Γ A L m hs ⟨hz, s, p, e, hp, he, hpe, hm⟩).toDimensionOnly
    · exact (hA6 V Γ A L m hs ⟨hz, hm⟩).toDimensionOnly
    · exact (hA7 V Γ A L m hs ⟨hz, hm⟩).toDimensionOnly
    · exact (hM22 V Γ A L m hs ⟨hz, hm⟩).toDimensionOnly

theorem g93StmtDimensionOnly_of_interfaces (hD : DescentOne) (hT : TwoComp)
    (hO : OneCompForDimensionOnly CompType) : G93StmtDimensionOnly := by
  intro V _ _ _ Γ A L H m h
  rcases h.H_eq with rfl | hL₂
  · exact hO V Γ A H m (OneCompSetting.of_g93Hyp h) (hD V Γ A H m h)
  · rcases hT V Γ A L H m h hL₂ with h14 | h15
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h14))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15)))))))))))))))

theorem g93StmtDimensionOnly_holds :
    G93StmtDimensionOnly := by
  refine g93StmtDimensionOnly_of_interfaces (descentOne_of_threeCover
      CFSG.QuasithinUnique.Vol2Native.threeCoverFactCat) TwoComp.twoComp_holds
    (oneCompForDimensionOnly_compType oneCompFor_famAlt5 Alt6.oneCompFor_famAlt6
      oneCompFor_famAlt7 (oneCompFor_famAlt8_of Ln2.oneCompFor_famLn2_four)
      (oneCompFor_famOddL2
        (oneCompFor_famOddL2Small_of L3.oneCompFor_famL3 Alt6.oneCompFor_famAlt6)
        oneCompFor_famOddL2Big)
      oneCompFor_famOddL3 (oneCompFor_famOddU3 G2.oneCompFor_famU33 oneCompFor_famOddU3Big)
      (L2.oneCompFor_famL2_of_cases L2.case6_holds L2.case7_holds L2.case16_holds) L3.oneCompFor_famL3 oneCompFor_famU3 Sp4.oneCompFor_famSp4
      G2.oneCompFor_famG2 oneCompFor_fam3D4 oneCompFor_fam2F4 oneCompFor_famSz
      oneCompFor_famTits_of_smith Ln2.oneCompFor_famLn2_four Ln2.oneCompFor_famLn2_five ?_
      (oneCompFor_famCoverSL3 L3.oneCompFor_famCoverSL3Two
        CFSG.Quasithin.Background.Harris.OrdinaryProofs.oneCompFor_famCoverSU3Two
        oneCompFor_famCoverOdd)
      oneCompFor_famHat_A6 oneCompFor_famHat_A7 oneCompFor_famHat_M22)
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_M11
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_M12
  · exact oneCompForDimensionOnly_famSpor_M22
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_M23
  · exact oneCompForDimensionOnly_famSpor_M24
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_J1
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_J2
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_J4
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_HS
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_He
  · exact OneCompFor.toDimensionOnly oneCompFor_famSpor_Ru

end CFSG.Quasithin.G11.Harris
