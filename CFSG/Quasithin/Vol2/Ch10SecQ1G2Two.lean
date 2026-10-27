module

public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Recognition.CertU33Perm
public import Certificates.Certificate113
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17028
public import Certificates.Certificate17951
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate19953
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open CFSG.Open

theorem card_g2Two_commutator
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 6048 := by
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_g2Two_commutator_equiv hK
  rw [Nat.card_congr (e.trans CFSG.Quasithin.u33EquivSubG2.symm).toEquiv]
  exact CFSG.Quasithin.card_u33Pres

end C10P01

open C10P01 CFSG.Open

theorem factB4aG2Derived_holds :
    FactB4aG2Derived := by
  intro K _ _ hK X _ hX π
  exact not_surjective_of_isSimpleGroup (CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK)
    (by rw [card_g2Two_commutator hK]; exact not_shapeCard_6048) hX π

theorem factG2TwoNormal_holds :
    FactG2TwoNormal := by
  intro K _ _ hK H _ π hπ N _ hNq
  have hc : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 6048 := card_g2Two_commutator hK
  have hs : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
    CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK
  have hD : (commutator ↥(quasithinG2 K)).map (quasithinG2 K).subtype =
      ⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eD : ↥(commutator ↥(quasithinG2 K)) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
    ((commutator ↥(quasithinG2 K)).equivMapOfInjective (quasithinG2 K).subtype
      (quasithinG2 K).subtype_injective).trans (MulEquiv.subgroupCongr hD)
  have hDs : IsSimpleGroup ↥(commutator ↥(quasithinG2 K)) := eD.isSimpleGroup
  have hDc : Nat.card ↥(commutator ↥(quasithinG2 K)) = 6048 :=
    (Nat.card_congr eD.toEquiv).trans hc
  let ρ : ↥(commutator ↥(quasithinG2 K)) →* H := π.comp (commutator ↥(quasithinG2 K)).subtype
  have hρ : ρ.range = commutator H := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, commutator_def, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ]
  have : Group.IsPerfect ↥N := hNq.1
  have hN0 := ne_bot_of_isQuasisimple hNq
  rcases hDs.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
  · have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hk
    let eρ : ↥(commutator ↥(quasithinG2 K)) ≃* ↥(commutator H) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hρ)
    have hHs : IsSimpleGroup ↥(commutator H) := eρ.symm.isSimpleGroup
    rw [eq_commutator_of_isPerfect N hN0 hHs, ← Nat.card_congr eρ.toEquiv, hDc]
  · exfalso
    have hd : ∀ d, ρ d = 1 := fun d => MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top d)
    have hbot : commutator H = ⊥ := by
      rw [← hρ, eq_bot_iff]
      rintro _ ⟨d, rfl⟩
      exact Subgroup.mem_bot.mpr (hd d)
    apply hN0
    rw [eq_bot_iff, ← hbot]
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (commutator_def H).symm

end CFSG.Quasithin.Vol2.Ch10.SecA
