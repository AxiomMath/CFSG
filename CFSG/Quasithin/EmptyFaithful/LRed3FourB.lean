module

public import CFSG.Quasithin.EmptyFaithful.LRed3FourA
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Timmesfeld.Final.PSU33
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate19953
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate17951
public import Certificates.Certificate17028
public import Certificates.Certificate17002
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
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
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
  CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem lred3_equiv_m22 {x y : Fin 24}
    (hxy : x ≠ y) :
    Nonempty (↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨τ, hτ, h0, h1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  have hmap := map_conj_stab01 hτ
  rw [h0, h1] at hmap
  let e : ↥mog22 ≃* ↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) :=
    ((AutPerm ⊓ stab 0 ⊓ stab 1).equivMapOfInjective _ (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact ⟨e.symm.trans mog22EquivM22⟩

variable {Y : Type} [Group Y]

theorem lred3_four_of_m22
    (hY : CFSG.IsQuasisimple Y) {x y : Fin 24} (hxy : x ≠ y)
    (π : ↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨hs, -⟩ := stab_props_m22 hxy
  obtain ⟨e⟩ := lred3_cq_simple hY hs π hπ
  obtain ⟨f⟩ := lred3_equiv_m22 hxy
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans f⟩))))))))

theorem lred3_equiv_g2derived_psu33
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (StatedProj (StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) ≃*
      ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) := by
  obtain ⟨g⟩ := CFSG.Quasithin.H13.nonempty_g2Two_commutator_equiv hK
  obtain ⟨u⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨p⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact ⟨(p.trans u.symm).trans (u33EquivSubG2.trans g.symm)⟩

theorem lred3_four_of_g2derived
    (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (π : ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hK
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  have hP : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 3 (2 * 1)) 3 1 hK9 3
      le_rfl hne
  obtain ⟨e⟩ := lred3_cq_simple hY hP (π.comp eP.toMonoidHom) (hπ.comp eP.surjective)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance, inferInstance,
      hK9, ⟨e⟩⟩)))))

end CFSG.Quasithin
