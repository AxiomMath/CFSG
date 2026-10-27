module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadAct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadHj
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

theorem exists_mulEquiv_GL_of_eight {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a * a = 1) (hcard : Nat.card W = 8) :
    Nonempty (MulAut W ≃* GL (Fin 3) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun a => by rw [pow_two]; exact hsq a) (n := 3) (by rw [hcard]; norm_num)
  exact ⟨CFSG.SectionRank.Ccomm.elemAutEquivGL e⟩

theorem card_mulAut_eight {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hsq : ∀ a : W, a * a = 1) (hcard : Nat.card W = 8) : Nat.card (MulAut W) = 168 := by
  obtain ⟨e⟩ := exists_mulEquiv_GL_of_eight hcomm hsq hcard
  rw [Nat.card_congr e.toEquiv]
  exact card_GL_three_two

theorem card_mulAut_subgroup_eight {Γ : Type*} [Group Γ] [Finite Γ] (V : Subgroup Γ)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hcard : Nat.card V = 8) : Nat.card (MulAut ↥V) = 168 :=
  card_mulAut_eight (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (hsq a a.2)) hcard

theorem isSimpleGroup_mulAut_eight {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a * a = 1) (hcard : Nat.card W = 8) :
    IsSimpleGroup (MulAut W) := by
  obtain ⟨e⟩ := exists_mulEquiv_GL_of_eight hcomm hsq hcard
  have := isSimpleGroup_GL_three_two
  exact e.isSimpleGroup

theorem le_centralizer_of_solvable_normal {Γ : Type*} [Group Γ] [Finite Γ] (V N R : Subgroup Γ)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hcard : Nat.card V = 8) (hN : N ≤ Subgroup.normalizer (V : Set Γ))
    (hsurj : Function.Surjective (conjAut V N hN)) (hRG : R ≤ Subgroup.normalizer (V : Set Γ))
    (hnorm : Subgroup.normalizer (V : Set Γ) ≤ Subgroup.normalizer (R : Set Γ))
    (hs : Group.IsSolvable ↥R) : R ≤ Subgroup.centralizer (V : Set Γ) := by
  set G := Subgroup.normalizer (V : Set Γ) with hG
  let ρ : ↥G →* MulAut ↥V := V.normalizerMonoidHom
  have hρs : Function.Surjective ρ := fun α => by
    obtain ⟨n, hn⟩ := hsurj α
    exact ⟨Subgroup.inclusion hN n, hn⟩
  have hc : ∀ a b : ↥V, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hq : ∀ a : ↥V, a * a = 1 := fun a => Subtype.ext (hsq a a.2)
  have hcard' : Nat.card ↥V = 8 := hcard
  have hsimple := isSimpleGroup_mulAut_eight hc hq hcard'
  have hn : (R.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hnorm g.2) (x : Γ)).mp hx
    simpa using this
  have hsolv : Group.IsSolvable ↥(R.subgroupOf G) := by
    have := hs
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRG).symm.surjective
  have hnb : ((R.subgroupOf G).map ρ).Normal := hn.map ρ hρs
  rcases hsimple.eq_bot_or_eq_top_of_normal ((R.subgroupOf G).map ρ) with h | h
  · intro r hr
    have h1 : ρ ⟨r, hRG hr⟩ = 1 := by
      have : ρ ⟨r, hRG hr⟩ ∈ (R.subgroupOf G).map ρ :=
        Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hr)
      rw [h, Subgroup.mem_bot] at this
      exact this
    exact (normalizerMonoidHom_eq_one_iff' V ⟨r, hRG hr⟩).mp h1
  · exfalso
    have hsq' : Group.IsSolvable (MulAut ↥V) := by
      have := hsolv
      refine Group.isSolvable_of_surjective (f := ρ.comp (R.subgroupOf G).subtype) ?_
      intro q
      have hq' : q ∈ (R.subgroupOf G).map ρ := by rw [h]; exact Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq'
      exact ⟨⟨x, hx⟩, rfl⟩
    refine not_isSolvable_of_simple ?_ hsq'
    rw [card_mulAut_eight hc hq hcard']
    norm_num

end CFSG.Quasithin.J4Rad
