module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType

section Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus


@[expose] def ggLangReidx {R N : ℕ} (h : R = N) (v : Fin R → ℤ) : Fin N → ℤ :=
  fun j => v (Fin.cast h.symm j)

@[expose] noncomputable def ggPsiBar (t : StatedLieTag) (n f : ℕ) :
    ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) →* GGAutU t n f :=
  MulAut.conj

structure GGLangData (L : Type) [Field L] [IsAlgClosed L] (t : StatedLieTag) (n f p : ℕ)
    (Bs : Subgroup (GGAutU t n f))
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) where
  τ : Tag
  tag_five : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8
  rank_eq : (ggU (absTag t) 6 f).D.rank = τ.rank
  p₀ : ℕ
  setup : LangSetup τ L p₀
  q_eq : setup.D.q = 2 ^ f
  ι : ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) →* ModGL τ L
  ι_inj : Function.Injective ι
  ι_range : ι.range = setup.Γ
  center_bot : Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) = ⊥
  ζ : Lˣ
  ζ_order : orderOf ζ = p
  a : Bs → (Fin τ.rank → Lˣ)
  a_torus : ∀ b, rootDiagUnit τ (a b) ∈ setup.D.torus
  a_coord : ∀ (b : Bs) (j : Fin τ.rank),
    a b j = ζ ^ ZMod.val (Multiplicative.toAdd (coord b) (Fin.cast rank_eq.symm j))
  a_act : ∀ (b : Bs) (c : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K),
    ι ((b : GGAutU t n f) c) = rootDiagUnit τ (a b) * ι c * (rootDiagUnit τ (a b))⁻¹
  roots_iff : ∀ v : Fin (ggU (absTag t) 6 f).D.rank → ℤ,
    v ∈ (ggU (absTag t) 6 f).D.roots ↔ IsRoot τ (ggLangReidx rank_eq v)
  ε : ℤ
  ε_cases : ε = 1 ∨ ε = -1
  p_dvd : (p : ℤ) ∣ ((2 : ℤ) ^ f) - ε
  rho_eq : ∀ v ∈ (ggU (absTag t) 6 f).D.roots,
    setup.ρ (ggLangReidx rank_eq v) = ε • ggLangReidx rank_eq (latPerm π v)
  gram_eq : ∃ k : ℤ, 0 < k ∧ ∀ α β,
    latGram S α β = k * iform (ggLangReidx rank_eq α) (ggLangReidx rank_eq β)
  pi_diag : ∀ j k : Fin (ggU (absTag t) 6 f).D.rank,
    τ.cartan (Fin.cast rank_eq (π j)) (Fin.cast rank_eq (π k)) =
      τ.cartan (Fin.cast rank_eq j) (Fin.cast rank_eq k)

@[expose] def GGModelLangData (L : Type) [Field L] [IsAlgClosed L] (Mod : GGModelFamily) : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ) (ht : GGExcFive t) (hadm : GGKnownAdm t n f) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f),
    Nonempty (GGLangData L t n f p (Mod t n f ht hadm p hp hp2 hreg).Bfull
      (Mod t n f ht hadm p hp hp2 hreg).S (Mod t n f ht hadm p hp hp2 hreg).π
      (Mod t n f ht hadm p hp hp2 hreg).coord)

end Assembly

end CFSG.StandardType
