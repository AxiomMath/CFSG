module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
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

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

private theorem kg3_w3_sq_add_self_add_one :
    (wordMat .E6 e6ThreeWord) ^ 2 + (wordMat .E6 e6ThreeWord) + 1 = 0 := by
  rw [e6Three_wordMat]
  ext i j
  rw [pow_two, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
  exact (show ∀ i j : Fin Tag.E6.rank,
      (∑ k : Fin Tag.E6.rank, (toMat Tag.E6.rank e6ThreeMat) i k *
          (toMat Tag.E6.rank e6ThreeMat) k j)
        + (toMat Tag.E6.rank e6ThreeMat) i j + (if i = j then 1 else 0) = 0 from by
    decide +kernel) i j

private theorem kg3_rootChar_single {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) (j : Fin Tag.E6.rank) :
    rootChar a (Pi.single j 1) = a j := by
  simpa using rootChar_nsmul_single a j 1

private theorem kg3_torus_exponent_seven {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup .E6 L 7) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot .E6 γ → S.ρ γ = (wordMat .E6 e6ThreeWord) *ᵥ γ) :
    ∀ x ∈ S.D.torus, x ^ 7 = 1 := by
  have hmat := kg3_w3_sq_add_self_add_one
  intro x hx
  obtain ⟨a, ha⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hx).1
  have hxa : x = rootDiagUnit .E6 a := ha.symm
  have hxd : rootDiagUnit .E6 a ∈ S.D.torus := by rw [← hxa]; exact hx
  have ha7 : a ^ 7 = 1 := by
    funext j
    let M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := wordMat .E6 e6ThreeWord
    let e : Fin Tag.E6.rank → ℤ := Pi.single j 1
    let m₁ : Fin Tag.E6.rank → ℤ := M *ᵥ e
    let m₂ : Fin Tag.E6.rank → ℤ := M *ᵥ m₁
    have he_root : IsRoot .E6 e := isRoot_single .E6 j
    have hρe : S.ρ e = M *ᵥ e := hρ e he_root
    have hroot1 : rootChar a m₁ = rootChar a e ^ 2 := by
      have h := S.frob.rootChar_eq a hxd e he_root
      rw [hρe, hq] at h
      exact h
    have hρe_root : IsRoot .E6 (S.ρ e) := (S.frob.isRoot_iff e).2 he_root
    have h2a : S.ρ (S.ρ e) = m₂ := by
      have hρρ : S.ρ (S.ρ e) = M *ᵥ (S.ρ e) := hρ (S.ρ e) hρe_root
      rw [hρρ, hρe]
    have h2b : S.ρ e = m₁ := by rw [hρe]
    have hroot2 : rootChar a m₂ = rootChar a m₁ ^ 2 := by
      have h := S.frob.rootChar_eq a hxd (S.ρ e) hρe_root
      rw [h2a, h2b, hq] at h
      exact h
    have hvec : m₂ + m₁ + e = 0 := by
      have h := congrArg (fun N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ => N *ᵥ e) hmat
      rw [pow_two, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.one_mulVec, Matrix.zero_mulVec] at h
      exact h
    have hsum : rootChar a (m₂ + m₁ + e) = rootChar a m₂ * rootChar a m₁ * rootChar a e := by
      rw [add_assoc, rootChar_add, rootChar_add, mul_assoc]
    have hzero : rootChar a (m₂ + m₁ + e) = 1 := by rw [hvec, rootChar_zero]
    have hej : rootChar a e = a j := kg3_rootChar_single a j
    rw [hsum, hroot2, hroot1, hej] at hzero
    rw [show (a j ^ 2) ^ 2 * (a j ^ 2) * a j = a j ^ 7 by group] at hzero
    exact hzero
  calc x ^ 7 = (rootDiagUnit .E6 a) ^ 7 := by rw [hxa]
    _ = rootDiagUnit .E6 (a ^ 7) := rootDiagUnit_pow a 7
    _ = rootDiagUnit .E6 1 := by rw [ha7]
    _ = 1 := rootDiagUnit_one

private theorem kg3_commutator_self_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem k3a_sylow
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup .E6 L 7) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot .E6 γ → S.ρ γ = (wordMat .E6 e6ThreeWord) *ᵥ γ)
    (hsyl : ∃ S₀ : Sylow 7 S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ)
    (hord : 7 ^ (Nat.card S.Γ).factorization 7 = 7 ^ 3) :
    Nat.card S.E = 7 ^ 3 ∧ ∃ P : Sylow 7 S.Γ, (P : Subgroup S.Γ) = S.E.subgroupOf S.Γ := by
  have hexp : ∀ x ∈ S.D.torus, x ^ 7 = 1 := kg3_torus_exponent_seven S hq hρ
  obtain ⟨S₀, hS₀⟩ := hsyl
  have hEΓ : S.E ≤ S.Γ := fun x hx => (S.E_le hx).2
  have hS0_le_E : (S₀ : Subgroup S.Γ) ≤ S.E.subgroupOf S.Γ := by
    intro y hy
    have htor : (y : ModGL .E6 L) ∈ S.D.torus := hS₀ hy
    exact S.E_all _ ⟨htor, y.2⟩ (hexp _ htor)
  have hE7 : IsPGroup 7 S.E := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (S.E_exp g.1 g.2)
  have hE7' : IsPGroup 7 (S.E.subgroupOf S.Γ) :=
    hE7.of_equiv (Subgroup.subgroupOfEquivOfLe hEΓ).symm
  have heq : S.E.subgroupOf S.Γ = (S₀ : Subgroup S.Γ) := S₀.is_maximal' hE7' hS0_le_E
  haveI hfin : Finite S.Γ := by
    have hΓmodel : S.Γ ≤ S.D.model := kg3_commutator_self_le_self S.D.model
    have h := S.finite
    exact Finite.of_injective (Subgroup.inclusion hΓmodel) (Subgroup.inclusion_injective hΓmodel)
  have hcardE : Nat.card S.E = 7 ^ 3 := by
    have h1 : Nat.card S.E = Nat.card (S.E.subgroupOf S.Γ) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv).symm
    have h2 : Nat.card (S.E.subgroupOf S.Γ) = Nat.card S₀ := by rw [heq]
    have h3 : Nat.card S₀ = 7 ^ (Nat.card S.Γ).factorization 7 := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      exact Sylow.card_eq_multiplicity S₀
    exact h1.trans (h2.trans (h3.trans hord))
  exact ⟨hcardE, S₀, heq.symm⟩

end CFSG.StandardType.GGKG3
