module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
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
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.ExcThreeAtTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

@[expose] def kacMark {r : ℕ} (θ : Fin r → ℤ) : Option (Fin r) → ℤ
  | none => 1
  | some j => θ j

@[expose] def kacBoundaryMark {τ : Tag} (θ : Fin τ.rank → ℤ)
    (C : Finset (Option (Fin τ.rank))) : ℤ :=
  ∑ z : Option (Fin τ.rank), if z ∉ C ∧ ∃ y ∈ C, y ≠ z ∧
      iform (τ := τ) (extRootOf θ y) (extRootOf θ z) ≠ 0 then kacMark θ z else 0

section Generic

variable {τ : Tag}

theorem kacBoundaryMark_le (K : KacData τ) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {x : Option (Fin τ.rank)} {C : Finset (Option (Fin τ.rank))}
    (hC : K.comp p μ x = (C : Set (Option (Fin τ.rank)))) : kacBoundaryMark K.θ C ≤ p := by
  have hnz : ∀ z, z ∉ C → (∃ y ∈ C, y ≠ z ∧
      iform (τ := τ) (extRootOf K.θ y) (extRootOf K.θ z) ≠ 0) → ¬ K.IsZ p μ z := by
    rintro z hzC ⟨y, hy, hyz, hif⟩ hz
    have hy' : y ∈ K.comp p μ x := by
      rw [hC]
      exact hy
    have hadj : K.Adj y z := ⟨hyz, by rw [extRoot_eq_extRootOf]; exact hif⟩
    have hzx : z ∈ K.comp p μ x :=
      ⟨hz, hy'.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hy'.1, hz, hadj⟩)⟩
    rw [hC] at hzx
    exact hzC (Finset.mem_coe.1 hzx)
  unfold kacBoundaryMark
  rw [Fintype.sum_option]
  have h0 : (if none ∉ C ∧ ∃ y ∈ C, y ≠ none ∧
      iform (τ := τ) (extRootOf K.θ y) (extRootOf K.θ none) ≠ 0 then kacMark K.θ none else 0) ≤
        (p : ℤ) - K.θ ⬝ᵥ μ := by
    have hle := hμ.2
    split_ifs with h
    · have hz := hnz none h.1 h.2
      change ¬ K.θ ⬝ᵥ μ = p at hz
      simp only [kacMark]
      omega
    · omega
  have hj : ∀ j : Fin τ.rank, (if some j ∉ C ∧ ∃ y ∈ C, y ≠ some j ∧
      iform (τ := τ) (extRootOf K.θ y) (extRootOf K.θ (some j)) ≠ 0 then
        kacMark K.θ (some j) else 0) ≤ K.θ j * μ j := by
    intro j
    have hθ := K.θ_nonneg j
    have hμj := hμ.1 j
    split_ifs with h
    · have hz := hnz (some j) h.1 h.2
      change ¬ μ j = 0 at hz
      simp only [kacMark]
      exact le_mul_of_one_le_right hθ (by omega)
    · exact mul_nonneg hθ hμj
  calc _ ≤ ((p : ℤ) - K.θ ⬝ᵥ μ) + ∑ j, K.θ j * μ j :=
        add_le_add h0 (Finset.sum_le_sum fun j _ => hj j)
    _ = p := by
        rw [show ∑ j, K.θ j * μ j = K.θ ⬝ᵥ μ from rfl]
        ring

theorem not_shape_of_kacBoundaryMark {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {a : Fin τ.rank → Lˣ} (hTp : rootDiagUnit τ a ^ p = 1) {r n : ℕ}
    (hshape : ∀ C : Finset (Option (Fin τ.rank)), C.card = r → kacCount τ K.θ C = n →
      (p : ℤ) < kacBoundaryMark K.θ C)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = r ∧
       (componentRoots (rootCharHom a) i).ncard = n) := by
  rintro ⟨hrank, hncard⟩
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime hp hpL hK hTp
  obtain ⟨x, -, hi⟩ := hall i
  let C : Finset (Option (Fin τ.rank)) := (Set.toFinite (K.comp p μ x)).toFinset
  have hCcoe : K.comp p μ x = (C : Set (Option (Fin τ.rank))) :=
    (Set.toFinite _).coe_toFinset.symm
  have hCp : ∃ z, z ∉ C := by
    obtain ⟨z, hz⟩ := exists_not_mem_comp K hp.pos μ x
    exact ⟨z, fun h => hz ((Set.toFinite _).mem_toFinset.1 h)⟩
  rw [hCcoe] at hi
  have hrankC : compRank (componentRoots (rootCharHom a) i) = C.card := by
    rw [hi, compRank_image, compRank_rootsOf K hK hCp]
  have hncardC : (componentRoots (rootCharHom a) i).ncard = kacCount τ K.θ C := by
    rw [hi, ncard_image_smul, ncard_rootsOf K hK hCp]
  exact absurd (kacBoundaryMark_le K hμ hCcoe)
    (not_le.2 (hshape C (hrankC ▸ hrank) (hncardC ▸ hncard)))

end Generic

section Counting

set_option maxRecDepth 100000

theorem kacBoundaryMark_E8_three : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 3 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C = 12 →
      3 < kacBoundaryMark (τ := .E8) ![2, 3, 4, 6, 5, 4, 3, 2] C := by
  decide +kernel

theorem kacBoundaryMark_E7_three : ∀ C : Finset (Option (Fin Tag.E7.rank)), C.card = 3 →
    kacCount .E7 ![2, 2, 3, 4, 3, 2, 1] C = 12 →
      3 < kacBoundaryMark (τ := .E7) ![2, 2, 3, 4, 3, 2, 1] C := by
  decide +kernel

theorem kacBoundaryMark_E6_three : ∀ C : Finset (Option (Fin Tag.E6.rank)), C.card = 3 →
    kacCount .E6 ![1, 2, 2, 3, 2, 1] C = 12 →
      3 < kacBoundaryMark (τ := .E6) ![1, 2, 2, 3, 2, 1] C := by
  decide +kernel

theorem kacBoundaryMark_F4_three : ∀ C : Finset (Option (Fin Tag.F4.rank)), C.card = 3 →
    kacCount .F4 ![2, 3, 4, 2] C = 12 →
      3 < kacBoundaryMark (τ := .F4) ![2, 3, 4, 2] C := by
  decide +kernel

theorem kacBoundaryMark_E8_four :
    3 < kacBoundaryMark (τ := .E8) ![2, 3, 4, 6, 5, 4, 3, 2]
      ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E8.rank))) := by
  decide +kernel

theorem kacBoundaryMark_E7_four :
    3 < kacBoundaryMark (τ := .E7) ![2, 2, 3, 4, 3, 2, 1]
      ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E7.rank))) := by
  decide +kernel

end Counting

section Statements

variable {L : Type} [Field L]
  [IsAlgClosed L] {p₀ : ℕ}

theorem not_a3Shape_of_three_E8 (S : LangSetup Tag.E8 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 3 ∧
       (componentRoots (rootCharHom a) i).ncard = 12) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_E8 hTp
    (fun C h1 h2 => kacBoundaryMark_E8_three C h1 h2) i

theorem not_a3Shape_of_three_E7 (S : LangSetup Tag.E7 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTp : rootDiagUnit Tag.E7 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 3 ∧
       (componentRoots (rootCharHom a) i).ncard = 12) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_E7 hTp
    (fun C h1 h2 => kacBoundaryMark_E7_three C h1 h2) i

theorem not_a3Shape_of_three_E6 (S : LangSetup Tag.E6 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTp : rootDiagUnit Tag.E6 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 3 ∧
       (componentRoots (rootCharHom a) i).ncard = 12) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_E6 hTp
    (fun C h1 h2 => kacBoundaryMark_E6_three C h1 h2) i

theorem not_a3Shape_of_three_F4 (S : LangSetup Tag.F4 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 3 ∧
       (componentRoots (rootCharHom a) i).ncard = 12) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_F4 hTp
    (fun C h1 h2 => kacBoundaryMark_F4_three C h1 h2) i

theorem not_d4Shape_of_three_E8 (S : LangSetup Tag.E8 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_E8 hTp
    (fun C h1 h2 => by
      rw [kacCount_E8_four C h1 h2]
      exact kacBoundaryMark_E8_four) i

theorem not_d4Shape_of_three_E7 (S : LangSetup Tag.E7 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTp : rootDiagUnit Tag.E7 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_E7 hTp
    (fun C h1 h2 => by
      rw [kacCount_E7_four C h1 h2]
      exact kacBoundaryMark_E7_four) i

theorem not_d4Shape_of_three_F4 (S : LangSetup Tag.F4 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) :=
  not_shape_of_kacBoundaryMark S Nat.prime_three h3 facts_F4 hTp
    (fun C h1 h2 => absurd h2 (kacCount_F4_four C h1)) i

end Statements

end CFSG.StandardType.ExcThreeAtTwo
