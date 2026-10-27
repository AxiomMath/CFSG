module

public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three
public import CFSG.RankThree.Lattice.SteinbergBIRoots
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
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

namespace CFSG.StandardType.LangSeven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

private def langSeven_e7C : List (List ℤ) :=
  [[5, 6, 4, 0, 1, 0, 0], [2, 0, 2, 2, 0, 1, 0], [1, 2, 2, 5, 0, 0, 1]]

private def langSeven_e8C : List (List ℤ) :=
  [[6, 4, 2, 1, 0, 0, 0, 0], [3, 0, 2, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0],
   [3, 0, 0, 0, 0, 0, 4, 1]]

private def langSeven_dotL (n : ℕ) (u v : List ℤ) : ℤ :=
  (List.ofFn fun k : Fin n => vget u k * vget v k).sum

private theorem langSeven_dotL_eq (n : ℕ) (u v : List ℤ) :
    langSeven_dotL n u v = toVec n u ⬝ᵥ toVec n v := by
  simp [langSeven_dotL, dotProduct, List.sum_ofFn, toVec]

private theorem langSeven_e7_eig : ∀ c ∈ langSeven_e7C, ∀ j ∈ List.range Tag.E7.rank,
    (vget (lmulVecT Tag.E7.rank e7ThreeMat c) j - 2 * vget c j) % 7 = 0 := by
  decide +kernel

private theorem langSeven_e8_eig : ∀ c ∈ langSeven_e8C, ∀ j ∈ List.range Tag.E8.rank,
    (vget (lmulVecT Tag.E8.rank e8ThreeMat c) j - 2 * vget c j) % 7 = 0 := by
  decide +kernel

private theorem langSeven_e7_fc_data :
    ∀ l ∈ Tag.E7.artifactRoots, ∃ c ∈ langSeven_e7C, langSeven_dotL Tag.E7.rank c l % 7 ≠ 0 := by
  decide +kernel

private theorem langSeven_e8_fc_data :
    ∀ l ∈ Tag.E8.artifactRoots, ∃ c ∈ langSeven_e8C, langSeven_dotL Tag.E8.rank c l % 7 ≠ 0 := by
  decide +kernel

private theorem langSeven_zpow_vec_mem_fixedCharTuples {τ : Tag} {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 7 = 1) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (x : Fin τ.rank → ℤ)
    (hx : ∀ j, (7 : ℤ) ∣ (Mᵀ *ᵥ x) j - 2 * x j) :
    (fun k => ζ ^ x k) ∈ fixedCharTuples M Fr := by
  rw [mem_fixedCharTuples_iff]
  intro u
  rw [rootChar_zpow, rootChar_zpow]
  have h1 : Units.map Fr.toMonoidHom (ζ ^ (x ⬝ᵥ u)) = ζ ^ (2 * (x ⬝ᵥ u)) := by
    rw [map_zpow]
    have : Units.map Fr.toMonoidHom ζ = ζ ^ 2 := Units.ext (by simp [hFr])
    rw [this, zpow_mul]
    rfl
  have hdiv : (7 : ℤ) ∣ x ⬝ᵥ (M *ᵥ u) - 2 * (x ⬝ᵥ u) := by
    have e : x ⬝ᵥ (M *ᵥ u) - 2 * (x ⬝ᵥ u) = (Mᵀ *ᵥ x - (2 : ℤ) • x) ⬝ᵥ u := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, sub_dotProduct, smul_dotProduct,
        smul_eq_mul]
    rw [e, dotProduct]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (by simpa using hx j) _
  obtain ⟨k, hk⟩ := hdiv
  have e : x ⬝ᵥ (M *ᵥ u) = 2 * (x ⬝ᵥ u) + 7 * k := by linarith
  have h7 : ζ ^ (7 * k) = 1 := by
    have h7' : ζ ^ (7 : ℤ) = 1 := by simpa using hζ
    rw [zpow_mul, h7', one_zpow]
  rw [h1, e, zpow_add, h7, mul_one]

theorem langSeven_fc_E7 {L : Type} [Field L] (ζ : Lˣ)
    (hζ : orderOf ζ = 7) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2)
    (γ : Fin Tag.E7.rank → ℤ) (hγ : IsRoot Tag.E7 γ) :
    ∃ a : Fin Tag.E7.rank → Lˣ, a ∈ fixedCharTuples (wordMat Tag.E7 e7ThreeWord) Fr ∧
      (∀ j, a j ^ 7 = 1) ∧ rootChar a γ ≠ 1 := by
  have hζ7 : ζ ^ 7 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hγ
  obtain ⟨c, hc, hne⟩ := langSeven_e7_fc_data l hl
  refine ⟨fun k => ζ ^ toVec Tag.E7.rank c k, ?_, ?_, ?_⟩
  · rw [e7Three_wordMat]
    refine langSeven_zpow_vec_mem_fixedCharTuples hζ7 hFr _ _ fun j => ?_
    have h := langSeven_e7_eig c hc j (List.mem_range.2 j.2)
    rw [← toVec_lmulVecT]
    exact Int.dvd_of_emod_eq_zero h
  · intro j
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ7, one_zpow]
  · rw [rootChar_zpow, Ne, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← langSeven_dotL_eq]
    intro h
    exact hne (Int.emod_eq_zero_of_dvd (by exact_mod_cast h))

theorem langSeven_fc_E8 {L : Type} [Field L] (ζ : Lˣ)
    (hζ : orderOf ζ = 7) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2)
    (γ : Fin Tag.E8.rank → ℤ) (hγ : IsRoot Tag.E8 γ) :
    ∃ a : Fin Tag.E8.rank → Lˣ, a ∈ fixedCharTuples (wordMat Tag.E8 e8ThreeWord) Fr ∧
      (∀ j, a j ^ 7 = 1) ∧ rootChar a γ ≠ 1 := by
  have hζ7 : ζ ^ 7 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hγ
  obtain ⟨c, hc, hne⟩ := langSeven_e8_fc_data l hl
  refine ⟨fun k => ζ ^ toVec Tag.E8.rank c k, ?_, ?_, ?_⟩
  · rw [e8Three_wordMat]
    refine langSeven_zpow_vec_mem_fixedCharTuples hζ7 hFr _ _ fun j => ?_
    have h := langSeven_e8_eig c hc j (List.mem_range.2 j.2)
    rw [← toVec_lmulVecT]
    exact Int.dvd_of_emod_eq_zero h
  · intro j
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ7, one_zpow]
  · rw [rootChar_zpow, Ne, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← langSeven_dotL_eq]
    intro h
    exact hne (Int.emod_eq_zero_of_dvd (by exact_mod_cast h))

end CFSG.StandardType.LangSeven
