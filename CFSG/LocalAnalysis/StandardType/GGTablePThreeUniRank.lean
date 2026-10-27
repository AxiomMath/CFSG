module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
import CFSG.RankThree.PartTwo.Sec8.Hering418L2
import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.GH74.Statements
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
import CFSG.LocalAnalysis.ComponentInitial.LiftOddQuotient
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.StatementsL3
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Item413AutL2
import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
import CFSG.RankThree.PartTwo.Sec4.Item47
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import Certificates.Certificate2022
import Certificates.Certificate2022Base
import Certificates.Certificate2121
import Certificates.Certificate2122
import Certificates.Certificate2123
import Certificates.Certificate2202
import Certificates.Certificate2214
import Certificates.Certificate2215
import Certificates.Certificate2217
import Certificates.Certificate2283
import Certificates.Certificate2288
import Certificates.Certificate3084
import Certificates.Certificate3171
import Certificates.Certificate3171Base
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG

private lemma uniRank_scalar_pow_eq_one_of_isHermIsometry {K : Type} [Field K] {k : ℕ} (i : Fin k)
    {q : ℕ} {c : Kˣ}
    (h : IsHermIsometry q ((Matrix.GeneralLinearGroup.scalar (Fin k) c : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K)) : (c : K) ^ (q + 1) = 1 := by
  let v : Fin k → K := Pi.single i 1
  have hv := h v v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_const_mulVec] at hv
  simp only [Pi.smul_apply, smul_eq_mul] at hv
  have hL : (∑ j : Fin k, ((c : K) * v j) ^ q * ((c : K) * v j)) = (c : K) ^ (q + 1) := by
    rw [Finset.sum_eq_single i]
    · dsimp only [v]
      rw [Pi.single_eq_same, mul_one, pow_succ]
    · intro j _ hj
      dsimp only [v]
      rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hR : (∑ j : Fin k, v j ^ q * v j) = 1 := by
    rw [Finset.sum_eq_single i]
    · dsimp only [v]
      rw [Pi.single_eq_same, one_pow, mul_one]
    · intro j _ hj
      dsimp only [v]
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hL, hR] at hv
  exact hv

private lemma uniRank_natCard_le_of_forall_scalar_norm {K : Type} [Field K] {k : ℕ} (i : Fin k) {q : ℕ}
    {H : Subgroup (GL (Fin k) K)}
    (hiso : ∀ g ∈ H, IsHermIsometry q (g : Matrix (Fin k) (Fin k) K)) {Z : Subgroup H}
    (hZ : ∀ z : Z, ∃ c : Kˣ, (z : GL (Fin k) K) = Matrix.GeneralLinearGroup.scalar (Fin k) c) :
    Nat.card Z ≤ q + 1 := by
  classical
  let φ : Z → rootsOfUnity (q + 1) K := fun z =>
    ⟨Classical.choose (hZ z), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have h := hiso ((z : H) : GL (Fin k) K) (z : H).2
      rw [Classical.choose_spec (hZ z)] at h
      exact uniRank_scalar_pow_eq_one_of_isHermIsometry i h⟩
  have hinj : Function.Injective φ := by
    intro z w hzw
    have h1 : (Classical.choose (hZ z) : Kˣ) = Classical.choose (hZ w) :=
      congrArg (fun u : rootsOfUnity (q + 1) K => (u : Kˣ)) hzw
    apply Subtype.ext
    apply Subtype.ext
    rw [Classical.choose_spec (hZ z), Classical.choose_spec (hZ w), h1]
  haveI : NeZero (q + 1) := ⟨by omega⟩
  calc Nat.card Z ≤ Nat.card (rootsOfUnity (q + 1) K) := Nat.card_le_card_of_injective φ hinj
    _ ≤ q + 1 := card_rootsOfUnity K (q + 1)

theorem uni_gu_three_rank {K : Type} [Field K] [Finite K] [CharP K 2] {q k : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hk : k = 2 ∨ k = 3) (H : Subgroup (GL (Fin k) K))
    (hiso : ∀ g ∈ H, IsHermIsometry q (g : Matrix (Fin k) (Fin k) K))
    (hcomm : ∀ g ∈ H, ∀ h ∈ H,
      ∃ c : Kˣ, g * h * g⁻¹ * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin k) c)
    (hcube : ∀ g ∈ H, ∃ c : Kˣ, g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin k) c) :
    Nat.card H ≤ 3 ^ (k - 1) * (q + 1) := by
  have hq2 : 2 ≤ q := by
    have h3le : 3 ≤ q + 1 := Nat.le_of_dvd (by norm_num) hq3
    omega
  rcases hk with rfl | rfl
  ·
    have h3ne : ringChar K ≠ 3 := by
      have hrc : ringChar K = 2 := ringChar.eq K 2
      rw [hrc]
      norm_num
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      nlinarith [hq2]
    let qmap : GL (Fin 2) K →* Matrix.ProjGenLinGroup (Fin 2) K := Matrix.ProjGenLinGroup.mk
    let E : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K) := H.map qmap
    let Z : Subgroup H := qmap.ker.subgroupOf H
    have hker : qmap.ker = Subgroup.center (GL (Fin 2) K) := Matrix.ProjGenLinGroup.ker_mk
    have hscalar : ∀ c : Kˣ, qmap (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 :=
      fun c => Matrix.ProjGenLinGroup.mk_scalar c
    have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨c, hc⟩ := hcomm g hg h hh
      have hgh : g * h = Matrix.GeneralLinearGroup.scalar (Fin 2) c * (h * g) := by
        rw [← hc]
        group
      calc qmap g * qmap h = qmap (g * h) := (map_mul qmap g h).symm
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 2) c * (h * g)) := by rw [hgh]
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * qmap (h * g) := map_mul qmap _ _
        _ = 1 * qmap (h * g) := by rw [hscalar c]
        _ = qmap h * qmap g := by rw [one_mul, map_mul]
    have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨c, hc⟩ := hcube g hg
      calc qmap g ^ 3 = qmap (g ^ 3) := by rw [map_pow]
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by rw [hc]
        _ = 1 := hscalar c
    have hEcard : Nat.card E ≤ 3 :=
      CFSG.RankThree.PartTwo.Sec4.Hering418L2.card_le_three_of_pgl2 h3ne h4 E hEcomm hEexp
    have hZscalar : ∀ z : Z, ∃ c : Kˣ,
        (z : GL (Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      intro z
      have hz : ((z : H) : GL (Fin 2) K) ∈ qmap.ker := Subgroup.mem_subgroupOf.mp z.2
      rw [hker, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz
      exact ⟨c, hc.symm⟩
    have hZcard : Nat.card Z ≤ q + 1 :=
      uniRank_natCard_le_of_forall_scalar_norm (0 : Fin 2) hiso hZscalar
    have hHcard : Nat.card H = Nat.card Z * Nat.card E := by
      have hf := Subgroup.card_ker_mul_card_range (qmap.comp H.subtype)
      have hker_eq : (qmap.comp H.subtype).ker = Z := by
        ext x
        simp [Z, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hrange_eq : (qmap.comp H.subtype).range = E := by
        ext x
        simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, E]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨y, y.2, hy⟩
        · rintro ⟨g, hg, hgx⟩
          exact ⟨⟨g, hg⟩, hgx⟩
      rw [hker_eq, hrange_eq] at hf
      exact hf.symm
    calc Nat.card H = Nat.card Z * Nat.card E := hHcard
      _ ≤ (q + 1) * 3 := Nat.mul_le_mul hZcard hEcard
      _ = 3 ^ (2 - 1) * (q + 1) := by ring
  ·
    have h3 : (3 : K) ≠ 0 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3eq : (3 : K) = (2 : K) + 1 := by norm_num
      rw [h3eq, h2, zero_add]
      exact one_ne_zero
    let S := CFSG.Open.StatedScalars (Fin 3) K
    let qmap : GL (Fin 3) K →* GL (Fin 3) K ⧸ S := QuotientGroup.mk' S
    let E : Subgroup (GL (Fin 3) K ⧸ S) := H.map qmap
    let Z : Subgroup H := qmap.ker.subgroupOf H
    have hscalar : ∀ c : Kˣ, qmap (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
      intro c
      apply MonoidHom.mem_ker.mp
      rw [QuotientGroup.ker_mk']
      change Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K).range
      exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
    have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨c, hc⟩ := hcomm g hg h hh
      have hgh : g * h = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (h * g) := by
        rw [← hc]
        group
      calc qmap g * qmap h = qmap (g * h) := (map_mul qmap g h).symm
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 3) c * (h * g)) := by rw [hgh]
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 3) c) * qmap (h * g) := map_mul qmap _ _
        _ = 1 * qmap (h * g) := by rw [hscalar c]
        _ = qmap h * qmap g := by rw [one_mul, map_mul]
    have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨c, hc⟩ := hcube g hg
      calc qmap g ^ 3 = qmap (g ^ 3) := by rw [map_pow]
        _ = qmap (Matrix.GeneralLinearGroup.scalar (Fin 3) c) := by rw [hc]
        _ = 1 := hscalar c
    have hEcard : Nat.card E ≤ 9 :=
      CFSG.RankThree.PartTwo.Sec4.card_le_nine_of_pgl3 (K := K) h3 E hEcomm hEexp
    have hZscalar : ∀ z : Z, ∃ c : Kˣ,
        (z : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      intro z
      have hz : ((z : H) : GL (Fin 3) K) ∈ qmap.ker := Subgroup.mem_subgroupOf.mp z.2
      rw [QuotientGroup.ker_mk'] at hz
      change ((z : H) : GL (Fin 3) K) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K).range at hz
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz
      exact ⟨c, hc.symm⟩
    have hZcard : Nat.card Z ≤ q + 1 :=
      uniRank_natCard_le_of_forall_scalar_norm (0 : Fin 3) hiso hZscalar
    have hHcard : Nat.card H = Nat.card Z * Nat.card E := by
      have hf := Subgroup.card_ker_mul_card_range (qmap.comp H.subtype)
      have hker_eq : (qmap.comp H.subtype).ker = Z := by
        ext x
        simp [Z, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hrange_eq : (qmap.comp H.subtype).range = E := by
        ext x
        simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, E]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨y, y.2, hy⟩
        · rintro ⟨g, hg, hgx⟩
          exact ⟨⟨g, hg⟩, hgx⟩
      rw [hker_eq, hrange_eq] at hf
      exact hf.symm
    calc Nat.card H = Nat.card Z * Nat.card E := hHcard
      _ ≤ (q + 1) * 9 := Nat.mul_le_mul hZcard hEcard
      _ = 3 ^ (3 - 1) * (q + 1) := by ring

end CFSG.StandardType.TablePThreeKG

end
