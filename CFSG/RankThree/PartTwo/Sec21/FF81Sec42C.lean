module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec42Q
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79KStmt
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42S6
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec44
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Prop33
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS1
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
public import CFSG.GroupTheory.CardSupInf
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R34
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open P51T
open Q42
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

structure Data42 (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G) (J : Subgroup G) (t τ₁ τ₃ : G) :
    Prop where
  h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀
  hJ : J ≤ L ⊓ Cen b₂
  φ : Nonempty (↥J ≃* Equiv.Perm (Fin 6))
  hb₁J : b₁ ∈ J
  hb₃J : b₃ ∈ J
  hJdec : ∀ y ∈ L ⊓ Cen b₂, ∃ k : ℕ, ∃ j ∈ J, y = b₂ ^ k * j
  hL1 : L ⊓ Cen (b₁ * b₂) ≤ Nor (Subgroup.closure {b₁, b₂})
  hL3 : L ⊓ Cen (b₃ * b₂) ≤ Nor (Subgroup.closure {b₃, b₂})
  ht2 : orderOf t = 2
  htb : t * b * t⁻¹ = b₂
  htb₂ : t * b₂ * t⁻¹ = b
  htJ : ∀ j ∈ J, t * j = j * t
  hτ₁b : τ₁ * b * τ₁⁻¹ = b₁
  hτ₁c : τ₁ * b₁ * τ₁⁻¹ = b
  hτ₁2 : τ₁ * b₂ * τ₁⁻¹ = b₂
  hτ₃b : τ₃ * b * τ₃⁻¹ = b₃
  hτ₃c : τ₃ * b₃ * τ₃⁻¹ = b
  hτ₃2 : τ₃ * b₂ * τ₃⁻¹ = b₂

theorem vec_e0_ne : ∀ c : ZMod 3, e 0 ≠ c • (e 0 + e 2) := by decide

section Data

variable {J : Subgroup G} {t τ₁ τ₃ : G} (D : Data42 b L B b₁ b₂ b₃ t₀ J t τ₁ τ₃)
include D

theorem Data42.comm : b * b₂ = b₂ * b := D.h4.b2_comm

theorem Data42.b3 : b ^ 3 = 1 := D.h4.b3

theorem Data42.x3 : (b * b₂) ^ 3 = 1 := by
  rw [(Commute.mul_pow (show Commute b b₂ from D.comm) 3), D.b3, D.h4.basis.b_facts.2.1, one_mul]

theorem Data42.cL {l : G} (hl : l ∈ L) (hl₂ : l ∈ Cen b₂) : l ∈ Cen (b * b₂) :=
  mem_cen_mul (D.h4.basis.hyp.hLC hl) hl₂

theorem Data42.cb : b ∈ Cen (b * b₂) :=
  mem_cen_mul (Subgroup.mem_centralizer_singleton_iff.mpr rfl) (mem_cen_of_commute D.comm)

theorem Data42.cb₂ : b₂ ∈ Cen (b * b₂) :=
  mem_cen_mul (mem_cen_of_commute D.comm.symm) (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

theorem Data42.cJ {j : G} (hj : j ∈ J) : j ∈ Cen (b * b₂) := D.cL (D.hJ hj).1 (D.hJ hj).2

theorem Data42.cb₁ : b₁ ∈ Cen (b * b₂) := D.cJ D.hb₁J

theorem Data42.cb₃ : b₃ ∈ Cen (b * b₂) := D.cJ D.hb₃J

theorem Data42.ct : t ∈ Cen (b * b₂) := mem_cen_of_conj (by
  calc t * (b * b₂) * t⁻¹ = (t * b * t⁻¹) * (t * b₂ * t⁻¹) := by group
    _ = b * b₂ := by rw [D.htb, D.htb₂, D.comm])

theorem Data42.cB : B ≤ Cen (b * b₂) := by
  obtain ⟨hbB, -, hb2B, -⟩ := D.h4.basis.mem
  have hc := comm_of_isElemAb D.h4.basis.mono.1
  intro y hy
  exact mem_cen_mul (mem_cen_of_commute (hc y hy b hbB)) (mem_cen_of_commute (hc y hy b₂ hb2B))

theorem Data42.cbz (i : ℤ) : b ^ i ∈ Cen (b * b₂) := (Cen _).zpow_mem D.cb i

theorem Data42.qb₂ : qq (b * b₂) b₂ = (qq (b * b₂) b)⁻¹ := by
  rw [← qq_inv D.cb]
  have h : b₂ = b⁻¹ * (b * b₂) ^ (1 : ℤ) := by rw [zpow_one]; group
  rw [show qq (b * b₂) b₂ = qq (b * b₂) (b⁻¹ * (b * b₂) ^ (1 : ℤ)) from congrArg _ h]
  rw [qq_mul ((Cen _).inv_mem D.cb) ((Cen _).zpow_mem
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl : b * b₂ ∈ Cen (b * b₂)) 1), qq_xpow, mul_one]

theorem Data42.closure_le : Subgroup.closure ({b, b₂} : Set G) ≤ Subgroup.closure {b, b * b₂} := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (hy | hy) <;> rw [hy]
  · exact Subgroup.subset_closure (by simp)
  · rw [show b₂ = b⁻¹ * (b * b₂) by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))

theorem Data42.mem_E₀ (k j : ℤ) : b ^ k * (b * b₂) ^ j ∈ Subgroup.closure ({b, b₂} : Set G) :=
  Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) _)

theorem Data42.lift {u : G} (hu : u ∈ Cen (b * b₂))
    (h : qq (b * b₂) u ∈ Nor (Subgroup.zpowers (qq (b * b₂) b))) :
    u * b * u⁻¹ ∈ Subgroup.closure ({b, b₂} : Set G) := by
  obtain ⟨k, j, hkj⟩ := lift_nor' hu D.cb h
  rw [hkj]; exact D.mem_E₀ k j

theorem Data42.fs {u : G} (hu : u ∈ Cen (b * b₂))
    (h : qq (b * b₂) u ∈ Nor (Subgroup.zpowers (qq (b * b₂) b))) :
    (u * b * u⁻¹ = b ∧ u * b₂ * u⁻¹ = b₂) ∨ (u * b * u⁻¹ = b₂ ∧ u * b₂ * u⁻¹ = b) :=
  D.h4.fix_or_swap hu (D.lift hu h)

theorem Data42.nor_of {u : G} (hu : u ∈ Cen (b * b₂))
    (h : u * b * u⁻¹ ∈ Subgroup.closure ({b, b₂} : Set G)) :
    qq (b * b₂) u ∈ Nor (Subgroup.zpowers (qq (b * b₂) b)) :=
  nor_of' hu D.cb (D.closure_le h)

theorem Data42.inj_J : ∀ k ∈ J, (∃ i : ℤ, k = (b * b₂) ^ i) → k = 1 := by
  rintro k hk ⟨i, rfl⟩
  obtain ⟨φ⟩ := D.φ
  refine eq_one_of_central φ hk fun j hj => ?_
  exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (D.cJ hj)).symm i)).eq

theorem Data42.hyp_ord_b : orderOf (qq (b * b₂) b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← qq_pow D.cb, D.b3, qq_one]
  · intro h
    obtain ⟨k, hk⟩ := (qq_eq_one_iff D.cb).mp h
    haveI := D.h4.basis.mono.1.1
    obtain ⟨β, hβ⟩ := D.h4.exists_coord
    obtain ⟨hbB, -, hb2B, -⟩ := D.h4.basis.mem
    have hc := congrArg (cvG β) hk
    rw [cvG_zpow β (B.mul_mem hbB hb2B) k, cvG_mul β hbB hb2B, hβ.1, hβ.2.2.1,
      ← Int.cast_smul_eq_zsmul (ZMod 3)] at hc
    exact vec_e0_ne _ hc

theorem Data42.hyp_ord_t : orderOf (qq (b * b₂) t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← qq_pow D.ct, ← D.ht2, pow_orderOf_eq_one, qq_one]
  · intro h
    obtain ⟨k, hk⟩ := (qq_eq_one_iff D.ct).mp h
    have hc : t * b * t⁻¹ = b := by
      rw [hk]
      exact conj_of_mem_cen ((Cen b).zpow_mem (mem_cen_of_commute (by
        rw [mul_assoc, ← D.comm])) k)
    exact D.h4.b_ne_b₂ (by rw [← D.htb, hc])

theorem Data42.hyp_tb :
    qq (b * b₂) t * qq (b * b₂) b * (qq (b * b₂) t)⁻¹ = (qq (b * b₂) b)⁻¹ := by
  rw [← qq_conj D.ct D.cb, D.htb, D.qb₂]

theorem Data42.hyp_J : Nonempty (↥(img (b * b₂) J) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨φ⟩ := D.φ
  obtain ⟨ψ⟩ := img_equiv (fun _ hj => D.cJ hj) D.inj_J
  exact ⟨ψ.trans φ⟩

theorem Data42.hyp_Jb : img (b * b₂) J ≤ Cen (qq (b * b₂) b) := by
  intro y hy
  obtain ⟨j, hj, hjc, rfl⟩ := mem_img.mp hy
  exact qq_mem_cen hjc D.cb (D.h4.basis.b_comm (D.hJ hj).1).symm

theorem Data42.hyp_Jt : img (b * b₂) J ≤ Cen (qq (b * b₂) t) := by
  intro y hy
  obtain ⟨j, hj, hjc, rfl⟩ := mem_img.mp hy
  exact qq_mem_cen hjc D.ct (D.htJ j hj).symm

theorem Data42.hyp_norJ :
    Nor (Subgroup.zpowers (qq (b * b₂) b)) ≤ Nor (img (b * b₂) J) := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := qq_surj _ y
  obtain ⟨φ⟩ := D.φ
  have hfs := D.fs hu hy
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨j, hj, hjc, rfl⟩ := mem_img.mp hz
  rw [SetLike.mem_coe, ← qq_conj hu hjc]
  exact qq_mem_img (D.h4.basis.conj_mem_J D.hJ D.hJdec φ hfs hj)
    ((Cen _).mul_mem ((Cen _).mul_mem hu hjc) ((Cen _).inv_mem hu))

theorem Data42.opp_le_M : Opp 3 (Cen b) ≤ Opp 3 (Cen b ⊓ Cen b₂) := by
  refine le_opp_of_normalizes (fun o ho => ⟨opp_le _ ho, D.h4.basis.opp_mem_cen ho D.h4.basis.hb₂⟩)
    ?_ (coprime_card_opp _)
  intro s hs o ho
  exact conj_mem_opp_of_mem_nor (Subgroup.le_normalizer hs.1) ho

theorem Data42.nor_pair {u : G}
    (h : (u * b * u⁻¹ = b ∧ u * b₂ * u⁻¹ = b₂) ∨ (u * b * u⁻¹ = b₂ ∧ u * b₂ * u⁻¹ = b)) :
    u ∈ Nor (Cen b ⊓ Cen b₂) :=
  Subgroup.mem_normalizer_fintype fun y hy => preserve_cen_pair h y hy

theorem Data42.cM {m : G} (hm : m ∈ Opp 3 (Cen b ⊓ Cen b₂)) : m ∈ Cen (b * b₂) :=
  mem_cen_mul (opp_le _ hm).1 (opp_le _ hm).2

theorem Data42.img_M : img (b * b₂) (Opp 3 (Cen b ⊓ Cen b₂)) ≤
    Opp 3 (Nor (Subgroup.zpowers (qq (b * b₂) b))) := by
  refine le_opp_of_normalizes ?_ ?_ (coprime_card_img (coprime_card_opp _))
  · intro y hy
    obtain ⟨m, hm, hmc, rfl⟩ := mem_img.mp hy
    exact mem_nor_of_mem_cen (qq_mem_cen hmc D.cb
      (Subgroup.mem_centralizer_singleton_iff.mp (opp_le _ hm).1))
  · intro s hs y hy
    obtain ⟨u, hu, rfl⟩ := qq_surj _ s
    obtain ⟨m, hm, hmc, rfl⟩ := mem_img.mp hy
    rw [← qq_conj hu hmc]
    exact qq_mem_img (conj_mem_opp_of_mem_nor (D.nor_pair (D.fs hu hs)) hm)
      ((Cen _).mul_mem ((Cen _).mul_mem hu hmc) ((Cen _).inv_mem hu))

theorem Data42.dec_fix {c : G} (hcb : c ∈ Cen b) (hcb₂ : c ∈ Cen b₂) :
    ∃ m ∈ Opp 3 (Cen b ⊓ Cen b₂), ∃ i : ℤ, ∃ k : ℕ, ∃ j ∈ J, c = m * b ^ i * b₂ ^ k * j := by
  obtain ⟨o, ho, i, l, hl, hc⟩ := D.h4.basis.cen_dec hcb
  have ho₂ : o ∈ Cen b₂ := D.h4.basis.opp_mem_cen ho D.h4.basis.hb₂
  have hbi : b ^ i ∈ Cen b₂ := (Cen b₂).zpow_mem (mem_cen_of_commute D.comm) i
  have hl₂ : l ∈ Cen b₂ := by
    have : l = (o * b ^ i)⁻¹ * c := by rw [hc]; group
    rw [this]; exact (Cen _).mul_mem ((Cen _).inv_mem ((Cen _).mul_mem ho₂ hbi)) hcb₂
  obtain ⟨k, j, hj, rfl⟩ := D.hJdec l ⟨hl, hl₂⟩
  exact ⟨o, D.opp_le_M ho, i, k, j, hj, by rw [hc]; group⟩

theorem Data42.hyp_N :
    setMul (Opp 3 (Nor (Subgroup.zpowers (qq (b * b₂) b))))
      (Subgroup.closure {qq (b * b₂) b, qq (b * b₂) t} ⊔ img (b * b₂) J) =
      Nor (Subgroup.zpowers (qq (b * b₂) b)) := by
  ext y
  constructor
  · rintro ⟨o, ho, k, hk, rfl⟩
    refine Subgroup.mul_mem _ (opp_le _ ho) ?_
    refine (sup_le ((Subgroup.closure_le _).mpr ?_) ?_) hk
    · rintro z (hz | hz) <;> rw [hz]
      · exact mem_nor_of_mem_cen (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      · exact mem_nor_zpowers (by rw [D.hyp_tb]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
    · exact fun z hz => mem_nor_of_mem_cen (D.hyp_Jb hz)
  · intro hy
    obtain ⟨u, hu, rfl⟩ := qq_surj _ y
    obtain ⟨s, c, hsc, hs, hsN, hsQ, hcb, hcb₂⟩ : ∃ s c : G, u = s * c ∧ s ∈ Cen (b * b₂) ∧
        s ∈ Nor (Cen b ⊓ Cen b₂) ∧
        qq (b * b₂) s ∈ Subgroup.closure {qq (b * b₂) b, qq (b * b₂) t} ∧
        c ∈ Cen b ∧ c ∈ Cen b₂ := by
      rcases D.fs hu hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨1, u, by group, (Cen _).one_mem, Subgroup.one_mem _,
          by rw [qq_one]; exact Subgroup.one_mem _, mem_cen_of_conj h1, mem_cen_of_conj h2⟩
      · refine ⟨t, t⁻¹ * u, by group, D.ct, D.nor_pair (Or.inr ⟨D.htb, D.htb₂⟩),
          Subgroup.subset_closure (by simp), mem_cen_of_conj ?_, mem_cen_of_conj ?_⟩
        · calc t⁻¹ * u * b * (t⁻¹ * u)⁻¹ = t⁻¹ * (u * b * u⁻¹) * t := by group
            _ = b := by rw [h1, ← D.htb]; group
        · calc t⁻¹ * u * b₂ * (t⁻¹ * u)⁻¹ = t⁻¹ * (u * b₂ * u⁻¹) * t := by group
            _ = b₂ := by rw [h2, ← D.htb₂]; group
    obtain ⟨m, hm, i, k, j, hj, rfl⟩ := D.dec_fix hcb hcb₂
    subst hsc
    have hmc := D.cM hm
    have hm' : s * m * s⁻¹ ∈ Opp 3 (Cen b ⊓ Cen b₂) := conj_mem_opp_of_mem_nor hsN hm
    have hsmc := D.cM hm'
    have hbk : b ^ i * b₂ ^ k ∈ Cen (b * b₂) := (Cen _).mul_mem (D.cbz i) ((Cen _).pow_mem D.cb₂ k)
    have hr : b ^ i * b₂ ^ k * j ∈ Cen (b * b₂) := (Cen _).mul_mem hbk (D.cJ hj)
    refine ⟨qq _ (s * m * s⁻¹), D.img_M (qq_mem_img hm' hsmc), qq _ (s * (b ^ i * b₂ ^ k * j)),
      ?_, ?_⟩
    · rw [qq_mul hs hr, qq_mul hbk (D.cJ hj), qq_mul (D.cbz i) ((Cen _).pow_mem D.cb₂ k),
        qq_zpow D.cb, qq_pow D.cb₂, D.qb₂]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hsQ) (Subgroup.mul_mem _
        (Subgroup.mul_mem _ ?_ ?_) (Subgroup.mem_sup_right (qq_mem_img hj (D.cJ hj))))
      · exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i)
      · exact Subgroup.mem_sup_left
          (Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))) k)
    · rw [← qq_mul hsmc ((Cen _).mul_mem hs hr)]
      congr 1; group

theorem Data42.closure13_le_J : Subgroup.closure ({b₁, b₃} : Set G) ≤ J :=
  (Subgroup.closure_le J).mpr (by rintro y (hy | hy) <;> rw [hy]; exacts [D.hb₁J, D.hb₃J])

theorem Data42.card13 : Nat.card (Subgroup.closure ({b₁, b₃} : Set G)) = 9 := by
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := D.h4.basis.b_facts
  refine card_pair_of_card_triple h2 h1 h3 h13 h12.symm h23 ?_
  rw [show ({b₂, b₁, b₃} : Set G) = {b₁, b₂, b₃} from Set.insert_comm _ _ _, D.h4.basis.elem.2]
  norm_num

theorem Data42.img13 : img (b * b₂) (Subgroup.closure {b₁, b₃}) =
    Subgroup.closure {qq (b * b₂) b₁, qq (b * b₂) b₃} := by
  rw [img_closure, Set.image_pair]
  rintro y (hy | hy) <;> rw [hy]
  exacts [D.cb₁, D.cb₃]

theorem Data42.hyp_E9 : IsElemAb 3 2 (Subgroup.closure {qq (b * b₂) b₁, qq (b * b₂) b₃}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : Subgroup.closure ({b₁, b₃} : Set G) ≤ Subgroup.closure {b₁, b₂, b₃} :=
    Subgroup.closure_mono (by intro y hy; rcases hy with hy | hy <;> simp [hy])
  haveI := D.h4.basis.elem.1
  have hc := comm_of_isElemAb D.h4.basis.elem
  haveI : IsElementaryAbelian 3 (Subgroup.closure ({b₁, b₃} : Set G)) :=
    CFSG.IsElementaryAbelian.of_forall (fun a ha c hc' => hc a (hsub ha) c (hsub hc'))
      (fun a ha => elemPow_eq_one_of_isElementaryAbelian a (hsub ha))
  haveI : IsElementaryAbelian 3 ((Subgroup.closure ({b₁, b₃} : Set G)).subgroupOf
      (Cen (b * b₂))) :=
    IsElementaryAbelian.subgroupOf (fun _ h => D.cJ (D.closure13_le_J h))
  rw [← D.img13]
  refine ⟨IsElementaryAbelian.map (π (b * b₂)), ?_⟩
  obtain ⟨ψ⟩ := img_equiv (K := Subgroup.closure ({b₁, b₃} : Set G))
    (fun _ h => D.cJ (D.closure13_le_J h)) (fun k hk => D.inj_J k (D.closure13_le_J hk))
  rw [Nat.card_congr ψ.toEquiv, D.card13]; norm_num

theorem Data42.hyp_mono : ∀ n ∈ img (b * b₂) J ⊓
    Nor (Subgroup.closure {qq (b * b₂) b₁, qq (b * b₂) b₃}),
    ∀ y ∈ ({qq (b * b₂) b₁, qq (b * b₂) b₃} : Set (Q (b * b₂))),
      n * y * n⁻¹ ∈ ({qq (b * b₂) b₁, (qq (b * b₂) b₁)⁻¹, qq (b * b₂) b₃, (qq (b * b₂) b₃)⁻¹} :
        Set (Q (b * b₂))) := by
  rintro n ⟨hnJ, hnN⟩ y hy
  obtain ⟨j, hj, hjc, rfl⟩ := mem_img.mp hnJ
  obtain ⟨c, hcJ, hcC, hcE, ⟨g, hg⟩, rfl⟩ : ∃ c : G, c ∈ J ∧ c ∈ Cen (b * b₂) ∧
      c ∈ Subgroup.closure ({b₁, b₃} : Set G) ∧ (∃ g : G, g * b * g⁻¹ = c) ∧
      qq (b * b₂) c = y := by
    rcases hy with hy | hy <;> rw [hy]
    · exact ⟨b₁, D.hb₁J, D.cb₁, Subgroup.subset_closure (by simp), D.h4.conj_b.1, rfl⟩
    · exact ⟨b₃, D.hb₃J, D.cb₃, Subgroup.subset_closure (by simp), D.h4.conj_b.2.2, rfl⟩
  have hqc : qq (b * b₂) c ∈ Subgroup.closure {qq (b * b₂) b₁, qq (b * b₂) b₃} := by
    rw [← D.img13]; exact qq_mem_img hcE hcC
  have hwJ : j * c * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hcJ) (J.inv_mem hj)
  have hwC := D.cJ hwJ
  have hmem := (Subgroup.mem_normalizer_iff.mp hnN _).mp hqc
  rw [← qq_conj hjc hcC] at hmem ⊢
  rw [← D.img13] at hmem
  obtain ⟨e, heE, heC, he⟩ := mem_img.mp hmem
  have heJ : e ∈ J := D.closure13_le_J heE
  have hew : e = j * c * j⁻¹ := by
    have h1 : qq (b * b₂) (e⁻¹ * (j * c * j⁻¹)) = 1 := by
      rw [qq_mul ((Cen _).inv_mem heC) hwC, qq_inv heC, he, inv_mul_cancel]
    obtain ⟨i, hi⟩ := (qq_eq_one_iff ((Cen _).mul_mem ((Cen _).inv_mem heC) hwC)).mp h1
    have := D.inj_J _ (J.mul_mem (J.inv_mem heJ) hwJ) ⟨i, hi⟩
    exact (inv_mul_eq_one.mp this)
  have hw : j * c * j⁻¹ ∈ ({b₁, b₁⁻¹, b₃, b₃⁻¹} : Set G) :=
    D.h4.mono_pair (hew ▸ heE) ⟨j * g, by rw [← hg]; group⟩
  rcases hw with h | h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (qq_inv D.cb₁))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (qq_inv D.cb₃)))

theorem Data42.line {c τ : G} (hc : c = b₁ ∨ c = b₃) (hcL : c ∈ L) (hcC : c ∈ Cen (b * b₂))
    (hτb : τ * b * τ⁻¹ = c) (hτc : τ * c * τ⁻¹ = b) (hτ2 : τ * b₂ * τ⁻¹ = b₂)
    (hLevi : L ⊓ Cen (c * b₂) ≤ Nor (Subgroup.closure {c, b₂})) :
    setMul (Opp 3 (Nor (Subgroup.zpowers (qq (b * b₂) c))))
      (Nor (Subgroup.zpowers (qq (b * b₂) b)) ⊓ Nor (Subgroup.zpowers (qq (b * b₂) c))) =
      Nor (Subgroup.zpowers (qq (b * b₂) c)) := by
  have hc3 : orderOf c = 3 := by rw [← hτb, orderOf_conj']; exact D.h4.basis.hyp.ord
  have key : ∀ u ∈ Cen (b * b₂), qq (b * b₂) u ∈ Nor (Subgroup.zpowers (qq (b * b₂) c)) →
      u * c * u⁻¹ ∈ Subgroup.zpowers c := fun u hu h => by
    obtain ⟨k, j, hkj⟩ := lift_nor' hu hcC h
    refine D.h4.mem_zpowers_of_line hc hu ?_
    rw [hkj]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
  have himg : img (b * b₂) (Opp 3 (Cen c)) ≤ Opp 3 (Nor (Subgroup.zpowers (qq (b * b₂) c))) := by
    refine le_opp_of_normalizes ?_ ?_ (coprime_card_img (coprime_card_opp _))
    · intro y hy
      obtain ⟨o, ho, hoc, rfl⟩ := mem_img.mp hy
      exact mem_nor_of_mem_cen (qq_mem_cen hoc hcC
        (Subgroup.mem_centralizer_singleton_iff.mp (opp_le _ ho)))
    · intro s hs y hy
      obtain ⟨u, hu, rfl⟩ := qq_surj _ s
      obtain ⟨o, ho, hoc, rfl⟩ := mem_img.mp hy
      have hz := key u hu hs
      have hne : u * c * u⁻¹ ≠ 1 := fun h1 => by
        have : c = 1 := by
          calc c = u⁻¹ * (u * c * u⁻¹) * u := by group
            _ = 1 := by rw [h1]; group
        rw [this, orderOf_one] at hc3; norm_num at hc3
      have hN := mem_nor_cen_of_conj (eq_or_eq_inv_of_orderOf_three hc3 hz hne)
      rw [← qq_conj hu hoc]
      exact qq_mem_img (conj_mem_opp_of_mem_nor hN ho)
        ((Cen _).mul_mem ((Cen _).mul_mem hu hoc) ((Cen _).inv_mem hu))
  ext y
  constructor
  · rintro ⟨o, ho, n, hn, rfl⟩
    exact Subgroup.mul_mem _ (opp_le _ ho) hn.2
  · intro hy
    obtain ⟨u, hu, rfl⟩ := qq_surj _ y
    obtain ⟨o, ho, n, hon, hn, hnc, hnb, -⟩ :=
      D.h4.nor_line hcL hτb hτc hτ2 hLevi hu (key u hu hy)
    have ho' : o ∈ Opp 3 (Cen c) := by rwa [conjBy_opp, ← cen_conj, hτb] at ho
    have hoC : o ∈ Cen (b * b₂) := by
      have : o = u * n⁻¹ := by rw [hon]; group
      rw [this]; exact (Cen _).mul_mem hu ((Cen _).inv_mem hn)
    refine ⟨qq _ o, himg (qq_mem_img ho' hoC), qq _ n, ⟨D.nor_of hn hnb, nor_of' hn hcC ?_⟩, ?_⟩
    · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hnc
    · rw [hon, qq_mul hoC hn]

theorem Data42.hyp_lines : ∀ y ∈ ({qq (b * b₂) b₁, qq (b * b₂) b₃} : Set (Q (b * b₂))),
    setMul (Opp 3 (Nor (Subgroup.zpowers y)))
      (Nor (Subgroup.zpowers (qq (b * b₂) b)) ⊓ Nor (Subgroup.zpowers y)) =
      Nor (Subgroup.zpowers y) := by
  rintro y (hy | hy) <;> rw [hy]
  · exact D.line (Or.inl rfl) D.h4.basis.hb₁ D.cb₁ D.hτ₁b D.hτ₁c D.hτ₁2 D.hL1
  · exact D.line (Or.inr rfl) D.h4.basis.hb₃ D.cb₃ D.hτ₃b D.hτ₃c D.hτ₃2 D.hL3

theorem Data42.hyp_R : ∀ R : Subgroup (Q (b * b₂)), IsPGroup 2 R →
    Subgroup.closure {qq (b * b₂) b, qq (b * b₂) b₁, qq (b * b₂) b₃} ≤ Nor R → R = ⊥ := by
  intro R hR2 hRN
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hco : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]; exact Nat.Coprime.pow_right n (by norm_num)
  obtain ⟨K, hKC, hKco, hK1, hK2, hK3⟩ := lift_opp D.x3 R hco
  have hord : ∀ k ∈ K, Nat.Coprime 3 (orderOf k) := fun k hk => by
    rw [← Subgroup.orderOf_mk (H := K) k hk]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hKco
  have hKne : K ≠ ⊥ := by
    obtain ⟨r, hr, hr1⟩ := R.bot_or_exists_ne_one.resolve_left hne
    obtain ⟨g, hg, rfl⟩ := qq_surj _ r
    obtain ⟨k, hk, i, rfl⟩ := hK2 g hg hr
    intro hK
    rw [hK, Subgroup.mem_bot] at hk
    apply hr1
    rw [hk, one_mul, qq_xpow]
  have hK2g : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := hR2 ⟨qq _ k, hK1 k hk⟩
    have h1 : qq (b * b₂) (k ^ 2 ^ n) = 1 := by
      rw [qq_pow (hKC hk)]; simpa using congrArg Subtype.val hn
    obtain ⟨i, hi⟩ := (qq_eq_one_iff ((Cen _).pow_mem (hKC hk) _)).mp h1
    have hz : k ^ 2 ^ n ∈ Subgroup.zpowers (b * b₂) := by
      rw [hi]; exact Subgroup.zpow_mem_zpowers _ i
    have : k ^ 2 ^ n = 1 := eq_one_of_mem_zpowers_of_coprime D.x3 hz
      (Nat.Coprime.coprime_dvd_right (orderOf_pow_dvd _) (hord k hk))
    exact ⟨n, Subtype.ext (by simpa using this)⟩
  have hgen : ∀ g ∈ Cen (b * b₂), qq (b * b₂) g ∈ Nor R → g ∈ Nor K := fun g hg hgR =>
    Subgroup.mem_normalizer_fintype fun k hk => by
      have hkC := hKC hk
      have hc : g * k * g⁻¹ ∈ Cen (b * b₂) :=
        (Cen _).mul_mem ((Cen _).mul_mem hg hkC) ((Cen _).inv_mem hg)
      refine hK3 _ hc ?_ ?_
      · rw [qq_conj hg hkC]; exact (Subgroup.mem_normalizer_iff.mp hgR _).mp (hK1 k hk)
      · rw [orderOf_conj']; exact hord k hk
  have hBN : B ≤ Nor K := by
    rw [D.h4.basis.mono.2.1]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy | hy | hy) <;> rw [hy]
    · exact hgen b D.cb (hRN (Subgroup.subset_closure (by simp)))
    · exact hgen b₁ D.cb₁ (hRN (Subgroup.subset_closure (by simp)))
    · exact hgen b₂ D.cb₂
        (by rw [D.qb₂]; exact Subgroup.inv_mem _ (hRN (Subgroup.subset_closure (by simp))))
    · exact hgen b₃ D.cb₃ (hRN (Subgroup.subset_closure (by simp)))
  have h4 := AS.four_le_localRank_of hKne hK2g D.h4.basis.mono.1 hBN
  have h3 := D.h4.basis.rank3
  omega

theorem Data42.hyp_conj : ∀ h : Q (b * b₂),
    conjBy h (Subgroup.zpowers (qq (b * b₂) b)) ≤ Nor (Subgroup.zpowers (qq (b * b₂) b)) →
    conjBy h (Subgroup.zpowers (qq (b * b₂) b)) = Subgroup.zpowers (qq (b * b₂) b) := by
  intro h hh
  obtain ⟨u, hu, rfl⟩ := qq_surj _ h
  rw [conjBy_zpowers, ← qq_conj hu D.cb] at hh ⊢
  obtain ⟨y, hydef⟩ : ∃ y : G, y = u * b * u⁻¹ := ⟨_, rfl⟩
  rw [← hydef] at hh ⊢
  have hyC : y ∈ Cen (b * b₂) := by
    rw [hydef]; exact (Cen _).mul_mem ((Cen _).mul_mem hu D.cb) ((Cen _).inv_mem hu)
  have hyN := hh (Subgroup.mem_zpowers _)
  have hy3 : y ^ 3 = 1 := by rw [hydef, conj_pow, D.b3]; group
  rcases D.fs hyC hyN with ⟨h1, h2⟩ | ⟨h1, h2⟩
  swap
  · exfalso
    have : y ^ 3 * b * (y ^ 3)⁻¹ = b₂ := by
      calc y ^ 3 * b * (y ^ 3)⁻¹ = y * (y * (y * b * y⁻¹) * y⁻¹) * y⁻¹ := by
            rw [pow_three]; group
        _ = b₂ := by rw [h1, h2, h1]
    rw [hy3] at this
    exact D.h4.b_ne_b₂ (by simpa using this)
  have hyb : y ∈ Cen b := mem_cen_of_conj h1
  have hyb₂ : y ∈ Cen b₂ := mem_cen_of_conj h2
  obtain ⟨l, hl, hl3, k, hlk⟩ := D.h4.basis.hyp.cube_decomp hyb hy3
  have hbk₂ : b ^ k ∈ Cen b₂ := (Cen b₂).zpow_mem (mem_cen_of_commute D.comm) k
  have hl₂ : l ∈ Cen b₂ := by
    have : l = y * (b ^ k)⁻¹ := by rw [hlk]; group
    rw [this]; exact (Cen _).mul_mem hyb₂ ((Cen _).inv_mem hbk₂)
  obtain ⟨m, j, hj, hlm⟩ := D.hJdec l ⟨hl, hl₂⟩
  have hcomm : Commute ((b₂ ^ m)⁻¹) l :=
    (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp hl₂).symm m).inv_left
  have hj3 : j ^ 3 = 1 := by
    have hj' : j = (b₂ ^ m)⁻¹ * l := by rw [hlm]; group
    rw [hj', hcomm.mul_pow, hl3, mul_one, inv_pow, ← pow_mul, mul_comm, pow_mul,
      D.h4.basis.b_facts.2.1, one_pow, inv_one]
  obtain ⟨φ⟩ := D.φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' := (Subgroup.closure ({b₁, b₃} : Set G)).subgroupOf J with hE'
  have hE'c : Nat.card E' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.closure13_le_J).toEquiv, D.card13]
  have hJc : Nat.card J = 720 := by rw [Nat.card_congr φ.toEquiv, S6Aut.card_perm_six]
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'c]; norm_num)
  have hidx : ¬ 3 ∣ E'.index := by
    have h := E'.index_mul_card
    rw [hE'c, hJc] at h
    have : E'.index = 80 := by omega
    rw [this]; norm_num
  obtain ⟨v, hvJ, hv⟩ := exists_conjBy_le_sylow (H := J) (A := Subgroup.zpowers j)
    (Subgroup.zpowers_le.mpr hj) (isPGroup_three_zpowers (k := 1) (by rw [pow_one]; exact hj3))
    (hE'p.toSylow hidx)
  have hvj : v * j * v⁻¹ ∈ Subgroup.closure ({b₁, b₃} : Set G) := by
    have h1 : v * j * v⁻¹ ∈ conjBy v (Subgroup.zpowers j) := by
      rw [mem_conjBy_iff, show v⁻¹ * (v * j * v⁻¹) * v = j by group]
      exact Subgroup.mem_zpowers j
    have h2 := hv h1
    rw [IsPGroup.toSylow_coe, hE', Subgroup.subgroupOf_map_subtype] at h2
    exact h2.1
  have hvb : v * b = b * v :=
    Subgroup.mem_centralizer_singleton_iff.mp (D.h4.basis.hyp.hLC (D.hJ hvJ).1)
  have hvb₂ : v * b₂ = b₂ * v := Subgroup.mem_centralizer_singleton_iff.mp (D.hJ hvJ).2
  have hvx := conj_of_mem_cen (D.cJ hvJ)
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := D.h4.basis.mem
  have hEB : Subgroup.closure ({b₁, b₃} : Set G) ≤ B :=
    (Subgroup.closure_le B).mpr (by rintro z (hz | hz) <;> rw [hz]; exacts [hb1B, hb3B])
  have hy'B : v * y * v⁻¹ ∈ B := by
    have e1 : v * b₂ ^ m * v⁻¹ = b₂ ^ m := by rw [(Commute.pow_right hvb₂ m).eq]; group
    have e2 : v * b ^ k * v⁻¹ = b ^ k := by rw [(Commute.zpow_right hvb k).eq]; group
    have : v * y * v⁻¹ = (v * b₂ ^ m * v⁻¹) * (v * j * v⁻¹) * (v * b ^ k * v⁻¹) := by
      rw [hlk, hlm]; group
    rw [this, e1, e2]
    exact B.mul_mem (B.mul_mem (B.pow_mem hb2B m) (hEB hvj)) (B.zpow_mem hbB k)
  obtain ⟨-, ⟨g₂, hg₂⟩, -⟩ := D.h4.conj_b
  have hc1 : ∃ g : G, g * b * g⁻¹ = v * y * v⁻¹ := ⟨v * u, by rw [hydef]; group⟩
  have hc2 : ∃ g : G, g * b * g⁻¹ = (v * y * v⁻¹)⁻¹ * (b * b₂) := by
    refine ⟨v * u * g₂, ?_⟩
    calc v * u * g₂ * b * (v * u * g₂)⁻¹ = v * (u * (g₂ * b * g₂⁻¹) * u⁻¹) * v⁻¹ := by group
      _ = v * (u * b * u⁻¹)⁻¹ * (u * (b * b₂) * u⁻¹) * v⁻¹ := by rw [hg₂]; group
      _ = v * (u * b * u⁻¹)⁻¹ * (b * b₂) * v⁻¹ := by rw [conj_of_mem_cen hu]
      _ = (v * y * v⁻¹)⁻¹ * (v * (b * b₂) * v⁻¹) := by rw [hydef]; group
      _ = (v * y * v⁻¹)⁻¹ * (b * b₂) := by rw [hvx]
  have hback : ∀ z : G, v * z = z * v → v * y * v⁻¹ = z → y = z := fun z hz e => by
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (v * z) := by rw [e, mul_assoc, ← hz]
      _ = z := by group
  rcases D.h4.eq_of_conj_pair hy'B hc1 hc2 with e | e
  · rw [hback b hvb e]
  · rw [hback b₂ hvb₂ e, D.qb₂, Subgroup.zpowers_inv]

theorem Data42.odd : Odd (Nat.card (Opp 3 (Cen (b * b₂)))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Opp 3 (Cen (b * b₂))) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 4) D.h4.basis.mono.1.2
  have hBN : B ≤ Nor (Opp 3 (Cen (b * b₂))) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun o ho =>
      conj_mem_opp_of_mem_nor (Subgroup.le_normalizer (D.cB hy)) ho
  obtain ⟨S, -, hS, hS2, hSN⟩ := exists_two_subgroup_of_even hBp (coprime_card_opp _) hBN h2
  have h4 := AS.four_le_localRank_of hS hS2 D.h4.basis.mono.1 hSN
  have h3 := D.h4.basis.rank3
  omega

theorem Data42.fs79 (hFS : Prop2At (Q (b * b₂))) :
    setMul (Opp 3 (⊤ : Subgroup (Q (b * b₂)))) (Nor (Subgroup.zpowers (qq (b * b₂) b))) =
      Set.univ :=
  hFS (qq _ b) (qq _ t) (qq _ b₁) (qq _ b₃) (img _ J) D.hyp_ord_b D.hyp_ord_t
    D.hyp_tb D.hyp_J D.hyp_Jb D.hyp_Jt D.hyp_norJ D.hyp_N (qq_mem_img D.hb₁J D.cb₁)
    (qq_mem_img D.hb₃J D.cb₃) D.hyp_E9 D.hyp_mono D.hyp_lines D.hyp_R D.hyp_conj

theorem Data42.conc (hFS : Prop2At (Q (b * b₂))) :
    Conc (b * b₂) (Subgroup.closure {b, b₂}) := by
  refine ⟨D.odd, ?_⟩
  ext g
  constructor
  · rintro ⟨o, ho, n, hn, rfl⟩
    exact (Cen _).mul_mem (opp_le _ ho) hn.1
  · intro hg
    have hgu : qq (b * b₂) g ∈ setMul (Opp 3 (⊤ : Subgroup (Q (b * b₂))))
        (Nor (Subgroup.zpowers (qq (b * b₂) b))) := by
      rw [D.fs79 hFS]; trivial
    obtain ⟨ob, hob, nb, hnb, he⟩ := hgu
    obtain ⟨n, hnC, rfl⟩ := qq_surj _ nb
    obtain ⟨K, hKC, hKco, hK1, hK2, hK3⟩ := lift_opp D.x3 (Opp 3 ⊤) (coprime_card_opp _)
    have hgn : qq (b * b₂) (g * n⁻¹) ∈ Opp 3 (⊤ : Subgroup (Q (b * b₂))) := by
      rw [qq_mul hg ((Cen _).inv_mem hnC), qq_inv hnC, he, mul_inv_cancel_right]; exact hob
    obtain ⟨k, hk, i, hki⟩ := hK2 _ ((Cen _).mul_mem hg ((Cen _).inv_mem hnC)) hgn
    have hKO : K ≤ Opp 3 (Cen (b * b₂)) := by
      refine le_opp_of_normalizes hKC (fun s hs k hk => ?_) hKco
      have hkC := hKC hk
      refine hK3 _ ((Cen _).mul_mem ((Cen _).mul_mem hs hkC) ((Cen _).inv_mem hs)) ?_ ?_
      · rw [qq_conj hs hkC]
        exact conj_mem_opp_of_mem_nor (Subgroup.mem_normalizer_iff.mpr fun _ => by simp)
          (hK1 k hk)
      · rw [orderOf_conj', ← Subgroup.orderOf_mk (H := K) k hk]
        exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hKco
    have hxi : (b * b₂) ^ i ∈ Cen (b * b₂) :=
      (Cen _).zpow_mem (Subgroup.mem_centralizer_singleton_iff.mpr rfl) i
    have hwC : (b * b₂) ^ i * n ∈ Cen (b * b₂) := (Cen _).mul_mem hxi hnC
    have hqw : qq (b * b₂) ((b * b₂) ^ i * n) = qq (b * b₂) n := by
      rw [qq_mul hxi hnC, qq_xpow, one_mul]
    have hwb := D.lift hwC (by rw [hqw]; exact hnb)
    have hwN : (b * b₂) ^ i * n ∈ Nor (Subgroup.closure ({b, b₂} : Set G)) := by
      refine mem_nor_of_gen fun y hy => ?_
      rcases hy with hy | hy <;> rw [hy]
      · exact hwb
      · rw [show (b * b₂) ^ i * n * b₂ * ((b * b₂) ^ i * n)⁻¹ =
            (((b * b₂) ^ i * n) * b * ((b * b₂) ^ i * n)⁻¹)⁻¹ *
            (((b * b₂) ^ i * n) * (b * b₂) * ((b * b₂) ^ i * n)⁻¹) by group,
          conj_of_mem_cen hwC]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hwb) (Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    refine ⟨k, hKO hk, (b * b₂) ^ i * n, ⟨hwC, hwN⟩, ?_⟩
    calc g = (g * n⁻¹) * n := by group
      _ = k * (b * b₂) ^ i * n := by rw [hki]
      _ = k * ((b * b₂) ^ i * n) := by group

end Data

end CFSG.RankThree.PartTwo.Sec21.FF81
