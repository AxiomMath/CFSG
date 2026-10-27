module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGStdPosAutHolds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRoot
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LieType.Steinberg.CentralExt.Unipotent
import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem ggBstar_eq_of_normalizes_two {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTN : Bs ≤ Subgroup.normalizer (T : Set G)) :
    Bs = B := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hle : Nat.card Bs ≤ p ^ LargeEvenTwoLocalRank p G :=
    TableB.card_le_of_twoLocal hcfg.1.2.2.2.2.2.1.1 ⟨T, hT1, hT2, rfl⟩ hTN hcfg.2.1.2.1
  exact (Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 (hB ▸ hle)).symm

theorem GGConfig.not_normalizes_two_of_B_lt_Bs {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ¬ Bs ≤ Subgroup.normalizer (T : Set G) := by
  intro hTN
  exact hlt.ne (ggBstar_eq_of_normalizes_two hcfg hT2 hT1 hTN).symm

theorem GGConfig.twoCenter_eq_bot_of_B_lt_Bs {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs)
    (hNX : Bs ≤ Subgroup.normalizer (X : Set G)) : Line63.H5.twoCenter X = ⊥ := by
  by_contra hne
  have hle : Line63.H5.twoCenter X ≤ Subgroup.normalizer (X : Set G) := by
    intro z hz
    exact Subgroup.le_normalizer hz.1
  have hnorm : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Line63.H5.twoCenter X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp
      (Line63.H5.twoCenter_normal X)
  exact hcfg.not_normalizes_two_of_B_lt_Bs hlt (Line63.H5.isPGroup_twoCenter X) hne
    (hNX.trans hnorm)

theorem GGConfig.odd_card_center_of_B_lt_Bs {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs)
    (hNX : Bs ≤ Subgroup.normalizer (X : Set G)) :
    Odd (Nat.card (Subgroup.center ↥X)) := by
  by_contra hodd
  have hdiv : 2 ∣ Nat.card (Subgroup.center ↥X) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  have hz2 : ((z : ↥X) : G) ^ 2 = 1 := by
    have hpow : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg (fun a : Subgroup.center ↥X => ((a : ↥X) : G)) hpow
  have hzC : ((z : ↥X) : G) ∈ Line63.H5.twoCenter X := by
    refine ⟨(z : ↥X).2, ?_, ?_⟩
    · intro l hl
      exact (congrArg (fun a : ↥X => (a : G))
        ((Subgroup.mem_center_iff.mp z.2) ⟨l, hl⟩)).symm
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := G)).ne'
      rw [hk, pow_succ', pow_mul, hz2, one_pow]
  rw [hcfg.twoCenter_eq_bot_of_B_lt_Bs hlt hNX, Subgroup.mem_bot] at hzC
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hzC)
  rw [hz1, orderOf_one] at hz
  omega

theorem GGConfig.odd_card_central_kernel_of_B_lt_Bs {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hlt : B < Bs)
    (hNX : Bs ≤ Subgroup.normalizer (X : Set G)) {R : Type} [Group R]
    (ψ : ↥X →* R) (hker : ψ.ker ≤ Subgroup.center ↥X) : Odd (Nat.card ψ.ker) :=
  (hcfg.odd_card_center_of_B_lt_Bs hlt hNX).of_dvd_nat (Subgroup.card_dvd_of_le hker)

theorem ggSecFiveRoute_bstar_eq_of_split
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) : Bs = B := by
  obtain ⟨t, n, f, ψ, hloc⟩ :=
    ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg L (Or.inl rfl) hsplit
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  obtain ⟨⟨-, -, hadm, hrank⟩, ⟨-, -, ht, -⟩, -, -, -⟩ := hloc
  obtain ⟨-, -, xp, C, O, hE⟩ := ggStdPos_bruhatData (f := f) hrank ht
  set ψ' := ψ.comp (MulAut.conj k).toMonoidHom
  have hr : 0 < (ggU t n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm hrank]
    omega
  set γ : Fin (ggU t n f).D.rank → ℤ := Pi.single ⟨0, hr⟩ 1
  have hγ : γ ∈ (ggU t n f).D.roots := single_mem_roots ⟨0, hr⟩
  set T : Subgroup G := ((ggU t n f).D.rootGroup γ).map ψ'
  have hT2 : IsPGroup 2 T := (isPGroup_of_isParametrization (p := 2) hE.param hγ).map ψ'
  have hT1 : T ≠ ⊥ := by
    obtain ⟨b, -, z, hz, hne⟩ := ggKGPosNoTrivRootStmt_holds G p Bs L t n f ψ' hloc' hstd γ hγ
    intro hbot
    have hzT : ψ' z ∈ T := Subgroup.mem_map_of_mem ψ' hz
    rw [hbot, Subgroup.mem_bot] at hzT
    exact hne (by rw [hzT, mul_one, mul_inv_cancel])
  have key : ∀ c ∈ Bs, ∀ z ∈ (ggU t n f).D.rootGroup γ, c * ψ' z * c⁻¹ ∈ T := by
    intro c hc z hz
    obtain ⟨h, hh, hcz⟩ := hstd c hc γ hγ
    have hN := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
    rw [hcz z hz]
    exact Subgroup.mem_map_of_mem ψ' ((Subgroup.mem_normalizer_iff.mp hN z).mp hz)
  refine ggBstar_eq_of_normalizes_two hcfg.1.1 hT2 hT1 ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    exact key c hc z hz
  · intro hg
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    have hk := key c⁻¹ (Bs.inv_mem hc) z hz
    have e : c⁻¹ * ψ' z * c⁻¹⁻¹ = g := by
      rw [hzg]
      group
    rwa [e] at hk

theorem GGConfig.bstar_eq_of_linear_diagonal
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hm : 1 ≤ m) (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) : Bs = B := by
  obtain ⟨T, hT1, hT2, -, hTN⟩ :=
    exists_twoSubgroup_le_map_blockSpecialLinear hker hdiag
      (I := Finset.univ) (by simpa using Nat.succ_le_succ hm)
  exact ggBstar_eq_of_normalizes_two hcfg hT2 hT1 hTN

end CFSG.StandardType

end
