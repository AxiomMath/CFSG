module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoYhat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem Dn_le_of_K11 (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {N : Subgroup G} (hKN : t.Ky ≤ N)
    (hrank : CFSG.Open.pRank 3 (t.Dn N) = 1) (hO : t.On N ≤ c.S.M)
    (hX : (∃ ℓ f : ℕ, CFSG.Blueprint.LieModel (t.Dhat N) .PSL 2 ℓ f) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor (t.Dhat N) .J1) :
    t.Dn N ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  let D : Subgroup G := t.Dn N
  let π : ↥D →* t.Dhat N := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥D)
  let ZD : Subgroup (t.Dhat N) := t.DhatZ N
  let MD : Subgroup (t.Dhat N) := ((c.S.M).subgroupOf D).map π
  haveI hPnormal : (CFSG.pPrimeCore 3 ↥D).Normal := CFSG.pPrimeCore_normal
  have hZD_card : Nat.card ZD = 3 := t.card_DhatZ hZN
  have hZsub_card : Nat.card (t.Z.subgroupOf D : Subgroup ↥D) = 3 :=
    t.card_Z_subgroupOf_Dn hZN
  have hZD3 : IsPGroup 3 (t.Z.subgroupOf D) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hZsub_card]
    norm_num
  have hcop3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥D) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hmapnorm : (Subgroup.normalizer (t.Z.subgroupOf D : Set ↥D)).map π =
      Subgroup.normalizer (ZD : Set (t.Dhat N)) :=
    CFSG.GroupTheory.normal_coprime_quotient_normalizer 3
      (CFSG.pPrimeCore 3 ↥D) hcop3 (t.Z.subgroupOf D) hZD3
  have hnorm_le : Subgroup.normalizer (ZD : Set (t.Dhat N)) ≤ MD := by
    rw [← hmapnorm]
    intro xhat hxhat
    obtain ⟨x, hxnorm, hxπ⟩ := Subgroup.mem_map.mp hxhat
    refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ?_, hxπ⟩
    have hxN : x ∈ (Subgroup.normalizer (t.Z : Set G)).subgroupOf D := by
      rw [Subgroup.subgroupOf_normalizer_eq (t.Z_le_Dn hZN)]
      exact hxnorm
    exact t.normalizer_Z_le hp hN hZ (Subgroup.mem_subgroupOf.mp hxN)
  have hKD : t.Ky ≤ D := t.Ky_le_Dn hK32 hGA hSp hKN
  have hKyM : t.Ky ≤ c.S.M := (t.Ky_le.trans inf_le_left).trans c.hyp81.1
  have hKyNormOn : t.Ky ≤ Subgroup.normalizer (t.On N : Set G) :=
    hKD.trans (CFSG.ABGLocalTools.le_normalizer_map_subtype D (CFSG.pPrimeCore 3 ↥D))
  have hKyNormOn' : t.Ky ≤
      Subgroup.normalizer ((t.Ky ⊓ t.On N : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.On N)
      ⟨Subgroup.le_normalizer hk, hKyNormOn hk⟩
  have hKyO_le_N : t.Ky ⊓ t.On N ≤ t.d.N := by
    rcases t.le_N_or_eq_Ky hK32 hGA hSp inf_le_left hKyNormOn' with hle | heq
    · exact hle
    · exfalso
      have hKyO : t.Ky ≤ t.On N := (le_of_eq heq.symm).trans inf_le_right
      exact t.not_Z_le_On (t.Z_le_Ky.trans hKyO)
  let ψ : ↥t.Ky →* t.Dhat N := π.comp (Subgroup.inclusion hKD)
  let φ : ↥t.Ky →* ↥MD := ψ.codRestrict MD fun k =>
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKD k,
      Subgroup.mem_subgroupOf.mpr (hKyM k.2), rfl⟩
  have hφker : φ.ker ≤ (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hk1 : ψ k = 1 := by
      have h := congrArg Subtype.val hk
      change ψ k = 1 at h
      exact h
    have hkO : (⟨k, hKD k.2⟩ : ↥D) ∈ CFSG.pPrimeCore 3 ↥D :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥D) _).mp hk1
    have hkOn : (k : G) ∈ t.On N := Subgroup.mem_map.mpr ⟨⟨k, hKD k.2⟩, hkO, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨k.2, hKyO_le_N (Subgroup.mem_inf.mpr ⟨k.2, hkOn⟩)⟩)
  have hnot : ¬ CFSG.HallHigman.IsPSolvable 3 ↥MD :=
    t.not_isPSolvable_of_ker_le hK32 hGA hSp φ hφker
  have htop : MD = ⊤ :=
    hK11 (t.Dhat N) (t.isSimpleGroup_Dhat hZN hrank)
      (fun P hP => t.isCyclic_of_isPGroup_Dhat hrank hP) hX ZD MD hZD_card hnorm_le hnot
  exact t.Dn_le_of_map_eq_top le_rfl hO htop

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
