module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinSylowNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerFixesCentralInvolutionOfLargeDihedralSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralInvolutionMemLargeDihedralSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
open scoped Pointwise
namespace CFSG.GorensteinWalter
noncomputable section
universe u

/-- A Sylow subgroup of `C_G(x)` containing the Klein core has controlled normalizer. -/
public theorem firstCase_klein_centralizer_sylow_normalizer_le_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {x : G} (hxU : x ∈ c.U) :
    let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
    ∃ Q : Sylow 2 C,
      twoCoreOf c.Hhat ≤
          ((Q : Subgroup C).map C.subtype : Subgroup G) ∧
        Subgroup.normalizer
            (((Q : Subgroup C).map C.subtype : Subgroup G) : Set G) ≤ c.Hhat := by
  classical
  dsimp
  let V : Subgroup G := twoCoreOf c.Hhat
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hVklein : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hklein
  have hVcent : V ≤ C := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z = x := by simpa using hz
    subst z
    have hvU : v ∈ twoCoreOf c.Hhat := hv
    have hcent := (show twoCoreOf c.Hhat ≤
        Subgroup.centralizer (c.U : Set G) from by
      have h26 := theorem_2_6 hmin c
      simpa [h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat) hvU
    exact Subgroup.mem_centralizer_iff.mp hcent x hxU
  have hVnorm : Subgroup.normalizer (V : Set G) = c.Hhat := by
    simpa [V] using firstCase_klein_normalizer_twoCore_eq_Hhat hmin c hklein
  have hVcard : Nat.card V = 4 := hVklein.card_four
  have hCent : ∀ v : G, v ∈ V → v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ c.Hhat := by
    intro v hv hvne
    exact firstCase_klein_centralizer_twoCore_le_Hhat hmin c hklein v hv hvne
  have hVCp : IsPGroup 2 (V.subgroupOf C) := by
    have hVp : IsPGroup 2 V := by
      apply IsPGroup.of_card (n := 2)
      rw [hVcard]
      norm_num
    exact hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVcent).symm
  obtain ⟨Q, hVQ⟩ := hVCp.exists_le_sylow
  let QG : Subgroup G := (Q : Subgroup C).map C.subtype
  have hQGcard : Nat.card QG = Nat.card Q := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (Q : Subgroup C) C.subtype
        C.subtype_injective).toEquiv).symm
  have hQGp : IsPGroup 2 QG := Q.isPGroup'.map C.subtype
  obtain ⟨P, hQGP⟩ := hQGp.exists_le_sylow
  have hVleQG : V ≤ QG := by
    intro v hv
    let vC : C := ⟨v, hVcent hv⟩
    have hvQ : vC ∈ (Q : Subgroup C) := hVQ (Subgroup.mem_subgroupOf.mpr hv)
    exact Subgroup.mem_map.mpr ⟨vC, hvQ, rfl⟩
  by_cases hlarge : 8 ≤ Nat.card QG
  · obtain ⟨P, hQGP⟩ := hQGp.exists_le_sylow
    let eS := Classical.choice c.dihedralEquiv
    let eP : P ≃* DihedralGroup (2 ^ c.m) :=
      (Sylow.equiv P c.S).trans eS
    have hnorm := firstCase_klein_large_twoSubgroup_normalizer_le_Hhat
      V QG (P : Subgroup G) c.Hhat
      hVleQG hQGP hVklein hlarge (by
        have hS8 := firstCase_klein_S_card hmin c hfirst hklein
        have hScard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := by
          obtain ⟨e⟩ := c.dihedralEquiv
          simpa using (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
        rw [hS8] at hScard
        have hmPow : 2 ^ c.m = 4 := by omega
        have hmEq : c.m = 2 := by
          apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
          simpa using hmPow
        omega) eP hCent
    exact ⟨Q, by simpa [V, QG] using hVleQG, by simpa [QG] using hnorm⟩
  · have hQcard4 : Nat.card QG = 4 := by
      have hQpow := Q.isPGroup'.exists_card_eq
      rcases hQpow with ⟨n, hn⟩
      have hnG : Nat.card QG = 2 ^ n := hQGcard.trans hn
      have hVd : Nat.card V ∣ Nat.card QG := Subgroup.card_dvd_of_le hVleQG
      rw [hVcard, hnG] at hVd
      have hnge : 2 ≤ n := by
        rcases (Nat.dvd_prime_pow Nat.prime_two).mp hVd with ⟨k, hkn, hk⟩
        have hk2 : k = 2 := by
          apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
          norm_num at hk ⊢
          exact hk.symm
        omega
      have hnlt : n < 3 := by
        by_contra hn3
        have hn3' : 3 ≤ n := by omega
        have hpow : 2 ^ 3 ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3'
        apply hlarge
        rw [hnG]
        norm_num at hpow ⊢
        exact hpow
      have hn2 : n = 2 := by omega
      rw [hnG, hn2]
      norm_num
    have hQeq : QG = V := by
      exact (Subgroup.eq_of_le_of_card_ge hVleQG (by
        rw [hQcard4, hVcard])).symm
    refine ⟨Q, by simpa [V, QG] using hVleQG, ?_⟩
    change Subgroup.normalizer (QG : Set G) ≤ c.Hhat
    rw [hQeq]
    exact hVnorm.le

end
end CFSG.GorensteinWalter
