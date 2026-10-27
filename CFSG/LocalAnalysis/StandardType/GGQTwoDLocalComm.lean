module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGQTwoDNode
import CFSG.LocalAnalysis.StandardType.GGQTwoDRigidGen
import CFSG.LocalAnalysis.StandardType.GGQTwoDRigidPair
import CFSG.LocalAnalysis.StandardType.GGQTwoDReflLin
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G}

private lemma rankOne_inf_cube_eq_one (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs) {r r' : MulAut ↥Bs} (hr : GGIsReflection 3 r)
    (hr' : GGIsReflection 3 r') (hrI : r ∈ ggInduced ⊤ Bs)
    (hr'I : r' ∈ ggInduced ⊤ Bs) (h6 : Nat.card (ggRankOne Bs r) = 6)
    (h6' : Nat.card (ggRankOne Bs r') = 6) (hne : r ≠ r') :
    ∀ g ∈ ggRankOne Bs r, g ∈ ggRankOne Bs r' → g ^ 3 = 1 → g = 1 := by
  obtain ⟨a, ha1, haS, har, haz⟩ := exists_root_ggRankOne hBs hSC hrI h6
  obtain ⟨b, hb1, hbS, hbr, hbz⟩ := exists_root_ggRankOne hBs hSC hr'I h6'
  intro g hg hg' hg3
  by_contra hg1
  have ha3 : (a : G) ^ 3 = 1 := hBs.2 a a.2
  have hb3 : (b : G) ^ 3 = 1 := hBs.2 b b.2
  have horda : orderOf (a : G) = 3 := orderOf_eq_prime ha3 (by simpa using ha1)
  have hordg : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hga : g ∈ Subgroup.zpowers (a : G) := haz g hg hg3
  have hgb : g ∈ Subgroup.zpowers (b : G) := hbz g hg' hg3
  have hcardg : Nat.card (Subgroup.zpowers g) = 3 := by
    rw [Nat.card_zpowers, hordg]
  have hcarda : Nat.card (Subgroup.zpowers (a : G)) = 3 := by
    rw [Nat.card_zpowers, horda]
  have hordb : orderOf (b : G) = 3 := orderOf_eq_prime hb3 (by simpa using hb1)
  have hcardb : Nat.card (Subgroup.zpowers (b : G)) = 3 := by
    rw [Nat.card_zpowers, hordb]
  have heqa : Subgroup.zpowers g = Subgroup.zpowers (a : G) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hga)
      (by simp [hcarda, hcardg])
  have heqb : Subgroup.zpowers g = Subgroup.zpowers (b : G) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgb)
      (by simp [hcardb, hcardg])
  have hab : Subgroup.zpowers (a : G) = Subgroup.zpowers (b : G) := heqa.symm.trans heqb
  have hca : (a : G) ∈ Subgroup.zpowers (b : G) := by
    rw [← hab]
    exact Subgroup.mem_zpowers _
  rcases Subgroup.mem_zpowers_iff.mp hca with ⟨n, hn⟩
  have hn' : b ^ n = a := Subtype.ext (by simpa using hn)
  have hba : r' a = a⁻¹ := by
    rw [← hn', map_zpow, hbr]
    simp
  have ht : GGIsTransvection 3 (r * r') :=
    isTransvection_mul_of_apply_eq_inv (p := 3) (by norm_num) hBs hr hr' hne ha1 har hba
  exact hNT (r * r') (mul_mem_ggInduced hrI hr'I) ht

theorem ggRankOne_commute_ggRankOne (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {r r' : MulAut ↥Bs} (hr : GGIsReflection 3 r) (hr' : GGIsReflection 3 r')
    (hrI : r ∈ ggInduced ⊤ Bs) (hr'I : r' ∈ ggInduced ⊤ Bs)
    (h6 : Nat.card (ggRankOne Bs r) = 6) (h6' : Nat.card (ggRankOne Bs r') = 6)
    (hcomm : r * r' = r' * r) (hne : r ≠ r') :
    ∀ x ∈ ggRankOne Bs r, ∀ y ∈ ggRankOne Bs r', x * y = y * x := by
  intro x hx y hy
  have hle : ggRankOne Bs r ≤ Subgroup.centralizer (ggRankOne Bs r' : Set G) := by
    rw [ggRankOne]
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨huC, k, hk⟩
    obtain ⟨a, ha1, haS, har, haz⟩ := exists_root_ggRankOne hBs hSC hr'I h6'
    have hra : r a = a :=
      apply_eq_self_of_commute_of_isReflection (p := 3) (by norm_num) hBs hr hr' hcomm hne har
    have haH : (a : G) ∈ ggHyperplane Bs r := (mem_ggHyperplane_iff' a).mpr hra
    have hua : u * (a : G) = (a : G) * u :=
      ((Subgroup.mem_centralizer_iff.mp huC) (a : G) haH).symm
    have huS : u ∈ ggRankOne Bs r := Subgroup.subset_closure ⟨huC, k, hk⟩
    have huN : u ∈ Subgroup.normalizer (ggHyperplane Bs r' : Set G) :=
      ggRankOne_le_normalizer_ggHyperplane hBs hSC hr hrI h6 hr' hcomm hne huS
    have huNC : u ∈ Subgroup.normalizer
        (Subgroup.centralizer (ggHyperplane Bs r' : Set G) : Set G) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
        (ggHyperplane Bs r') huN
    have huU : u ∈ Subgroup.normalizer (ggRankOne Bs r' : Set G) := by
      rw [ggRankOne]
      exact ggMem_normalizer_oTwoPrime huNC
    have hcube : ∀ g ∈ ggRankOne Bs r', g ^ 3 = 1 → u * g = g * u := by
      intro g hg hg3
      rcases Subgroup.mem_zpowers_iff.mp (haz g hg hg3) with ⟨n, hn⟩
      rw [← hn]
      exact (show Commute u (a : G) from hua).zpow_right n
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (commute_of_card_six h6'
      (ggOTwoPrime_exists_ne_comm_of_card_six h6') hk huU hcube z hz).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem ggRankOne_commute_ggRankTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs) {r r₁ r₂ : MulAut ↥Bs} (hr : GGIsReflection 3 r)
    (hr₁ : GGIsReflection 3 r₁) (hr₂ : GGIsReflection 3 r₂) (hrI : r ∈ ggInduced ⊤ Bs)
    (hr₁I : r₁ ∈ ggInduced ⊤ Bs) (hr₂I : r₂ ∈ ggInduced ⊤ Bs)
    (h6 : Nat.card (ggRankOne Bs r) = 6) (h6₁ : Nat.card (ggRankOne Bs r₁) = 6)
    (h6₂ : Nat.card (ggRankOne Bs r₂) = 6) (hc₁ : r * r₁ = r₁ * r) (hc₂ : r * r₂ = r₂ * r)
    (hne₁ : r ≠ r₁) (hne₂ : r ≠ r₂) (hne : r₁ ≠ r₂)
    (hpair : UnitaryBlockStandardPair K 2 1 (ggRankTwo Bs r₁ r₂) (ggRankOne Bs r₁)
      (ggRankOne Bs r₂)) :
    ∀ x ∈ ggRankOne Bs r, ∀ y ∈ ggRankTwo Bs r₁ r₂, x * y = y * x := by
  intro x hx y hy
  have hle : ggRankOne Bs r ≤ Subgroup.centralizer (ggRankTwo Bs r₁ r₂ : Set G) := by
    rw [ggRankOne]
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨huC, k, hk⟩
    have huS : u ∈ ggRankOne Bs r := Subgroup.subset_closure ⟨huC, k, hk⟩
    have huN₁ : u ∈ Subgroup.normalizer (ggHyperplane Bs r₁ : Set G) :=
      ggRankOne_le_normalizer_ggHyperplane hBs hSC hr hrI h6 hr₁ hc₁ hne₁ huS
    have huN₂ : u ∈ Subgroup.normalizer (ggHyperplane Bs r₂ : Set G) :=
      ggRankOne_le_normalizer_ggHyperplane hBs hSC hr hrI h6 hr₂ hc₂ hne₂ huS
    have huNinf : u ∈ Subgroup.normalizer
        ((ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂ : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨huN₁, huN₂⟩
    have huNC : u ∈ Subgroup.normalizer
        (Subgroup.centralizer
          ((ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂ : Subgroup G) : Set G) : Set G) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
        (ggHyperplane Bs r₁ ⊓ ggHyperplane Bs r₂) huNinf
    have huW : u ∈ Subgroup.normalizer (ggRankTwo Bs r₁ r₂ : Set G) := by
      rw [ggRankTwo]
      exact ggMem_normalizer_oTwoPrime huNC
    obtain ⟨a, ha1, haS, har, haz⟩ := exists_root_ggRankOne hBs hSC hr₁I h6₁
    obtain ⟨b, hb1, hbS, hbr, hbz⟩ := exists_root_ggRankOne hBs hSC hr₂I h6₂
    have hra : r a = a :=
      apply_eq_self_of_commute_of_isReflection (p := 3) (by norm_num) hBs hr hr₁ hc₁ hne₁ har
    have hrb : r b = b :=
      apply_eq_self_of_commute_of_isReflection (p := 3) (by norm_num) hBs hr hr₂ hc₂ hne₂ hbr
    have haH : (a : G) ∈ ggHyperplane Bs r := (mem_ggHyperplane_iff' a).mpr hra
    have hbH : (b : G) ∈ ggHyperplane Bs r := (mem_ggHyperplane_iff' b).mpr hrb
    have hua : u * (a : G) = (a : G) * u :=
      ((Subgroup.mem_centralizer_iff.mp huC) (a : G) haH).symm
    have hub : u * (b : G) = (b : G) * u :=
      ((Subgroup.mem_centralizer_iff.mp huC) (b : G) hbH).symm
    have hcU : ∀ g ∈ ggRankOne Bs r₁, g ^ 3 = 1 → u * g = g * u := by
      intro g hg hg3
      rcases Subgroup.mem_zpowers_iff.mp (haz g hg hg3) with ⟨n, hn⟩
      rw [← hn]
      exact (show Commute u (a : G) from hua).zpow_right n
    have hcV : ∀ g ∈ ggRankOne Bs r₂, g ^ 3 = 1 → u * g = g * u := by
      intro g hg hg3
      rcases Subgroup.mem_zpowers_iff.mp (hbz g hg hg3) with ⟨n, hn⟩
      rw [← hn]
      exact (show Commute u (b : G) from hub).zpow_right n
    have hUV : ∀ g ∈ ggRankOne Bs r₁, g ∈ ggRankOne Bs r₂ → g ^ 3 = 1 → g = 1 :=
      rankOne_inf_cube_eq_one hBs hSC hNT hr₁ hr₂ hr₁I hr₂I h6₁ h6₂ hne
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (commute_of_unitaryBlockStandardPair hK hpair hUV hk huW hcU hcV z hz).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

end CFSG.StandardType.QTwo

end
