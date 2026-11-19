module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormLB
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec717ZNStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q

@[expose] def Sec717CorBHypStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    CorBHyp ((bar M Q L).subgroupOf (bar M Q (H0 M Z)))

@[expose] def Sec717RecogStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    CentTwoInV hc t Z0 →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    CorBHyp ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) → FStarL6 M Q Z

@[expose] def Sec717CaseOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    CentTwoInV hc t Z0 →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∀ g ∈ M, conjSubgroup g Z0 ≤ NormH0 M Z Z0 → conjSubgroup g Z0 ≤ hc.CN t) →
    FStarL6 M Q Z

theorem step717CaseA_of_parts (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hNR : Sec7NormZ0Statement)
    (hZV : Sec7ZVStatement) (h713 : Stroth713Statement) (hZN : Sec717ZNStatement)
    (hCent : Sec715CentStatement) (hCase1 : Sec717CaseOneStatement)
    (hMove : Sec717MoveStatement) (hCorB : Sec717CorBHypStatement)
    (hRecog : Sec717RecogStatement) : Step717CaseAStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 L hL hLn
  have hn4 : ¬ OmegaPlusNat hc t 4 := fun h => by have := hp3.eq_of_plus h; omega
  have hnom : ¬ OmegaMinusNat hc t 2 := fun h => by
    have := omegaPlusNat_eq_omegaMinusNat (by norm_num) hp3 h
    omega
  have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
  have hF := h713 G M Q Z B hc n t hs hn4 Z0 hZ0
  have hZN' := hZN G M Q Z B hc n t hs hp3 Z0 hZ0
  have hN2 := sec7_CN_pgroup_bar h34 h311a hc hs
  have hC : CentTwoInV hc t Z0 := fun k _ hk2 hkc =>
    hCent G M Q Z B hc n t hs (Or.inl hp3) Z0 hZ0 hZN' k hk2 hkc
  by_cases hcase1 : ∀ g ∈ M, conjSubgroup g Z0 ≤ NormH0 M Z Z0 → conjSubgroup g Z0 ≤ hc.CN t
  · exact hCase1 G M Q Z B hc n t hs hp3 Z0 hZ0 hZN' hTI hF hC L hL hLn hcase1
  · push Not at hcase1
    obtain ⟨g, hg, hgK, hgN⟩ := hcase1
    obtain ⟨h, hh, hgh⟩ := Ctx.exists_H0_conj hc hs hZ0 hZt hZcard hN2 hTI hC hg
    have hcase2 : ∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧
        ¬ conjSubgroup h Z0 ≤ hc.CN t := ⟨h, hh, hgh ▸ hgK, hgh ▸ hgN⟩
    have hmove := hMove G M Q Z B hc n t hs hp3 Z0 hZ0 hZN' hTI L hL hLn hcase2
    have hcorb := hCorB G M Q Z B hc n t hs hp3 Z0 hZ0 hZN' hTI L hL hLn hcase2 hmove
    exact hRecog G M Q Z B hc n t hs hp3 Z0 hZ0 hZN' hTI hF hC L hL hLn hcorb

end CFSG.RankThree.GF2n.Stroth80
