module

public import CFSG.RankThree.GF2n.Stroth80.Sec717CorBWC
public import CFSG.RankThree.GF2n.Stroth80.Sec717LElemAb

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec717InvolutionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    ∀ x ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
      ∀ y ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
        x ≠ 1 → y ≠ 1 → x * x = 1 → y * y = 1 →
          ∃ h : ↥(bar M Q (H0 M Z)), h * x * h⁻¹ = y

@[expose] def Sec717NormalizeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    ∀ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), z ≠ 1 →
      ∀ h : ↥(bar M Q (H0 M Z)),
        h * z * h⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) →
        h * z * h⁻¹ ∉ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) →
          conjSubgroup h ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) =
            (bar M Q L).subgroupOf (bar M Q (H0 M Z))

@[expose] def Sec717WCStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    ∀ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), z ≠ 1 →
      ∀ g : ↥(bar M Q (H0 M Z)),
        conjSubgroup g ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) ≤
            Subgroup.centralizer {z} →
          conjSubgroup g ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) =
            (bar M Q L).subgroupOf (bar M Q (H0 M Z))

theorem sec717CorBHyp_of_parts (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hCN : Sec7CommNStatement)
    (hCM : Sec7CentreMpStatement) (hZc : Sec7ZCardStatement)
    (hInv : Sec717InvolutionStatement) (hNorm : Sec717NormalizeStatement)
    (hWC : Sec717WCStatement) : Sec717CorBHypStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0C hTI L hL hLn hcase hmove
  have hL' := hL
  unfold Sec717L at hL'
  have hLc : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ Q := hL'.2.2.2.2.1
  have hLsq : ∀ x ∈ L, x * x ∈ Q :=
    sec717L_sq_mem_Q h51 hA hPts hCN hCM hZc hc hs hp3 hZ0 hL
  have hLM : L ≤ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp (hL'.2.1 hx)).1
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hZM : ∀ z ∈ Z0, z ∈ M := fun z hz => hc.Rt_le_M t (Ctx.mem_CN.mp (hZN hz)).1
  have hZH : ∀ z ∈ Z0, z ∈ H0 M Z := fun z hz => hc.Rt_le_H0 t (Ctx.mem_CN.mp (hZN hz)).1
  have hT : IsElemAbelian 2 ((bar M Q L).subgroupOf (bar M Q (H0 M Z))) :=
    sec717_bar_isElemAbelian hLM hLc hLsq
  have hZT : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
    intro z hz
    obtain ⟨s, hs0, hsz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hz)
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
      ⟨s, Subgroup.mem_subgroupOf.mpr (hL'.2.2.2.2.2 (Subgroup.mem_subgroupOf.mp hs0)), hsz⟩)
  have hZQ : ¬ Z0 ≤ Q := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    have h2 := hZc G M Q Z B hc n t hs Z0 hZ0
    have h3 : 0 < Nat.card Q := Nat.card_pos
    have h4 := hc.hyp.q4
    rw [h2] at h1
    nlinarith
  obtain ⟨z0, hz0Z, hz0Q⟩ : ∃ z0 ∈ Z0, z0 ∉ Q := by
    by_contra hcon
    exact hZQ (fun z hz => by_contra fun hzQ => hcon ⟨z, hz, hzQ⟩)
  have hz0M : z0 ∈ M := hZM z0 hz0Z
  have hz0H : z0 ∈ H0 M Z := hZH z0 hz0Z
  have hZs : ∃ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), z ≠ 1 := by
    refine ⟨⟨QuotientGroup.mk (⟨z0, hz0M⟩ : ↥M), Subgroup.mem_map.mpr
      ⟨⟨z0, hz0M⟩, Subgroup.mem_subgroupOf.mpr hz0H, rfl⟩⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
        ⟨⟨z0, hz0M⟩, Subgroup.mem_subgroupOf.mpr hz0Z, rfl⟩)
    · intro h
      apply hz0Q
      have h1 : (QuotientGroup.mk (⟨z0, hz0M⟩ : ↥M) : ↥M ⧸ Q.subgroupOf M) = 1 :=
        congrArg Subtype.val h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
  have sq1 : ∀ x ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hT.2 x hx
  have hC1 : ∀ x ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
      ∀ y ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), x ≠ 1 → y ≠ 1 →
        ∃ h : ↥(bar M Q (H0 M Z)), h * x * h⁻¹ = y :=
    fun x hx y hy hx1 hy1 =>
      hInv G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0C hTI L hL hLn hcase hmove x hx y hy hx1 hy1
        (sq1 x hx) (sq1 y hy)
  have hC2 := hNorm G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0C hTI L hL hLn hcase hmove
  have hC3 := hWC G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0C hTI L hL hLn hcase hmove
  exact sec717_corBHyp_of_isWC (sec717_isWC_of_data hT hZT hZs hC1 hC2 hC3)

end CFSG.RankThree.GF2n.Stroth80
