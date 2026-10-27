module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.PerfectAutomorphisms

theorem involutionCentralizerOn_of_facts (Sh : ShapePred)
    (hSh : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L → OddShape5 L)
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      OuterFixedNotElem (↥L ⧸ Subgroup.center ↥L)) :
    InvolutionCentralizerOn Sh := by
  intro Y _ _ L b hLsh hb hb2 hx
  obtain ⟨hq, hodd, -⟩ := hSh Y L hLsh
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  let α : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨b, hb⟩
  have hαcoe : ∀ x : ↥L, ((α x : ↥L) : Y) = b * (x : Y) * b⁻¹ := by
    intro x
    dsimp only [α]
    rfl
  have hbn : (⟨b, hb⟩ : ↥(Subgroup.normalizer (L : Set Y))) * ⟨b, hb⟩ = 1 := by
    ext
    exact hb2
  have hα : α * α = 1 := by
    dsimp only [α]
    rw [← map_mul, hbn, map_one]
  let Z : Subgroup ↥L := Subgroup.center ↥L
  by_cases hinner : ∃ g : ↥L, ∀ x : ↥L, α x = g * x * g⁻¹
  · obtain ⟨g, hg⟩ := hinner
    let c₀ : Y := (g : Y)⁻¹ * b
    have hb_eq : b = (g : Y) * c₀ := by
      dsimp only [c₀]
      group
    have hc0 : c₀ ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcl : b * l * b⁻¹ = (g : Y) * l * (g : Y)⁻¹ := by
        have hval := congrArg Subtype.val (hg ⟨l, hl⟩)
        rw [hαcoe ⟨l, hl⟩] at hval
        simpa using hval
      have hconj : c₀ * l * c₀⁻¹ = l := by
        have h1 : c₀ * l * c₀⁻¹ = (g : Y)⁻¹ * (b * l * b⁻¹) * (g : Y) := by
          dsimp only [c₀]
          group
        rw [hcl] at h1
        rw [h1]
        group
      have hcl' : c₀ * l = l * c₀ := by
        have h2 := congrArg (fun t : Y => t * c₀) hconj
        simpa [mul_assoc] using h2
      exact hcl'.symm
    have hg2Z : g ^ 2 ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hαα : α (α x) = x := by
        have h2 := congrArg (fun f : MulAut ↥L => f x) hα
        simpa [MulAut.mul_apply] using h2
      have hfix : g * (g * x * g⁻¹) * g⁻¹ = x := by
        rw [hg x] at hαα
        rw [hg (g * x * g⁻¹)] at hαα
        exact hαα
      have h2 := congrArg (fun t : ↥L => t * (g * g)) hfix
      have h3 : g * g * x = x * g * g := by simpa [mul_assoc] using h2
      simpa [pow_two, mul_assoc] using h3.symm
    have hZodd : Odd (Nat.card Z) := hodd
    have hx2pow : (g ^ 2 : ↥L) ^ (Nat.card Z) = 1 := by
      have hcard := pow_card_eq_one' (x := (⟨g ^ 2, hg2Z⟩ : Z))
      have hcoe := congrArg (fun z : Z => (z : ↥L)) hcard
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hcoe
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul hx2pow hZodd 1
    let w : ↥L := (g ^ 2) ^ k
    have hwZ : w ∈ Z := Subgroup.pow_mem Z hg2Z k
    have hww : w * w = g ^ 2 := by
      have h2 : w * w = (g ^ 2) ^ (2 * k) := by
        dsimp only [w]
        rw [← pow_add]
        congr 1
        omega
      rw [h2, ← hk, pow_one]
    let s : ↥L := g * w⁻¹
    have hss : s * s = 1 := by
      have hwinvcomm : w⁻¹ * (g : ↥L) = (g : ↥L) * w⁻¹ :=
        (Subgroup.mem_center_iff.mp (Subgroup.inv_mem Z hwZ) g).symm
      calc s * s = (g * w⁻¹) * (g * w⁻¹) := rfl
        _ = g * (w⁻¹ * g) * w⁻¹ := by group
        _ = g * (g * w⁻¹) * w⁻¹ := by rw [hwinvcomm]
        _ = (g * g) * (w⁻¹ * w⁻¹) := by group
        _ = (w * w) * (w⁻¹ * w⁻¹) := by rw [hww, pow_two]
        _ = 1 := by group
    have hwcent : (w : Y) ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcommw : (⟨l, hl⟩ : ↥L) * w = w * (⟨l, hl⟩ : ↥L) :=
        Subgroup.mem_center_iff.mp hwZ _
      simpa using congrArg Subtype.val hcommw
    have hc : (w : Y) * c₀ ∈ Subgroup.centralizer (L : Set Y) :=
      Subgroup.mul_mem _ hwcent hc0
    refine ⟨(s : Y), s.2, ?_, (w : Y) * c₀, hc, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_one] using congrArg Subtype.val hss
    · rw [hb_eq]
      dsimp only [s]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  · exfalso
    have hαbar : onCenterQuotient α * onCenterQuotient α = 1 := by
      have h2 := map_mul (centerQuotientHom ↥L) α α
      rw [hα, map_one] at h2
      exact h2.symm
    have hnotinner : ¬ ∃ g : ↥L ⧸ Z, ∀ y, onCenterQuotient α y = g * y * g⁻¹ := by
      intro hbar
      exact hinner (isInner_of_onCenterQuotient_inner α hbar)
    obtain ⟨xbar, hxbar_fix, hxbar_sq⟩ :=
      h Y L hLsh (onCenterQuotient α) hαbar hnotinner
    obtain ⟨x, hxfix, hxmk⟩ :=
      exists_fixed_lift_centerQuotient hodd α hα xbar hxbar_fix
    have hcomm : (x : Y) * b = b * (x : Y) := by
      have hxval : b * (x : Y) * b⁻¹ = (x : Y) := by
        have hval := congrArg Subtype.val hxfix
        rw [hαcoe x] at hval
        exact hval
      have h2 : b * (x : Y) = (x : Y) * b := by
        have h3 := congrArg (fun t : Y => t * b) hxval
        simpa [mul_assoc] using h3
      exact h2.symm
    have hx2Z : x * x ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro l
      have hY := hx (x : Y) x.2 hcomm (l : Y) l.2
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hY.symm
    have hone : (QuotientGroup.mk (x * x) : ↥L ⧸ Z) = 1 :=
      (QuotientGroup.eq_one_iff (x * x)).mpr hx2Z
    have hxbar2 : xbar * xbar = 1 := by
      have hmul : (QuotientGroup.mk (x * x) : ↥L ⧸ Z)
          = (QuotientGroup.mk x : ↥L ⧸ Z) * (QuotientGroup.mk x : ↥L ⧸ Z) :=
        QuotientGroup.mk_mul Z x x
      rw [hone] at hmul
      rw [hxmk] at hmul
      exact hmul.symm
    exact hxbar_sq hxbar2

end CFSG.LocalAnalysis.WeakClosure81

end
