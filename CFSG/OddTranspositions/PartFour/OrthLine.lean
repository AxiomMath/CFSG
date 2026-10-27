module

public import CFSG.OddTranspositions.PartFour.RootLift
public import CFSG.OddTranspositions.PartFour.LinePolar
import CFSG.OddTranspositions.PartFour.LineCount
import CFSG.OddTranspositions.PartFour.SideConditions

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem orthLine_not_isSolvable (hC : HypothesisC D)
    {x y : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hxy : orderOf (x * y) ≠ 1) : ¬ Group.IsSolvable (Halpha D hC.alpha) := by
  intro hsol
  haveI := hsol
  have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ :=
    top_le_iff.mp (le_sSup ⟨Subgroup.normal_top, inferInstance⟩)
  apply hxy
  rw [orderOf_eq_one_iff]
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective _ (x * y)
  rw [← hz, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, htop]
  exact Subgroup.mem_top z

theorem false_of_lineMem_of_class (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (hf : 2 ≤ f)
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    (hcount : (perpMem (imageClass hC) '' lineMem (imageClass hC) v w).ncard ≤ 2 ^ f)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ f + 1) : False := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨x, hx, y, hy, hxy⟩ := hord
  have hHns := orthLine_not_isSolvable hC (x := x) (y := y) (by omega)
  have hn3 := not_threeTransp_of_pow_ne_one hC (hS₀ hx) (hS₀ hy) (fun k hk hk3 h => by
    have := Nat.le_of_dvd hk (orderOf_dvd_of_pow_eq_one h)
    omega)
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨j, hj, hm⟩ := exists_ncard_orbit_Malpha_eq_two_pow_mul_of_class h89 h113 hC hrad hW
    hn3 hMZ hHns S₀ hS₀ (by omega) hinv hgen hconj ⟨x, hx, y, hy, hxy⟩ hβ
  have hle := ncard_blockLine_le h89 h113 hC hrad hW hn3 hMZ hv hw hvw hne hβ
  have hΔ := ncard_blockLine_diff_eq h113 hC hrad hn3 hHns hβ
  have hαℓ : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hℓ := Set.ncard_diff_singleton_add_one hαℓ (Set.toFinite _)
  have hβΔ : β ∈ blockLine D hC.alpha β \ {hC.alpha} :=
    ⟨right_mem_blockLine hβ.1 hβ.2.1, fun h => hβ.2.2.1 (Set.mem_singleton_iff.mp h)⟩
  have hr : 0 < (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, Set.mem_image_of_mem _ hβΔ⟩
  have hmq : 2 ^ f ≤ 2 ^ (f * j) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right f hj)
  have hrm := Nat.le_mul_of_pos_left ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard hr
  omega

end CFSG.OddTranspositions.PartFour
