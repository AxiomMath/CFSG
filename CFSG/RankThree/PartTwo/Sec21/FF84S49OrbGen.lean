module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCount
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem op2_conjBy_ge (g : G) (H : Subgroup G) : conjBy g (Op 2 H) ≤ Op 2 (conjBy g H) := by
  refine op2_of_normal (conjBy_le_iff.2 (op2_le H)) ?_ ((op2_isPGroup H).map (MulAut.conj g).toMonoidHom)
  refine normal_subgroupOf_of ?_ (conjBy_le_iff.2 (op2_le H))
  intro h hh
  rw [mem_nor_conjBy]
  exact le_nor_op2 H (mem_conjBy_iff.1 hh)

theorem op2_conjBy (g : G) (H : Subgroup G) : Op 2 (conjBy g H) = conjBy g (Op 2 H) := by
  refine le_antisymm ?_ (op2_conjBy_ge g H)
  have h := op2_conjBy_ge g⁻¹ (conjBy g H)
  rw [conjBy_inv_conjBy] at h
  have h2 := conjBy_le_iff (g := g) |>.2 h
  rwa [conjBy_conjBy_inv] at h2

theorem cen_conjBy (g x : G) : Cen (g * x * g⁻¹) = conjBy g (Cen x) := conjBy_cen.symm

theorem cen_le_nor_conj {S : Subgroup G} {g : G} (hg : g ∈ Nor S) (x : G) :
    Cen (g * x * g⁻¹) ≤ Nor S ↔ Cen x ≤ Nor S := by
  constructor
  · intro h w hw
    have h1 : g * w * g⁻¹ ∈ Cen (g * x * g⁻¹) := by
      rw [cen_conjBy]
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    have h2 := mul_mem (mul_mem (inv_mem hg) (h h1)) hg
    simpa [mul_assoc] using h2
  · intro h w hw
    have h1 : g⁻¹ * w * g ∈ Cen x := by
      rw [cen_conjBy, mem_conjBy_iff] at hw
      exact hw
    have h2 := mul_mem (mul_mem hg (h h1)) (inv_mem hg)
    simpa [mul_assoc] using h2

theorem order5_move {S : Subgroup G} (hS : IsElemAb 2 6 S) {y : G} (hy : orderOf y = 5)
    (hn : y ∈ Nor S) (hnc : ¬ S ≤ Cen y) {X : Set G} (hXS : X ⊆ S) (hX9 : X.ncard = 9)
    (h1 : (1 : G) ∉ X) : ∃ u ∈ X, y * u * y⁻¹ ∉ X := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy5 : y ^ 5 = 1 := hy ▸ pow_orderOf_eq_one y
  have hcard := B_order5_fixed hS hy hn hnc
  let f0 : ↥X → ↥X := fun u => ⟨y * u * y⁻¹, hcon u.1 u.2⟩
  let f : Function.End ↥X := f0
  have hfk : ∀ (k : ℕ) (u : ↥X), ((f0^[k] u : ↥X) : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [Function.iterate_succ_apply', show ((f0 (f0^[k] u) : ↥X) : G) =
        y * ((f0^[k] u : ↥X) : G) * y⁻¹ from rfl, ih]
      simp [pow_succ', mul_assoc]
  have hf : f ^ 5 ^ 1 = 1 := by
    show f0^[5 ^ 1] = id
    funext u
    apply Subtype.ext
    rw [hfk, pow_one, hy5]
    simp
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hX : Nat.card ↥X = 9 := by
    rw [Nat.card_coe_set_eq]; exact hX9
  have hfix : Nat.card f.fixedPoints ≤ 3 := by
    set T : Set G := ((S ⊓ Cen y : Subgroup G) : Set G) \ {1} with hT
    have hT3 : T.ncard = 3 := by
      rw [hT, Set.ncard_diff_singleton_of_mem (one_mem (S ⊓ Cen y))]
      have : ((S ⊓ Cen y : Subgroup G) : Set G).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hcard
      omega
    let g : f.fixedPoints → ↥T := fun u =>
      ⟨(u.1 : ↥X).1, by
        have hfu : y * ((u.1 : ↥X) : G) * y⁻¹ = ((u.1 : ↥X) : G) := congrArg Subtype.val u.2
        refine ⟨⟨hXS (u.1 : ↥X).2, ?_⟩, ?_⟩
        · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
          calc ((u.1 : ↥X) : G) * y = (y * ((u.1 : ↥X) : G) * y⁻¹) * y := by rw [hfu]
            _ = y * ((u.1 : ↥X) : G) := by group
        · intro h
          exact h1 (by rw [Set.mem_singleton_iff] at h; exact h ▸ (u.1 : ↥X).2)⟩
    have hginj : Function.Injective g := by
      intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext this)
    have h3 : Nat.card f.fixedPoints ≤ Nat.card ↥T := Nat.card_le_card_of_injective g hginj
    rw [Nat.card_coe_set_eq T, hT3] at h3
    exact h3
  rw [hX] at hmod
  have : 9 % 5 = Nat.card f.fixedPoints % 5 := hmod
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
