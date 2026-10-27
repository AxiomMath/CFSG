module

public import CFSG.RankThree.PartTwo.Sec21.Item229URoots

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly (IsElemAbelian)
open URoots (V3 coord_mul coord_pow orderOf_coord card_zpowers_coord)
open Matrix
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_centralizer_of_fixes_four [Finite G] {V : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) {a : G} (haV : a ∈ Subgroup.normalizer (V : Set G)) (ha3 : a ^ 3 = 1)
    {v : G} (hvV : v ∈ V) (hv1 : v ≠ 1) (hav : a * v * a⁻¹ = v) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  have hconj : ∀ x ∈ V, a * x * a⁻¹ ∈ V := fun x hx => (Subgroup.mem_normalizer_iff.mp haV x).mp hx
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← sq]; exact hVe.2 x hx
  have key : ∀ x ∈ V, a * x * a⁻¹ = x := by
    intro x hx
    by_contra hne
    set y := a * x * a⁻¹ with hy
    have hyV : y ∈ V := hconj x hx
    have hyvx : y = v * x := by
      by_contra hyvx
      have hx1 : x ≠ 1 := by
        rintro rfl
        apply hne
        rw [hy]
        group
      have hxv : x ≠ v := by rintro rfl; exact hne hav
      have hy1 : y ≠ 1 := by
        intro h
        apply hx1
        calc x = a⁻¹ * y * a := by rw [hy]; group
          _ = 1 := by rw [h]; group
      have hyv : y ≠ v := by
        intro h
        apply hxv
        calc x = a⁻¹ * y * a := by rw [hy]; group
          _ = a⁻¹ * (a * v * a⁻¹) * a := by rw [h, hav]
          _ = v := by group
      have hvx1 : v * x ≠ 1 := fun h => hxv (by
        calc x = v * (v * x) := by rw [← mul_assoc, hsq v hvV, one_mul]
          _ = v := by rw [h, mul_one])
      have hvxv : v * x ≠ v := fun h => hx1 (by
        calc x = v * (v * x) := by rw [← mul_assoc, hsq v hvV, one_mul]
          _ = 1 := by rw [h, hsq v hvV])
      have hvxx : v * x ≠ x := fun h => hv1 (by
        calc v = v * x * x := by rw [mul_assoc, hsq x hx, mul_one]
          _ = 1 := by rw [h, hsq x hx])
      have hinj : Function.Injective (fun i : Fin 5 => (![(1 : G), v, x, y, v * x] i)) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first
          | exact absurd hij.symm hv1 | exact absurd hij hv1
          | exact absurd hij.symm hx1 | exact absurd hij hx1
          | exact absurd hij.symm hy1 | exact absurd hij hy1
          | exact absurd hij.symm hvx1 | exact absurd hij hvx1
          | exact absurd hij.symm hxv | exact absurd hij hxv
          | exact absurd hij.symm hyv | exact absurd hij hyv
          | exact absurd hij.symm hvxv | exact absurd hij hvxv
          | exact absurd hij.symm hne | exact absurd hij hne
          | exact absurd hij.symm hvxx | exact absurd hij hvxx
          | exact absurd hij.symm hyvx | exact absurd hij hyvx
      have hmem : ∀ i : Fin 5, ![(1 : G), v, x, y, v * x] i ∈ V := by
        intro i
        fin_cases i
        · exact V.one_mem
        · exact hvV
        · exact hx
        · exact hyV
        · exact V.mul_mem hvV hx
      have h5 := Nat.card_le_card_of_injective
        (fun i : Fin 5 => (⟨_, hmem i⟩ : V)) (fun i j h => hinj (congrArg Subtype.val h))
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hV4] at h5
      omega
    have h2 : a * y * a⁻¹ = x := by
      rw [hyvx, show a * (v * x) * a⁻¹ = (a * v * a⁻¹) * (a * x * a⁻¹) by group, hav, ← hy,
        hyvx, ← mul_assoc, hsq v hvV, one_mul]
    have h3 : a ^ 3 * x * (a ^ 3)⁻¹ = y := by
      calc a ^ 3 * x * (a ^ 3)⁻¹ = a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev]
            group
        _ = y := by rw [← hy, h2]
    rw [ha3, one_mul, inv_one, mul_one] at h3
    exact hne h3.symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * a = a * x * a⁻¹ * a := by rw [key x hx]
    _ = a * x := by group

end CFSG.RankThree.PartTwo.Sec21
