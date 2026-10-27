module

public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.RankCount

variable {G : Type*} [Group G] [Finite G]

theorem le_localRank_of_fixed_quotient {V W F : Subgroup G} (hWF : W ≤ F) (hFV : F ≤ V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (h3 : ∀ x ∈ V, x ^ 3 = 1)
    {t : G} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (htF : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ W)
    {a c : ℕ} (ha : Nat.card ↥(W ⊓ Subgroup.centralizer ({t} : Set G)) = 3 ^ a)
    (hc : Nat.card F = 3 ^ c * Nat.card W) :
    a + c ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  set C : Subgroup G := F ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have htt : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hsup : W ⊔ C = F := by
    refine le_antisymm (sup_le hWF inf_le_left) fun f hf => ?_
    set w := t * f * t⁻¹ * f⁻¹ with hw
    have hwW : w ∈ W := htF f hf
    have hfV : f ∈ V := hFV hf
    have htf : t * f * t⁻¹ ∈ V := htV f hfV
    have htf' : t * f * t⁻¹ = w * f := by rw [hw, inv_mul_cancel_right]
    set u := f * (t * f * t⁻¹) with hu
    have huF : u ∈ F := mul_mem hf (by rw [htf']; exact mul_mem (hWF hwW) hf)
    have huC : u ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : t * u * t⁻¹ = u := by
        calc t * u * t⁻¹ = t * f * t⁻¹ * (t * (t * f * t⁻¹) * t⁻¹) := by rw [hu]; group
          _ = t * f * t⁻¹ * f := by
            congr 1
            calc t * (t * f * t⁻¹) * t⁻¹ = (t * t) * f * (t⁻¹ * t⁻¹) := by group
              _ = f := by rw [← pow_two, ht2, htt, ← pow_two, ht2, one_mul, mul_one]
          _ = u := by rw [hu]; exact hcomm _ htf _ hfV
      calc u * t = t * u * t⁻¹ * t := by rw [e]
        _ = t * u := by group
    have hf3 : f * f * f = 1 := by rw [← pow_three']; exact h3 f hfV
    have hwf : w * f = f * w := hcomm _ (hFV (hWF hwW)) _ hfV
    have hfu : f = w * u⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, hu, htf', ← mul_assoc, hwf, ← mul_assoc, hf3, one_mul]
    rw [hfu]
    exact mul_mem (Subgroup.mem_sup_left hwW) (Subgroup.mem_sup_right (inv_mem ⟨huF, huC⟩))
  have hWC : ∀ x ∈ W, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    hcomm x (hFV (hWF hx)) y (hFV (Subgroup.mem_inf.mp hy).1)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W C hWC).1
  have hinf : W ⊓ C = W ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hCdef, ← inf_assoc, inf_eq_left.mpr hWF]
  rw [hsup, hinf, ha, hc] at hprod
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hCcard : Nat.card C = 3 ^ (a + c) := by
    rw [pow_add]
    have : Nat.card W * (3 ^ c * 3 ^ a) = Nat.card W * Nat.card C := by
      rw [← hprod]; ring
    have h := Nat.eq_of_mul_eq_mul_left hWpos this
    rw [← h, mul_comm]
  refine CFSG.RankThree.PartTwo.Sec3.le_localRank_of_commute_involution (by norm_num) ht1 ht2
    ⟨⟨fun x y => Subtype.ext (hcomm _ (hFV (Subgroup.mem_inf.mp x.2).1) _
      (hFV (Subgroup.mem_inf.mp y.2).1))⟩⟩
    (fun x hx => h3 x (hFV (Subgroup.mem_inf.mp hx).1)) inf_le_right hCcard

end CFSG.RankThree.PartTwo.Sec21.FF81.RankCount
