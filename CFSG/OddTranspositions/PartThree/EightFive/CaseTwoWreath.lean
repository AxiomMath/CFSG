module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.PartThree.Ten.SwapBlocks
public import Certificates.Certificate43
public import Certificates.Certificate113

import CFSG.OddTranspositions.PartThree.Ten.Assembly
import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open Equiv WreathEndgame

theorem four_dvd_orderOf_swap_mul_swap_mul_swap {m : ℕ} {i j k l p r : Fin m} (hij : i ≠ j)
    (hkl : k ≠ l) (hpr : p ≠ r) (hdisj : (swap i j).Disjoint (swap k l))
    (h1 : Odd (orderOf (swap i j * swap p r))) (h2 : Odd (orderOf (swap k l * swap p r))) :
    4 ∣ orderOf (swap i j * swap k l * swap p r) := by
  obtain ⟨hik, hil, hjk, hjl⟩ := (swapDisjoint_iff hij hkl).1 hdisj
  have core : ∀ {i j k l : Fin m}, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      4 ∣ orderOf (swap i j * swap k l * swap i k) := by
    intro i j k l hij hik hil hjk hjl hkl
    have h4 : orderOf (finRotate 4) = 4 :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
    have hu : Function.Injective ![i, l, k, j] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
    rw [← h4]
    refine CentralSymSplit.orderOf_dvd_of_apply_eq ![i, l, k, j] hu _ (finRotate 4) ?_
    intro x
    fin_cases x <;>
      simp [swap_apply_of_ne_of_ne, hik, hil, hjk, hjl, hij.symm, hik.symm, hil.symm,
        hjk.symm, hjl.symm, hkl.symm]
  have key : ∀ {p r : Fin m}, (p = i ∨ p = j) → (r = k ∨ r = l) →
      4 ∣ orderOf (swap i j * swap k l * swap p r) := by
    intro p r hp hr
    rcases hp with hp | hp <;> rcases hr with hr | hr <;> rw [hp, hr]
    · exact core hij hik hil hjk hjl hkl
    · rw [swap_comm k l]
      exact core hij hil hik hjl hjk hkl.symm
    · rw [swap_comm i j]
      exact core hij.symm hjk hjl hik hil hkl
    · rw [swap_comm i j, swap_comm k l]
      exact core hij.symm hjl hjk hil hik hkl.symm
  have hmeet : ∀ {a b : Fin m}, a ≠ b → Odd (orderOf (swap a b * swap p r)) →
      p = a ∨ p = b ∨ r = a ∨ r = b := by
    intro a b hab hodd
    by_contra hcon
    push Not at hcon
    obtain ⟨hpa, hpb, hra, hrb⟩ := hcon
    rw [WreathClass.orderOf_swap_mul_swap hab hpr (Ne.symm hpa) (Ne.symm hra) (Ne.symm hpb)
      (Ne.symm hrb)] at hodd
    exact absurd hodd (by decide)
  rcases hmeet hij h1 with hp | hp | hr | hr
  · refine key (Or.inl hp) ?_
    rcases hmeet hkl h2 with h | h | h | h
    · exact absurd (hp.symm.trans h) hik
    · exact absurd (hp.symm.trans h) hil
    · exact Or.inl h
    · exact Or.inr h
  · refine key (Or.inr hp) ?_
    rcases hmeet hkl h2 with h | h | h | h
    · exact absurd (hp.symm.trans h) hjk
    · exact absurd (hp.symm.trans h) hjl
    · exact Or.inl h
    · exact Or.inr h
  · rw [swap_comm p r]
    refine key (Or.inl hr) ?_
    rcases hmeet hkl h2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hr.symm.trans h) hik
    · exact absurd (hr.symm.trans h) hil
  · rw [swap_comm p r]
    refine key (Or.inr hr) ?_
    rcases hmeet hkl h2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hr.symm.trans h) hjk
    · exact absurd (hr.symm.trans h) hjl

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem isSwapBlock_image {f m : ℕ} (Φ : G ≃* L2Wreath f m)
    (hΦ : ∀ x, x ∈ D ↔ Φ x ∈ swapSet f m) {β : Set G} (hβ : IsBlock D β) :
    SwapBlocks.IsSwapBlock (Φ '' β) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hΦ x).1 (hβ.subset hx)
  · rintro w _ ⟨x, hx, rfl⟩ ⟨y, hy, hyw⟩
    set g : G := Φ.symm w with hg
    have hgw : Φ g = w := by simp [hg]
    have hgx : g * x * g⁻¹ = y := Φ.injective (by rw [hyw, map_mul, map_mul, map_inv, hgw])
    have hgN : g ∈ Subgroup.normalizer β := by
      by_contra hgn
      exact Set.disjoint_left.mp (hβ.disjoint_conj hgn)
        (show g * x * g⁻¹ ∈ β by rw [hgx]; exact hy) ⟨x, hx, rfl⟩
    rw [SwapBlocks.mem_conjStab]
    intro x'
    obtain ⟨y', rfl⟩ := Φ.surjective x'
    have hconj : w * Φ y' * w⁻¹ = Φ (g * y' * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hgw]
    rw [hconj]
    constructor
    · rintro ⟨z', hz', hz'eq⟩
      have hz'y : z' = g * y' * g⁻¹ := Φ.injective hz'eq
      refine ⟨y', ?_, rfl⟩
      have := (hgN y').2 (hz'y ▸ hz')
      exact this
    · rintro ⟨z', hz', hz'eq⟩
      have hz'y : z' = y' := Φ.injective hz'eq
      exact ⟨g * y' * g⁻¹, (hgN y').1 (hz'y ▸ hz'), rfl⟩

theorem faithfulOnBlocks_of_thirdKind_of_mem_alpha
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (hu : u ∈ hC.alpha) (htri : IsTriangle D u w v) (hthird : IsThirdKind u w v)
    (hv : v ∈ DalphaStar D hC.alpha) {a : G} (ha : a ∈ hC.alpha) (hau : a ≠ u) :
    FaithfulOnBlocks hC.alpha := by
  classical
  by_contra hF
  have hK : blockKernel hC.alpha ≠ ⊥ := fun h =>
    hF (faithfulOnBlocks_iff_blockKernel_eq_bot.mpr h)
  obtain ⟨f, m, hf, Φ, hΦ⟩ := exists_l2Wreath_class_of_blockKernel_ne_bot hC hrad hK
  have hS := hC.setup
  have hD := hS.oddT
  have hblock := hC.isBlock_alpha
  have huD : u ∈ D := hblock.subset hu
  have hm2 : 2 ≤ m := two_le_of_mem_swapSet (hΦ u huD)
  have hiff : ∀ x, x ∈ D ↔ Φ x ∈ swapSet f m := mem_D_iff_mem_swapSet hS hm2 Φ hΦ
  have hB : SwapBlocks.IsSwapBlock (Φ '' hC.alpha) := isSwapBlock_image Φ hiff hblock
  have hus : Φ u ∈ Φ '' hC.alpha := ⟨u, hu, rfl⟩
  have hnot1 : Φ '' hC.alpha ≠ {Φ u} := by
    intro h
    have hmem : Φ a ∈ ({Φ u} : Set (L2Wreath f m)) := h ▸ ⟨a, ha, rfl⟩
    exact hau (Φ.injective hmem)
  have hnotall : Φ '' hC.alpha ≠ swapSet f m := by
    intro h
    apply hblock.ne_univ
    refine Set.Subset.antisymm hblock.subset fun x hx => ?_
    have hmem : Φ x ∈ Φ '' hC.alpha := h ▸ (hiff x).1 hx
    obtain ⟨y, hy, hyx⟩ := hmem
    exact Φ.injective hyx ▸ hy
  obtain ⟨i, j, hij, hur, -⟩ := hΦ u huD
  rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | rfl | hm5
  ·
    have h01 : ∀ i j : Fin 2, i ≠ j → swap i j = swap 0 1 := by decide
    have hsup : ∀ b ∈ Φ '' hC.alpha, b.right = swap 0 1 := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i', j', hij', hr, -⟩ := hΦ x (hblock.subset hx)
      rw [hr, h01 i' j' hij']
    have hseq := eq_swp_of_right_eq (hΦ u huD) (by decide : (0 : Fin 2) ≠ 1) (hsup _ hus)
    rcases SwapBlocks.eq_singleton_or_sameSwaps hf hB (by decide : (0 : Fin 2) ≠ 1)
      (hseq ▸ hus) hsup with h | h
    · exact hnot1 (by rw [h, ← hseq])
    · refine hnotall (h.trans (Set.Subset.antisymm (fun x hx => hx.1) fun x hx => ⟨hx, ?_⟩))
      obtain ⟨i', j', hij', hr, -⟩ := hx
      rw [hr, h01 i' j' hij']
  · exact false_of_three_four hS hC.conn (Or.inl rfl) Φ hΦ
  · exact false_of_three_four hS hC.conn (Or.inr rfl) Φ hΦ
  ·
    rcases SwapBlocks.swap_block_trichotomy hf hm5 hB hus hij hur with h | h | h
    · exact hnot1 h
    · have hvD : v ∈ D := htri.2.1
      have hwD : w ∈ D := htri.2.2.1
      have hvα : v ∉ hC.alpha := fun h' =>
        Set.disjoint_left.mp (disjoint_alpha_DalphaStar hblock) h' hv
      obtain ⟨k, l, hkl, hvr, -⟩ := hΦ v hvD
      obtain ⟨p, r, hpr, hwr, -⟩ := hΦ w hwD
      have hne : swap i j ≠ swap k l := by
        intro heq
        have hmem : Φ v ∈ Φ '' hC.alpha := h ▸ ⟨hΦ v hvD, hvr.trans heq.symm⟩
        obtain ⟨y, hy, hyv⟩ := hmem
        exact hvα (Φ.injective hyv ▸ hy)
      have hright : ∀ x y : G, (Φ (x * y)).right = (Φ x).right * (Φ y).right := fun x y => by
        rw [map_mul, SemidirectProduct.mul_right]
      have hcomm : Commute (swap i j) (swap k l) := by
        have h' := htri.2.2.2.2.1.eq
        rw [commute_iff_eq, ← hur, ← hvr, ← hright, ← hright, h']
      have hdisj := (WreathEndgame.swap_commute_cases hij hkl hcomm).resolve_left hne
      have hdvd : ∀ x : G, orderOf (Φ x).right ∣ orderOf x := fun x => by
        have := orderOf_map_dvd (SemidirectProduct.rightHom.comp Φ.toMonoidHom) x
        simpa [MulEquiv.orderOf_eq] using this
      have h1 : Odd (orderOf (swap i j * swap p r)) := by
        rw [← hur, ← hwr, ← hright]
        exact (hD.odd_of_not_commute huD hwD htri.2.2.2.2.2.1).of_dvd_nat (hdvd _)
      have h2 : Odd (orderOf (swap k l * swap p r)) := by
        rw [← hvr, ← hwr, ← hright]
        exact (hD.odd_of_not_commute hvD hwD htri.2.2.2.2.2.2).of_dvd_nat (hdvd _)
      have h4 := four_dvd_orderOf_swap_mul_swap_mul_swap hij hkl hpr hdisj h1 h2
      obtain ⟨n, hn, -, hord⟩ := hthird
      have h4' : 4 ∣ 2 * n := by
        rw [← hord]
        refine h4.trans ?_
        rw [← hur, ← hvr, ← hwr, ← hright, ← hright]
        exact hdvd _
      obtain ⟨c, rfl⟩ := hn
      omega
    · exact hnotall h

end CFSG.OddTranspositions.PartThree
