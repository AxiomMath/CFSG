module

import CFSG.RankThree.GF2n.Tim81.Sec6.S64Fix
import CFSG.RankThree.GF2n.Tim81.Sec6.S64Section
import CFSG.RankThree.GF2n.Tim81.Sec6.KWModule
import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import CFSG.RankThree.GF2n.Tim81.Sec6.S61
public import CFSG.RankThree.GF2n.Tim81.Sec6.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

private theorem Sec45Shape.kOf_props_of_card (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hK : Nat.card (kOf V H) = Nat.card V ^ 4 ∨ Nat.card (kOf V H) = Nat.card V ^ 8) :
    (∀ c ∈ Subgroup.normalizer (kOf V H : Set G),
      c ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) →
      (∀ x ∈ H, ⁅c, x⁆ ∈ kOf V H) → c * c ∈ kOf V H →
      ∀ k ∈ kOf V H, ⁅c, k⁆ ∈ Tim79a.xOf V H) ∧
    (∀ k ∈ kOf V H, k * k = 1 → k ∈ Tim79a.xOf V H) := by
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  rcases hK with hK4 | hK8
  · have hKW : kOf V H = Tim79a.xOf V H :=
      (Subgroup.eq_of_le_of_card_ge hWK (by rw [hK4, hS.card_xOf_eq_pow_four])).symm
    refine ⟨fun c _ hcW _ _ k hk => ?_, fun k hk _ => by rw [← hKW]; exact hk⟩
    rw [hKW] at hk
    rw [commutatorElement_def]
    exact (Tim79a.xOf V H).mul_mem ((Subgroup.mem_normalizer_iff.mp hcW k).mp hk)
      ((Tim79a.xOf V H).inv_mem hk)
  · obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
    letI := hField
    letI := hFintype
    letI := hCharP
    exact ⟨fun c hcK hcW hcH hc2 =>
        hS.commutator_mem_xOf_of_mul_self_mem h hw hcK hcW hcH hc2 hK8
          hS.card_xOf_eq_pow_four,
      fun k hk hk2 =>
        hS.mem_xOf_of_mul_self_eq_one h hw hK8 hS.card_xOf_eq_pow_four hk hk2⟩

theorem Sec6Hyp.mem_xOf_of_mem_Pc_sup_xOf (hS : Sec6Hyp M V) {g : G}
    (hA : conjSubgroup g V ∈ sigmaSet M V)
    (hInv : ∀ k ∈ kOf V (hOf M V g), k * k = 1 → k ∈ Tim79a.xOf V (hOf M V g))
    {B : Subgroup G} (hBP : B ⊓ Pc M V = ⊥) {b : G} (hb : b ∈ B) (hb2 : b * b = 1)
    (hbPW : b ∈ Pc M V ⊔ Tim79a.xOf V (hOf M V g)) :
    b ∈ Tim79a.xOf V (hOf M V g) := by
  have h := hS.sec5.toRootHyp
  have hSg : Sec45Shape M V (hOf M V g) g := hS.sec5.shape hA
  have hWPA : Tim79a.xOf V (hOf M V g) ≤ Pc M V ⊔ conjSubgroup g V := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨z, hz, rfl⟩ := hU
    by_cases hzV : conjSubgroup z V = V
    · rw [hzV]
      exact h.toHyp.le_Pc.trans le_sup_left
    · obtain ⟨p, hp, hpz⟩ := hS.res.i5a M V hS.sec5 (hOf M V g) g z hSg hz hzV
      rw [hpz]
      exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left hp)
  obtain ⟨y, hy, a, ha, rfl⟩ := exists_mul_of_mem_sup (V := Pc M V)
    (U := conjSubgroup g V) ((hS.sec5.le_M_of_mem_sigmaSet hA).1.trans h.toHyp.le_normalizer_Pc)
    (sup_le le_sup_left hWPA hbPW)
  by_cases ha1 : a = 1
  · subst a
    rw [mul_one] at hb ⊢
    have : y ∈ B ⊓ Pc M V := ⟨hb, hy⟩
    rw [hBP, Subgroup.mem_bot] at this
    rw [this]
    exact (Tim79a.xOf V (hOf M V g)).one_mem
  obtain ⟨y₀, hy₀H, -, hVy₀, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hy₀V : conjSubgroup y₀ V ≠ V := by
    rw [← hVy₀]
    exact ne_of_mem_sigmaSet h hA
  have ha' : a ∈ conjSubgroup y₀ V := by
    rw [← hVy₀]
    exact ha
  have ha2 : a * a = 1 := h.toHyp.mul_self_eq_one_of_mem_conj ha
  have hya : ⁅y, a⁆ = y * y := by
    calc ⁅y, a⁆ = y * (a * a) * ((y * a) * (y * a))⁻¹ * y := by
          simp only [commutatorElement_def]
          group
      _ = y * y := by rw [ha2, hb2, inv_one]; group
  have hyK : y ∈ kOf V (hOf M V g) := hSg.mem_kOf_of_commutator_mem h hy₀H hy₀V ha' ha1 hy
    (by rw [hya]; exact h.toHyp.mul_self_mem_of_mem_Pc hy)
  have haW : a ∈ Tim79a.xOf V (hOf M V g) := conjSubgroup_le_xOf_of_mem hy₀H ha'
  have hyy : y * y = 1 := by
    rw [← hya]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hyK).2 a haW).symm)
  exact (Tim79a.xOf V (hOf M V g)).mul_mem (hInv y hyK hyy) haW

theorem Sec6Hyp.stmt64 (hS : Sec6Hyp M V) :
    ∀ n : ℕ, Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) → n ≤ 3 → NoCommPair M V →
      ∀ B ∈ omegaSet V, B ≤ M → B = V ∨ B ∈ sigmaSet M V := by
  intro n hnP hn3 hNC B hB hBM
  by_cases hBV : B = V
  · exact Or.inl hBV
  right
  obtain ⟨g₁, -, rfl⟩ := Tim79a.mem_omegaOf.mp hB
  have h := hS.sec5.toRootHyp
  obtain ⟨hBP, hBC⟩ := h.conj_inf_Pc_eq_bot_of_conj_le hBM hBV
  have hB2 : IsPGroup 2 ↥(conjSubgroup g₁ V) :=
    h.toHyp.isPGroup_V.map (MulAut.conj g₁).toMonoidHom
  obtain ⟨A, hA, hAB2⟩ := hS.exists_mem_sigmaSet_isPGroup_sup hBM hB2
  obtain ⟨g, rfl, -⟩ := id hA
  have hSg := hS.sec5.shape hA
  obtain ⟨n₀, hn₀2, hn₀P, hKcard⟩ := hS.stmt61b
  have hn_eq : n = n₀ := by
    have hq : 1 < Nat.card V := by
      have := h.four_le_card
      omega
    have := Nat.pow_right_injective hq (hnP.symm.trans hn₀P)
    omega
  subst n
  have hK : Nat.card (kOf V (hOf M V g)) = Nat.card V ^ 4 ∨
      Nat.card (kOf V (hOf M V g)) = Nat.card V ^ 8 := by
    have hK0 := (hKcard g hA).2.2
    rcases (show n₀ = 2 ∨ n₀ = 3 by omega) with rfl | rfl
    · exact Or.inl (by simpa using hK0)
    · exact Or.inr (by simpa using hK0)
  obtain ⟨hSec, hInv⟩ := hSg.kOf_props_of_card h hK
  have hBH : ∀ a ∈ conjSubgroup g₁ V, conjSubgroup a (hOf M V g) = hOf M V g := fun a ha => by
    obtain ⟨p, hp, hpa⟩ := hS.exists_conj_eq_conj_of_isPGroup_sup hNC hA hBM hAB2 ha
    exact h.toHyp.conjSubgroup_hOf_eq_of_conj_eq_conj (hBM ha) hp hpa
  have hBW : conjSubgroup g₁ V ≤ Tim79a.xOf V (hOf M V g) := fun b hb => by
    obtain ⟨hbK, hbW⟩ := h.toHyp.mem_normalizer_kOf_and_xOf (hBM hb) (hBH b hb)
    obtain ⟨u, hu, hcK⟩ := hSg.exists_mem_Pc_commutator_mem_kOf h hBC hBH hb
    have hb2 := h.toHyp.mul_self_eq_one_of_mem_conj hb
    exact hS.mem_xOf_of_mem_Pc_sup_xOf hA hInv hBP hb hb2
      (hSg.mem_Pc_sup_xOf_of_fix h (hBM hb) (hBC hb) hb2 hbK hbW hu hcK hSec hInv)
  obtain ⟨y, hyH, hy⟩ := hSg.exists_mem_eq_of_conj_le_xOf h hBW
  rw [hy]
  exact hSg.conjSubgroup_mem_sigmaSet h hyH (fun h' => hBV (hy.trans h'))

end CFSG.RankThree.GF2n.Tim81
