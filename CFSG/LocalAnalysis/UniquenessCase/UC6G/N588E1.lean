module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S37
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem Z_le_H : m.Z ≤ m.H := fun z hz =>
  mem_centralizer_iff.2 fun y hy => by
    haveI : IsCyclic m.Z := isCyclic_of_prime_card (hp := ⟨m.hr⟩) m.card_Z
    have := (IsCyclic.commGroup (α := m.Z)).mul_comm ⟨z, hz⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this.symm

theorem A_le_H : m.A ≤ m.H := sup_le m.Z_le_H m.hZ.E_le_centralizer

theorem H_eq_sup_of {W : Subgroup G} (hWH : W ≤ m.H) (hHW : m.H ≤ normalizer (W : Set G))
    {t : G} (htW : t ∈ W) (htA : t ∈ m.A) (htZ : t ∉ m.Z) : m.H = W ⊔ (m.H ⊓ m.M) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hel := m.isElemAbelian_A
  have htr : t ^ m.r = 1 := hel.2 t htA
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ m.Z.one_mem)
  have htcard : Nat.card (zpowers t) = m.r := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htr ht1
  have hZt : m.Z ⊓ zpowers t = ⊥ := by
    have h := inf_eq_bot_of_not_le_of_card_prime m.hr htcard
      (fun h => htZ (h (mem_zpowers t)))
    rw [inf_comm] at h
    exact h
  have hcommZt : ∀ z ∈ m.Z, ∀ s ∈ zpowers t, z * s = s * z := fun z hz s hs =>
    mem_centralizer_iff.1 (hWH ((zpowers_le.2 htW) hs)) z hz
  have hX : Nat.card ↥(m.Z ⊔ zpowers t) = m.r ^ 2 := by
    rw [card_sup_of_commute_of_disjoint hcommZt hZt, m.card_Z, htcard, pow_two]
  have hXA : m.Z ⊔ zpowers t ≤ m.A := sup_le m.Z_le_A (zpowers_le.2 htA)
  have hXE : (m.Z ⊔ zpowers t) ⊓ m.E ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a ∈ m.Z ⊔ zpowers t, ∀ e ∈ m.E, a * e = e * a := fun a ha e he =>
      congrArg Subtype.val (hel.1.is_comm.comm ⟨a, hXA ha⟩ ⟨e, m.E_le_A he⟩)
    have hcard := card_sup_of_commute_of_disjoint hcomm hbot
    rw [hX, m.d.E_card] at hcard
    have hle : Nat.card ↥(m.Z ⊔ zpowers t ⊔ m.E) ≤ Nat.card ↥m.A :=
      Subgroup.card_le_of_le (sup_le hXA m.E_le_A)
    rw [hcard, m.card_A] at hle
    have : m.r ^ 3 < m.r ^ 2 * m.r ^ 2 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
    omega
  have htp : IsPGroup m.r (zpowers t) := IsPGroup.of_card (n := 1) (by rw [htcard, pow_one])
  obtain ⟨T, hT, htT⟩ := exists_isSylowOf_ge (zpowers_le.2 htW) htp
  have hfr := frattini_of_isSylowOf hWH hHW hT
  have hZT : ∀ z ∈ m.Z, ∀ s ∈ T, z * s = s * z := fun z hz s hs =>
    mem_centralizer_iff.1 (hWH (hT.le hs)) z hz
  have hZTp : IsPGroup m.r ↥(m.Z ⊔ T) := by
    have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [m.card_Z, pow_one])
    have hn : T ≤ normalizer (m.Z : Set G) :=
      (hT.le.trans hWH).trans (Subgroup.centralizer_le_normalizer _)
    exact hZp.to_sup_of_normal_left' hT.isPGroup hn
  have hNT : m.H ⊓ normalizer (T : Set G) ≤ normalizer ((m.Z ⊔ T : Subgroup G) : Set G) := by
    rintro h ⟨hhH, hhT⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨z, hz, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hZT hx
    have hzh : h * z * h⁻¹ = z := by
      rw [← mem_centralizer_iff.1 hhH z hz, mul_inv_cancel_right]
    have hsh : h * s * h⁻¹ ∈ T := (mem_normalizer_iff.1 hhT s).1 hs
    rw [show h * (z * s) * h⁻¹ = (h * z * h⁻¹) * (h * s * h⁻¹) by group, hzh]
    exact (m.Z ⊔ T).mul_mem (mem_sup_left hz) (mem_sup_right hsh)
  have hNM := m.d.normalizer_le_of_le_pGroup m.hC (X := (m.Z ⊔ zpowers t) ⊓ m.E)
    (S := m.Z ⊔ T) inf_le_right hXE
    ((inf_le_left).trans (sup_le_sup_left htT _)) hZTp
  refine le_antisymm ?_ (sup_le hWH inf_le_left)
  calc m.H = W ⊔ (m.H ⊓ normalizer (T : Set G)) := hfr
    _ ≤ W ⊔ (m.H ⊓ m.M) := sup_le_sup_left (le_inf inf_le_left (hNT.trans hNM)) _

theorem H_le_M_of_le_M {W : Subgroup G} (hWH : W ≤ m.H) (hHW : m.H ≤ normalizer (W : Set G))
    (hWM : W ≤ m.M) {t : G} (htW : t ∈ W) (htA : t ∈ m.A) (htZ : t ∉ m.Z) : m.H ≤ m.M := by
  rw [m.H_eq_sup_of hWH hHW htW htA htZ]
  exact sup_le hWM inf_le_right

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
