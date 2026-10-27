module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C623Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621b
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S37

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IrrOn)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem A_eq_Z_sup_inf_L (h620 : m.C620) : m.A = m.Z ⊔ (m.A ⊓ m.L) := by
  refine le_antisymm ?_ (sup_le m.Z_le_A inf_le_left)
  intro a ha
  obtain ⟨z, hz, l, hl, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (fun z hz l hl => m.Z_comm_L hz hl) (h620.1 ha)
  have hlA : l ∈ m.A := by
    have := m.A.mul_mem (m.A.inv_mem (m.Z_le_A hz)) ha
    simpa using this
  exact (m.Z ⊔ (m.A ⊓ m.L)).mul_mem (mem_sup_left hz) (mem_sup_right ⟨hlA, hl⟩)

theorem exists_mul_of_mem_A (h620 : m.C620) {a : G} (ha : a ∈ m.A) :
    ∃ z ∈ m.Z, ∃ e ∈ m.A ⊓ m.L, a = z * e := by
  have ha' : a ∈ m.Z ⊔ (m.A ⊓ m.L) := by rwa [← m.A_eq_Z_sup_inf_L h620]
  exact exists_mul_of_mem_sup_of_commute (H := m.Z) (K := m.A ⊓ m.L)
    (fun z hz e he => m.Z_comm_L hz (Subgroup.mem_inf.1 he).2) ha'

variable {m}

theorem mem_normalizer_A_of_mem_normalizer_E (h620 : m.C620) {x : G} (hxL : x ∈ m.L)
    (hxN : x ∈ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G)) : x ∈ normalizer (m.A : Set G) := by
  refine mem_normalizer_of_forward_uc6 fun a ha => ?_
  obtain ⟨z, hz, e, he, rfl⟩ := m.exists_mul_of_mem_A h620 ha
  have hxz : x * z * x⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (m.Z_comm_L hz hxL).symm
  have hxe : x * e * x⁻¹ ∈ m.A ⊓ m.L := (mem_normalizer_iff.1 hxN e).1 he
  rw [conj_mul_eq_of_eq hxz rfl]
  exact (m.A_eq_Z_sup_inf_L h620).symm ▸ (m.Z ⊔ (m.A ⊓ m.L)).mul_mem (mem_sup_left hz) (mem_sup_right hxe)

theorem c621x_of_inverting (h620 : m.C620) {x : G} (hxL : x ∈ m.L)
    (hxN : x ∈ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G))
    (hinv : ∀ e ∈ m.A ⊓ m.L, x * x * e * (x * x)⁻¹ = e⁻¹) : m.C621x := by
  have hxA := mem_normalizer_A_of_mem_normalizer_E h620 hxL hxN
  have hxz : ∀ z ∈ m.Z, x * z * x⁻¹ = z := fun z hz => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (m.Z_comm_L hz hxL).symm
  have hx2z : ∀ z ∈ m.Z, x * x * z * (x * x)⁻¹ = z := fun z hz => by
    calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
      _ = z := by rw [hxz z hz, hxz z hz]
  have hya : ∀ z ∈ m.Z, ∀ e ∈ m.A ⊓ m.L, x * x * (z * e) * (x * x)⁻¹ = z * e⁻¹ :=
    fun z hz e he => conj_mul_eq_of_eq (hx2z z hz) (hinv e he)
  have hZE : ∀ e ∈ m.A ⊓ m.L, e ∈ m.Z → e = 1 := fun e he hz => by
    have h : e ∈ m.Z ⊓ m.L := ⟨hz, he.2⟩
    rwa [inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2, Subgroup.mem_bot] at h
  refine ⟨x, hxA, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨z, hz, e, he, rfl⟩ := m.exists_mul_of_mem_A h620 ha
    have h4 : x ^ 4 = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    have hy2 : (x * x) * ((x * x) * (z * e) * (x * x)⁻¹) * (x * x)⁻¹ = z * e := by
      rw [hya z hz e he, hya z hz e⁻¹ (inv_mem he), inv_inv]
    have hc : (x * x) * (x * x) * (z * e) * ((x * x) * (x * x))⁻¹ = z * e :=
      calc (x * x) * (x * x) * (z * e) * ((x * x) * (x * x))⁻¹
          = (x * x) * ((x * x) * (z * e) * (x * x)⁻¹) * (x * x)⁻¹ := by group
        _ = z * e := hy2
    rw [h4]
    exact ((mul_inv_eq_iff_eq_mul).1 hc).symm
  · intro a ha
    obtain ⟨z, hz, e, he, rfl⟩ := m.exists_mul_of_mem_A h620 ha
    rw [sq, hya z hz e he]
    constructor
    · intro h
      have he1 : e = 1 :=
        eq_one_of_inv_eq_of_pow_odd m.hr m.d.odd (mul_left_cancel h) (m.isElemAbelian_A.2 e he.1)
      rw [he1, mul_one]
      exact hz
    · intro hmem
      have heZ : e ∈ m.Z := by
        have := m.Z.mul_mem (m.Z.inv_mem hz) hmem
        simpa using this
      rw [hZE e he heZ]
      simp

theorem c621_of_inverting (hr3 : m.r = 3) (h620 : m.C620) {x : G} (hxL : x ∈ m.L)
    (hxN : x ∈ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G))
    (hinv : ∀ e ∈ m.A ⊓ m.L, x * x * e * (x * x)⁻¹ = e⁻¹) : m.C621 := by
  have hxA := mem_normalizer_A_of_mem_normalizer_E h620 hxL hxN
  intro W hWE hWN
  have hmem : x ∈ m.L ⊓ normalizer (m.A : Set G) := ⟨hxL, hxA⟩
  refine eq_bot_or_eq_of_inverting ?_ ?_ hWE hinv fun w hw => ?_
  · rw [m.card_A_inf_L h620, hr3]
    norm_num
  · intro e he
    have := m.isElemAbelian_A.2 e he.1
    rwa [hr3] at this
  · exact (mem_normalizer_iff.1 (hWN hmem) w).1 hw

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
