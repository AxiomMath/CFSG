module

public import CFSG.RankThree.GF2n.Parrott.Section3Lift

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem sup_zpowers_center_inf_eq {J₁ : Subgroup G}
    (hsq : ∀ x ∈ J z, x * x ∈ centerIn (J z)) (hZJ₁ : centerIn (J z) ≤ J₁) {j : J z}
    (hj : (j : G) ∉ J₁) :
    (Subgroup.zpowers (j : G) ⊔ centerIn (J z)) ⊓ J₁ = centerIn (J z) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxsup, hxJ1⟩ := Subgroup.mem_inf.mp hx
    have hcomm : ∀ y ∈ Subgroup.zpowers (j : G), ∀ c ∈ centerIn (J z), Commute y c := by
      intro y hy c hc
      exact Subgroup.mem_centralizer_iff.mp hc.2 y
        (Subgroup.zpowers_le_of_mem j.2 hy)
    obtain ⟨y, hy, c, hc, hxyc⟩ := (CFSG.mem_sup_of_commute hcomm).mp hxsup
    obtain ⟨k, hk⟩ :=
      (Submonoid.mem_powers_iff y (j : G)).mp ((mem_powers_iff_mem_zpowers).mpr hy)
    have hxJ1' : (j : G) ^ k * c ∈ J₁ := by
      rw [hk, hxyc]
      exact hxJ1
    have hcJ1 : c ∈ J₁ := hZJ₁ hc
    have hjkJ1 : (j : G) ^ k ∈ J₁ := by
      have hmul := J₁.mul_mem hxJ1' (J₁.inv_mem hcJ1)
      simpa using hmul
    have hsq_center : ∀ m : ℕ, (j : G) ^ (2 * m) ∈ centerIn (J z) := by
      intro m
      have hm : (j : G) ^ m ∈ J z := (J z).pow_mem j.2 m
      have hsq := hsq _ hm
      rw [show 2 * m = m + m by omega, pow_add]
      exact hsq
    rw [← hxyc, ← hk]
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exact (centerIn (J z)).mul_mem (hsq_center m) hc
    · have hprevJ1 : (j : G) ^ (2 * m) ∈ J₁ := hZJ₁ (hsq_center m)
      have hpow : (j : G) ^ (2 * m + 1) = (j : G) * (j : G) ^ (2 * m) := by
        rw [pow_succ']
      have hjn : (j : G) ∈ J₁ := by
        have hmul := J₁.mul_mem hjkJ1 (J₁.inv_mem hprevJ1)
        rw [hpow] at hmul
        have heq : (j : G) * (j : G) ^ (2 * m) * ((j : G) ^ (2 * m))⁻¹ = (j : G) := by
          group
        rwa [heq] at hmul
      exact absurd hjn hj
  · exact le_inf le_sup_right hZJ₁

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def J1sub (h : Tim79a.ParrottHyp z) : Subgroup G :=
  ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊔ centerIn (J z)

theorem J1sub_le_J (h : Tim79a.ParrottHyp z) :
    J1sub (z := z) (D := D) h ≤ J z := by
  rw [J1sub]
  refine sup_le ?_ inf_le_left
  rw [Subgroup.commutator_le]
  intro a ha y hy
  obtain ⟨aH, haH, rfl⟩ := Subgroup.mem_map.mp ha
  change ⁅(aH : G), y⁆ ∈ J z
  have hconj : (aH : G) * y * (aH : G)⁻¹ ∈ J z := by
    have hyH : (⟨y, J_le_H hy⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
      Subgroup.mem_subgroupOf.mpr hy
    have hconjH := hN.conj_mem (⟨y, J_le_H hy⟩ : ↥(H z)) hyH aH
    simpa using Subgroup.mem_subgroupOf.mp hconjH
  have heq : ⁅(aH : G), y⁆ = ((aH : G) * y * (aH : G)⁻¹) * y⁻¹ := by
    rw [commutatorElement_def]
  rw [heq]
  exact (J z).mul_mem hconj ((J z).inv_mem hy)

theorem commutator_le_J1sub (h : Tim79a.ParrottHyp z) :
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ≤
      J1sub (z := z) (D := D) h :=
  le_sup_left

theorem center_le_J1sub (h : Tim79a.ParrottHyp z) :
    centerIn (J z) ≤ J1sub (z := z) (D := D) h :=
  le_sup_right

theorem sup_zpowers_center_inf_J1sub (h : Tim79a.ParrottHyp z) {j : J z}
    (hj : (j : G) ∉ J1sub (z := z) (D := D) h) :
    (Subgroup.zpowers (j : G) ⊔ centerIn (J z)) ⊓ J1sub (z := z) (D := D) h =
      centerIn (J z) :=
  sup_zpowers_center_inf_eq (fun _ hx => sq_mem_centerIn_J h hx)
    (center_le_J1sub (z := z) (D := D) h) hj

end CFSG.RankThree.GF2n.Parrott
