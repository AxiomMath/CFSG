module

public import CFSG.CGT.Timmesfeld75.Sec3Conj
public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Helpers

variable {G : Type} [Group G]

theorem mul_comm_of_conj_mem_H0 {M Z X : Subgroup G} (hXM0 : X ≤ H0 M Z) {g a c : G}
    (ha : g * a * g⁻¹ ∈ X) (hc : g * c * g⁻¹ ∈ Z) : a * c = c * a := by
  have hcen : g * a * g⁻¹ ∈ M ⊓ Subgroup.centralizer (Z : Set G) := hXM0 ha
  have h3 : (g * c * g⁻¹) * (g * a * g⁻¹) = (g * a * g⁻¹) * (g * c * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcen).2 (g * c * g⁻¹) hc
  have h4 : g * (a * c) * g⁻¹ = g * (c * a) * g⁻¹ := by
    calc g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (g * c * g⁻¹) * (g * a * g⁻¹) := h3.symm
      _ = g * (c * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h4)

theorem not_le_bot_of_strothHyp {M Q Z : Subgroup G} (H : StrothHyp M Q Z) : ¬ Z ≤ ⊥ := by
  intro h
  have h4 := H.q4
  rw [le_bot_iff.mp h, Subgroup.card_bot] at h4
  omega

end Helpers

section Props

variable {G : Type} [Group G] [Finite G]

@[expose] def OmegaProp (M Q Z : Subgroup G) : Prop :=
  ∀ A C : Subgroup G, (∃ g : G, A = conjSubgroup g Z) → (∃ g : G, C = conjSubgroup g Z) →
    A ≤ Q → C ≤ Q → A ≠ Z → C ≠ Z → (∀ a ∈ A, ∀ c ∈ C, a * c = c * a) → A ≤ C ⊔ Z

@[expose] def P2Prop (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
    ∃ B' : Subgroup G, (∃ g : G, B' = conjSubgroup g Z) ∧ B' ≤ Q ⊓ QB X

end Props

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem tiFusion_of_omega_p2 (H : StrothHyp M Q Z) (hΩ : OmegaProp M Q Z)
    (hP : P2Prop M Q Z) : TIFusion M Q Z := by
  refine tiFusion_of_not_sit H ?_
  intro X x hs
  have h12 : Post12 M Q Z X := smith_1_12 hs
  obtain ⟨g, hg⟩ := hs.conj
  obtain ⟨B', ⟨k, rfl⟩, hB'⟩ := hP X x hs
  have hB'Q : conjSubgroup k Z ≤ Q := by
    intro y hy
    exact (Subgroup.mem_inf.mp (hB' hy)).1
  have hB'X : conjSubgroup k Z ≤ QB X := by
    intro y hy
    exact (Subgroup.mem_inf.mp (hB' hy)).2
  have hBX : conjSubgroup k Z ≠ X := by
    intro e
    have hXQ0 : X ≤ Q := by
      rw [← e]
      exact hB'Q
    have hxQ : x ∈ X ⊓ Q := ⟨hs.mem, hXQ0 hs.mem⟩
    rw [h12.2, Subgroup.mem_bot] at hxQ
    exact hs.ne_one hxQ
  have hB'Z : conjSubgroup k Z ≠ Z := by
    intro e
    rw [e] at hB'X
    have hZbot : Z ≤ Z ⊓ QB X := le_inf le_rfl hB'X
    rw [Z_inf_QB_eq_bot hs h12] at hZbot
    exact not_le_bot_of_strothHyp H hZbot
  have hXk : X ≤ QB (conjSubgroup k Z) :=
    (H.le_QB_iff_le_QB (B := conjSubgroup k Z) (C := X) ⟨k, rfl⟩ ⟨g, hg⟩ hBX).mp hB'X
  have hZk : Z ≤ QB (conjSubgroup k Z) :=
    (H.le_QB_iff_le_QB (B := conjSubgroup k Z) (C := Z) ⟨k, rfl⟩
      ⟨1, (conjSubgroup_one Z).symm⟩ hB'Z).mp (by rw [H.QB_Z]; exact hB'Q)
  rw [QB_conj_eq H k] at hXk hZk
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hA_Q : conjSubgroup k⁻¹ X ≤ Q := conjSubgroup_le_iff.mpr (by rw [inv_inv]; exact hXk)
  have hC_Q : conjSubgroup k⁻¹ Z ≤ Q := conjSubgroup_le_iff.mpr (by rw [inv_inv]; exact hZk)
  have hZ_conj : Z ≤ conjSubgroup k⁻¹ Q := conjSubgroup_le_iff.mp hB'Q
  have hCZ : conjSubgroup k⁻¹ Z ⊔ Z ≤ conjSubgroup k⁻¹ Q :=
    sup_le (conjSubgroup_mono hZQ) hZ_conj
  have hA_ne : conjSubgroup k⁻¹ X ≠ Z := by
    intro e
    apply hBX
    have e2 := congrArg (conjSubgroup k) e
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at e2
    exact e2.symm
  have hC_ne : conjSubgroup k⁻¹ Z ≠ Z := by
    intro e
    apply hB'Z
    have e2 := congrArg (conjSubgroup k) e
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at e2
    exact e2.symm
  have hcomm : ∀ a ∈ conjSubgroup k⁻¹ X, ∀ c ∈ conjSubgroup k⁻¹ Z, a * c = c * a := by
    intro a ha c hc
    have ha' : k * a * k⁻¹ ∈ X := by
      have h := mem_conjSubgroup.mp ha
      rwa [inv_inv] at h
    have hc' : k * c * k⁻¹ ∈ Z := by
      have h := mem_conjSubgroup.mp hc
      rwa [inv_inv] at h
    exact mul_comm_of_conj_mem_H0 h12.1 ha' hc'
  have hΩA : conjSubgroup k⁻¹ X ≤ conjSubgroup k⁻¹ Z ⊔ Z :=
    hΩ (conjSubgroup k⁻¹ X) (conjSubgroup k⁻¹ Z)
      ⟨k⁻¹ * g, by rw [hg, conjSubgroup_conjSubgroup]⟩ ⟨k⁻¹, rfl⟩
      hA_Q hC_Q hA_ne hC_ne hcomm
  have hXQ : X ≤ Q := by
    intro y hy
    have ha : k⁻¹ * y * k ∈ conjSubgroup k⁻¹ X := by
      rw [mem_conjSubgroup, inv_inv]
      have e : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
      rw [e]
      exact hy
    have hb : k⁻¹ * y * k ∈ conjSubgroup k⁻¹ Q := hCZ (hΩA ha)
    rw [mem_conjSubgroup, inv_inv] at hb
    have e : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
    rw [e] at hb
    exact hb
  have hxQ : x ∈ X ⊓ Q := ⟨hs.mem, hXQ hs.mem⟩
  rw [h12.2, Subgroup.mem_bot] at hxQ
  exact hs.ne_one hxQ

end Main

end CFSG.RankThree.GF2n.Smith81
