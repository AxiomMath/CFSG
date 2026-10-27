module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G]

theorem conj_mem_of_normal_subgroupOf {Q H : Subgroup G} (hQH : Q ≤ H)
    (hQn : (Q.subgroupOf H).Normal) {g y : G} (hg : g ∈ H) (hy : y ∈ Q) : g * y * g⁻¹ ∈ Q := by
  have h1 := hQn.conj_mem ⟨y, hQH hy⟩ hy ⟨g, hg⟩
  rwa [Subgroup.mem_subgroupOf] at h1

theorem sup_zpowers_of_commute [Finite G] {p : ℕ} {x w : G} (hx : orderOf x = p)
    (hw : orderOf w = p) (hxw : x * w = w * x)
    (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers w = ⊥) :
    let E := Subgroup.zpowers x ⊔ Subgroup.zpowers w
    (∀ y ∈ E, ∃ s ∈ Subgroup.zpowers x, ∃ r ∈ Subgroup.zpowers w, s * r = y) ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) ∧ p ^ 2 ≤ Nat.card E := by
  intro E
  have hc : Commute x w := hxw
  have hle : Subgroup.zpowers w ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact (hc.zpow_left i).eq
  have hdec : ∀ y ∈ E, ∃ s ∈ Subgroup.zpowers x, ∃ r ∈ Subgroup.zpowers w, s * r = y := by
    intro y hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hy
    obtain ⟨s, hs, r, hr, rfl⟩ := hy
    exact ⟨s, hs, r, hr, rfl⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, Commute a b := by
    intro a ha b hb
    obtain ⟨s, hs, r, hr, rfl⟩ := hdec a ha
    obtain ⟨s', hs', r', hr', rfl⟩ := hdec b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp hs'
    obtain ⟨j', rfl⟩ := Subgroup.mem_zpowers_iff.mp hr'
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact Commute.zpow_zpow_self x i i'
    · exact hc.zpow_zpow i j'
    · exact (hc.zpow_zpow i' j).symm
    · exact Commute.zpow_zpow_self w j j'
  refine ⟨hdec, fun a ha b hb => (hcomm a ha b hb).eq, fun a ha => ?_, ?_⟩
  · obtain ⟨s, hs, r, hr, rfl⟩ := hdec a ha
    have hsr : Commute s r := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      exact hc.zpow_zpow i j
    have hs1 : s ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx ▸ orderOf_dvd_of_mem_zpowers hs)
    have hr1 : r ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (hw ▸ orderOf_dvd_of_mem_zpowers hr)
    rw [hsr.mul_pow, hs1, hr1, one_mul]
  · let φ : Subgroup.zpowers x × Subgroup.zpowers w → E := fun st =>
      ⟨st.1 * st.2, Subgroup.mul_mem_sup st.1.2 st.2.2⟩
    have hφ : Function.Injective φ := by
      rintro ⟨s, r⟩ ⟨s', r'⟩ hsr
      have h1 : (s : G) * r = s' * r' := congrArg Subtype.val hsr
      have h2 : (s' : G)⁻¹ * s = r' * (r : G)⁻¹ := by
        calc (s' : G)⁻¹ * s = (s' : G)⁻¹ * (s * r) * (r : G)⁻¹ := by group
          _ = (s' : G)⁻¹ * (s' * r') * (r : G)⁻¹ := by rw [h1]
          _ = r' * (r : G)⁻¹ := by group
      have h3 : (s' : G)⁻¹ * s ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers w :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ s'.2) s.2,
          h2 ▸ Subgroup.mul_mem _ r'.2 (Subgroup.inv_mem _ r.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have hs : (s : G) = s' := by
        calc (s : G) = s' * ((s' : G)⁻¹ * s) := by group
          _ = s' := by rw [h3, mul_one]
      have hr : (r : G) = r' := by
        calc (r : G) = (s : G)⁻¹ * (s * r) := by group
          _ = (s' : G)⁻¹ * (s' * r') := by rw [h1, hs]
          _ = r' := by group
      exact Prod.ext (Subtype.ext hs) (Subtype.ext hr)
    have h1 := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx, hw, ← pow_two] at h1

variable [Finite G]

theorem card_eq_relIndex_mul_card_inf {H M B : Subgroup G} (hMB : M ⊔ B = H) (hBH : B ≤ H)
    (hBM : B ≤ Subgroup.normalizer (M : Set G)) :
    Nat.card M = B.relIndex H * Nat.card (M ⊓ B : Subgroup G) := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer hBM
  have h2 := Subgroup.relIndex_mul_card B H
  rw [inf_eq_left.mpr hBH] at h2
  rw [hMB, ← h2] at h1
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B))
  rw [← h1]
  ring

theorem card_le_of_conj_coset {M Q B : Subgroup G} {u : G} (huM : u ∈ M) (hu2 : orderOf u = 2)
    (hcomm : ∀ m ∈ M, u * m * u⁻¹ * m⁻¹ ∈ Q)
    (hC : M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Q ⊔ B)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hQM : Q ≤ M) :
    Nat.card M ≤ Nat.card Q * (Nat.card Q * Nat.card (M ⊓ B : Subgroup G)) := by
  classical
  have huinv : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu2
  have hclass : conjugacyWithin M u ⊆ (fun y => u * y) '' (Q : Set G) := by
    rintro _ ⟨m, rfl⟩
    refine ⟨u⁻¹ * ((m : G)⁻¹ * u * m), ?_, by group⟩
    have h1 := hcomm _ (M.inv_mem m.2)
    have heq : u * (m : G)⁻¹ * u⁻¹ * (m : G)⁻¹⁻¹ = u⁻¹ * ((m : G)⁻¹ * u * m) := by
      rw [huinv, inv_inv]
      group
    rwa [heq] at h1
  have hclass_card : Nat.card (conjugacyWithin M u) ≤ Nat.card Q := by
    calc Nat.card (conjugacyWithin M u) ≤ Nat.card ((fun y => u * y) '' (Q : Set G)) :=
          Nat.card_mono (Set.toFinite _) hclass
      _ = Nat.card Q := Nat.card_image_of_injective (mul_right_injective u) _
  have hsub : ((M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) ⊆
      Set.range (fun st : Q × (M ⊓ B : Subgroup G) => (st.1 : G) * st.2) := by
    intro g hg
    have hg' : g ∈ ((Q ⊔ B : Subgroup G) : Set G) := hC hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q B hBQ] at hg'
    obtain ⟨y, hy, b, hb, rfl⟩ := hg'
    have hbM : b ∈ M := by
      have h1 := M.mul_mem (M.inv_mem (hQM hy)) (Subgroup.mem_inf.mp hg).1
      rwa [inv_mul_cancel_left] at h1
    exact ⟨(⟨y, hy⟩, ⟨b, Subgroup.mem_inf.mpr ⟨hbM, hb⟩⟩), rfl⟩
  have hcent_card : Nat.card (M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
      Nat.card Q * Nat.card (M ⊓ B : Subgroup G) := by
    calc Nat.card (M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
          Nat.card (Set.range (fun st : Q × (M ⊓ B : Subgroup G) => (st.1 : G) * st.2)) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (Q × (M ⊓ B : Subgroup G)) := Finite.card_range_le _
      _ = Nat.card Q * Nat.card (M ⊓ B : Subgroup G) := Nat.card_prod _ _
  rw [← FinalChain.card_conjugacyWithin_mul huM]
  exact Nat.mul_le_mul hclass_card hcent_card

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
