module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldClass

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem pair_involution_fixed_field_and_orbit
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z)
    {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) {e : ℕ} (hQcard : Nat.card Q = 2 ^ e)
    (hQ4 : 4 ≤ Nat.card Q) (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {X : Subgroup G} (hXB : X ≤ pairPointStabilizer H beta)
    (hXnormal : (X.subgroupOf (pairPointStabilizer H beta)).Normal)
    (hXcyclic : IsCyclic X) (hXcard : Nat.card X = Nat.card Q - 1)
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    (htB : conjugacyWithin (pairPointStabilizer H beta) t = (fun x => t * x) '' (X : Set G))
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    let Y := Subgroup.centralizer ({u} : Set G)
    let E := Q ⊓ Y
    let X₀ := X ⊓ Y
    let D := involutionPointClass z
    4 ≤ Nat.card E ∧
      (Q ≤ Y → Nat.card E = Nat.card Q ∧ X₀ = X) ∧
      (¬ Q ≤ Y → Even e ∧ Nat.card E = 2 ^ (e / 2) ∧ Nat.card Q = Nat.card E ^ 2) ∧
      IsCyclic X₀ ∧ Nat.card X₀ = Nat.card E - 1 ∧
      (∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1},
        ∃! x : X₀, (x : G)⁻¹ * a * x = b) ∧
      (∃ tu ∈ (fun x => t * x) '' (X : Set G), Commute tu u ∧
        tu ∈ rightPairFlipFiber H z beta ∧
        rightCosetTranslate H beta tu = rightCosetMk H 1) ∧
      Y ≠ ⊤ ∧ ¬ Y ≤ H ∧
      {omega : rightCosetSpace H | ∃ y ∈ Y,
          rightCosetTranslate H (rightCosetMk H 1) y = omega} =
        {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} ∧
      (∀ (r : G) (hr : r ∈ E), r ≠ 1 →
        InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hr.2⟩ : Y) ∧
          InvolutionPointCentralSylow (⟨r, hr.2⟩ : Y) ∧
          D ∩ (Y : Set G) = conjugacyWithin Y r ∧
          E ≤ Subgroup.closure (conjugacyWithin Y r)) ∧
      Nat.card ↥(D ∩ (Y : Set G)) =
        (Nat.card E - 1) *
          Nat.card {omega : rightCosetSpace H // rightCosetTranslate H omega u = omega} := by
  intro Y E X₀ D
  have hBH : pairPointStabilizer H beta ≤ H := pairPointStabilizer_le_point H beta
  have huH : u ∈ H := hBH huB
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  have hQnorm := point_subgroup_normalized hQclass
  have hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q := fun x hx => hQnorm x (hBH (hXB hx))
  have huQ : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q := hQnorm u huH
  have huX : ∀ x ∈ X, u⁻¹ * x * u ∈ X := by
    intro x hx
    have hmem := hXnormal.conj_mem (⟨x, hXB hx⟩ : pairPointStabilizer H beta) hx
      (⟨u, huB⟩ : pairPointStabilizer H beta)⁻¹
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      using hmem
  obtain ⟨hE2, hcentralcase, hnoncentral, hX₀cyclic, hX₀card, hX₀reg⟩ :=
    fixed_field_structure hQ hQcard hQ4 hXQ hXcyclic hXcard hXregular hu huQ huX
  have he : 2 ≤ e := by
    by_contra he
    have hle : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard, hQcard]
    exact odd_two_pow_sub_one (by omega)
  obtain ⟨tu, htuX, htucomm, htuflip, htuβ⟩ :=
    exists_commuting_flip h.distinguished_order ht hXodd htB huB hu
  have htuH : tu ∉ H := by
    intro htuH
    apply hbeta
    rw [← htuflip.2]
    exact (translate_base_iff H tu).mpr htuH
  obtain ⟨hYtop, hYH⟩ := centralizer_proper_escape hsimple hnonab hu htucomm htuH
  have hinherit : ∀ (r : G) (hr : r ∈ E), r ≠ 1 →
      InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hr.2⟩ : Y) ∧
        InvolutionPointCentralSylow (⟨r, hr.2⟩ : Y) ∧
        D ∩ (Y : Set G) = conjugacyWithin Y r ∧
        E ≤ Subgroup.closure (conjugacyWithin Y r) := by
    intro r hr hr1
    refine class_member_inheritance h hcentral hQclass hYH hr hr1 ?_
    intro w hw
    obtain ⟨x, hx, _⟩ := hX₀reg r ⟨hr, hr1⟩ w hw
    exact ⟨⟨x, x.2.2⟩, hx⟩
  obtain ⟨r, hrQ, hr1, hrY⟩ := exists_nonidentity_commute hQcard (by omega) hu huQ
  have hDY := (hinherit r ⟨hrQ, hrY⟩ hr1).2.2.1
  have horbit := fixed_set_eq_orbit h hQcard (by omega) hQclass huH hu (hQH hrQ) hDY
  have hE4 : 4 ≤ Nat.card E := by
    by_contra hlt
    by_cases hQY : Q ≤ Y
    · have hEQ : Nat.card E = Nat.card Q := (hcentralcase hQY).1
      omega
    · obtain ⟨_, hEe, hQE⟩ := hnoncentral hQY
      have hE2' : Nat.card E = 2 := by
        rw [hEe] at hlt hE2 ⊢
        rcases Nat.lt_or_ge (e / 2) 2 with hk | hk
        · rcases Nat.lt_or_ge (e / 2) 1 with hk' | hk'
          · rw [show e / 2 = 0 by omega, pow_zero] at hE2
            omega
          · rw [show e / 2 = 1 by omega, pow_one]
        · have h4 : 2 ^ 2 ≤ 2 ^ (e / 2) := Nat.pow_le_pow_right (by norm_num) hk
          omega
      have hQ4' : Nat.card Q = 4 := by
        rw [hQE, hE2']
        norm_num
      have hnocentral := no_conjugate_centralizes h hQclass hQY horbit
      obtain ⟨S, hzS, hzcenter⟩ := hcentral
      obtain ⟨N, hN, hNindex⟩ := transfer_index_two hQ4' hQnorm S
        (central_sylow_le_point h S hzS hzcenter).2 hu hnocentral
      exact simple_no_normal_index_two hsimple hnonab N hN hNindex
  exact ⟨hE4, hcentralcase, hnoncentral, hX₀cyclic, hX₀card, hX₀reg,
    ⟨tu, htuX, htucomm, htuflip, htuβ⟩, hYtop, hYH, horbit, hinherit,
    class_centralizer_card h hQclass horbit⟩

end CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
