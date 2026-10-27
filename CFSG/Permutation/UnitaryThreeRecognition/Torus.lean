module

public import CFSG.Permutation.UnitaryThreeRecognition.Orbits
public import CFSG.Permutation.UnitaryThreeRecognition.Basic

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def swapFix (G : Type*) [Group G] [MulAction G Ω] (a b : Ω) (s : G) : Subgroup G :=
  pairStab G a b ⊓ Subgroup.centralizer ({s} : Set G)

theorem mem_swapFix {a b : Ω} {s t : G} :
    t ∈ swapFix G a b s ↔ t ∈ pairStab G a b ∧ s * t = t * s := by
  simp only [swapFix, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]

theorem card_mul_card_le_card_mul_card_inf [Finite G] {H₁ H₂ L : Subgroup G} (h₁ : H₁ ≤ L)
    (h₂ : H₂ ≤ L) : Nat.card H₁ * Nat.card H₂ ≤ Nat.card L * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
  have e₁ := Subgroup.relIndex_mul_card H₁ L
  have e₂ := Subgroup.relIndex_mul_card H₂ L
  have e₃ := Subgroup.relIndex_mul_card (H₁ ⊓ H₂) L
  rw [inf_of_le_left h₁] at e₁
  rw [inf_of_le_left h₂] at e₂
  rw [inf_of_le_left (le_trans inf_le_left h₁)] at e₃
  have hle : (H₁ ⊓ H₂).relIndex L ≤ H₁.relIndex L * H₂.relIndex L := Subgroup.relIndex_inf_le
  set r₁ := H₁.relIndex L
  set r₂ := H₂.relIndex L
  set r := (H₁ ⊓ H₂).relIndex L
  have hL : 0 < Nat.card L := Nat.card_pos
  have hr₁ : 0 < r₁ := by
    rcases Nat.eq_zero_or_pos r₁ with h | h
    · rw [h, zero_mul] at e₁; omega
    · exact h
  have hr₂ : 0 < r₂ := by
    rcases Nat.eq_zero_or_pos r₂ with h | h
    · rw [h, zero_mul] at e₂; omega
    · exact h
  have key : Nat.card H₁ * Nat.card H₂ * (r₁ * r₂) ≤
      Nat.card L * Nat.card (H₁ ⊓ H₂ : Subgroup G) * (r₁ * r₂) := by
    calc Nat.card H₁ * Nat.card H₂ * (r₁ * r₂) = (r₁ * Nat.card H₁) * (r₂ * Nat.card H₂) := by
          ring
      _ = Nat.card L * Nat.card L := by rw [e₁, e₂]
      _ = Nat.card L * (r * Nat.card (H₁ ⊓ H₂ : Subgroup G)) := by rw [e₃]
      _ ≤ Nat.card L * ((r₁ * r₂) * Nat.card (H₁ ⊓ H₂ : Subgroup G)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ hle
      _ = Nat.card L * Nat.card (H₁ ⊓ H₂ : Subgroup G) * (r₁ * r₂) := by ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hr₁ hr₂)

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem card_pairStab_dvd_swapFix_mul [Finite G] {b : Ω} (hb : b ≠ a) {s : G}
    (hsa : s • a = b) (hsb : s • b = a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁) :
    Nat.card (pairStab G a b) ∣ Nat.card (swapFix G a b s) * (Nat.card Q - 1) := by
  classical
  let X := {u : G // u ∈ Q ∧ u ≠ 1}
  let act : MulAction (pairStab G a b) X :=
    { smul := fun t u => ⟨(t : G) * u * (t : G)⁻¹, hQ.normal t t.property.1 u u.2.1, by
        intro h
        apply u.2.2
        have := congrArg (fun z => (t : G)⁻¹ * z * t) h
        simpa [mul_assoc] using this⟩
      one_smul := fun u => Subtype.ext (by
        change ((1 : pairStab G a b) : G) * u * ((1 : pairStab G a b) : G)⁻¹ = u
        simp)
      mul_smul := fun t₁ t₂ u => Subtype.ext (by
        change (t₁ * t₂ : G) * u * (t₁ * t₂ : G)⁻¹ =
          (t₁ : G) * ((t₂ : G) * u * (t₂ : G)⁻¹) * (t₁ : G)⁻¹
        group) }
  let K : Subgroup (pairStab G a b) := (swapFix G a b s).subgroupOf (pairStab G a b)
  have hK : ∀ u : X, stabilizer (pairStab G a b) u ≤ K := by
    intro u t ht
    have htu : (t : G) * u * (t : G)⁻¹ = u := congrArg Subtype.val ht
    have hcomm' : (t : G) * u = u * t := by
      calc (t : G) * u = (t : G) * u * (t : G)⁻¹ * t := by group
        _ = u * t := by rw [htu]
    have := hQ.conj_eq_of_commute hb hsa hsb hcomm u.2.1 u.2.2 t.property hcomm'
    rw [Subgroup.mem_subgroupOf, mem_swapFix]
    refine ⟨t.property, ?_⟩
    calc s * (t : G) = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [this]
  have hdvd := card_dvd_card_mul_of_stabilizer_le K hK
  have hKcard : Nat.card K = Nat.card (swapFix G a b s) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hXcard : Nat.card X = Nat.card Q - 1 := by
    have e : X ≃ {u : Q // u ≠ 1} :=
      { toFun := fun u => ⟨⟨u.1, u.2.1⟩, fun h => u.2.2 (congrArg Subtype.val h)⟩
        invFun := fun u => ⟨u.1, u.1.property, fun h => u.2 (Subtype.ext h)⟩
        left_inv := fun u => rfl
        right_inv := fun u => rfl }
    rw [Nat.card_congr e]
    let : Fintype Q := Fintype.ofFinite Q
    have h1 := Set.card_ne_eq (1 : Q)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
    exact h1
  rw [hKcard, hXcard] at hdvd
  exact hdvd

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
