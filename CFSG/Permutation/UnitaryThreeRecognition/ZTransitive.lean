module

public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorus

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem exists_conj_eq_of_mem_centQ [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {z₁ z₂ : G} (hz₁ : z₁ ∈ centQ Q j) (hz₁1 : z₁ ≠ 1) (hz₂ : z₂ ∈ centQ Q j)
    (hz₂1 : z₂ ≠ 1) : ∃ t ∈ pairStab G a b, t * z₁ * t⁻¹ = z₂ := by
  classical
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hT := hQ.card_pairStab_eq_mul_swapFix hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd
    hd hQcard hΩcard hTcard hsa hs2
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  let T := pairStab G a b
  let X : Set G := {u | u ∈ centQ Q j ∧ u ≠ 1}
  have hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    intro t ht x hx
    refine ⟨hQ.conj_mem_centQ hcomm hj ht hx.1, ?_⟩
    intro h
    apply hx.2
    have := congrArg (fun y => t⁻¹ * y * t) h
    simpa [mul_assoc] using this
  let act : MulAction T X := conjAction T X hX
  let x0 : X := ⟨z₁, hz₁, hz₁1⟩
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup T x0)
  rw [Nat.card_prod] at hos
  let K : Subgroup T := (swapFix G a b s).subgroupOf T
  have hstabK : stabilizer T x0 ≤ K := by
    intro t ht
    have htz : (t : G) * z₁ = z₁ * t := (mem_stabilizer_conjAction_iff t x0).mp ht
    have := hQ.conj_eq_of_commute hb hsa hsb hcomm (mem_centQ.mp hz₁).1 hz₁1 t.property htz
    rw [Subgroup.mem_subgroupOf, mem_swapFix]
    refine ⟨t.property, ?_⟩
    calc s * (t : G) = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [this]
  have hKstab : K ≤ stabilizer T x0 := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    exact (mem_stabilizer_conjAction_iff t x0).mpr
      (hQ.swapFix_commute_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hQcard
        hΩcard hTcard hsa hs2 ht hz₁)
  have hKcard : Nat.card K = Nat.card (swapFix G a b s) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hstabcard : Nat.card (stabilizer T x0) = Nat.card (swapFix G a b s) := by
    rw [le_antisymm hstabK hKstab, hKcard]
  have hXcard : Nat.card X = p ^ f - 1 := by
    have e : X ≃ {u : centQ Q j // u ≠ 1} :=
      { toFun := fun u => ⟨⟨u.1, u.2.1⟩, fun h => u.2.2 (congrArg Subtype.val h)⟩
        invFun := fun u => ⟨u.1, u.1.property, fun h => u.2 (Subtype.ext h)⟩
        left_inv := fun u => rfl
        right_inv := fun u => rfl }
    rw [Nat.card_congr e]
    let : Fintype (centQ Q j) := Fintype.ofFinite _
    have h1 := Set.card_ne_eq (1 : centQ Q j)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hZ] at h1
    exact h1
  have horb : Nat.card (orbit T x0) = p ^ f - 1 := by
    have hWpos : 0 < Nat.card (swapFix G a b s) := Nat.card_pos
    rw [hstabcard] at hos
    refine Nat.eq_of_mul_eq_mul_right hWpos ?_
    rw [hos]
    exact hT
  by_contra hno
  push Not at hno
  have hx2 : z₂ ∈ X := ⟨hz₂, hz₂1⟩
  have hyorb : (⟨z₂, hx2⟩ : X) ∉ orbit T x0 := by
    rintro ⟨t, ht⟩
    have h1 : ((t • x0 : X) : G) = z₂ := congrArg Subtype.val ht
    rw [conjAction_smul_val] at h1
    exact hno t t.property h1
  have hlt : Nat.card (orbit T x0) < Nat.card X := by
    have hinj : Function.Injective (fun z : orbit T x0 => (z.1 : X)) := by
      intro z₁ z₂ h
      exact Subtype.ext h
    have hnotsurj : ¬ Function.Surjective (fun z : orbit T x0 => (z.1 : X)) := by
      intro hs
      obtain ⟨z, hz⟩ := hs ⟨z₂, hx2⟩
      apply hyorb
      rw [← hz]
      exact z.2
    let : Fintype (orbit T x0) := Fintype.ofFinite _
    let : Fintype X := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_not_surjective _ hinj hnotsurj
  omega

theorem card_swapFix_mul [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1) :
    Nat.card (swapFix G a b s) * d = p ^ f + 1 := by
  have hT := hQ.card_pairStab_eq_mul_swapFix hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd
    hd hQcard hΩcard hTcard hsa hs2
  have hq : 3 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
  have h2 : p ^ (2 * f) - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    rw [mul_comm 2 f, pow_mul, ← nat_mul_self_sub_one (p ^ f) (by omega), sq]
  rw [hT, h2, mul_assoc] at hTcard
  exact Nat.eq_of_mul_eq_mul_left (by omega) hTcard

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
