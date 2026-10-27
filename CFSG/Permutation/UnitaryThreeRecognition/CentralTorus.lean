module

public import CFSG.Permutation.UnitaryThreeRecognition.TorusIndex
public import CFSG.Permutation.UnitaryThreeRecognition.Conj

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem conj_mem_centQ {b : Ω}
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) {t : G} (ht : t ∈ pairStab G a b) {z : G}
    (hz : z ∈ centQ Q j) : t * z * t⁻¹ ∈ centQ Q j := by
  obtain ⟨hzQ, hzj⟩ := mem_centQ.mp hz
  refine mem_centQ.mpr ⟨hQ.normal t ht.1 z hzQ, ?_⟩
  have htj : t * j = j * t := hcomm t ht j hj
  calc j * (t * z * t⁻¹) = (j * t) * z * t⁻¹ := by group
    _ = (t * j) * z * t⁻¹ := by rw [htj]
    _ = t * (j * z) * t⁻¹ := by group
    _ = t * (z * j) * t⁻¹ := by rw [hzj]
    _ = t * z * t⁻¹ * (t * j * t⁻¹) := by group
    _ = t * z * t⁻¹ * (j * t * t⁻¹) := by rw [htj]
    _ = t * z * t⁻¹ * j := by group

theorem swapFix_commute_centQ [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {w : G} (hw : w ∈ swapFix G a b s) {z : G} (hz : z ∈ centQ Q j) : w * z = z * w := by
  classical
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
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
  let x0 : X := ⟨z, hz, hz1⟩
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup T x0)
  rw [Nat.card_prod] at hos
  let K : Subgroup T := (swapFix G a b s).subgroupOf T
  have hstabK : stabilizer T x0 ≤ K := by
    intro t ht
    have htz : (t : G) * z = z * t := (mem_stabilizer_conjAction_iff t x0).mp ht
    have := hQ.conj_eq_of_commute hb hsa hsb hcomm (mem_centQ.mp hz).1 hz1 t.property htz
    rw [Subgroup.mem_subgroupOf, mem_swapFix]
    refine ⟨t.property, ?_⟩
    calc s * (t : G) = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [this]
  have hKcard : Nat.card K = Nat.card (swapFix G a b s) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
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
  have horb : Nat.card (orbit T x0) ≤ p ^ f - 1 := by
    rw [← hXcard]
    exact Nat.card_le_card_of_injective (fun y => y.1) (fun y₁ y₂ h => Subtype.ext h)
  have hstabcard : Nat.card (swapFix G a b s) ≤ Nat.card (stabilizer T x0) := by
    have hqpos : 0 < p ^ f - 1 := by
      have : 3 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
      omega
    have : (p ^ f - 1) * Nat.card (swapFix G a b s) ≤
        (p ^ f - 1) * Nat.card (stabilizer T x0) := by
      calc (p ^ f - 1) * Nat.card (swapFix G a b s) = Nat.card T := hT.symm
        _ = Nat.card (orbit T x0) *
            Nat.card (stabilizer T x0) := hos.symm
        _ ≤ (p ^ f - 1) * Nat.card (stabilizer T x0) :=
            Nat.mul_le_mul_right _ horb
    exact Nat.le_of_mul_le_mul_left this hqpos
  have hstab_eq : stabilizer T x0 = K :=
    Subgroup.eq_of_le_of_card_ge hstabK (by rw [hKcard]; exact hstabcard)
  have hwK : (⟨w, (mem_swapFix.mp hw).1⟩ : T) ∈ K := by
    rw [Subgroup.mem_subgroupOf]; exact hw
  rw [← hstab_eq] at hwK
  exact (mem_stabilizer_conjAction_iff _ x0).mp hwK

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
