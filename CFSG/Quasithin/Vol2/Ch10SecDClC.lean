module

public import CFSG.Quasithin.Vol2.Ch10SecDClB
public import CFSG.Quasithin.Vol2.Ch10SecD33H

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjugate_le_of_mem {A B : Subgroup G} {g : G} (hAB : A ≤ B) (hg : g ∈ B) :
    CFSG.conjugate A g ≤ B := fun x hx => by
  have hx' : g * x * g⁻¹ ∈ A := SecA.mem_conjugate_iff.mp hx
  have e1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e1]
  exact B.mul_mem (B.mul_mem (B.inv_mem hg) (hAB hx')) hg

theorem false_of_comm (hW : FactSymFiveWrTwo) {Y K₁ H H' : Subgroup G}
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hHY : H ≤ Y) (hK₁ : K₁ ∈ cComp Y) {s : G}
    (hsY : s ∈ Y) (hO : oTwoUpper H ≤ K₁ ⊔ CFSG.conjugate K₁ s) (hY2 : pCoreOf 2 Y ≤ H)
    (hK₁H' : K₁ ≤ H') (hsH' : s ∈ H') {y : G} (hyH : y ∈ H)
    (hyK : y ∈ K₁ ⊔ CFSG.conjugate K₁ s) (hyo : Odd (orderOf y)) (hy1 : y ≠ 1)
    (hc1 : ∀ k ∈ K₁, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H')
    (hc2 : ∀ k ∈ K₁, s * y * s⁻¹ * k * (s * y * s⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 H') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₂ := CFSG.conjugate K₁ s with hK₂def
  have hK₂ : K₂ ∈ cComp Y := conjugate_mem_cComp hK₁ hsY
  have h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := le_normalizer_of_mem_cComp hK₂ hK₁
  have h21 : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := le_normalizer_of_mem_cComp hK₁ hK₂
  have hyN1 : y ∈ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer h21 hyK
  have hyN2 : y ∈ Subgroup.normalizer (K₂ : Set G) := sup_le h12 Subgroup.le_normalizer hyK
  have hK₂H' : K₂ ≤ H' := conjugate_le_of_mem hK₁H' hsH'
  have hO2 : ∀ K : Subgroup G, K ≤ H' → K ⊓ pCoreOf 2 H' ≤ pCoreOf 2 K := fun K hK =>
    le_pCoreOf_of_normalizes inf_le_left
      (fun k hk => mem_normalizer_inf (Subgroup.le_normalizer hk)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H' (hK hk)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H').to_le inf_le_right)
  have hcK : ∀ {K : Subgroup G}, y ∈ Subgroup.normalizer (K : Set G) → ∀ k ∈ K,
      y * k * y⁻¹ * k⁻¹ ∈ K := fun {K} hyN k hk =>
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN k).mp hk) (K.inv_mem hk)
  have hu1 : y ∈ barCent K₁ :=
    mem_barCent_iff.mpr ⟨hyN1, fun k hk => hO2 K₁ hK₁H' ⟨hcK hyN1 k hk, hc1 k hk⟩⟩
  have hu2 : y ∈ barCent K₂ := mem_barCent_iff.mpr ⟨hyN2, fun k' hk' => by
    have hk : s * k' * s⁻¹ ∈ K₁ := SecA.mem_conjugate_iff.mp hk'
    have h1 := hc2 _ hk
    have e1 : s * y * s⁻¹ * (s * k' * s⁻¹) * (s * y * s⁻¹)⁻¹ * (s * k' * s⁻¹)⁻¹ =
        s * (y * k' * y⁻¹ * k'⁻¹) * s⁻¹ := by group
    rw [e1] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H' (H'.inv_mem hsH')) _).mp h1
    have e2 : s⁻¹ * (s * (y * k' * y⁻¹ * k'⁻¹) * s⁻¹) * s⁻¹⁻¹ = y * k' * y⁻¹ * k'⁻¹ := by
      group
    rw [e2] at h2
    exact hO2 K₂ hK₂H' ⟨hcK hyN2 k' hk', h2⟩⟩
  have hyO := le_pCoreOf_of_barCent hW e hHY (subnormal_of_mem_cComp hK₁)
    (subnormal_of_mem_cComp hK₂) h12 hO hY2 hyH hu1 hu2
  exact hy1 (eq_one_of_odd_of_mem (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hyO hyo)

theorem comm_mem_of_commutator_le {K' J H' : Subgroup G} (hK' : IsSubnormal K' H')
    (h : ⁅K', J⁆ ≤ pCoreOf 2 K') : ∀ j ∈ J, ∀ k ∈ K', j * k * j⁻¹ * k⁻¹ ∈ pCoreOf 2 H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro j hj k hk
  have h1 := Subgroup.commutator_mem_commutator hj hk
  rw [commutatorElement_def, Subgroup.commutator_comm] at h1
  exact A4.pCoreOf_le_of_subnormal 2 hK' (h h1)

end CFSG.Quasithin.Vol2.Ch10.SecD
