module

public import CFSG.Quasithin.EmptyFaithful.E111RMain

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e1_data {P S V : Subgroup G} (hVP : V ≤ P) (hSyl : IsSylowIn 2 (S ⊓ P) P)
    (hE1 : E1.EOne ↥P (V.subgroupOf P)) :
    ∃ (p : ℕ) (R YR : Subgroup G), p.Prime ∧ p ≠ 2 ∧ R = twoResidual P ∧ R ≤ P ∧ YR ≤ R ∧
      YR ≤ S ⊓ P ∧ (∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      (∀ x ∈ P, ∀ y ∈ YR, x * y * x⁻¹ ∈ YR) ∧ P = R ⊔ (S ⊓ P) ∧
      (∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ YR) ∧ R ≤ ⁅R, V⁆ ⊔ YR := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hp, hp2, R₁, hR₁P, hPR₁, hO₂R₁, hR₁p, hP2, -, hcomm, -⟩ :=
    E1.eOneAmb_of_eOne hVP hE1
  set O₂ : Subgroup G := pCoreOf 2 P with hO₂
  have hO₂P : O₂ ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPO₂ : P ≤ Subgroup.normalizer (O₂ : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hO₂n : ∀ x ∈ P, ∀ z ∈ O₂, x * z * x⁻¹ ∈ O₂ := fun x hx z hz =>
    (Subgroup.mem_normalizer_iff.mp (hPO₂ hx) z).mp hz
  set R : Subgroup G := twoResidual P with hRdef
  have hRP : R ≤ P := twoResidual_le P
  have hPR : ∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual P hx) r).mp hr
  have hRR₁ : R ≤ R₁ := twoResidual_le_of_isTwoQuotient hR₁P hPR₁ hP2
  have hR₁RO : R₁ ≤ R ⊔ O₂ := by
    intro x hx
    obtain ⟨k, hk⟩ := hR₁p x hx
    obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient P x (hR₁P hx)
    exact E1.mem_of_pow_mem_of_coprime (a := 2 ^ j) (b := p ^ k)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2) |>.pow j k)
      (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hk)
  have hO₂S : O₂ ≤ S ⊓ P := by
    have hNn : (O₂.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hO₂P).mpr hPO₂
    exact hSyl.le_of_normal hO₂P hNn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
  have hYRn : ∀ x ∈ P, ∀ y ∈ R ⊓ O₂, x * y * x⁻¹ ∈ R ⊓ O₂ := fun x hx y hy =>
    ⟨hPR x hx y hy.1, hO₂n x hx y hy.2⟩
  refine ⟨p, R, R ⊓ O₂, hp, hp2, rfl, hRP, inf_le_left, inf_le_right.trans hO₂S, hPR, hYRn, ?_,
    ?_, ?_⟩
  ·
    refine le_antisymm (E1.le_twoResidual_sup_of_isSylowIn hSyl) (sup_le hRP inf_le_right)
  ·
    intro x hx
    obtain ⟨k, hk⟩ := hR₁p x (hRR₁ hx)
    exact ⟨k, R.pow_mem hx _, hk⟩
  ·
    have hVN : ∀ v ∈ V, ∀ r ∈ R, v * r * v⁻¹ ∈ R := fun v hv r hr => hPR v (hVP hv) r hr
    have hcR : ⁅R, V⁆ ≤ R := Subgroup.commutator_le.mpr fun r hr v hv => by
      have := R.mul_mem hr (hVN v hv r⁻¹ (R.inv_mem hr))
      simpa [commutatorElement_def, mul_assoc] using this
    have hR₁V : ⁅R₁, V⁆ ≤ ⁅R, V⁆ ⊔ O₂ := by
      refine Subgroup.commutator_le.mpr fun x hx v hv => ?_
      obtain ⟨r, hr, z, hz, rfl⟩ := exists_mul_of_mem_sup
        (fun w hw => le_normalizer_twoResidual P (hO₂P hw)) (hR₁RO hx)
      rw [E1.comm_mul_left]
      have hzv : ⁅z, v⁆ ∈ O₂ := by
        have h1 := hO₂n v (hVP hv) z⁻¹ (O₂.inv_mem hz)
        have h2 := O₂.mul_mem hz h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using h2
      have h1 : r * ⁅z, v⁆ * r⁻¹ ∈ O₂ := hO₂n r (hRP hr) _ hzv
      have h2 : ⁅r, v⁆ ∈ ⁅R, V⁆ := Subgroup.commutator_mem_commutator hr hv
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)
    have hRO : R ≤ ⁅R, V⁆ ⊔ O₂ := fun x hx =>
      (sup_le hR₁V le_sup_right) (hcomm (hRR₁ hx))
    intro x hx
    have hx2 : x ∈ O₂ ⊔ ⁅R, V⁆ := by rw [sup_comm]; exact hRO hx
    obtain ⟨z, hz, c, hc, rfl⟩ := exists_mul_of_mem_sup
      (fun c hc => hPO₂ (hRP (hcR hc))) hx2
    have hzR : z ∈ R := by
      have : z = (z * c) * c⁻¹ := by group
      rw [this]
      exact R.mul_mem hx (R.inv_mem (hcR hc))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (⟨hzR, hz⟩ : z ∈ R ⊓ O₂))
      (Subgroup.mem_sup_left hc)

end CFSG.Quasithin.RonanE111
