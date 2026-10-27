module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.Open CFSG.Blueprint C11P9A CFSG.QuasithinUnique.Setup.X6

variable {Q : Type} [Group Q]

theorem eq_or_eq_of_ne [Finite Q] {S : Subgroup Q} {B : Fin 2 → Subgroup Q} (hP : ParabPair S B)
    {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂) :
    ∃ k : Fin 2, B₂ = B k := by
  rcases hP.eq_or_eq_of_isL24Sub h₂ with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exfalso
    subst h
    exact hP.not_isL24Sub_top h₁ hne h₂

theorem part1 [Finite Q] {S : Subgroup Q} {B : Fin 2 → Subgroup Q} (hP : ParabPair S B)
    {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂)
    (H : Subgroup Q) (hB₂H : B₂ ≤ H) (hSH : S ≤ H) :
    H = ⊤ ∨ H ≤ Subgroup.normalizer (B₂ : Set Q) := by
  have hB₂X : B₂ ≤ perfectCore H := le_perfectCore_of_perfect hB₂H h₂.2.1
  have hHN : H ≤ Subgroup.normalizer (perfectCore H : Set Q) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H)
  have hX1 : perfectCore H ≠ ⊥ := fun h => h₂.1 (le_bot_iff.mp (h ▸ hB₂X))
  obtain ⟨k, hk⟩ := eq_or_eq_of_ne hP hne h₁ h₂
  rcases hP.classify _ hX1 (perfectCore_perfect H) (hSH.trans hHN) with h | h | h
  · right
    have hk0 : k = 0 := by
      by_contra hk0
      have hk1 : k = 1 := by omega
      exact hP.not_le₁₀ (hk1 ▸ hk ▸ h ▸ hB₂X)
    rw [hk, hk0, ← h]
    exact hHN
  · right
    have hk1 : k = 1 := by
      by_contra hk1
      have hk0 : k = 0 := by omega
      exact hP.not_le₀₁ (hk0 ▸ hk ▸ h ▸ hB₂X)
    rw [hk, hk1, ← h]
    exact hHN
  · left
    exact eq_top_iff.mpr (h ▸ perfectCore_le H)

theorem exists_conj_of_card_nine [Finite Q] {M E T : Subgroup Q} (hEM : E ≤ M) (hTM : T ≤ M)
    (hE : Nat.card ↥E = 9) (hT : Nat.card ↥T = 9) (hM : ¬ 27 ∣ Nat.card ↥M) :
    ∃ m ∈ M, E = T.map (MulAut.conj m).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : ∀ {X : Subgroup Q}, X ≤ M → Nat.card ↥X = 9 →
      IsPGroup 3 ↥(X.subgroupOf M) ∧ ¬ 3 ∣ (X.subgroupOf M).index := by
    intro X hXM hX
    have hc : Nat.card ↥(X.subgroupOf M) = 9 := by
      rw [← hX]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
    refine ⟨IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), fun h3 => hM ?_⟩
    have hi := (X.subgroupOf M).card_mul_index
    rw [hc] at hi
    rw [← hi]
    exact Nat.mul_dvd_mul_left 9 h3
  obtain ⟨hE3, hEi⟩ := hsub hEM hE
  obtain ⟨hT3, hTi⟩ := hsub hTM hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M (hT3.toSylow hTi) (hE3.toSylow hEi)
  refine ⟨g, g.2, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · have hx' : (⟨x, hEM hx⟩ : ↥M) ∈ ((hE3.toSylow hEi : Sylow 3 ↥M) : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    refine ⟨(g : Q)⁻¹ * x * g, Subgroup.mem_subgroupOf.mp hx', ?_⟩
    simp [mul_assoc]
  · obtain ⟨y, hy, rfl⟩ := hx
    have hy' : (⟨y, hTM hy⟩ : ↥M) ∈ ((hT3.toSylow hTi : Sylow 3 ↥M) : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr hy
    have h1 : g * (⟨y, hTM hy⟩ : ↥M) * g⁻¹ ∈
        ((hE3.toSylow hEi : Sylow 3 ↥M) : Subgroup ↥M) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, mul_assoc] using hy'
    simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp h1

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
