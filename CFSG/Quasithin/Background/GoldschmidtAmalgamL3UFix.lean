module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

theorem GoldHyp.inf_normalizer_le_right (h : GoldHyp A B) :
    B ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) ≤ A ⊓ B := by
  have hTM : A ⊓ B ≤ B ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hmul2 := Subgroup.relIndex_mul_relIndex _ _ _ hTM
    (inf_le_left : B ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) ≤ B)
  rw [h.relIndex_right] at hmul2
  have hdvd2 : (B ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D)).relIndex B ∣ 3 :=
    Dvd.intro_left _ hmul2
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with k1 | k3
  · exact (h.not_normal_T_right fun g hg => (Subgroup.relIndex_eq_one.mp k1 hg).2).elim
  · rw [k3] at hmul2
    exact Subgroup.relIndex_eq_one.mp (by omega)

theorem GoldHyp.inf_conjSub_le_pCoreOf_right (h : GoldHyp A B) {c : D} (hcB : c ∈ B)
    (hcA : c ∉ A) : A ⊓ B ⊓ conjSub c (A ⊓ B) ≤ pCoreOf 2 B := by
  have hQT : pCoreOf 2 B ≤ A ⊓ B := h.vertex_right.pCoreOf_le
  have hQ2 : (pCoreOf 2 B).relIndex (A ⊓ B) = 2 := h.vertex_right.relIndex_pCoreOf_T
  have hQN : ∀ t : D, t ∈ pCoreOf 2 B ↔ c * t * c⁻¹ ∈ pCoreOf 2 B := fun t =>
    Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hcB) t
  intro y hy
  by_contra hyQ
  have hy' : c⁻¹ * y * c ∈ A ⊓ B := mem_conjSub.mp hy.2
  have hy'Q : c⁻¹ * y * c ∉ pCoreOf 2 B := fun hq => hyQ (by
    have := (hQN _).mp hq
    simpa [mul_assoc] using this)
  have hle : conjSub c (A ⊓ B) ≤ A ⊓ B := by
    intro s hs
    by_cases hsQ : s ∈ pCoreOf 2 B
    · exact hQT hsQ
    · have ht : c⁻¹ * s * c ∈ A ⊓ B := mem_conjSub.mp hs
      have htQ : c⁻¹ * s * c ∉ pCoreOf 2 B := fun hq => hsQ (by
        have := (hQN _).mp hq
        simpa [mul_assoc] using this)
      have h1 := GoldAmL3.mul_inv_mem_of_relIndex_eq_two hQ2 ht hy' htQ hy'Q
      have h2 : s * y⁻¹ ∈ pCoreOf 2 B := by
        have := (hQN _).mp h1
        have e : c * (c⁻¹ * s * c * (c⁻¹ * y * c)⁻¹) * c⁻¹ = s * y⁻¹ := by group
        rwa [e] at this
      have e : s = (s * y⁻¹) * y := by group
      rw [e]
      exact (A ⊓ B).mul_mem (hQT h2) hy.1
  have heq : conjSub c (A ⊓ B) = A ⊓ B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hcN : c ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
    mem_normalizer_of_conjSub_eq heq
  exact hcA (h.inf_normalizer_le_right ⟨hcB, hcN⟩).1

end GoldAmL

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem mem_ballStab_one_of_fix_two {u v w : CosetGeom (A ⊔ B) A B} (hu : vtype u = true)
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w) (hvw : v ≠ w) {x : D}
    (hxu : x ∈ stab u) (hxv : x ∈ stab v) (hxw : x ∈ stab w) : x ∈ ballStab 1 u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  have hadj : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) :=
    (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm
  have hv0 : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (g⁻¹ • v) := by
    have := (smul_adj g⁻¹).mpr hv
    rwa [inv_smul_smul] at this
  have hw0 : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (g⁻¹ • w) := by
    have := (smul_adj g⁻¹).mpr hw
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk1, hk0⟩ := exists_stab_smul_eq hadj hv0
  obtain ⟨k', hk1', hk0'⟩ := exists_stab_smul_eq hadj hw0
  have hkB : (k : D) ∈ B := by
    have := mem_stab_of_smul_eq hk1
    rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  have hkB' : (k' : D) ∈ B := by
    have := mem_stab_of_smul_eq hk1'
    rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  have hcB : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ B := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact B.mul_mem (B.inv_mem hkB) hkB'
  have hcA : ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∉ A := fun hA => hvw (by
    have e0 : (k⁻¹ * k' : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B :=
      smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) hA
    have e1 : k' • γ₀ (A ⊔ B) A B = k • γ₀ (A ⊔ B) A B := by
      have : k' = k * (k⁻¹ * k') := by group
      rw [this, mul_smul, e0]
    have e2 : g⁻¹ • v = g⁻¹ • w := by rw [← hk0, ← hk0', e1]
    exact smul_left_cancel g⁻¹ e2)
  obtain rfl : v = (g * k) • γ₀ (A ⊔ B) A B := by rw [mul_smul, hk0, smul_inv_smul]
  obtain rfl : w = (g * k') • γ₀ (A ⊔ B) A B := by rw [mul_smul, hk0', smul_inv_smul]
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hxu
  rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B), mem_conjSub] at hxv hxw
  rw [ballStab_smul, mem_conjSub]
  set y : D := ((g * k : ↥(A ⊔ B)) : D)⁻¹ * x * ((g * k : ↥(A ⊔ B)) : D) with hy
  have hyA : y ∈ A := hxv
  have hyB : y ∈ B := by
    have e : y = (k : D)⁻¹ * ((g : D)⁻¹ * x * g) * k := by
      simp only [hy, Subgroup.coe_mul]
      group
    rw [e]
    exact B.mul_mem (B.mul_mem (B.inv_mem hkB) hxu) hkB
  have hyc : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ A := by
    have e : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) =
        ((g * k' : ↥(A ⊔ B)) : D)⁻¹ * x * ((g * k' : ↥(A ⊔ B)) : D) := by
      simp only [hy, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hxw
  have hycB : ((k⁻¹ * k' : ↥(A ⊔ B)) : D)⁻¹ * y * ((k⁻¹ * k' : ↥(A ⊔ B)) : D) ∈ B :=
    B.mul_mem (B.mul_mem (B.inv_mem hcB) hyB) hcB
  have hmem : y ∈ A ⊓ B ⊓ conjSub ((k⁻¹ * k' : ↥(A ⊔ B)) : D) (A ⊓ B) :=
    ⟨⟨hyA, hyB⟩, mem_conjSub.mpr ⟨hyc, hycB⟩⟩
  have hQ : y ∈ pCoreOf 2 B := h.gold.inf_conjSub_le_pCoreOf_right hcB hcA hmem
  have hQ' : (g : D)⁻¹ * x * g ∈ pCoreOf 2 B := by
    have e : (g : D)⁻¹ * x * g = (k : D) * y * (k : D)⁻¹ := by
      simp only [hy, Subgroup.coe_mul]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hkB) y).mp hQ
  have hle := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₁ (A ⊔ B) A B)
  rw [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at hle
  exact hle hQ'

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
