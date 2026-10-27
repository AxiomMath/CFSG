module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Quasithin.E3
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem relIndex_sup_of_le_normalizer [Group Γ] {H K : Subgroup Γ}
    (hH : H ≤ Subgroup.normalizer (K : Set Γ)) :
    K.relIndex (H ⊔ K) = K.relIndex H := by
  set C : Subgroup Γ := H ⊔ K with hCdef
  have hHC : H ≤ C := le_sup_left
  have hKC : K ≤ C := le_sup_right
  have hCN : C ≤ Subgroup.normalizer (K : Set Γ) := sup_le hH Subgroup.le_normalizer
  have hN : (K.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hCN
  haveI : (K.subgroupOf C).Normal := hN
  have hsup : H.subgroupOf C ⊔ K.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHC hKC]
    exact Subgroup.subgroupOf_self C
  have key := Subgroup.relIndex_sup_right (H.subgroupOf C) (K.subgroupOf C)
  rw [hsup, Subgroup.relIndex_top_right] at key
  have e1 : K.relIndex C = (K.subgroupOf C).index := rfl
  rw [e1, key]
  exact Subgroup.relIndex_subgroupOf hHC

theorem mQuot_commutator_le_five [Finite Γ] {V U W₀ W₁ R : Subgroup Γ} {v : Γ}
    (hV : IsPGroup 2 ↥V) (hU : Nat.card ↥U = 16) (hVc : Nat.card ↥V ≤ 2 ^ 10)
    (hUV : U ≤ V) (hUW₀ : U ≤ W₀) (hW₀W₁ : W₀ ≤ W₁) (hW₁R : W₁ ≤ R) (hVR : ¬ V ≤ R)
    (hcomm : ⁅W₁, Subgroup.zpowers v⁆ ≤ V ⊓ R) (hPN : V ⊓ R ≤ Subgroup.normalizer (W₀ : Set Γ)) :
    mQuot (⁅W₁, Subgroup.zpowers v⁆ ⊔ W₀) W₀ ≤ 5 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup Γ := V ⊓ R with hPdef
  set A : Subgroup Γ := ⁅W₁, Subgroup.zpowers v⁆ ⊔ W₀ with hAdef
  have hUP : U ≤ P := le_inf hUV (hUW₀.trans (hW₀W₁.trans hW₁R))
  have hPV : P ≤ V := inf_le_left
  have hPne : P ≠ V := by
    intro h
    apply hVR
    intro x hx
    have hxP : x ∈ P := h ▸ hx
    exact hxP.2
  have hA : A ≤ P ⊔ W₀ := sup_le_sup_right hcomm _
  have hW₀A : W₀ ≤ A := le_sup_right
  have h1 : W₀.relIndex A ∣ W₀.relIndex (P ⊔ W₀) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex W₀ A (P ⊔ W₀) hW₀A hA)
  have h2 : W₀.relIndex (P ⊔ W₀) = W₀.relIndex P := relIndex_sup_of_le_normalizer hPN
  have h3 : W₀.relIndex P ∣ U.relIndex P := Subgroup.relIndex_dvd_of_le_left (L := P) hUW₀
  have h4 : U.relIndex V = U.relIndex P * P.relIndex V :=
    (Subgroup.relIndex_mul_relIndex U P V hUP hPV).symm
  have h5 : P.relIndex V ≠ 1 := fun h => hPne (le_antisymm hPV (Subgroup.relIndex_eq_one.mp h))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hV
  have hPdvd : P.relIndex V ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card (H := P) (K := V)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hPdvd
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso
      apply h5
      rw [hi, h0, pow_zero]
    · exact h0
  have hUVdvd : U.relIndex V ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card (H := U) (K := V)
  have hUcard : U.relIndex V * 16 = Nat.card ↥V := by
    have := Subgroup.relIndex_mul_card (H := U) (K := V)
    rw [inf_eq_left.mpr hUV, hU] at this
    exact this
  have hUV64 : U.relIndex V ≤ 64 := by
    have : U.relIndex V * 16 ≤ 2 ^ 10 := hUcard ▸ hVc
    omega
  have hPU : U.relIndex P ∣ 2 ^ n :=
    (Dvd.intro _ h4.symm).trans hUVdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hPU
  have hiP : 2 ≤ P.relIndex V := by
    rw [hi]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
  have h2le : 2 * U.relIndex P ≤ 64 := by
    have : U.relIndex P * 2 ≤ U.relIndex P * P.relIndex V := Nat.mul_le_mul_left _ hiP
    omega
  have hxy : W₀.relIndex A ∣ U.relIndex P := h1.trans (h2 ▸ h3)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hj ▸ hxy)
  have hj5 : j ≤ 5 := by
    by_contra hc
    simp only [not_le] at hc
    have h64 : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hc
    norm_num at h64
    omega
  have hk5 : k ≤ 5 := by
    have hkj : k ≤ j := by
      have hxle : W₀.relIndex A ≤ U.relIndex P :=
        Nat.le_of_dvd (by rw [hj]; exact pow_pos (by norm_num) j) hxy
      have h2k : 2 ^ k ≤ 2 ^ j := by rw [← hk, ← hj]; exact hxle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2k
    omega
  unfold mQuot
  rw [hk, padicValNat.prime_pow]
  exact hk5

end CFSG.Quasithin.H13.L827X
