module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.LocDblDcos

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc

variable {Γ : Type} [Group Γ]

theorem sylow_of_card_two [Finite Γ] {K : Subgroup Γ} {k : ℕ} (hK : Nat.card K = 2 ^ k)
    (hnd : ¬ 2 ^ (k + 1) ∣ Nat.card Γ) : ∃ S : Sylow 2 Γ, S.toSubgroup = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨K, IsPGroup.of_card (n := k) hK, ?_⟩, rfl⟩
  intro R hR hle
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card R
  rw [hm] at hdvd
  have hmk : m ≤ k := by
    by_contra hc
    push Not at hc
    exact hnd ((pow_dvd_pow 2 (by omega)).trans hdvd)
  have hRK : Nat.card R ≤ Nat.card K := by
    rw [hm, hK]
    exact Nat.pow_le_pow_right (by norm_num) hmk
  exact (Subgroup.eq_of_le_of_card_ge hle hRK).symm

open Pointwise in
theorem exists_conj_of_card_two [Finite Γ] {K K' : Subgroup Γ} {k : ℕ} (hK : Nat.card K = 2 ^ k)
    (hK' : Nat.card K' = 2 ^ k) (hnd : ¬ 2 ^ (k + 1) ∣ Nat.card Γ) :
    ∃ g : Γ, K.map (MulAut.conj g).toMonoidHom = K' := by
  obtain ⟨S, hS⟩ := sylow_of_card_two hK hnd
  obtain ⟨S', hS'⟩ := sylow_of_card_two hK' hnd
  haveI : Finite (Sylow 2 Γ) :=
    Finite.of_injective (fun S : Sylow 2 Γ => (S : Subgroup Γ)) (fun S T h => Sylow.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S S'
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • S.toSubgroup = S'.toSubgroup := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [hS, hS'] at h1
  rw [← h1]
  rfl

theorem no_overgroup_of_sylow [Finite Γ] {R : Subgroup Γ} (hR : Nat.card R = 2 ^ 10)
    (hnd : ¬ 2 ^ (10 + 1) ∣ Nat.card Γ) (h9 : 9 ∣ Nat.card Γ)
    (hkey : ∀ X : Subgroup Γ, R ≤ X → X ≠ ⊤ → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False) :
    ∀ X S : Subgroup Γ, Nat.card S = 2 ^ 10 → S ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False := by
  intro X S hS hSX h5 h9X
  obtain ⟨g, hg⟩ := exists_conj_of_card_two (K := R) (K' := S) (k := 10) hR hS hnd
  let c : Γ ≃* Γ := (MulAut.conj g⁻¹ : Γ ≃* Γ)
  have hRX : R ≤ X.map c.toMonoidHom := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨g * y * g⁻¹, hSX ?_, ?_⟩
    · rw [← hg]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    · simp [c, MulAut.conj_apply, mul_assoc]
  have hcardX : Nat.card (X.map c.toMonoidHom) = Nat.card X :=
    Nat.card_congr (X.equivMapOfInjective c.toMonoidHom c.injective).toEquiv.symm
  have hne : X.map c.toMonoidHom ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top] at hcardX
    exact h9X (hcardX ▸ h9)
  exact hkey _ hRX hne (hcardX ▸ h5) (hcardX ▸ h9X)

theorem no_overgroup_transport {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ X S : Subgroup B, Nat.card S = 2 ^ 10 → S ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False) :
    ∀ X S : Subgroup A, Nat.card S = 2 ^ 10 → S ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False := by
  intro X S hS hSX h5 h9
  have hS' : Nat.card (S.map e.toMonoidHom) = 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hS
  have hX : Nat.card (X.map e.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective e.injective
  exact h (X.map e.toMonoidHom) (S.map e.toMonoidHom) hS' (Subgroup.map_mono hSX) (hX ▸ h5) (hX ▸ h9)

end CFSG.Quasithin.H13.LocDbl
