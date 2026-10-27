module

public import CFSG.Quasithin.EmptyFaithful.T1515C6P

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_invariant_R_sylow_of_prime (p : ℕ) [Fact p.Prime] {R S P : Subgroup G}
    (hRP : R ≤ P) (hRS : R ≤ S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hSR : S ≤ Subgroup.normalizer (R : Set G))
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) (hS2 : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ R.relIndex P) :
    ∃ Y : Subgroup G, IsSylowIn p Y P ∧ S ≤ Subgroup.normalizer ((R ⊔ Y : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := S ⊔ P with hH
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := sup_le hSP Subgroup.le_normalizer
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := sup_le hSR hPR
  have hPH : P ≤ H := le_sup_right
  have hSH : S ≤ H := le_sup_left
  obtain ⟨Y₀, hY₀, -⟩ := exists_isSylowIn_ge p (bot_le : (⊥ : Subgroup G) ≤ P)
    (by simp [IsPGroup] : IsPGroup p (⊥ : Subgroup G))
  have hY₀P : Y₀ ≤ P := hY₀.1
  set Q₀ : Subgroup G := R ⊔ Y₀ with hQ₀
  have hQ₀P : Q₀ ≤ P := sup_le hRP hY₀P
  have hQ₀H : Q₀ ≤ H := hQ₀P.trans hPH
  set A : Subgroup G := H ⊓ Subgroup.normalizer (Q₀ : Set G) with hA
  have hconjR : ∀ h ∈ H, A1b.conjSub h R = R := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHR hh)
  have hconjP : ∀ h ∈ H, A1b.conjSub h P = P := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh)
  have hconjQ : ∀ h ∈ H, ∀ Y : Subgroup G, A1b.conjSub h (R ⊔ Y) = R ⊔ A1b.conjSub h Y := by
    intro h hh Y
    unfold A1b.conjSub
    rw [Subgroup.map_sup]
    congr 1
    exact hconjR h hh
  have hfrat : ∀ h ∈ H, ∃ p ∈ P, p⁻¹ * h ∈ A := by
    intro h hh
    have hS3 : IsSylowIn p (A1b.conjSub h Y₀) P := by
      have := isSylowIn_conjSub hY₀ h
      rwa [hconjP h hh] at this
    obtain ⟨p, hp, hpeq⟩ := isSylowIn_conj_of hY₀ hS3
    have hp' : p⁻¹ ∈ H := H.inv_mem (hPH hp)
    have hnorm : p⁻¹ * h ∈ Subgroup.normalizer (Q₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show A1b.conjSub (p⁻¹ * h) Q₀ = Q₀
      rw [A1b.conjSub_mul, hQ₀, hconjQ h hh, ← hpeq, hconjQ p⁻¹ hp', ← A1b.conjSub_mul]
      simp [A1b.conjSub_one]
    exact ⟨p, hp, H.mul_mem hp' hh, hnorm⟩
  have hAnormP : A ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans hHP
  have hHeq : A ⊔ P = H := by
    apply le_antisymm (sup_le inf_le_left hPH)
    intro h hh
    obtain ⟨p, hp, hpA⟩ := hfrat h hh
    have : h = p * (p⁻¹ * h) := by group
    rw [this]
    exact (A ⊔ P).mul_mem (Subgroup.mem_sup_right hp) (Subgroup.mem_sup_left hpA)
  have hR3 : R.relIndex Q₀ * Q₀.relIndex P = R.relIndex P :=
    Subgroup.relIndex_mul_relIndex R Q₀ P le_sup_left hQ₀P
  have hAodd : ¬ 2 ∣ A.relIndex H := by
    have h1 := B6.relIndex_inf_eq_relIndex_sup hAnormP
    rw [hHeq] at h1
    have hQAP : Q₀ ≤ A ⊓ P := le_inf (fun x hx => ⟨hQ₀H hx, Subgroup.le_normalizer hx⟩) hQ₀P
    have h2 : (A ⊓ P).relIndex P ∣ Q₀.relIndex P := Subgroup.relIndex_dvd_of_le_left P hQAP
    rw [← h1]
    intro hd
    exact hodd (hR3 ▸ dvd_mul_of_dvd_right (hd.trans h2) _)
  have hSsyl : IsSylowTwoOf S H := by
    refine ⟨hSH, hS2, ?_⟩
    have h1 := B6.relIndex_inf_eq_relIndex_sup hSP
    have hRSP : R ≤ S ⊓ P := le_inf hRS hRP
    have h2 : (S ⊓ P).relIndex P ∣ R.relIndex P := Subgroup.relIndex_dvd_of_le_left P hRSP
    intro hd
    have hd' : 2 ∣ S.relIndex H := hd
    rw [hH, ← h1] at hd'
    exact hodd (hd'.trans h2)
  obtain ⟨S₁, hS₁A, -⟩ := exists_isSylowIn_ge 2 (bot_le : (⊥ : Subgroup G) ≤ A)
    (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup G))
  have hS₁H : IsSylowTwoOf S₁ H := by
    refine ⟨hS₁A.1.trans inf_le_left, hS₁A.2.1, ?_⟩
    have h1 : S₁.relIndex A * A.relIndex H = S₁.relIndex H :=
      Subgroup.relIndex_mul_relIndex S₁ A H hS₁A.1 inf_le_left
    intro hd
    have hd' : 2 ∣ S₁.relIndex H := hd
    rw [← h1] at hd'
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd' with h2 | h2
    · exact hS₁A.2.2 h2
    · exact hAodd h2
  obtain ⟨h, hhH, hS₁eq⟩ := IsSylowTwoOf.exists_conj hSsyl hS₁H
  have hhinv : h⁻¹ ∈ H := H.inv_mem hhH
  refine ⟨A1b.conjSub h⁻¹ Y₀, ?_, ?_⟩
  · have := isSylowIn_conjSub hY₀ h⁻¹
    rwa [hconjP h⁻¹ hhinv] at this
  · rw [← hconjQ h⁻¹ hhinv]
    show S ≤ Subgroup.normalizer ((A1b.conjSub h⁻¹ Q₀ : Subgroup G) : Set G)
    rw [← A1b.conjSub_normalizer]
    intro s hs
    rw [A1b.mem_conjSub_iff]
    have hsS₁ : h * s * h⁻¹ ∈ S₁ := by
      rw [hS₁eq]
      exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
    have := (hS₁A.1.trans inf_le_right) hsS₁
    simpa using this

end CFSG.Quasithin
