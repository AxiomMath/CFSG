module

public import CFSG.RankThree.PartOne.K133C.OrthForm

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Moving

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : (ι → K) → K} {J : Matrix ι ι K}

theorem exists_moving_orth {p : ℕ} (hpK : (p : K) ≠ 0) (hP : PolarQuad Q J) {s : ι → K} (hs0 : s ≠ 0)
    (hs : Q s = 0) (F : Subgroup (GL ι K)) (hFQ : F ≤ orthSub Q) (hpow : ∀ h ∈ F, h ^ p = 1)
    (hfix : ∀ h ∈ F, (h : Matrix ι ι K) *ᵥ s = s) (hF1 : ∃ h ∈ F, h ≠ 1) :
    ∃ S : Subgroup (GL ι K), S ≤ orthSub Q ∧ IsPGroup 2 S ∧
      (∀ h ∈ F, ∀ x ∈ S, h * x * h⁻¹ ∈ S) ∧ ∃ h ∈ F, ∃ x ∈ S, h * x * h⁻¹ ≠ x := by
  have hψs : (J *ᵥ s) ⬝ᵥ s = 0 := by rw [dotProduct_comm]; exact hP.alt s
  have hψ : ∀ h ∈ F, ∀ y : ι → K,
      (J *ᵥ s) ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = (J *ᵥ s) ⬝ᵥ y := by
    intro h hh y
    have h1 : (J *ᵥ s) ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = bf J ((h : Matrix ι ι K) *ᵥ y) s :=
      dotProduct_comm _ _
    have h2 : (J *ᵥ s) ⬝ᵥ y = bf J y s := dotProduct_comm _ _
    rw [h1, h2]
    have := bf_map_of_mem_orthSub hP (hFQ hh) y s
    rw [hfix h hh] at this
    exact this
  have hsw_of : ∀ w : ι → K, (J *ᵥ s) ⬝ᵥ w = 0 → bf J s w = 0 := by
    intro w hw
    have h1 : (J *ᵥ s) ⬝ᵥ w = bf J w s := dotProduct_comm _ _
    rw [bf_comm J hP.symm, ← h1]
    exact hw
  refine ⟨radFlag s (J *ᵥ s) hψs ⊓ orthSub Q, inf_le_right, ?_, ?_, ?_⟩
  · intro g
    refine ⟨2, ?_⟩
    have := radFlag_pow_four (hψv := hψs) g.2.1
    apply Subtype.ext
    simpa using this
  · intro h hh x hx
    refine ⟨radFlag_normalized (hfix h hh) (hψ h hh) hx.1, ?_⟩
    exact (orthSub Q).mul_mem ((orthSub Q).mul_mem (hFQ hh) hx.2) ((orthSub Q).inv_mem (hFQ hh))
  · obtain ⟨w, hw, h, hh, hne⟩ := exists_moved_of_family (hψv := hψs) hpK F hpow hfix hψ hF1
      (fun w => eichGL hP s w)
      (fun h hh w hw => by
        rw [conj_eichGL hP (hFQ hh) hs (hsw_of w hw), hfix h hh])
      (fun w w' hw hw' hww => eichGL_inj hP hs0 (hsw_of w hw) (hsw_of w' hw') hww)
    have hsw := hsw_of w hw
    exact ⟨h, hh, eichGL hP s w,
      ⟨eichGL_mem_radFlag hP hsw hψs, eichGL_mem_orthSub hP hs hsw⟩, hne⟩

end Moving

section Commutator

variable {G : Type} [Group G] [Finite G]

theorem exists_moved_of_commutator_eq (F S : Subgroup G) (hS1 : S ≠ ⊥) (hSc : S = ⁅S, F⁆) :
    ∃ h ∈ F, ∃ x ∈ S, h * x * h⁻¹ ≠ x := by
  by_contra hno
  push Not at hno
  apply hS1
  rw [hSc, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x hx h hh => ?_
  rw [Subgroup.mem_bot]
  have h1 := hno h hh x (hSc ▸ hx)
  calc x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) := by group
    _ = x * (h * x * h⁻¹)⁻¹ := by group
    _ = 1 := by rw [h1, mul_inv_cancel]

theorem exists_commutator_two_group {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (F S N : Subgroup G)
    (hFp : IsPGroup p F) (hS2 : IsPGroup 2 S) (hSF : F ≤ Subgroup.normalizer (S : Set G))
    (hmv : ∃ h ∈ F, ∃ x ∈ S, h * x * h⁻¹ ≠ x) (hN : ⁅S, F⁆ ≤ N) :
    ∃ S' : Subgroup G, S' ≤ N ∧ IsPGroup 2 S' ∧ (∀ h ∈ F, ∀ x ∈ S', h * x * h⁻¹ ∈ S') ∧
      ∃ h ∈ F, ∃ x ∈ S', h * x * h⁻¹ ≠ x := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : ⁅S, F⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.1 hSF
  have hnorm : F ≤ Subgroup.normalizer ((⁅S, F⁆ : Subgroup G) : Set G) :=
    K133.le_normalizer_commutator' F S F hSF Subgroup.le_normalizer
  have hcop : Nat.Coprime (Nat.card F) (Nat.card S) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hFp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hS2
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hnil : Group.IsNilpotent S := hS2.isNilpotent
  have hdbl : ⁅⁅S, F⁆, F⁆ = ⁅S, F⁆ :=
    HNB.commutator_double_eq_self_of_coprime_solvable F S hSF hcop inferInstance
  have hne : ⁅S, F⁆ ≠ ⊥ := by
    obtain ⟨h, hh, x, hx, hxh⟩ := hmv
    intro hbot
    apply hxh
    have hc : ⁅x, h⁆ ∈ (⁅S, F⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hx hh
    rw [hbot, Subgroup.mem_bot] at hc
    have h1 : x * h * x⁻¹ * h⁻¹ = 1 := hc
    calc h * x * h⁻¹ = (h * x * h⁻¹ * x⁻¹) * x := by group
      _ = x := by
        have : h * x * h⁻¹ * x⁻¹ = 1 := by
          have h2 : x * h * x⁻¹ * h⁻¹ = 1 := h1
          calc h * x * h⁻¹ * x⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ := by group
            _ = 1 := by rw [h2, inv_one]
        rw [this, one_mul]
  refine ⟨⁅S, F⁆, hN, hS2.to_le hle, fun h hh x hx => ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 (hnorm hh) x).1 hx
    exact this
  · by_contra hno
    push Not at hno
    apply hne
    rw [← hdbl, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun x hx h hh => ?_
    rw [Subgroup.mem_bot]
    have h1 := hno h hh x hx
    calc x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) := by group
      _ = x * (h * x * h⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]

end Commutator

end CFSG.RankThree.PartOne.K133C
