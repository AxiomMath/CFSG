module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenMulti
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

theorem exists_three_subgroup_bar {K : Type} [Group K] [Finite K] {X T : Subgroup K} {n : ℕ}
    (hn : 8 ≤ n) (hO : CFSG.pCore 2 K = ⊥) (hXsn : CFSG.Open.IsSubnormal X ⊤)
    (hXT : X ⊔ T = ⊤) (hT : IsSylowOf 2 T ⊤) (hX : Nonempty (X ≃* alternatingGroup (Fin n))) :
    ∃ P : Subgroup K, IsElemAbelian 3 P ∧ 9 ≤ Nat.card P ∧ Permutes P T ∧
      (10 ≤ n ∨ X ≠ ⊤ → 9 < Nat.card P ∨ IrrOn (normalizer (P : Set K) ⊓ T) P) := by
  obtain ⟨e⟩ := hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have key : ∀ J : Subgroup K, T ≤ normalizer (J : Set K) →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) →
      (∀ P : Subgroup K, P ≤ J → IsPGroup 3 P → IsElemAbelian 3 P) →
      ∃ C : Subgroup K, IsElemAbelian 3 C ∧ Nat.card C = 3 ^ (Nat.card J).factorization 3 ∧
        Permutes C T := by
    intro J hTJ h23 hel
    obtain ⟨C, hC⟩ := exists_isSylowOf 3 J
    exact ⟨C, hel C hC.le hC.isPGroup, hC.card_eq, (coe_sup_eq_mul hT le_top hTJ h23 hC).2⟩
  have hpow : ∀ m k : ℕ, 0 < m → 3 ^ k ∣ m → 3 ^ k ≤ 3 ^ m.factorization 3 := by
    intro m k hm hk
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm.ne').1 hk)
  by_cases hTN : T ≤ normalizer (X : Set K)
  · obtain ⟨J, -, hTJ, h23, hel, hJ9, hJ27⟩ := exists_fibre_subgroup_of_mulEquiv hn e hT2 hTN
    obtain ⟨C, hCe, hCc, hCT⟩ := key J hTJ h23 hel
    have hC9 : 9 ≤ Nat.card C := by
      have := hpow (Nat.card J) 2 Nat.card_pos (by norm_num; exact hJ9)
      rw [← hCc] at this
      simpa using this
    by_cases hsmall : n ≤ 11 ∧ (10 ≤ n ∨ X ≠ ⊤)
    · have hXn : X.Normal := by
        have h1 : normalizer (X : Set K) = ⊤ := by
          rw [eq_top_iff, ← hXT]
          exact sup_le le_normalizer hTN
        exact normalizer_eq_top_iff.1 h1
      obtain ⟨ρ, hρ, hρX⟩ := exists_injective_hom (by omega) hXn hO hT2 hXT e
      have hA : alternatingGroup (Fin n) ≤ ρ.range := hρX ▸ map_le_range ρ X
      have hTρ : IsSylowOf 2 (T.map ρ) ρ.range := by
        refine isSylowOf_of_card (map_le_range ρ T) ?_
        rw [Subgroup.card_map_of_injective hρ, hT.card_eq, Subgroup.card_top,
          Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
      have hΓ : ¬ ρ.range ≤ alternatingGroup (Fin n) ∨ 10 ≤ Fintype.card (Fin n) := by
        rcases hsmall.2 with h10 | hXtop
        · exact Or.inr (by rw [Fintype.card_fin]; exact h10)
        · refine Or.inl fun hle => hXtop (eq_top_iff.2 fun g _ => ?_)
          obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (hρX ▸ hle ⟨g, rfl⟩)
          rw [← hρ hxg]
          exact hx
      obtain ⟨P', hP'Γ, hP'e, hP'9, hP'T, hP'irr⟩ :=
        exists_irr hA hTρ (by rw [Fintype.card_fin]; exact hn)
          (by rw [Fintype.card_fin]; exact hsmall.1) hΓ
      refine ⟨P'.comap ρ, isElemAbelian_comap_of_injective hρ hP'e, ?_,
        mul_comm_comap_of_injective hρ hP'Γ hP'T, fun _ => Or.inr ?_⟩
      · rw [card_comap_of_injective hρ hP'Γ, hP'9]
      · exact irr_comap_of_injective hρ hP'Γ hP'irr
    · refine ⟨C, hCe, hC9, hCT, fun hc => Or.inl ?_⟩
      have h12 : 12 ≤ n := by
        by_contra h
        exact hsmall ⟨by omega, hc⟩
      have := hpow (Nat.card J) 3 Nat.card_pos (by norm_num; exact hJ27 h12)
      rw [← hCc] at this
      norm_num at this
      omega
  · obtain ⟨J, hTJ, h23, hel, hJ27⟩ := exists_subgroup_of_not_le_normalizer hn hXsn e hT2 hTN
    obtain ⟨C, hCe, hCc, hCT⟩ := key J hTJ h23 hel
    have hC27 : 27 ≤ Nat.card C := by
      have := hpow (Nat.card J) 3 Nat.card_pos (by norm_num; exact hJ27)
      rw [← hCc] at this
      simpa using this
    exact ⟨C, hCe, by omega, hCT, fun _ => Or.inl (by omega)⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_three_subgroup {X T : Subgroup G} {n : ℕ} (hn : 8 ≤ n)
    (hXsn : CFSG.Open.IsSubnormal X (X ⊔ T)) (hT : IsSylowOf 2 T (X ⊔ T))
    (hX : Nonempty (Bar2 X ≃* alternatingGroup (Fin n))) :
    ∃ P : Subgroup G, P ≤ X ⊔ T ∧ IsElemAbelian 3 P ∧ 9 ≤ Nat.card P ∧ Permutes P T ∧
      (10 ≤ n ∨ X ⊔ T ≠ X ⊔ pCoreOf 2 (X ⊔ T) →
        9 < Nat.card P ∨ IrrOn (normalizer (P : Set G) ⊓ T) P) := by
  obtain ⟨e⟩ := hX
  obtain ⟨e'⟩ := nonempty_barOf_mulEquiv hXsn
  obtain ⟨Q, hQe, hQ9, hQT, hQirr⟩ := exists_three_subgroup_bar (K := Bar2 (X ⊔ T))
    (X := barOf (X ⊔ T) X) (T := barOf (X ⊔ T) T) hn (pCore_bar2_eq_bot _)
    (isSubnormal_barOf hXsn) (barOf_sup_eq_top X T) (isSylowOf_barOf hT) ⟨e'.trans e⟩
  have hQ3 : IsPGroup 3 Q := fun x => ⟨1, Subtype.ext (by simpa using hQe.2 x x.2)⟩
  obtain ⟨P, hPH, hPc, hPe, hPT, hPirr⟩ := exists_lift hT hQ3 hQT
  refine ⟨P, hPH, hPe hQe, hPc ▸ hQ9, hPT, fun hc => ?_⟩
  have hc' : 10 ≤ n ∨ barOf (X ⊔ T) X ≠ ⊤ := by
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr fun htop => h ((barOf_eq_top_iff le_sup_left).1 htop)
  rcases hQirr hc' with h | h
  · exact Or.inl (hPc ▸ h)
  · exact Or.inr (hPirr h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
