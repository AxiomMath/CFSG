module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Abel
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Peel

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

universe u

variable {K : Type*} [Field K]

private theorem p9uBound_finite_linearEquiv {V : Type u} [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] : Finite (V ≃ₗ[K] V) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype V := Module.fintypeOfFintype (Module.finBasis K V)
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => e.toEquiv)
    (fun _ _ h => LinearEquiv.toEquiv_injective h)

theorem three_pow_dvd_finrank_and_card_center_le [Finite K] (hK : Nat.card K = 4) (s : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {Q : Subgroup (V ≃ₗ[K] V)}, IsGoodIn (scalars K V) Q →
      Nat.card Q = 3 ^ (2 * s) * Nat.card (Subgroup.center Q) →
      3 ^ s ∣ Module.finrank K V ∧
        Nat.card (Subgroup.center Q) ≤ 3 ^ (Module.finrank K V / 3 ^ s) := by
  induction s with
  | zero =>
      intro V _ _ _ Q hQ hcard
      simp only [Nat.mul_zero, pow_zero, one_mul] at hcard
      haveI : Finite (V ≃ₗ[K] V) := p9uBound_finite_linearEquiv
      have hcenter : Subgroup.center Q = ⊤ :=
        Subgroup.eq_top_of_card_eq (Subgroup.center Q) hcard.symm
      have hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
        intro x hx y hy
        have hmem : (⟨x, hx⟩ : Q) ∈ Subgroup.center Q := by rw [hcenter]; trivial
        have h := Subgroup.mem_center_iff.1 hmem ⟨y, hy⟩
        simpa using h.symm
      refine ⟨?_, ?_⟩
      · rw [pow_zero]; exact one_dvd _
      · rw [pow_zero, Nat.div_one, ← hcard]
        exact card_le_three_pow_finrank_of_abelian_good hK hQ hab
  | succ s ih =>
      intro V _ _ _ Q hQ hcard
      haveI : Finite (V ≃ₗ[K] V) := p9uBound_finite_linearEquiv
      have hnab : ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
        intro hab
        have hcenter : Subgroup.center Q = ⊤ := by
          rw [Subgroup.eq_top_iff']
          intro z
          rw [Subgroup.mem_center_iff]
          intro w
          exact Subtype.ext (hab z.1 z.2 w.1 w.2).symm
        have hcardC : Nat.card (Subgroup.center Q) = Nat.card Q := by
          rw [hcenter, Subgroup.card_top]
        rw [hcardC] at hcard
        have hpos : 0 < Nat.card Q := Nat.card_pos
        have h3 : 3 ^ (2 * (s + 1)) = 1 := by
          have h : 3 ^ (2 * (s + 1)) * Nat.card Q = 1 * Nat.card Q := by
            rw [one_mul, ← hcard]
          exact Nat.eq_of_mul_eq_mul_right hpos h
        have hlt : 1 < 3 ^ (2 * (s + 1)) :=
          Nat.one_lt_pow (by omega : 2 * (s + 1) ≠ 0) (by norm_num : (1:ℕ) < 3)
        exact (ne_of_gt hlt) h3
      obtain ⟨U, Q', hdim, hQ', hcard', hcenter'⟩ := exists_peel_of_not_abelian hK hQ hnab
      have hcard'' : Nat.card Q' = 3 ^ (2 * s) * Nat.card (Subgroup.center Q') := by
        have h1 : 9 * Nat.card Q' =
            3 ^ (2 * (s + 1)) * Nat.card (Subgroup.center Q') := by
          rw [← hcard', hcenter']
          exact hcard
        have h2 : 3 ^ (2 * (s + 1)) = 9 * 3 ^ (2 * s) := by
          have he : 2 * (s + 1) = 2 * s + 2 := by ring
          rw [he, pow_add]
          ring
        rw [h2, mul_assoc] at h1
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9) h1
      obtain ⟨hdvd, hle⟩ := ih (V := U) hQ' hcard''
      have hexp : Module.finrank K V / 3 ^ (s + 1) = Module.finrank K U / 3 ^ s := by
        rw [hdim, pow_succ, mul_comm (3 ^ s) 3]
        exact Nat.mul_div_mul_left _ _ (by norm_num : 0 < 3)
      refine ⟨?_, ?_⟩
      · rw [hdim, pow_succ, mul_comm (3 ^ s) 3]
        exact Nat.mul_dvd_mul_left 3 hdvd
      · rw [← hcenter']
        calc Nat.card (Subgroup.center Q') ≤ 3 ^ (Module.finrank K U / 3 ^ s) := hle
          _ = 3 ^ (Module.finrank K V / 3 ^ (s + 1)) := by rw [hexp]

theorem three_pow_dvd_finrank_and_rank_le_of_isGoodIn [Finite K] (hK : Nat.card K = 4)
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q) {a s : ℕ}
    (ha : Nat.card Q = 3 ^ (a + 1))
    (hs : Nat.card Q = 3 ^ (2 * s) * Nat.card (Subgroup.center Q)) :
    3 ^ s ∣ Module.finrank K V ∧ a ≤ 2 * s + Module.finrank K V / 3 ^ s - 1 := by
  obtain ⟨hdvd, hle⟩ := three_pow_dvd_finrank_and_card_center_le hK s hQ hs
  refine ⟨hdvd, ?_⟩
  have h1 : 3 ^ (a + 1) ≤ 3 ^ (2 * s + Module.finrank K V / 3 ^ s) := by
    rw [← ha, hs]
    calc 3 ^ (2 * s) * Nat.card (Subgroup.center Q)
        ≤ 3 ^ (2 * s) * 3 ^ (Module.finrank K V / 3 ^ s) := Nat.mul_le_mul_left _ hle
      _ = 3 ^ (2 * s + Module.finrank K V / 3 ^ s) := (pow_add 3 (2 * s) _).symm
  have h2 : a + 1 ≤ 2 * s + Module.finrank K V / 3 ^ s :=
    (Nat.pow_le_pow_iff_right (by norm_num : (1:ℕ) < 3)).1 h1
  omega

end CFSG.StandardType.FrameRoute

end
