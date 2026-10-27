module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rF
import CFSG.GH74.BNPair.L15Maschke

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem uc22s21rc_exists_complement {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S R L : Subgroup K}
    (hS : IsPGroup 2 ↥S) (hR : IsPGroup q ↥R) (hSR : S ≤ normalizer (R : Set K))
    (hΦL : fratSub R ≤ L) (hLR : L ≤ R) (hSL : S ≤ normalizer (L : Set K)) :
    ∃ N : Subgroup K, fratSub R ≤ N ∧ N ≤ R ∧ S ≤ normalizer (N : Set K) ∧
      L ⊔ N = R ∧ L ⊓ N = fratSub R := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : fratSub R = fratGen q R := fratSub_eq_fratGen hq hR
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime q (Nat.card S) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have hconj : ∀ {H : Subgroup K}, S ≤ normalizer (H : Set K) →
      ∀ d ∈ S, ∀ x ∈ H, d * x * d⁻¹ ∈ H :=
    fun hSH d hd x hx => (Subgroup.mem_normalizer_iff.mp (hSH hd) x).mp hx
  have hSΦ : S ≤ normalizer (fratSub R : Set K) :=
    fun s hs => mem_normalizer_fratSub hq hR (hSR hs)
  obtain ⟨N, h1, h2, h3, h4, h5⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := q) (Q := R) (D := S) (T := L)
      (fratSub_le R)
      (fun x hx y hy => by
        rw [hF]
        exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy))
      (fun x hx => by
        rw [hF]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, rfl⟩))
      hcop (hconj hSR) (hconj hSΦ) hΦL hLR (hconj hSL)
  refine ⟨N, h1, h2, fun d hd => ?_, h4, h5⟩
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h3 d hd n, fun hn => ?_⟩
  simpa [mul_assoc] using h3 d⁻¹ (S.inv_mem hd) _ hn

theorem uc22s21rc_exists_piece_not_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S P J : Subgroup K}
    (hS : IsPGroup 2 ↥S) (hP : IsPGroup q ↥P) (hSP : S ≤ normalizer (P : Set K))
    (hSJ : S ≤ normalizer (J : Set K)) (hPJ : ¬ P ≤ J) :
    ∃ R : Subgroup K, R ≤ P ∧ IsPiece q S R ∧ ¬ R ≤ J := by
  classical
  obtain ⟨R, ⟨hRP, hSR, hRJ⟩, hmin⟩ := wellFounded_lt.has_min
    {R : Subgroup K | R ≤ P ∧ S ≤ normalizer (R : Set K) ∧ ¬ R ≤ J} ⟨P, le_rfl, hSP, hPJ⟩
  have hRq : IsPGroup q ↥R := hP.to_le hRP
  have hR0 : R ≠ ⊥ := fun h => hRJ (h ▸ bot_le)
  have hmin' : ∀ Z : Subgroup K, Z < R → S ≤ normalizer (Z : Set K) → Z ≤ J := by
    intro Z hZR hSZ
    by_contra hZJ
    exact hmin Z ⟨hZR.le.trans hRP, hSZ, hZJ⟩ hZR
  have hΦ : fratSub R ≤ J :=
    hmin' _ (fratSub_lt hR0) fun s hs => mem_normalizer_fratSub hq hRq (hSR hs)
  have hSL : S ≤ normalizer ((R ⊓ J : Subgroup K) : Set K) :=
    fun s hs => Subgroup.inf_normalizer_le_normalizer_inf ⟨hSR hs, hSJ hs⟩
  obtain ⟨N, -, hNR, hSN, hLN, hLN'⟩ := uc22s21rc_exists_complement hq hq2 hS hRq hSR
    (le_inf (fratSub_le R) hΦ) inf_le_left hSL
  have hNR' : N = R := by
    by_contra hne
    exact hRJ (hLN ▸ sup_le inf_le_right (hmin' N (lt_of_le_of_ne hNR hne) hSN))
  have hL : R ⊓ J = fratSub R := by
    rw [hNR', inf_eq_left.2 inf_le_left] at hLN'
    exact hLN'
  refine ⟨R, hRP, ⟨hR0, hRq, hSR, fun Z hZR hSZ => ?_⟩, hRJ⟩
  rcases hZR.eq_or_lt with h | h
  · exact Or.inr h
  · exact Or.inl (hL ▸ le_inf hZR (hmin' Z h hSZ))

theorem uc22s21rc_sSup_pieces {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S P : Subgroup K}
    (hS : IsPGroup 2 ↥S) (hP : IsPGroup q ↥P) (hSP : S ≤ normalizer (P : Set K)) :
    sSup {R : Subgroup K | R ≤ P ∧ IsPiece q S R} = P := by
  set J : Subgroup K := sSup {R : Subgroup K | R ≤ P ∧ IsPiece q S R} with hJ
  have hJP : J ≤ P := sSup_le fun R hR => hR.1
  have hSJ : S ≤ normalizer (J : Set K) := by
    rw [hJ, sSup_eq_iSup']
    exact le_trans (le_iInf fun R => R.2.2.2.2.1)
      (Subgroup.iInf_normalizer_le_normalizer_iSup fun R : {R : Subgroup K | R ≤ P ∧
        IsPiece q S R} => (R : Subgroup K))
  refine le_antisymm hJP ?_
  by_contra hPJ
  obtain ⟨R, hRP, hR, hRJ⟩ := uc22s21rc_exists_piece_not_le hq hq2 hS hP hSP hSJ hPJ
  exact hRJ (le_sSup ⟨hRP, hR⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
