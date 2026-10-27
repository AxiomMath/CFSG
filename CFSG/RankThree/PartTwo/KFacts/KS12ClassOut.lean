module

public import CFSG.RankThree.PartTwo.KFacts.KS12Class
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem mem_range_conj_alternatingGroup_six {φ : MulAut (alternatingGroup (Fin 6))}
    (hφ : ∃ k : ℕ, φ ^ 3 ^ k = 1) :
    φ ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  obtain ⟨k, hk⟩ := hφ
  set q := QuotientGroup.mk' (inner (alternatingGroup (Fin 6))) φ with hq
  have hq3 : q ^ 3 ^ k = 1 := by rw [hq, ← map_pow, hk, map_one]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer (alternatingGroup (Fin 6)))) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      Sec4.Item434Alt.not_three_dvd_card_outer_six)
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  have hq1 : q = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  exact hq1

theorem exists_conj_of_mulEquiv {S Y : Type*} [Group S] [Group Y] (e : S ≃* Y)
    (hY : ∀ τ : MulAut Y, (∃ k : ℕ, τ ^ 3 ^ k = 1) → ∃ y : Y, τ = MulAut.conj y)
    (σ : MulAut S) (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) : ∃ s : S, σ = MulAut.conj s := by
  obtain ⟨k, hk⟩ := hσ
  obtain ⟨y, hy⟩ := hY (MulAut.congr e σ) ⟨k, by rw [← map_pow, hk, map_one]⟩
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [hy, congr_mulAutConj, MulEquiv.apply_symm_apply]

theorem ks12OutSimple :
    KS12OutSimple := by
  intro S _ _ hS σ hσ
  rcases hS with h6 | h7 | h22
  · obtain ⟨e⟩ := h6
    refine exists_conj_of_mulEquiv e (fun τ hτ => ?_) σ hσ
    obtain ⟨y, hy⟩ := mem_range_conj_alternatingGroup_six hτ
    exact ⟨y, hy.symm⟩
  · obtain ⟨e⟩ := h7
    exact exists_conj_of_mulEquiv e
      (KS14.ks18A7M22 _ (Or.inl ⟨MulEquiv.refl _⟩)).2.2.1 σ hσ
  · obtain ⟨e⟩ := h22
    exact exists_conj_of_mulEquiv e
      (KS14.ks18A7M22 _ (Or.inr ⟨MulEquiv.refl _⟩)).2.2.1 σ hσ

theorem ks12OutInner :
    KS12OutInner :=
  ks12OutInner_of ks12OutSimple

end CFSG.RankThree.PartTwo.KFacts
