module

public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem odd_of_nParam_le_zero {H : Subgroup G} (h : nParam H ≤ 0) : Odd (Nat.card H) := by
  by_contra hH
  simp only [nParam, hH, ↓reduceIte] at h
  have hmem : ∀ i ∈ {i : ℕ | 0 < i ∧ InE i H}, (1 : ℕ∞) ≤ i := fun i hi => by
    exact_mod_cast hi.1
  have h1 : (1 : ℕ∞) ≤ ⨅ i ∈ {i : ℕ | 0 < i ∧ InE i H}, (i : ℕ∞) :=
    le_iInf₂ fun i hi => hmem i hi
  have := h1.trans h
  simp at this

theorem nParam_le_of_generated {n : ℕ} {H T : Subgroup G} (hT : IsSylowIn 2 T H)
    {Δ : Set (Subgroup G)} (hΔ : ⨆ D ∈ Δ, D = H) (hTΔ : ∀ D ∈ Δ, T ≤ D)
    (hn : ∀ D ∈ Δ, nParam D ≤ n) : nParam H ≤ n := by
  have hDH : ∀ D ∈ Δ, D ≤ H := fun D hD => hΔ ▸ le_iSup₂ (f := fun D (_ : D ∈ Δ) => D) D hD
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  ·
    have hTb : T = ⊥ := by
      by_cases hΔe : Δ = ∅
      · rw [hΔe] at hΔ
        have h1 : H = ⊥ := by simpa using hΔ.symm
        exact le_bot_iff.mp (h1 ▸ hT.le)
      · obtain ⟨D, hD⟩ := Set.nonempty_iff_ne_empty.mpr hΔe
        have hDodd : Odd (Nat.card D) := odd_of_nParam_le_zero (by exact_mod_cast hn D hD)
        have hTD : IsSylowIn 2 T D := B6.isSylowTwoOf_mono hT (hTΔ D hD) (hDH D hD)
        exact eq_bot_of_isSylowIn_odd hTD hDodd
    have hrel := hT.not_dvd_relIndex
    rw [hTb, Subgroup.relIndex_bot_left] at hrel
    have hodd : Odd (Nat.card H) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hrel)
    have h0 : nParam H = 0 := by
      simp only [nParam, hodd, ↓reduceIte]
    rw [h0]
    exact zero_le
  · have hall : ∀ D ∈ Δ, InEFor n D T := fun D hD =>
      (nParam_le_iff hpos).mp (hn D hD) T (B6.isSylowTwoOf_mono hT (hTΔ D hD) (hDH D hD))
    have hfor : InEFor n H T := inEFor_of_generated hT hΔ hTΔ hall
    exact (nParam_le_iff hpos).mpr ((inE_iff_inEFor hT).mpr hfor)

end E1

end CFSG.Quasithin
