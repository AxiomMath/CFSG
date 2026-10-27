module

public import CFSG.Quasithin.Vol2.KGFactInsp4316Props
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318POutHe
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.LargeExtraspecial.OutSixBasic

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outTwoFam_or_oddOutLie {S : Type} [Group S] (h : A23List S) :
    OutTwoFam S ∨ OddOutLie S := by
  rcases h with h1 | ⟨p, hp, hp2, ⟨f, hf, hm⟩ | hm | hm⟩ | (⟨f, h3⟩ | hT) | h4 | h5
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hm⟩))
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inl hm⟩)
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr hm⟩)
  · exact Or.inr (Or.inr ⟨f, h3⟩)
  · exact Or.inl (Or.inr (Or.inr (Or.inl hT)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h5))))

theorem not_dvd_outer_of_outTwoFam
    {S : Type} [Group S] [Finite S] (h : OutTwoFam S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer S) := by
  rcases h with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨r, f, -, -, hf, hm⟩ | hm | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · by_cases h6 : n = 6
    · subst h6
      exact A318P.not_dvd_outer_alternating_six e hp hp2
    · exact A318P.not_dvd_outer_alternating (by omega) e hp hp2
  · exact A318P.not_dvd_outer_psl_two_odd hf hm hp hp2
  · exact A318P.not_dvd_outer_tits hm hp hp2
  · exact A318P.not_dvd_outer_psl_binary (by omega) hm hp hp2
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A318P.not_dvd_outer_M11 e hp hp2
    · exact A318P.not_dvd_outer_M12 e hp hp2
    · exact A318P.not_dvd_outer_M22 e hp hp2
    · exact A318P.not_dvd_outer_M23 e hp hp2
    · exact A318P.not_dvd_outer_M24 e hp hp2
    · exact A318P.not_dvd_outer_J1 e hp hp2
    · exact A318P.not_dvd_outer_J2 e hp hp2
    · exact A318P.not_dvd_outer_J4 e qSporOutTwo_holds hp hp2
    · exact A318P.not_dvd_outer_HS e hp hp2
    · exact A318P.not_dvd_outer_He e hp hp2
    · exact A318P.not_dvd_outer_Ru e hp hp2

variable {X : Type} [Group X]

theorem dvd_card_outer_of_not_mem [Finite X] {S : Subgroup X} [S.Normal]
    (hC : Subgroup.centralizer (S : Set X) = ⊥) {y : X} (hy : y ∉ S) {p : ℕ} (hp : p.Prime)
    (hyp : orderOf y = p) : p ∣ Nat.card (Outer ↥S) := by
  have hker := CFSG.LargeExtraspecial.S14.ker_conjOuter S (by rw [hC]; exact bot_le)
  set φ := CFSG.LargeExtraspecial.S14.conjOuter S with hφ
  have h1 : φ y ≠ 1 := fun h => hy (by rw [← hker]; exact MonoidHom.mem_ker.mpr h)
  have h2 : orderOf (φ y) ∣ p := hyp ▸ orderOf_map_dvd φ y
  have h3 : orderOf (φ y) = p := by
    rcases (Nat.dvd_prime hp).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have : Finite (Outer ↥S) := A318P.finite_outer _
  exact h3 ▸ orderOf_dvd_natCard (φ y)

theorem le_of_odd_commutator [Finite X] {S R Q : Subgroup X} [S.Normal]
    (hC : Subgroup.centralizer (S : Set X) = ⊥) (hodd : Odd (Nat.card ↥(commutator (Outer ↥S))))
    (hR : IsPGroup 2 ↥R) {x : X} (hQ : Q ≤ S) (hgen : R ≤ ⁅R, Subgroup.zpowers x⁆ ⊔ Q) :
    R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := CFSG.LargeExtraspecial.S14.ker_conjOuter S (by rw [hC]; exact bot_le)
  set φ := CFSG.LargeExtraspecial.S14.conjOuter S with hφ
  have hQφ : Q.map φ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hker]; exact hQ)
  have h1 : R.map φ ≤ commutator (Outer ↥S) := by
    calc R.map φ ≤ (⁅R, Subgroup.zpowers x⁆ ⊔ Q).map φ := Subgroup.map_mono hgen
      _ = ⁅R.map φ, (Subgroup.zpowers x).map φ⁆ := by
        rw [Subgroup.map_sup, hQφ, sup_bot_eq, Subgroup.map_commutator]
      _ ≤ commutator (Outer ↥S) := by
        rw [commutator_def]
        exact Subgroup.commutator_mono le_top le_top
  have : Finite (Outer ↥S) := A318P.finite_outer _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR.map φ)
  have h3 : Nat.card ↥(R.map φ) ∣ Nat.card ↥(commutator (Outer ↥S)) := Subgroup.card_dvd_of_le h1
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h3))
  have hbot : R.map φ = ⊥ := by
    rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
  rw [Subgroup.map_eq_bot_iff, hker] at hbot
  exact hbot

end CFSG.Quasithin.H13.KGInsp4316
