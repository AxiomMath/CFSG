module

public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private lemma ennolaFam_exc_twE6 {lab : LargeEvenLabel} (h : lab.tag = .twE6) : FamExc lab :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private lemma ennolaFam_exc_E7 {lab : LargeEvenLabel} (h : lab.tag = .E7) : FamExc lab :=
  Or.inr (Or.inl h)

private lemma ennolaFam_exc_E8 {lab : LargeEvenLabel} (h : lab.tag = .E8) : FamExc lab :=
  Or.inr (Or.inr (Or.inl h))

private lemma ennolaFam_exc_F4 {lab : LargeEvenLabel} (h : lab.tag = .F4) : FamExc lab :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

private lemma ennolaFam_row_fam {p : ℕ} {lab : LargeEvenLabel}
    (hrow : ggRowP_Ennola p lab) : FamUni lab ∨ FamOrth lab ∨ FamExc lab := by
  unfold ggRowP_Ennola ggRowP_E at hrow
  rcases hrow with hE | ⟨hF4, -, -⟩
  · rcases hE with h | h | h | h | h | h
    · rcases h.1 with ⟨ht, -⟩ | ht
      · exact Or.inl (Or.inl ht)
      · exact Or.inl (Or.inr ht)
    · obtain ⟨hD, h4, -, -⟩ := h
      exact Or.inr (Or.inl (Or.inl ⟨hD, by omega⟩))
    · obtain ⟨htD, h5, -, -⟩ := h
      exact Or.inr (Or.inl (Or.inr ⟨htD, by omega, by omega⟩))
    · exact Or.inr (Or.inr (ennolaFam_exc_twE6 h.1))
    · exact Or.inr (Or.inr (ennolaFam_exc_E7 h.1))
    · exact Or.inr (Or.inr (ennolaFam_exc_E8 h.1))
  · exact Or.inr (Or.inr (ennolaFam_exc_F4 hF4.1))

private lemma ennolaFam_row_dvd {p : ℕ} {lab : LargeEvenLabel}
    (hrow : ggRowP_Ennola p lab) : p ∣ 2 ^ lab.n + 1 := by
  rcases hrow with hE | ⟨-, -, h⟩
  · exact ggRowP_E.dvd hE
  · exact h

private lemma ennolaFam_row_twD_rank {p : ℕ} {lab : LargeEvenLabel}
    (hrow : ggRowP_Ennola p lab) : lab.tag = .twD → 3 ≤ lab.rank := by
  unfold ggRowP_Ennola ggRowP_E at hrow
  rcases hrow with hE | ⟨hF4, -, -⟩
  · rcases hE with h | h | h | h | h | h
    · intro htD
      rcases h.1 with ⟨ht, -⟩ | ⟨ht, hr⟩
      · rw [ht] at htD
        exact absurd htD (by decide)
      · omega
    · intro htD
      rw [h.1] at htD
      exact absurd htD (by decide)
    · intro htD
      obtain ⟨_, h5, _, _⟩ := h
      omega
    · intro htD
      rw [h.1] at htD
      exact absurd htD (by decide)
    · intro htD
      rw [h.1] at htD
      exact absurd htD (by decide)
    · intro htD
      rw [h.1] at htD
      exact absurd htD (by decide)
  · intro htD
    rw [hF4.1] at htD
    exact absurd htD (by decide)

private lemma ennolaFam_canonLabel_not_twD_two (lab : LargeEvenLabel) :
    ¬ ((canonLabel lab).tag = .twD ∧ (canonLabel lab).rank = 2) := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [canonLabel] <;> (try split_ifs) <;> simp_all

theorem tcjEnnolaSimple_of_families
    (hU : InnDiagAllEnnolaOn FamUni) (hO : InnDiagAllEnnolaOn FamOrth)
    (hE : InnDiagAllEnnolaOn FamExc) : TCJEnnolaSimple := by
  intro p hp hp2 S _ _ lab α K hlab hrow hcen hin hα hK labJ0 hJ0 hhas
  obtain ⟨labJ0', hJ0', hhas'⟩ := tcj_component_hasLabel p hp hp2 lab α K hlab hcen hin hα hK
  rw [tcj_ggFixSub_eq_fixSubgroup] at hK
  have hfam : FamUni lab ∨ FamOrth lab ∨ FamExc lab := ennolaFam_row_fam hrow
  have hdvdrow : p ∣ 2 ^ lab.n + 1 := ennolaFam_row_dvd hrow
  have hrank : lab.tag = .twD → 3 ≤ lab.rank := ennolaFam_row_twD_rank hrow
  have hcnlab : (canonLabel lab).n = lab.n := canonLabel_n_eq_self hlab hrank
  have hkey : ∃ k : ℕ, Odd k ∧ (canonLabel labJ0').n = k * (canonLabel lab).n := by
    rcases hfam with h | h | h
    · exact hU S p α K lab labJ0' h hp hp2 hrow hcen hin hα hhas' hK
    · exact hO S p α K lab labJ0' h hp hp2 hrow hcen hin hα hhas' hK
    · exact hE S p α K lab labJ0' h hp hp2 hrow hcen hin hα hhas' hK
  obtain ⟨k, hk, hkn⟩ := hkey
  by_cases hder : labJ0'.tag = .B2der ∨ labJ0'.tag = .G2der ∨ labJ0'.tag = .twF4der
  · have hcan1 : (canonLabel labJ0').n = 1 := tcjLabel_derived_canonLabel_n hder
    have hn1 : labJ0'.n = 1 := Nat.dvd_one.mp (hcan1 ▸ tcjLabel_n_dvd_canonLabel_n hJ0')
    have hk1 : k * (canonLabel lab).n = 1 := by rw [← hkn, hcan1]
    have hcnlab1 : (canonLabel lab).n = 1 := Nat.eq_one_of_mul_eq_one_left hk1
    have hlabn : lab.n = 1 := Nat.dvd_one.mp (hcnlab1 ▸ tcjLabel_n_dvd_canonLabel_n hlab)
    refine ⟨labJ0', hJ0', tcj_ggHasLabel_of_hasLabel hhas', ?_, ?_⟩
    · simpa [hn1, hlabn] using hdvdrow
    · rintro ⟨h1, -⟩
      rcases hder with h | h | h <;> rw [h] at h1 <;> exact absurd h1 (by decide)
  · have hnd : labJ0'.tag ≠ .B2der ∧ labJ0'.tag ≠ .G2der ∧ labJ0'.tag ≠ .twF4der :=
      ⟨fun h => hder (Or.inl h), fun h => hder (Or.inr (Or.inl h)),
        fun h => hder (Or.inr (Or.inr h))⟩
    refine ⟨canonLabel labJ0', tcjLabel_canonLabel_inLambda2 hJ0' hnd,
      tcjLabel_ggHasLabel_canonLabel hnd (tcj_ggHasLabel_of_hasLabel hhas'), ?_, ?_⟩
    · have hpow : 2 ^ lab.n + 1 ∣ 2 ^ (canonLabel labJ0').n + 1 := by
        have h := hk.nat_add_dvd_pow_add_pow (x := 2 ^ lab.n) (y := 1)
        have h' : 2 ^ lab.n + 1 ∣ 2 ^ (lab.n * k) + 1 := by
          simpa [← pow_mul] using h
        have he : lab.n * k = (canonLabel labJ0').n := by rw [hkn, hcnlab, mul_comm]
        rwa [he] at h'
      exact dvd_trans hdvdrow hpow
    · exact ennolaFam_canonLabel_not_twD_two labJ0'

end CFSG.StandardType.TCJ

end
