module

public import CFSG.LocalAnalysis.StandardType.GGTBTorReindex
public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
public import CFSG.LocalAnalysis.StandardType.GGTBTorDSplit
public import CFSG.LocalAnalysis.StandardType.GGTBTorDNsHolds

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem cartanA_three_reindex_swap :
    (CartanMatrix.A 3).reindex (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (0 : Fin 3) 1) =
      CartanMatrix.D 3 := by
  have hswap : (c[0, 1] : Equiv.Perm (Fin 3)) = Equiv.swap 0 1 := by decide +kernel
  have h := CartanMatrix.D_three'
  rw [hswap] at h
  have h' := congrArg (Matrix.reindex (Equiv.swap (0 : Fin 3) 1)
    (Equiv.swap (0 : Fin 3) 1)).symm h.symm
  rw [Equiv.symm_apply_apply] at h'
  simpa only [Matrix.reindex_symm, Equiv.symm_swap] using h'

theorem coxeterA_three_reindex_swap :
    (CoxeterMatrix.A 3).reindex (Equiv.swap (0 : Fin 3) 1) = ggCoxeterMatrixD 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CoxeterMatrix.reindex_apply, CoxeterMatrix.A, ggCoxeterMatrixD_apply,
      CartanMatrix.D_three, Equiv.swap_apply_def]

theorem GGTorusTorData.d_three_of_a_three {m : ℕ} {L : Type} [Group L]
    {A : Subgroup (MulAut L)}
    (h : GGTorusTorData m 3 (CartanMatrix.A 3) (CoxeterMatrix.A 3) L A) :
    GGTorusTorData m 3 (CartanMatrix.D 3) (ggCoxeterMatrixD 3) L A := by
  simpa only [cartanA_three_reindex_swap, coxeterA_three_reindex_swap] using
    h.reindex (Equiv.swap (0 : Fin 3) 1)

theorem GGTorusTorW.d_three_of_a_three {p r m : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)}
    (h : GGTorusTorW p r m 3 (CartanMatrix.A 3) (CoxeterMatrix.A 3) R I) :
    GGTorusTorW p r m 3 (CartanMatrix.D 3) (ggCoxeterMatrixD 3) R I := by
  intro L' _ _ ψ A hTB
  exact (h L' ψ A hTB).d_three_of_a_three

section Certificates


theorem ggTBTorD_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hrank : lab.rank = 3)
    (hrow :
      (lab.tag = .D ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank))) ∨
        (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank)) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
        (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank) R I := by
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at hrank
  subst rank
  have hpd : ¬ p ∣ 3 + 1 := fun h4 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
  rcases hrow with ⟨htag, hdiv⟩ | ⟨htag, hdiv, -⟩
  · dsimp only at htag
    subst tag
    rcases hdiv with hminus | ⟨-, hpar⟩
    · have hA : LargeEvenInLambda2 ⟨.A, 3, n⟩ :=
        ⟨hlab.1, by norm_num⟩
      have htor := ggTBTorAInd_holds p hp hp2 ⟨.A, 3, n⟩ hA (Or.inl rfl) hpd
        (by simpa [ggTorM] using hminus)
      intro Q hQ
      have hQA : LargeEvenRawDatum ⟨.A, 3, n⟩ Q := by
        simpa only [LargeEvenRawDatum, ↓reduceIte, Nat.reduceAdd] using hQ
      have hraw := htor Q hQA
      dsimp only [LargeEvenRawDatum] at hraw ⊢
      obtain ⟨K, i1, i2, hK, hQK, hTK⟩ := hraw
      refine ⟨K, i1, i2, hK, hQK, ?_⟩
      simpa [ggTorMpm, ggTorM, ggTorEnn, hminus] using
        hTK.d_three_of_a_three
    · norm_num at hpar
  · dsimp only at htag
    subst tag
    have hplus : p ∣ 2 ^ n + 1 := hdiv
    have hminus : ¬ p ∣ 2 ^ n - 1 := by
      intro hm
      have hpTwo : p ∣ 2 := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        have hd := Nat.dvd_sub hplus hm
        have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
        simpa only [heq] using hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpTwo)
    have hA : LargeEvenInLambda2 ⟨.twA, 3, n⟩ :=
      ⟨hlab.1, by norm_num⟩
    have htor := ggTBTorAInd_holds p hp hp2 ⟨.twA, 3, n⟩ hA (Or.inr rfl) hpd
      (by simpa [ggTorM] using hplus)
    intro Q hQ
    have hQA : LargeEvenRawDatum ⟨.twA, 3, n⟩ Q := by
      simpa [LargeEvenRawDatum] using hQ
    have hraw := htor Q hQA
    dsimp only [LargeEvenRawDatum] at hraw ⊢
    obtain ⟨K, i1, i2, hK, hQK, hTK⟩ := hraw
    refine ⟨K, i1, i2, hK, hQK, ?_⟩
    simpa [ggTorMpm, ggTorM, ggTorEnn, hminus, hplus] using
      hTK.d_three_of_a_three

end Certificates

theorem ggTBTorDHigh_of_nonsplit (h : GGTBTorDHighNonsplit) : GGTBTorDHigh := by
  intro p hp hp2 lab hlab hN hrow
  rcases hrow with ⟨htag, hminus | ⟨hplus, heven⟩⟩ | ⟨htag, hplus, hodd⟩
  · exact ggTBTorDHigh_split hp hp2 hlab hN htag hminus
  · exact h p hp hp2 lab hlab hN hplus (Or.inl ⟨htag, heven⟩)
  · exact h p hp hp2 lab hlab hN hplus (Or.inr ⟨htag, hodd⟩)

section Certificates


theorem ggTBTorD_of_high (h : GGTBTorDHigh) : GGTBTorD := by
  intro p hp hp2 lab hlab hrow
  have h3 : 3 ≤ lab.rank := by
    rcases hrow with ⟨ht, -⟩ | ⟨ht, -, ho⟩
    · simpa only [LargeEvenInLambda2, ht] using hlab.2
    · have h2 : 2 ≤ lab.rank := by
        simpa only [LargeEvenInLambda2, ht] using hlab.2
      have hne : lab.rank ≠ 2 := by
        intro heq
        rw [heq] at ho
        norm_num at ho
      omega
  rcases eq_or_lt_of_le h3 with hthree | hhigh
  · exact ggTBTorD_three hp hp2 hlab hthree.symm hrow
  · exact h p hp hp2 lab hlab hhigh hrow

theorem ggTBTorD_of_nonsplit (h : GGTBTorDHighNonsplit) : GGTBTorD :=
  ggTBTorD_of_high (ggTBTorDHigh_of_nonsplit h)

theorem ggTBTorD_holds : GGTBTorD :=
  ggTBTorD_of_nonsplit ggTBTorDHigh_nonsplit

end Certificates

end CFSG.StandardType
