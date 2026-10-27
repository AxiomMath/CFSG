module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases3
public import CFSG.Quasithin.EmptyFaithful.Insp9P7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Insp9

theorem B56Setting.primes_le_seven {D : Type} [Group D] [Finite D] {N : Subgroup D}
    (hs : B56Setting D N) (h4 : ¬ 2 ^ 4 ∣ Nat.card ↥N) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥N → r ≤ 7 := by
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := hs
  have hcard : Nat.card ↥(N.map ρ) = Nat.card ↥N := Subgroup.card_map_of_injective hρ
  rw [← hcard] at h4
  intro r hr hrN
  rw [← hcard] at hrN
  exact b56_primes_le_seven hcases h4 r hr hrN

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem prime_dvd_card_false (h : Data D₁ D₂ J N) (hs : B56Setting D N)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 8) {p : ℕ} (hp : p.Prime) (hp8 : 8 ≤ p)
    (hpD : p ∣ Nat.card D) : False := by
  have hD4 : ¬ 2 ^ 4 ∣ Nat.card D :=
    h.not_two_pow_dvd (k := 3) (by simpa using hT) (m := 4) (by norm_num)
  have hN4 : ¬ 2 ^ 4 ∣ Nat.card ↥N := fun hd =>
    hD4 (hd.trans (Subgroup.card_subgroup_dvd_card N))
  have hidx : N.index ∣ 3 * 8 := by
    have := h.index_dvd
    rwa [h.card_D₁, hT] at this
  have hpidx : ¬ p ∣ N.index := by
    intro hdvd
    have h1 : p ∣ 3 * 8 := hdvd.trans hidx
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 : p ∣ 2 ^ 3 * 3 := by norm_num; exact h1
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
    · have := Nat.le_of_dvd (by norm_num) h4; omega
  have hmul : Nat.card ↥N * N.index = Nat.card D := Subgroup.card_mul_index N
  have hpN : p ∣ Nat.card ↥N := by
    rw [← hmul] at hpD
    exact ((Nat.Prime.dvd_mul hp).mp hpD).resolve_right hpidx
  have := hs.primes_le_seven hN4 p hp hpN
  omega

omit [Finite D] in
theorem prime_dvd_card_pgl2 {q : ℕ} (hq : q.Prime) (h : F6.IsPGL2 q D) : q ∣ Nat.card D := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hGL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq (K := K) 2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K)
  have hS : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) ∣ q - 1 := by
    have := Subgroup.card_dvd_of_surjective
      (MonoidHom.rangeRestrict_surjective (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := K)))
    rwa [Nat.card_units, hK] at this
  have hSpos : 0 < Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) := Nat.card_pos
  have hq2 := hq.two_le
  have hSle : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) ≤ q - 1 := Nat.le_of_dvd (by omega) hS
  have hqGL : q ∣ Nat.card (GL (Fin 2) K) := by
    rw [hGL, hK]
    exact Dvd.dvd.mul_right (dvd_pow_self q (by norm_num)) _
  have hqGL' : q ∣ Nat.card (GL (Fin 2) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) *
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K) := by rw [← h1]; exact hqGL
  rcases (Nat.Prime.dvd_mul hq).mp hqGL' with hqD | hqS
  · rw [Nat.card_congr e.toEquiv]; exact hqD
  · exact absurd (Nat.le_of_dvd hSpos hqS) (by omega)

theorem inspCase5 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseFive H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseFive H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨⟨q, hq, hmod, hPGL⟩, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 8 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, card_D8]
    exact (prime_dvd_card_false h hs hT hq (by omega) (prime_dvd_card_pgl2 hq hPGL)).elim
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

theorem inspCase3 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseThree H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseThree H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨p, K, Z, hp, hmod, hK, -, -, -, -, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 8 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, card_D8]
    have hp2 : p ≠ 2 := by omega
    have hKcard := two_mul_card_psl_two_pow hp2 hK
    have hpK : p ∣ Nat.card ↥K := by
      have h1 : p ∣ 2 * Nat.card ↥K := by
        rw [hKcard]; simp
      exact ((Nat.Prime.dvd_mul hp).mp h1).resolve_left (fun h2 => by
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        omega)
    exact (prime_dvd_card_false h hs hT hp (by omega)
      (hpK.trans (Subgroup.card_subgroup_dvd_card K))).elim
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Insp9

end CFSG.Quasithin
