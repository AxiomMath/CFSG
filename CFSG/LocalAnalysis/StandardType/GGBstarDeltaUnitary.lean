module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly InndiagSU TableBUI

@[expose] def GGBstarBoundDeltaUnitaryDvdInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n d p : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → 5 ≤ d →
    p.Prime → p ∣ 2 ^ n + 1 → p ∣ d →
    GGBstarBoundDelta p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))

section Three

variable {K : Type} [Field K] [Finite K] {n p : ℕ}

theorem ggBstarBoundInn_unitary_three (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (h2 : 2 < 2 ^ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (r : ℕ) :
    GGBstarBoundInn p r (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hL A _ hA hAI _ h3 _ _ _ _
  exact absurd h3 (not_le.mpr (TableBUE.card_lt_unitary_three
    (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hpq hψ hker hL hA hAI))

theorem ggBstarBoundDelta_unitary_three (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (h2 : 2 < 2 ^ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (r : ℕ) :
    GGBstarBoundDelta p r (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hL A _ hA hAI _ h3 _ _ _
  exact absurd h3 (not_le.mpr (TableBUE.card_lt_unitary_three
    (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hpq hψ hker hL hA hAI))

theorem ggBstarBoundInn_unitary_all {d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    GGBstarBoundInn p (ggUnitaryTorusRank p d) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  by_cases hpd : p ∣ d
  · by_cases hd3 : d = 3
    · subst hd3
      have h2 : 2 < 2 ^ n := by
        rcases Nat.lt_or_ge 2 (2 ^ n) with h' | h'
        · exact h'
        · exfalso
          have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          exact hdq (by rw [show 2 ^ n = 2 by omega])
      exact ggBstarBoundInn_unitary_three hK hn h2 hp hpq _
    · have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
      have hd5 : 5 ≤ d := by
        by_contra hcon
        have hd4 : d = 4 := by omega
        rw [hd4] at hpd
        have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
      exact TableBUD.ggBstarBoundInn_unitary_dvd hK hn hd5 hp hpq hpd
  · exact ggBstarBoundInn_unitary hK hn hd hdq hp hpq hpd

end Three

section Labels

@[expose] def GGBstarDeltaUnitaryAt (p d : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  GGOutdiagOdd p R I ∧ GGBstarBoundInn p (ggUnitaryTorusRank p d) R I ∧
    (GGDeltaLocal p (ggUnitaryTorusRank p d) R I ∨ GGBstarBoundDelta p (ggUnitaryTorusRank p d) R I)

theorem unitary_ne_three_two {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA) : (lab.rank + 1, 2 ^ lab.n) ≠ (3, 2) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at h
  subst h
  obtain ⟨hl2, hl2n⟩ := hl
  have hl2n' : l = 2 → 2 ≤ n := hl2n
  intro he
  have h3 : l + 1 = 3 := congrArg Prod.fst he
  have h2 : 2 ^ n = 2 := congrArg Prod.snd he
  have hn2 : 2 ≤ n := hl2n' (by omega)
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  omega

theorem largeEvenLabelAll_unitaryLift {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGTableBUnitaryLiftLabel p lab)
    (P : ℕ → (R : Type) → [Group R] → Set (MulAut R) → Prop)
    (hP : ∀ (K : Type) [Field K] [Finite K] (n d : ℕ), Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n →
      3 ≤ d → (d, 2 ^ n) ≠ (3, 2) → p ∣ 2 ^ n + 1 → d = lab.rank + 1 →
      P d (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)))) :
    LargeEvenLabelAll lab fun R _ I _ => P (lab.rank + 1) R I := by
  have hn : 1 ≤ lab.n := hlab.1
  have hdq := unitary_ne_three_two (lab := lab)
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases hS.1 with h | ⟨h, hl3⟩
  · dsimp only at h hn hdq ⊢
    have hdq' := hdq hlab h
    subst h
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have hl2 : 2 ≤ l := hlab.2.1
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      hP K n (l + 1) hK hn (by omega) hdq' hS.2 rfl⟩
  · dsimp only at h hl3 hn ⊢
    subst h hl3
    have h32 : (3 : ℕ) ≠ 2 := by decide
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h32, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have hdq' : (4, 2 ^ n) ≠ (3, 2) := fun he => by
      have := congrArg Prod.fst he
      omega
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hP K n 4 hK hn (by norm_num) hdq' hS.2 rfl⟩

section Certificates

theorem ggBstarDeltaUnitaryAt_coprime {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGBstarDeltaUnitaryAt p d (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :=
  ⟨ggOutdiagOdd_unitary hK hn hd (fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])) p,
    ggBstarBoundInn_unitary hK hn hd hdq hp hpq hpd,
    Or.inl (ggDeltaLocal_of_prime (ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd)
        (StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp
            (TableBU.ne_two_of_dvd_two_pow_add_one hn hpq) hpd))⟩

theorem ggBstarDeltaUnitaryAt_of_delta (hdel : GGBstarBoundDeltaUnitaryDvdInput) {K : Type}
    [Field K] [Finite K] {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    GGBstarDeltaUnitaryAt p d (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hodd := ggOutdiagOdd_unitary hK hn hd (fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])) p
  have hinn := ggBstarBoundInn_unitary_all hK hn hd hdq hp hpq
  by_cases hpd : p ∣ d
  · by_cases hd3 : d = 3
    · subst hd3
      have h2 : 2 < 2 ^ n := by
        rcases Nat.lt_or_ge 2 (2 ^ n) with h' | h'
        · exact h'
        · exfalso
          have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          exact hdq (by rw [show 2 ^ n = 2 by omega])
      exact ⟨hodd, hinn, Or.inr (ggBstarBoundDelta_unitary_three hK hn h2 hp hpq _)⟩
    · have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
      have hd5 : 5 ≤ d := by
        by_contra hcon
        have hd4 : d = 4 := by omega
        rw [hd4] at hpd
        have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
      exact ⟨hodd, hinn, Or.inr (hdel K n d p hK hn hd5 hp hpq hpd)⟩
  · exact ggBstarDeltaUnitaryAt_coprime hK hn hd hdq hp hpq hpd

theorem ggBstarDeltaUnitaryInput_of_delta (hdel : GGBstarBoundDeltaUnitaryDvdInput) :
    GGBstarDeltaUnitaryInput :=
  fun p _ hp hlab hS =>
    largeEvenLabelAll_unitaryLift hlab hS (fun d R _ I => GGBstarDeltaUnitaryAt p d R I)
      fun _ _ _ _ _ hK hn hd hdq hpq _ =>
        ggBstarDeltaUnitaryAt_of_delta hdel hK hn hd hdq hp hpq

end Certificates

end Labels

end CFSG.StandardType
