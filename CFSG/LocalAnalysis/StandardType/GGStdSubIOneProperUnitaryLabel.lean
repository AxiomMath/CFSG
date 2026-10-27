module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperUnitary
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProper
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGIOneUnitaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1 ∧ p ≠ 3 ∧ 3 ≤ lab.rank

theorem largeEvenLabelAll_endNodeIOne_unitary {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hl : GGIOneUnitaryLabel p lab)
    (hZ : LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      GGEndNodeIOne p (ggUnitaryTorusRank p (lab.rank + 1)) R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq, hpd, hp3, hl3⟩ := hl
  dsimp only at htag hpq hpd hp3 hl3 hZ ⊢
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have h1 : n = 1 := by omega
    subst h1
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq))
  have hq : 2 < 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hr : ggUnitaryTorusRank p (l + 1) = l + 1 - 2 := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  rw [hr]
  intro Q hQ
  have hQ' := hZ Q hQ
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq', hZK⟩ := hQ'
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : l + 1 = 3 := congrArg Prod.fst he
    omega
  exact ⟨K, i1, i2, hK, hq', ggOutdiagOdd_of_prime fun φ hφ hφp =>
      TableBUE.mem_range_conj_of_pow_eq_one h hK (by omega) hdq hp hpq hpd hφ hφp,
    ggEndNodeIOne_unitary h hK hp hpq hpd hp3 (by omega) (Or.inl hq) hZK⟩

theorem ggStdSubIOneProperInputOn_unitary
    (ha₀ : GGLNoncyclicInput)
    (hZ : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      GGIOneUnitaryLabel p lab → LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R) :
    GGStdSubIOneProperInputOn GGIOneUnitaryLabel := by
  refine ggStdSubIOneProperInputOn_of_labels ha₀ fun p lab hp hlab hS _ Q hQ => ?_
  have h1 := largeEvenLabelAll_torusLift_twA hlab hS.1 hp hS.2.1 Q hQ
  have h2 := largeEvenLabelAll_endNodeIOne_unitary hp hlab hS (hZ p lab hp hlab hS) _ h1
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨⟨hq, hlift⟩, hO, hend⟩ => ⟨hq, hO, _, hlift, hend⟩) h2

end CFSG.StandardType
