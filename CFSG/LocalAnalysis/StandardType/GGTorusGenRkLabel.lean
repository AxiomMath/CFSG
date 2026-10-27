module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkPSU
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixOne
public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenTableBRk_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGTorusGenTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) := by
  by_cases h61 : (d, n) = (6, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h61
    exact ggTorusGenTableBRk_PSU_six_one hK hp hpq hpd
  · exact ggTorusGenTableBRk_PSU_of_ne_six_one hK hn hd hp hpq hpd h61

theorem largeEvenLabelAll_torusGenRk_twA_dvd
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hv : ¬ GGL48TableBVacLabel p lab) (h : GGL48TB0TwRowA p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk p R I lab.rank := by
  obtain ⟨ht, hpd, hpq⟩ := h
  have hn : 1 ≤ lab.n := hlab.1
  have hr2 : lab.rank ≠ 2 := fun h2 => hv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, h2⟩)))))
  have hrk : 2 ≤ lab.rank := by
    have := hlab.2
    rw [ht] at this
    exact this.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ lab.n := dvd_pow_self 2 (by omega)
    have := (Nat.dvd_add_right h2).mp hpq
    omega
  have hd5 : 5 ≤ lab.rank + 1 := by
    by_contra hlt
    have h4 : lab.rank + 1 = 4 := by omega
    rw [h4] at hpd
    have : p ∣ 2 ^ 2 := by simpa using hpd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    exact hp2 this
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn hpd hpq hd5 ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusGenTableBRk_PSU hK hn hd5 hp hpq hpd⟩⟩

end CFSG.StandardType
