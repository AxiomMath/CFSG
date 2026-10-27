module

public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTDModelA
public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftADepHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.SpecialLinear

@[expose] def GGTBTorANarrowLin : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .A → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

@[expose] def GGTBTorANarrowUni : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .twA → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

theorem ggTBTorANarrow_of_split (hA : GGTBTorANarrowLin) (hU : GGTBTorANarrowUni) :
    GGTBTorANarrow :=
  fun p hp hp2 lab hlab htag h6 hdvd hM => htag.elim
    (fun h => hA p hp hp2 lab hlab h h6 hdvd hM) (fun h => hU p hp hp2 lab hlab h h6 hdvd hM)

theorem ggTorusTorW_lin_label {p n l : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ l)
    (hM : p ∣ ggTorM ⟨.A, l, n⟩) :
    LargeEvenLabelAll ⟨.A, l, n⟩ fun R _ I _ =>
      GGTorusTorW p (l - 1 - ggTorEnn p ⟨.A, l, n⟩) (ggTorM ⟨.A, l, n⟩) l
        (CartanMatrix.A l) (CoxeterMatrix.A l) R I := by
  have hM' : p ∣ 2 ^ n - 1 := by simpa [ggTorM] using hM
  have hE : ggTorEnn p ⟨.A, l, n⟩ = 0 := by
    unfold ggTorEnn
    dsimp only
    rw [if_neg]
    intro h
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h hM'
    have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hM'
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  have key := ggTorusTorW_typeA (K := K) hp hp2 hpK h3
  simpa [ggTorM, hE, hK] using key

theorem ggTorusTorW_uni_label
    {p n l : ℕ} (hp : p.Prime) (hlab : LargeEvenInLambda2 ⟨.twA, l, n⟩)
    (h4 : 4 ≤ l) (hdvd : p ∣ l + 1) (hM : p ∣ ggTorM ⟨.twA, l, n⟩) (h63 : ¬ (p = 3 ∧ l = 5)) :
    LargeEvenLabelAll ⟨.twA, l, n⟩ fun R _ I _ =>
      GGTorusTorW p (l - 1 - ggTorEnn p ⟨.twA, l, n⟩) (ggTorM ⟨.twA, l, n⟩) l
        (CartanMatrix.A l) (CoxeterMatrix.A l) R I := by
  have hpq : p ∣ 2 ^ n + 1 := by simpa [ggTorM] using hM
  have hE : ggTorEnn p ⟨.twA, l, n⟩ = 1 := by
    unfold ggTorEnn
    dsimp only
    rw [if_pos hpq]
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  have h63' : ¬ (l + 1 = 6 ∧ p = 3) := fun h => h63 ⟨h.2, by omega⟩
  have key := ggTorusTorW_unitary LineU.unitaryUniversalCover_holds (K := K) hK hn h4 hp hpq hdvd
    h63'
  have e : l - 1 - 1 = l - 2 := by omega
  simpa [ggTorM, hE, e] using key

theorem ggTBTorANarrowLin_holds : GGTBTorANarrowLin := by
  intro p hp hp2 lab hlab htag h6 hdvd hM
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h6 hdvd hM ⊢
  subst htag
  exact ggTorusTorW_lin_label hp hp2 (by omega) hM

theorem ggTBTorANarrowUni_holds :
    GGTBTorANarrowUni := by
  intro p hp hp2 lab hlab htag h6 hdvd hM
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h6 hdvd hM ⊢
  subst htag
  exact ggTorusTorW_uni_label hp hlab (by omega) hdvd hM (fun h => by omega)

theorem ggTBTorANarrow_holds :
    GGTBTorANarrow :=
  ggTBTorANarrow_of_split ggTBTorANarrowLin_holds ggTBTorANarrowUni_holds

theorem ggTBTorA_holds :
    GGTBTorA := by
  intro p hp hp2 lab hlab htag h4 hdvd hM hex
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h4 hdvd hM hex ⊢
  rcases htag with h | h
  · subst h
    exact ggTorusTorW_lin_label hp hp2 (by omega) hM
  · subst h
    have hpq : p ∣ 2 ^ n + 1 := by simpa [ggTorM] using hM
    exact ggTorusTorW_uni_label hp hlab h4 hdvd hM (fun h' => hex ⟨h'.1, h'.2, hpq⟩)

theorem ggTorusTorW_uni_six_three_label
    {f : ℕ} (hf : 2 ≤ f) (hpq : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ I _ =>
      GGTorusTorW 3 4 (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ', ggTorusTorW_unitary_six_three hK hf hpq⟩

end CFSG.StandardType
