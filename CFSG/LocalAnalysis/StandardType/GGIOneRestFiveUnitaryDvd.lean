module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

section Certs

theorem largeEvenLabelAll_endNodeIOne_unitaryDvd (hR : GGIOneUnitaryDvdRootInput)
    (hD : GGIOneUnitaryDvdDeltaInput) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {p : ℕ} (hp : p.Prime) (h : GGIOneMoreUnitaryDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl3, hpq, hpd⟩ := h
  dsimp only at htag hl3 hpq hpd
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hd5 : 5 ≤ l + 1 := by
    by_contra hcon
    have hl : l = 3 := by omega
    subst hl
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  have h1 := largeEvenLabelAll_torusLift_twA hlab rfl hp hpq
  intro Q hQ
  have hQ' := h1 Q hQ
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hlift⟩ := hQ'
  have hdq := unitary_hdq (n := n) (by omega : 4 ≤ l + 1)
  exact ⟨K, i1, i2, hK, hq, InndiagSU.ggOutdiagOdd_unitary hK hn (by omega)
    (fun he => hdq (by rw [he.1, he.2])) p, _, hlift,
    ggEndNodeIOne_of_root_delta (hR K n (l + 1) p hK hn hd5 hp hpq hpd)
      (hD K n (l + 1) p hK hn hd5 hp hpq hpd)⟩

theorem ggStdSubIOneProperInputOn_unitaryDvd (ha₀ : GGLNoncyclicInput)
    (hR : GGIOneUnitaryDvdRootInput) (hD : GGIOneUnitaryDvdDeltaInput) :
    GGStdSubIOneProperInputOn GGIOneMoreUnitaryDvdLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_endNodeIOne_unitaryDvd hR hD hlab hp h

theorem largeEvenLabelAll_endNodeIOne_unitaryFiveTwo (hF : GGIOneUnitaryFiveTwoInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {p : ℕ}
    (h : GGIOneMoreUnitaryFiveTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hn, rfl⟩ := h
  dsimp only at htag hl hn
  subst htag hl hn
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h1 := largeEvenLabelAll_torusLift_twA hlab rfl Nat.prime_three hpq
  have hr : ggUnitaryTorusRank 3 (4 + 1) = 3 := by
    simp only [ggUnitaryTorusRank, show ¬ 3 ∣ 4 + 1 by norm_num, ↓reduceIte]
  intro Q hQ
  have hQ' := h1 Q hQ
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hlift⟩ := hQ'
  rw [hr] at hlift
  have hdq := unitary_hdq (n := 1) (by norm_num : 4 ≤ 4 + 1)
  exact ⟨K, i1, i2, hK, hq, InndiagSU.ggOutdiagOdd_unitary hK le_rfl (by norm_num)
    (fun he => hdq (by rw [he.1, he.2])) 3, 3, hlift, hF K (by rw [hK])⟩

theorem ggStdSubIOneProperInputOn_unitaryFiveTwo (ha₀ : GGLNoncyclicInput)
    (hF : GGIOneUnitaryFiveTwoInput) : GGStdSubIOneProperInputOn GGIOneMoreUnitaryFiveTwoLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ _ hlab h _ =>
    largeEvenLabelAll_endNodeIOne_unitaryFiveTwo hF hlab h

theorem ggStdSubIOneProperInputOn_unitaryRest (ha₀ : GGLNoncyclicInput)
    (hDR : GGIOneUnitaryDvdRootInput) (hDD : GGIOneUnitaryDvdDeltaInput)
    (hT : GGIOneUnitaryThreeRootInput) (hF : GGIOneUnitaryFiveTwoInput) :
    GGStdSubIOneProperInputOn GGIOneMoreUnitaryRestLabel :=
  ((ggStdSubIOneProperInputOn_unitaryDvd ha₀ hDR hDD).or
    ((ggStdSubIOneProperInputOn_unitaryThree ha₀ hT).or
      (ggStdSubIOneProperInputOn_unitaryFiveTwo ha₀ hF))).mono fun _ _ h =>
    ggIOneMoreUnitaryRestLabel_cover h

end Certs

end CFSG.StandardType
