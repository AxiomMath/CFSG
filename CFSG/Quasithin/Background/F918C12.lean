module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Ch10SecAModels
public import CFSG.RankThree.ThinCatalog.FiveModels

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Open

section Realizes

variable {V : Type*} [CommGroup V]

theorem realizesVia_injective_of_faithful {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

theorem card_eq_of_realizesVia_faithful_sec {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Nat.card ↥H = Nat.card D.Gam :=
  (Nat.card_congr (Equiv.ofBijective π ⟨realizesVia_injective_of_faithful hD h, h.1⟩)).symm

theorem card_dvd_of_realizesVia {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) : Nat.card ↥H ∣ Nat.card D.Gam := by
  have h1 := Subgroup.card_ker_mul_card_range π
  rw [MonoidHom.range_eq_top.mpr h.1, Subgroup.card_top] at h1
  exact ⟨Nat.card ↥π.ker, by rw [← h1, mul_comm]⟩

end Realizes

section Orders

open CFSG.Quasithin.Vol2.Ch11.SecA

theorem mul_sq_sub_one_ne_168 (q : ℕ) : q * (q ^ 2 - 1) ≠ 168 := by
  intro h
  have hq : q ≤ 6 := by
    by_contra hq
    push Not at hq
    have h1 : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have h2 : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right h1 1)
    omega
  interval_cases q <;> omega

theorem not_isPSL_two_two_of_isPSL_three_two {Y : Type} [Group Y] (h3 : IsPSL 3 2 1 Y) {n : ℕ}
    (h2 : IsPSL 2 2 n Y) : False := by
  obtain ⟨hn1, hcard⟩ := card_of_isPSL_two_two h2
  have h168 : Nat.card Y = 2 ^ 3 * 21 := card_L32 h3
  rw [hcard] at h168
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [oSL2] at h168
  · push Not at hn
    have h1 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2' : 2 ^ 8 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3' : 2 ^ 4 * (2 ^ 8 - 1) ≤ 2 ^ n * oSL2 n :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2' 1)
    omega

end Orders

section ModFiveAL32

variable {W : Type} [CommGroup W]

theorem not_binaryNaturalSL_two_l32 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hcard : Nat.card ↥L = 168) {n : ℕ} (h : BinaryNaturalSL L U Z 2 n) : False := by
  obtain ⟨K, hK, hKf, hc, π, hπ⟩ := h
  have hcL := card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
  have : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card ↥(StatedSL 2 K) = Fintype.card K * (Fintype.card K ^ 2 - 1) :=
    CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL_two K
  have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 2 K) := hcL
  rw [h1, hcard] at h2
  exact mul_sq_sub_one_ne_168 _ h2.symm

theorem not_binaryOrthogonalFour_l32 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hcard : Nat.card ↥L = 168) {a : ℕ} (h : BinaryOrthogonalFour L U Z a) : False := by
  obtain ⟨K, hK, hKf, hchar, hc, π, hπ⟩ := h
  have hcL := card_eq_of_realizesVia_faithful_sec
    (CFSG.Quasithin.Vol2.Ch10.SecA.twistTensor_faithful (F := K) a) hπ
  have : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card ↥(StatedSL 2 K) = Fintype.card K * (Fintype.card K ^ 2 - 1) :=
    CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL_two K
  have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 2 K) := hcL
  rw [h1, hcard] at h2
  exact mul_sq_sub_one_ne_168 _ h2.symm

theorem not_binaryNaturalSz_l32 {L : Subgroup (MulAut W)}
    {U Z : Subgroup W}
    (hcard : Nat.card ↥L = 168) {f : ℕ} (h : BinaryNaturalSz L U Z f) : False := by
  obtain ⟨a, ha, hf, K, hK, hKf, hc, π, hπ⟩ := h
  have hdvd := card_dvd_of_realizesVia hπ
  have h3 : 3 ∣ Nat.card (CFSG.Blueprint.suzukiGroup a K) := by
    rw [hcard] at hdvd
    exact (show 3 ∣ 168 by norm_num).trans hdvd
  exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel (p := 2) (f := f)
    ⟨rfl, a, ha, K, hK, hKf, hf, hc, ⟨MulEquiv.refl _⟩⟩ h3

theorem not_alternatingNatural_five_l32 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hcard : Nat.card ↥L = 168) (h : AlternatingNatural L U Z 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 5)) :=
    Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  omega

theorem modFiveA_l32 {Mp L : Subgroup (MulAut W)} {V : Subgroup W}
    (hL : IsPSL 3 2 1 ↥L)
    (h : ModFiveA Mp L V) : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1 := by
  have hcard : Nat.card ↥L = 168 := by
    have := CFSG.Quasithin.Vol2.Ch11.SecA.card_L32 hL
    omega
  rcases h.2 with ⟨n, hn⟩ | hn | ⟨f, hf⟩ | ⟨a, -, ha⟩ | hA
  · exact (not_binaryNaturalSL_two_l32 hcard hn).elim
  · exact hn
  · exact (not_binaryNaturalSz_l32 hcard hf).elim
  · exact (not_binaryOrthogonalFour_l32 hcard ha).elim
  · exact (not_alternatingNatural_five_l32 hcard hA).elim

end ModFiveAL32

end CFSG.Quasithin
