module

public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem eq_two_of_sl3_card {q : ℕ} (h : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 168) : q = 2 := by
  have hq : q ≤ 2 := by
    by_contra hq
    push Not at hq
    have h1 : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 3 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4
  interval_cases q <;> simp_all

theorem sp4_card_ne {q : ℕ} : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≠ 168 := by
  intro h
  have hq : q ≤ 2 := by
    by_contra hq
    push Not at hq
    have h1 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 3 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4
  interval_cases q <;> simp_all

theorem g2_card_ne {q : ℕ} : q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) ≠ 168 := by
  intro h
  have hq : q ≤ 2 := by
    by_contra hq
    push Not at hq
    have h1 : 3 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 3 ^ 6 - 1 ≤ q ^ 6 - 1 := Nat.sub_le_sub_right h1 1
    have h3 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4
  interval_cases q <;> simp_all

theorem sl2_card_ne {q : ℕ} : q * (q ^ 2 - 1) ≠ 168 := by
  intro h
  have hq : q ≤ 6 := by
    by_contra hq
    push Not at hq
    have h1 : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have h2 : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right h1 1)
    omega
  interval_cases q <;> omega

section G2Two

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Bridge.Alt57Model CFSG.Open
open scoped commutatorElement

theorem card_commutator_quasithinG2_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 6048 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := nonempty_commutator_equiv (MulEquiv.refl ↥(quasithinG2 K))
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  let F : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* U33G :=
    (((f1.trans f2).trans f3).trans u33EquivSubG2.symm)
  rw [Nat.card_congr F.toEquiv]
  exact card_u33Pres

end G2Two

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_sl2_168 (hc : Nat.card ↥L = 168) {n : ℕ} (h : BinaryNaturalSL L U Z 2 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_two1527d, hc] at h1
  exact sl2_card_ne h1.symm

theorem not_sp4_168 (hc : Nat.card ↥L = 168) {n : ℕ} (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp] at h1
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  exact sp4_card_ne (q := Nat.card F) (by simpa using h1.symm)

theorem not_g2_168 (hc : Nat.card ↥L = 168) {n : ℕ} (h : G2Natural L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hc] at hcard
  exact g2_card_ne hcard.symm

theorem not_g2d_168
    (hc : Nat.card ↥L = 168) (h : G2NaturalDerived L U Z 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcP := FFC.charP_two_of_card_pow hF
  have hΓ : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤ CFSG.Open.quasithinG2 F := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  have hcard : Nat.card ↥L = Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ hΓ) hπ, hπ.1⟩)).symm
  rw [card_commutator_quasithinG2_two (by simpa using hF), hc] at hcard
  omega

theorem not_alt_168 {m : ℕ} (hm : 5 ≤ m) (hne : m.factorial / 2 ≠ 168) (hc : Nat.card ↥L = 168)
    (h : AlternatingNatural L U Z m) : False := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin m)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful hm) hπ).toEquiv).symm
  rw [card_alternatingGroup1527d m (by omega), hc] at hcard
  exact hne hcard.symm

theorem not_a7Four_168 (hc : Nat.card ↥L = 168) (h : A7Four L U Z) : False := by
  obtain ⟨α, π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ).toEquiv).symm
  rw [card_alternatingGroup1527d 7 (by norm_num), hc] at hcard
  norm_num [Nat.factorial] at hcard

theorem not_tripleA6_168 (hc : Nat.card ↥L = 168) (h : TripleA6Six L U Z) : False := by
  obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥Γ₀ :=
    (Nat.card_congr (FFC.equivOfRealizes (FFModel.nat_faithful Γ₀) hπ).toEquiv).symm
  have h2 : Nat.card ↥Γ₀ = 1080 :=
    card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  omega

theorem not_sl_two_168 (hc : Nat.card ↥L = 168) {d : ℕ} (hd : d = 4 ∨ d = 5)
    {π : ↥(StatedSL d (ZMod 2)) →* ↥L}
    (hπ : (FFModel.nat (StatedSL d (ZMod 2))).RealizesVia L U Z π) : False := by
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at h1
  rcases hd with rfl | rfl <;> revert h1 <;> decide

theorem not_extSq_168 (hc : Nat.card ↥L = 168) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (h : SLExteriorTwo L U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(StatedSL d (ZMod 2)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
  rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at hcard
  rcases hd with rfl | rfl <;> revert hcard <;> decide

theorem binaryNaturalSL_three_one (hc : Nat.card ↥L = 168) {n : ℕ} (h : BinaryNaturalSL L U Z 3 n) :
    BinaryNaturalSL L U Z 3 1 := by
  obtain ⟨F, hF1, hF2, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, card_statedSL_three1527d] at h1
  have h2 : Nat.card F = 2 := eq_two_of_sl3_card h1.symm
  exact ⟨F, hF1, hF2, by rw [h2, pow_one], π, hπ⟩

end Excl

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem l3_natural_or_q_one
    (hB51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hB : B51Hyp G L)
    (hc : Nat.card ↥L = 168) :
    (1 : WithTop ℚ) ≤ qOf G ∨ BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1 := by
  obtain ⟨hp1, -⟩ := hB51 V hV G L hB
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · right
    rcases hi.2.1 with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact (not_sl2_168 hc h).elim
    · exact binaryNaturalSL_three_one hc h
    · exact (not_sp4_168 hc h).elim
    · exact (not_g2_168 hc h).elim
    · exact (not_g2d_168 hc h).elim
    · exact (not_alt_168 (m := 5) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
    · exact (not_alt_168 (m := 6) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
    · exact (not_alt_168 (m := 7) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
    · exact (not_a7Four_168 hc h).elim
    · exact (not_tripleA6_168 hc h).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (not_sl_two_168 hc (Or.inl rfl) hπ).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (not_sl_two_168 hc (Or.inr rfl) hπ).elim
    · exact (not_extSq_168 hc (Or.inl rfl) h).elim
    · exact (not_extSq_168 hc (Or.inr rfl) h).elim
  · left
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, -, -, hq⟩ := hii
    rw [hq]
    exact le_of_eq (by simp)
  · exfalso
    obtain ⟨hn, π, U₁, U₂, -, hreal, -⟩ := hiii.2
    exact not_sl_two_168 hc hn hreal
  · exfalso
    obtain ⟨-, n, hn, k, hk, -, hdir⟩ := hiv
    obtain ⟨I, π, -, -, -, hreal⟩ := hdir
    exact not_sl_two_168 hc hn (hreal ⟨0, hk⟩)

end Main

end S1549D

end CFSG.Quasithin
