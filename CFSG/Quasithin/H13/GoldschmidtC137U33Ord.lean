module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.B5NonInputs

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem sl2_num_ne (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 32 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 := Nat.mul_le_mul hq h2
    omega

theorem sl3_num_ne (n : ℕ) : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 4 ^ 3 - 1 ≤ (2 ^ n) ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem sp4_num_ne (n : ℕ) : (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 4 ^ 4 - 1 ≤ (2 ^ n) ^ 4 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem g2_num_ne (n : ℕ) : (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 4 ^ 6 - 1 ≤ (2 ^ n) ^ 6 - 1 := Nat.sub_le_sub_right h1 1
    have h3 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

section Exclude

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_natSL_two (hK : Nat.card ↥K = 6048) {n : ℕ} (h : BinaryNaturalSL K U Z 2 n) :
    False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hK, card_statedSL_two1527d, hF] at h1
  exact sl2_num_ne n h1.symm

theorem not_natSL_three (hK : Nat.card ↥K = 6048) {n : ℕ} (h : BinaryNaturalSL K U Z 3 n) :
    False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hK, card_statedSL_three1527d, hF] at h1
  exact sl3_num_ne n h1.symm

theorem not_natSp4 (hK : Nat.card ↥K = 6048) {n : ℕ} (h : BinaryNaturalSp4 K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hK, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF] at h1
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h1
  · exact sp4_num_ne n (by simpa using h1.symm)

theorem not_g2Natural (hK : Nat.card ↥K = 6048) {n : ℕ} (h : G2Natural K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  exact g2_num_ne n (hK ▸ hcard.symm)

theorem not_altNatural {m : ℕ} (hm : 2 ≤ m) (hlt : m.factorial / 2 < Nat.card ↥K)
    (h : AlternatingNatural K U Z m) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥(alternatingGroup (Fin m)) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [card_alternatingGroup1527d m hm] at h1
  omega

theorem not_a7Four (hK : Nat.card ↥K = 6048) (h : A7Four K U Z) : False := by
  obtain ⟨α, π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
  norm_num [Nat.factorial] at h1
  omega

theorem not_tripleA6Six (hK : Nat.card ↥K = 6048) (h : TripleA6Six K U Z) : False := by
  obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥Γ₀ = 1080 :=
    card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  omega

theorem not_natSL_four (hK : Nat.card ↥K = 6048) (h : BinaryNaturalSL K U Z 4 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
  have := Fintype.ofFinite F
  have h4 : Nat.card ↥(StatedSL 4 F) = 20160 := by
    rw [card_statedSL1527d (by norm_num), hF2]
    decide
  omega

theorem not_natSL_five (hK : Nat.card ↥K = 6048) (h : BinaryNaturalSL K U Z 5 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
  have := Fintype.ofFinite F
  have h5 : Nat.card ↥(StatedSL 5 F) = 9999360 := by
    rw [card_statedSL1527d (by norm_num), hF2]
    decide
  omega

theorem not_extSq (hK : Nat.card ↥K = 6048) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (h : SLExteriorTwo K U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  have hs : IsSimpleGroup (FFModel.extSq (ZMod 2) d).Gam :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
    have h1 : Nat.card (FFModel.extSq (ZMod 2) d).Gam = Nat.card ↥K :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
    rcases hd with rfl | rfl
    · rw [show (FFModel.extSq (ZMod 2) 4).Gam = StatedSL 4 (ZMod 2) from rfl,
        card_statedSL_four_zmod1527d] at h1
      omega
    · rw [show (FFModel.extSq (ZMod 2) 5).Gam = StatedSL 5 (ZMod 2) from rfl,
        card_statedSL_five_zmod1527d] at h1
      omega
  · have hsub : Subsingleton ↥K := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hπ.1 a
      obtain ⟨y, rfl⟩ := hπ.1 b
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]⟩
    have := Nat.card_of_subsingleton (1 : ↥K)
    omega

theorem g2NaturalDerived_of_modulePair (hK : Nat.card ↥K = 6048) (h : B42ModulePair K U Z) :
    G2NaturalDerived K U Z 1 := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (not_natSL_two hK h).elim
  · exact (not_natSL_three hK h).elim
  · exact (not_natSp4 hK h).elim
  · exact (not_g2Natural hK h).elim
  · exact h
  · exact (not_altNatural (m := 5) (by norm_num) (by rw [hK]; norm_num [Nat.factorial]) h).elim
  · exact (not_altNatural (m := 6) (by norm_num) (by rw [hK]; norm_num [Nat.factorial]) h).elim
  · exact (not_altNatural (m := 7) (by norm_num) (by rw [hK]; norm_num [Nat.factorial]) h).elim
  · exact (not_a7Four hK h).elim
  · exact (not_tripleA6Six hK h).elim
  · exact (not_natSL_four hK h).elim
  · exact (not_natSL_five hK h).elim
  · exact (not_extSq hK (Or.inl rfl) h).elim
  · exact (not_extSq hK (Or.inr rfl) h).elim

end Exclude

theorem not_isL345Type_of_card {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 6048) :
    ¬ IsL345Type Γ := by
  rintro (⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩)
  · have h3 := Nat.card_congr e.toEquiv
    rw [card_statedSL_three1527d, hK, hΓ] at h3
    exact sl3_num_ne n h3.symm
  · have h4 := Nat.card_congr e.toEquiv
    have := Fintype.ofFinite K
    have hc : Nat.card ↥(StatedSL 4 K) = 20160 := by
      rw [card_statedSL1527d (by norm_num), hK]
      decide
    omega
  · have h5 := Nat.card_congr e.toEquiv
    have := Fintype.ofFinite K
    have hc : Nat.card ↥(StatedSL 5 K) = 9999360 := by
      rw [card_statedSL1527d (by norm_num), hK]
      decide
    omega

end CFSG.Quasithin.H13.U3.GC137
