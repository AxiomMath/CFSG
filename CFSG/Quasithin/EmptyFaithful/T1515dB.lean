module

public import CFSG.Quasithin.EmptyFaithful.T1515dInputs
public import CFSG.Quasithin.EmptyFaithful.T1515M11
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.B69Num
public import CFSG.Quasithin.Background.B69SL2
public import CFSG.Quasithin.Vol2.KGNatG2Order
import CFSG.Adapters.StatedClassicalOrders

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Orders

theorem card_statedSL1527d {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 1 ≤ d) :
    Nat.card ↥(StatedSL d F) =
      Nat.card F ^ (d * (d - 1) / 2) * ∏ j ∈ Finset.Icc 2 d, (Nat.card F ^ j - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_eq_prod hd

theorem card_statedSL_two1527d {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem card_statedSL_three1527d {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

theorem card_statedSL_four_zmod1527d : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five_zmod1527d : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem card_alternatingGroup1527d (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem ne_card_sl2_1527d {F : Type} [Field F] [Finite F] {N : ℕ} (hN : N = 20160 ∨ N = 9999360) :
    Nat.card ↥(StatedSL 2 F) ≠ N := by
  intro h
  rw [card_statedSL_two1527d] at h
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  refine CFSG.Quasithin.B69.cubic_no (Nat.card F) 1 (by norm_num) (by norm_num) N hN ?_
  have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq
  calc N * 1 + Nat.card F = Nat.card F * (Nat.card F ^ 2 - 1) + Nat.card F := by rw [mul_one, h]
    _ = Nat.card F * (Nat.card F ^ 2 - 1 + 1) := by ring
    _ = Nat.card F ^ 3 := by rw [Nat.sub_add_cancel h1]; ring

theorem ne_card_sl3_1527d {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {N : ℕ}
    (hN : N = 20160 ∨ N = 9999360) : Nat.card ↥(StatedSL 3 F) ≠ N := by
  intro h
  rw [card_statedSL_three1527d, hF] at h
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := CFSG.Quasithin.B69.big_three (g := 1) (X := N) hq (by norm_num) 1 (Or.inl rfl)
      (Or.inr (by rw [mul_one]; exact h.symm))
    rcases hN with rfl | rfl <;> omega

theorem ne_card_sp4_1527d {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) {N : ℕ}
    (hN : N = 20160 ∨ N = 9999360) : Nat.card ↥(StatedSp 2 F) ≠ N := by
  intro h
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF] at h
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := CFSG.Quasithin.B69.big_four (X := N) hq (by
      rw [← h]
      norm_num)
    rcases hN with rfl | rfl <;> omega

theorem card_quasithinG2_1527d {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(CFSG.Open.quasithinG2 F) = Nat.card F ^ 6 * ((Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1)) := by
  have := FFC.charP_two_of_card_pow hF
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  exact CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup

end Orders

theorem ne_g2_num1527d {n N : ℕ} (hN : N = 20160 ∨ N = 9999360) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 4 ^ 6 - 1 ≤ (2 ^ n) ^ 6 - 1 := Nat.sub_le_sub_right h1 1
    have h3 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    rcases hN with rfl | rfl <;> norm_num at h4

theorem card_of_isHat1527d {X S : Type} [Group X] [Group S] [Finite X] (h : IsHat X S)
    (hS : Nat.card S = 360) : Nat.card X = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [Nat.card_congr e.toEquiv, hS, hc] at h1
  omega

theorem card_le_of_surjective1527d {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) : Nat.card B ≤ Nat.card A :=
  Nat.card_le_card_of_surjective f hf

section Exclude

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem card_eq_of_nat_realizes1527d {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {π : ↥Γ →* ↥K}
    (h : (FFModel.nat Γ).RealizesVia K U Z π) : Nat.card ↥K = Nat.card ↥Γ :=
  (Nat.card_congr (Equiv.ofBijective π
    ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ) h, h.1⟩)).symm

theorem not_binaryNaturalSL_two1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) {n : ℕ}
    (h : BinaryNaturalSL K U Z 2 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  exact ne_card_sl2_1527d (N := Nat.card ↥K) hN (card_eq_of_nat_realizes1527d hπ).symm

theorem not_binaryNaturalSL_three1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) {n : ℕ}
    (h : BinaryNaturalSL K U Z 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  exact ne_card_sl3_1527d hF (N := Nat.card ↥K) hN (card_eq_of_nat_realizes1527d hπ).symm

theorem not_binaryNaturalSp4_1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) {n : ℕ}
    (h : BinaryNaturalSp4 K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  exact ne_card_sp4_1527d hF (N := Nat.card ↥K) hN (card_eq_of_nat_realizes1527d hπ).symm

theorem not_g2Natural1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) {n : ℕ}
    (h : G2Natural K U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥K = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  exact ne_g2_num1527d (n := n) (N := Nat.card ↥K) hN hcard.symm

theorem not_g2NaturalDerived_one1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360)
    (h : G2NaturalDerived K U Z 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hG2 := card_quasithinG2_1527d hF
  have hfin : Finite ↥(CFSG.Open.quasithinG2 F) :=
    Nat.finite_of_card_ne_zero (by rw [hG2, hF]; norm_num)
  have h1 : Nat.card ↥K ≤ Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤
      Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  rw [hG2, hF] at h2
  norm_num at h2
  rcases hN with h | h <;> omega

theorem not_alternatingNatural1527d {n : ℕ} (hn : 2 ≤ n) (hlt : n.factorial / 2 < Nat.card ↥K)
    (h : AlternatingNatural K U Z n) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥(alternatingGroup (Fin n)) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [card_alternatingGroup1527d n hn] at h1
  omega

theorem not_a7Four1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) (h : A7Four K U Z) :
    False := by
  obtain ⟨α, π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
  rcases hN with h | h <;> norm_num [Nat.factorial] at h1 <;> omega

theorem not_tripleA6Six1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360)
    (h : TripleA6Six K U Z) : False := by
  obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
  have h1 : Nat.card ↥K ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥Γ₀ = 1080 :=
    card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  rw [h2] at h1
  rcases hN with h | h <;> omega

end Exclude

section CaseI

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem directSumOfCopies_one1527d {D : FFModel} {L : Subgroup (MulAut V)} {U : Subgroup V}
    {π : D.Gam →* ↥L} (h : D.RealizesVia L U ⊥ π) : DirectSumOfCopies L U ⊥ D 1 := by
  refine ⟨fun _ => U, π, fun _ => bot_le, fun i => ?_, ?_, fun _ => h⟩
  · have h1 : (⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥ :=
      iSup₂_eq_bot.2 fun j hj => absurd (Subsingleton.elim j i) hj
    show U ⊓ (⊥ ⊔ ⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥
    rw [h1, bot_sup_eq, inf_bot_eq]
  · show ⊥ ⊔ ⨆ _ : Fin 1, U = U
    rw [iSup_const, bot_sup_eq]

variable {K : Subgroup (MulAut V)}

omit [Finite V] in
theorem zbot_of_extSq_five1527d (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360)
    (hpart2 : B51Part2 K) (h : SLExteriorTwo K (commV K) (fixV K ⊓ commV K) 5) :
    fixV K ⊓ commV K = ⊥ := by
  rcases hN with h20 | h99
  · exfalso
    obtain ⟨π, hπ⟩ := h
    have hs : IsSimpleGroup (FFModel.extSq (ZMod 2) 5).Gam :=
      CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by norm_num)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
      have : Nat.card ↥(StatedSL 5 (ZMod 2)) = Nat.card ↥K :=
        Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
      rw [card_statedSL_five_zmod1527d] at this
      omega
    · have hsub : Subsingleton ↥K := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hπ.1 a
        obtain ⟨y, rfl⟩ := hπ.1 b
        have hx : x ∈ π.ker := by rw [htop]; trivial
        have hy : y ∈ π.ker := by rw [htop]; trivial
        rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]⟩
      have := Nat.card_of_subsingleton (1 : ↥K)
      omega
  · by_contra hZ
    have hnot : ¬ IsIntDirect (commV K) (fixV K) ⊤ := fun hd => hZ (by
      have := hd.2
      rwa [inf_comm] at this)
    obtain ⟨-, hl⟩ := hpart2.2 hnot
    rcases hl with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | hn | hn | hn | hn
    · exact not_binaryNaturalSL_two1527d (Or.inr h99) hn
    · exact not_binaryNaturalSp4_1527d (Or.inr h99) hn
    · exact not_g2Natural1527d (Or.inr h99) hn
    · exact not_alternatingNatural1527d (n := 6) (by norm_num) (by rw [h99]; norm_num [Nat.factorial]) hn
    · exact not_alternatingNatural1527d (n := 8) (by norm_num) (by rw [h99]; norm_num [Nat.factorial]) hn
    · exact not_g2NaturalDerived_one1527d (Or.inr h99) hn
    · exact not_binaryNaturalSL_three1527d (Or.inr h99) hn

theorem alt15127_of_caseI1527d (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hV : ∀ v : V, v ^ 2 = 1)
    (hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360) (hirr : commV K ∈ IrrPlus K ⊤)
    (hpair : B42ModulePair K (commV K) (fixV K ⊓ commV K))
    (hZ5 : SLExteriorTwo K (commV K) (fixV K ⊓ commV K) 5 → fixV K ⊓ commV K = ⊥) :
    Alt15127 K (commV K) := by
  rcases hpair with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (not_binaryNaturalSL_two1527d hN h).elim
  · exact (not_binaryNaturalSL_three1527d hN h).elim
  · exact (not_binaryNaturalSp4_1527d hN h).elim
  · exact (not_g2Natural1527d hN h).elim
  · exact (not_g2NaturalDerived_one1527d hN h).elim
  · refine (not_alternatingNatural1527d (n := 5) (by norm_num) ?_ h).elim
    rcases hN with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  · refine (not_alternatingNatural1527d (n := 6) (by norm_num) ?_ h).elim
    rcases hN with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  · refine (not_alternatingNatural1527d (n := 7) (by norm_num) ?_ h).elim
    rcases hN with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  · exact (not_a7Four1527d hN h).elim
  · exact (not_tripleA6Six1527d hN h).elim
  · have hZ := hI16 V hV K hirr (Or.inr (Or.inl h))
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    rw [hZ] at hπ
    exact Or.inr (Or.inr (Or.inr ⟨4, Or.inl rfl, 1, le_rfl, by norm_num,
      directSumOfCopies_one1527d hπ⟩))
  · have hZ := hI16 V hV K hirr (Or.inr (Or.inr h))
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    rw [hZ] at hπ
    exact Or.inr (Or.inr (Or.inr ⟨5, Or.inr rfl, 1, le_rfl, by norm_num,
      directSumOfCopies_one1527d hπ⟩))
  · exact Or.inl ⟨fixV K ⊓ commV K, le_rfl, hA8 V hV K hirr h, h⟩
  · have hZ := hZ5 h
    rw [hZ] at h
    exact Or.inr (Or.inl h)

end CaseI

theorem alt15127_of_b51 (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {J K : Subgroup (MulAut V)}
    (hB : B51Hyp J K) (hK : IsPSL 4 2 1 ↥K ∨ IsPSL 5 2 1 ↥K) : Alt15127 K (commV K) := by
  have hN : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360 := by
    rcases hK with h | h
    · left
      rw [card_of_isPSL_two1522 4 h]
      decide
    · right
      rw [card_of_isPSL_two1522 5 h]
      decide
  obtain ⟨hp1, hp2, -⟩ := h51 V hV J K hB
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · exact alt15127_of_caseI1527d hI16 hA8 hV hN hi.1 hi.2.1
      (fun h => zbot_of_extSq_five1527d hN hp2 h)
  · exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hF (N := Nat.card ↥K) hN
      (card_eq_of_nat_realizes1527d (hreal 0)).symm
  · exact Or.inr (Or.inr (Or.inl ⟨n, hiii.2⟩))
  · exact Or.inr (Or.inr (Or.inr hiv.2))

end CFSG.Quasithin
