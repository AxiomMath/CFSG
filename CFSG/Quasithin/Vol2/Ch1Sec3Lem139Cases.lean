module

public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139A5Case
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedLieTag StatedScalars StatedProj StatedSL StatedClassicalModel
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat)

@[expose] def Lemma139L42Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ T L Y : Subgroup G, quasithinIsSylowTwo T →
      quasithinIsLocal T L → quasithinIsLocal T Y → L ≤ Y → L ≠ Y → IsPSL 4 2 1 (ModO2 L) →
      ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) →
        ∃ ℓ ∈ L, ∀ x ∈ L, (t * x * t⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ pCoreOf 2 L

@[expose] def Lemma139A5Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ T L Y : Subgroup G, quasithinIsSylowTwo T →
      quasithinIsLocal T L → quasithinIsLocal T Y → L ≤ Y → L ≠ Y → L < conjClosure L T →
      IsAlt 5 (ModO2 L) →
      (IsSporadic .J1 (ModO2 Y) ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ IsPSL 2 p 1 (ModO2 Y)) →
      ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) →
        ∃ ℓ ∈ L, ∀ x ∈ L, (t * x * t⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ pCoreOf 2 L

variable {G : Type} [Group G]

@[expose] def Cases134E9He (H S P L : Subgroup G) : Prop :=
  ((∃ t ∈ S ⊓ Subgroup.normalizer (P : Set G), t ∉ Subgroup.normalizer (L : Set G) ∧
      P = (P ⊓ L) ⊔ conjByElt t (P ⊓ L) ∧ (P ⊓ L) ⊓ conjByElt t (P ⊓ L) = ⊥) ∧
    ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1)) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))))) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) ∧
    EmptyFaithfulMultiple.AutCyclic S P) ∨
  (S ≤ Subgroup.normalizer (L : Set G) ∧
    (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1)) ∨
  (H ≤ Subgroup.normalizer (L : Set G) ∧
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))

theorem ordBC_two_gt {n : ℕ} (hn : 2 ≤ n) : 20160 < ordBC 2 (2 ^ n) := by
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  generalize 2 ^ n = q at hq ⊢
  have hprod : ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  have hd : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h4 : 256 ≤ q ^ (2 * 2) :=
    calc 256 = 4 ^ (2 * 2) := by norm_num
      _ ≤ q ^ (2 * 2) := Nat.pow_le_pow_left hq _
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq _
    omega
  have h3 : 255 ≤ q ^ 4 - 1 := by
    have : 256 ≤ q ^ 4 :=
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq _
    omega
  unfold ordBC
  rw [hprod]
  refine Nat.lt_of_lt_of_le (show 20160 < 20161 by norm_num) ?_
  rw [Nat.le_div_iff_mul_le hd0]
  calc 20161 * Nat.gcd 2 (q - 1) ≤ 20161 * 2 := Nat.mul_le_mul_left _ hd
    _ ≤ 256 * (15 * 255) := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.mul_le_mul h4 (Nat.mul_le_mul h2 h3)

theorem a128FourList_of_sp4 {Y : Type} [Group Y] {n : ℕ} (hn : Even n)
    (h : StatedClassicalModel Y .PSp 2 2 n) : A128FourList Y := by
  have h1 : 1 ≤ n := by
    obtain ⟨⟨-, h1, -⟩, -⟩ := h
    exact h1
  have h2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hcard : Nat.card Y = ordBC 2 (2 ^ n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  have hbig := ordBC_two_gt h2
  have hL1 : ¬ IsPSL 3 2 1 Y := fun hL => by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
    have h4 : ordA (3 - 1) (2 ^ 1) = 168 := by decide
    omega
  have hL2 : ¬ IsPSL 3 2 2 Y := fun hL => by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
    have h4 : ordA (3 - 1) (2 ^ 2) = 20160 := by decide
    omega
  unfold A128FourList
  iterate 14 right
  exact ⟨Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨h2, h⟩))⟩, hL1, hL2⟩

theorem nonempty_gl4_of_model {Y : Type} [Group Y] (h : StatedClassicalModel Y .PSL 4 2 1) :
    Nonempty (Y ≃* L42.GL4) := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hF2 : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  have hone : ∀ a : F, a ≠ 0 → a = 1 := fun a ha => by
    have := FiniteField.pow_card_sub_one_eq_one a ha
    rwa [hF2, show 2 - 1 = 1 from rfl, pow_one] at this
  have hSL : StatedSL 4 F = ⊤ := by
    rw [eq_top_iff]
    intro A _
    exact Subgroup.subset_closure (hone _ (Matrix.GeneralLinearGroup.det_ne_zero A))
  have hsc : (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) = ⊥ := by
    have hbot : StatedScalars (Fin 4) F = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨u, rfl⟩
      have hu : u = 1 := Units.ext (hone _ u.ne_zero)
      rw [hu, map_one]
      exact Subgroup.one_mem _
    rw [hbot, Subgroup.bot_subgroupOf]
  have eF : F ≃+* ZMod 2 :=
    FiniteField.ringEquivOfCardEq (by rw [hF2, ZMod.card])
  exact ⟨e₀.trans ((QuotientGroup.quotientMulEquivOfEq hsc).trans
    (QuotientGroup.quotientBot.trans ((MulEquiv.subgroupCongr hSL).trans
      (Subgroup.topEquiv.trans (Units.mapEquiv (RingEquiv.mapMatrix eF).toMulEquiv)))))⟩

variable [Finite G]

theorem lemma139One_of_cases (h128two : Lemma128Two) (h128four : Lemma128Four)
    (hKG1 : Lemma139L42Inner) (hKG2 : Lemma139A5Inner) (h38 : A38ForSQTKCat)
    (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {H T X P K : Subgroup G} (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hX9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X) (hP3 : IsPGroup 3 P)
    (hP9 : Nat.card P = 9) (hK : quasithinIsLocal T K) (hXK : X ≤ conjClosure K T)
    (_hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hcases : Cases134E9He H T P K) :
    quasithinIsMaximalLocal T K := by
  have hlist : A128FourList (ModO2 K) → quasithinIsMaximalLocal T K :=
    h128four G hQ hs hnab T K hK
  rcases hcases with ⟨⟨t, ⟨htT, htP⟩, htK, hPdec, hPint⟩, -⟩ | ⟨-, h2⟩ | ⟨-, h3, -⟩ |
    ⟨hTK, h4⟩ | ⟨-, h5⟩
  ·
    have hlt : K < conjClosure K T := by
      refine lt_of_le_of_ne (le_conjClosure K T) fun h => htK ?_
      apply L139.mem_normalizer_of_conj_le
      intro k hk
      rw [h]
      exact mem_conjClosure htT hk
    refine ⟨hK, fun Y hY hKY => ?_⟩
    by_contra hYK
    rcases h128two G hQ hs hnab T K Y hK hY hKY hlt with h | ⟨hA5, hYt⟩
    · exact hYK h.symm
    · exact L139.a5_case_false h38 hQ hs hnab hT hX hX9 hPX hP3 hP9 hK htT htP htK hPdec hPint
        hA5 fun s hsT hsK =>
          hKG2 G hQ hs hnab T K Y hT hK hY hKY (Ne.symm hYK) hlt hA5 hYt s hsT hsK
  ·
    apply hlist
    refine Or.inr (Or.inr (Or.inl ⟨true, 3, Nat.prime_three, by norm_num, ?_⟩))
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3, h⟩
  ·
    obtain ⟨n, hn, hSp⟩ := h3
    exact hlist (a128FourList_of_sp4 hn hSp)
  ·
    rcases h4 with h | h | h
    · exact hlist (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · refine ⟨hK, fun Y hY hKY => ?_⟩
      by_contra hYK
      obtain ⟨e⟩ := nonempty_gl4_of_model h
      have hXK' : X ≤ K := hXK.trans (conjClosure_le fun t ht k hk =>
        (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
      exact L139.l42_false hT hX hX9 hPX hP3 hP9 hTK hXK' e fun t ht =>
        hKG1 G hQ hs hnab T K Y hT hK hY hKY (Ne.symm hYK) h t ht (hTK ht)
    · apply hlist
      unfold A128FourList
      iterate 12 right
      exact Or.inl h
  ·
    apply hlist
    unfold A128FourList
    iterate 10 right
    exact Or.inl h5

end CFSG.Quasithin.H13
