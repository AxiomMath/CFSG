module

public import CFSG.RankThree.PartTwo.Sec20.One
public import CFSG.RankThree.PartTwo.Sec3.Item321
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem exists_sec18H_of_ctx20One {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (h : Ctx20One G A M L N c T) :
    ∃ H : Subgroup G, Sec18.Sec18H G A M H c ∧ Sec18.Hyp187 A M H c ∧
      L = inSubgroup perfectResidual H ∧ N = Subgroup.normalizer (L : Set G) := by
  obtain ⟨H, hH, hH2, hL, hN, hch⟩ := h.one
  refine ⟨H, ⟨⟨h.toPartTwoStanding, h.partTwoS_eq, h.mem_partTwoE, h.mem_scriptM⟩,
    scriptHStar_subset A M hH, ?_⟩, ⟨hH, hH2, ?_⟩, hL, hN⟩
  · rw [← hL]
    exact h.centralizer_eq
  · intro h2
    rw [← hL, ← hN]
    exact hch h2

theorem sec18Std_of_hyp201 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) :
    Sec18Std G A M :=
  ⟨h.toPartTwoStanding, h.partTwoS_eq, h.mem_partTwoE, h.mem_scriptM⟩

theorem le_of_hyp201 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) : A ≤ M :=
  Sec18.sec18Std_le (sec18Std_of_hyp201 h)

theorem mem_of_hyp201 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) : c ∈ A := by
  have hc : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
  rw [← h.centralizer_eq] at hc
  exact hc.1

omit [Finite G] in
theorem self_mem_normalClosureIn (M : Subgroup G) (c : G) : c ∈ normalClosureIn M c :=
  Subgroup.subset_closure ⟨1, M.one_mem, by group⟩

omit [Finite G] in
theorem normalClosureIn_le {M : Subgroup G} {c : G} (hc : c ∈ M) : normalClosureIn M c ≤ M := by
  rw [normalClosureIn, Subgroup.closure_le]
  rintro _ ⟨m, hm, rfl⟩
  exact M.mul_mem (M.mul_mem hm hc) (M.inv_mem hm)

theorem kTwenty_le_of_hyp201 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) :
    kTwenty M c ≤ M :=
  normalClosureIn_le (Sec18.sec18Std_le (sec18Std_of_hyp201 h) (mem_of_hyp201 h))

theorem generalizedFitting_eq_of_pCoreOf_le (hchar : CFSG.Assembly.IsCharTwoType G)
    {M X : Subgroup G} (hM : CFSG.Assembly.IsTwoLocal M) (hXM : X ≤ M)
    (hOX : CFSG.Open.pCoreOf 2 M ≤ X) :
    CFSG.generalizedFitting X = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore]
  have h1 : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOX
      (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  intro x hx
  have hxG : (x : G) ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx y hy)
  have hxM : (x : G) ∈ CFSG.Open.pCoreOf 2 M :=
    hchar M hM ⟨hXM x.2, Subgroup.centralizer_le h1 hxG⟩
  obtain ⟨y, hy, hyx⟩ := h1 hxM
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem pCoreOf_le_of_isSylowOf {T M : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    CFSG.Open.pCoreOf 2 M ≤ T :=
  le_of_isSylowOf_of_normal (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M) le_rfl
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M) hT

theorem isSylowOf_sup_of_coprime {p : ℕ} [Fact p.Prime] {P D : Subgroup G} (hP : IsPGroup p P)
    (hD : ¬ p ∣ Nat.card D) (hPD : P ≤ Subgroup.normalizer (D : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf p P (P ⊔ D) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_left, hP, fun hdvd => hD ?_⟩
  have h1 := Subgroup.relIndex_mul_card P (P ⊔ D)
  rw [inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card D (P ⊔ D)
  rw [inf_eq_left.mpr le_sup_right] at h2
  have h3 : D.relIndex (P ⊔ D) = D.relIndex P := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hPD
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPD
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient P D hPD).toEquiv.symm
  have h4 := Subgroup.relIndex_mul_card D P
  rw [h3] at h2
  have hpos : 0 < D.relIndex P := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := Subgroup.relIndex_mul_card D P
    rw [h0, zero_mul] at this
    exact (Nat.card_pos (α := P)).ne' this.symm
  have key : P.relIndex (P ⊔ D) * Nat.card (D ⊓ P : Subgroup G) = Nat.card D := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc D.relIndex P * (P.relIndex (P ⊔ D) * Nat.card (D ⊓ P : Subgroup G))
        = P.relIndex (P ⊔ D) * (D.relIndex P * Nat.card (D ⊓ P : Subgroup G)) := by ring
      _ = P.relIndex (P ⊔ D) * Nat.card P := by rw [h4]
      _ = D.relIndex P * Nat.card D := by rw [h1, ← h2]
  exact hdvd.trans (Dvd.intro _ key)

theorem card_projSL_galois {m e : ℕ} (hm : 1 ≤ m) (he : 1 ≤ e) :
    Nat.card (projSL m (GaloisField 2 e)) =
      (2 ^ e) ^ (m * (m - 1) / 2) * (∏ j ∈ Finset.Icc 2 m, ((2 ^ e) ^ j - 1)) /
        Nat.gcd m (2 ^ e - 1) := by
  let φ : CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL m (GaloisField 2 e)) ≃* projSL m (GaloisField 2 e) :=
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL m _))
  rw [← Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hm,
    GaloisField.card 2 e (by omega)]

theorem eq_of_two_pow_mul_eq {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have key : ∀ {a b x y : ℕ}, Odd x → Odd y → 2 ^ a * x = 2 ^ b * y → a ≤ b := by
    intro a b x y hx hy h
    by_contra hab
    push Not at hab
    obtain ⟨k, rfl⟩ : ∃ k, a = b + 1 + k := ⟨a - (b + 1), by omega⟩
    have h2 : 2 ^ b * (2 * 2 ^ k * x) = 2 ^ b * y := by rw [← h]; ring
    have h3 : 2 * 2 ^ k * x = y := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    rw [← h3] at hy
    exact (Nat.not_even_iff_odd.mpr hy) ⟨2 ^ k * x, by ring⟩
  have hab : a = b := le_antisymm (key hx hy h) (key hy hx h.symm)
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem not_nonempty_projSL_two_equiv_three {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ¬ Nonempty (projSL 2 (GaloisField 2 m) ≃* projSL 3 (GaloisField 2 n)) := by
  rintro ⟨e⟩
  have hcard := Nat.card_congr e.toEquiv
  rw [card_projSL_galois (by norm_num) hm, card_projSL_galois (by norm_num) hn] at hcard
  simp only [show Finset.Icc 2 2 = {2} by rfl, show Finset.Icc 2 3 = {2, 3} by rfl,
    Finset.prod_singleton, Finset.prod_pair (show (2 : ℕ) ≠ 3 by norm_num)] at hcard
  norm_num at hcard
  set q := 2 ^ n with hq
  set a := 2 ^ m with ha
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have ha2 : 2 ≤ a := by
    rw [ha]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hodd_a : Odd (a - 1) := by
    have : Even a := by rw [ha]; exact (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 1, by omega⟩
  have hg2 : Nat.gcd 2 (a - 1) = 1 :=
    (Nat.coprime_two_left.mpr hodd_a)
  rw [hg2, Nat.div_one] at hcard
  set g := Nat.gcd 3 (q - 1) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgdvd : g ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    (Nat.gcd_dvd_right _ _).trans (((Nat.sub_one_dvd_pow_sub_one _ 2).mul_right _).mul_left _)
  have hgodd : Odd g := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q - 1)) with h1 | h3
    · rw [hg, h1]; exact odd_one
    · rw [hg, h3]; exact ⟨1, rfl⟩
  have hc : a * (a ^ 2 - 1) * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [hcard, Nat.div_mul_cancel hgdvd]
  have hoddq : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := by
    intro k hk
    have : Even (q ^ k) := by
      rw [hq, ← pow_mul]; exact (Nat.even_pow' (by positivity)).mpr even_two
    obtain ⟨j, hj⟩ := this
    have : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    exact ⟨j - 1, by omega⟩
  have hodda2 : Odd (a ^ 2 - 1) := by
    have : Even (a ^ 2) := by
      rw [ha, ← pow_mul]; exact (Nat.even_pow' (by positivity)).mpr even_two
    obtain ⟨j, hj⟩ := this
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact ⟨j - 1, by omega⟩
  have h2 : 2 ^ m * ((a ^ 2 - 1) * g) = 2 ^ (n * 3) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [pow_mul, ← hq, ← ha, ← mul_assoc, hc]
  obtain ⟨hmn, hodd⟩ := eq_of_two_pow_mul_eq (hodda2.mul hgodd)
    ((hoddq 2 (by norm_num)).mul (hoddq 3 (by norm_num))) h2
  have haq : a = q ^ 3 := by rw [ha, hmn, pow_mul, ← hq]
  rw [haq] at hodd
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hfac : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have : (q ^ 3) ^ 2 = (q ^ 3 - 1) * (q ^ 3 + 1) + 1 := by
      zify [hq3]
      ring
    omega
  rw [hfac] at hodd
  have hpos : 0 < q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have h3 : (q ^ 3 + 1) * g = q ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc (q ^ 3 - 1) * ((q ^ 3 + 1) * g) = (q ^ 3 - 1) * (q ^ 3 + 1) * g := by ring
      _ = (q ^ 2 - 1) * (q ^ 3 - 1) := hodd
      _ = (q ^ 3 - 1) * (q ^ 2 - 1) := by ring
  have h4 : q ^ 2 - 1 < q ^ 3 + 1 := by
    have : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have h5 : q ^ 3 + 1 ≤ (q ^ 3 + 1) * g := Nat.le_mul_of_pos_right _ hgpos
  omega

theorem thompsonOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    Sec3.thompsonOf T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  rw [Sec3.thompsonOf, Ne, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective,
    CFSG.higherElemThompson_zero]
  exact CFSG.RankThree.Coprime.elemThompson_ne_bot hT

omit [Finite G] in
theorem mem_omegaOneCenter_top_iff {S : Type*} [Group S] (z : S) :
    z ∈ CFSG.omegaOneCenter (⊤ : Subgroup S) ↔ z ∈ Subgroup.center S ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, hz⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, Subgroup.mem_top y⟩)
  · rintro ⟨hz, hz2⟩
    refine ⟨⟨⟨z, Subgroup.mem_top z⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩,
      hz2⟩
    exact Subgroup.mem_center_iff.mp hz y

omit [Finite G] in
theorem omegaOneCenter_top_characteristic {S : Type*} [Group S] :
    (CFSG.omegaOneCenter (⊤ : Subgroup S)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro φ _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hz
  rw [mem_omegaOneCenter_top_iff]
  refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, by
    change φ z ^ 2 = 1
    rw [← map_pow, hz.2, map_one]⟩
  obtain ⟨y, rfl⟩ := φ.surjective y
  change φ y * φ z = φ z * φ y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz.1 y]

theorem omegaZOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    Sec3.omegaZOf T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hZ := hT.center_nontrivial
  rw [Sec3.omegaZOf, Ne, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective]
  intro hbot
  have hdvd : 2 ∣ Nat.card (Subgroup.center T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.of_equiv (hT.to_subgroup (Subgroup.center T))
      (MulEquiv.refl _)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center T) :=
      Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr
        ((Subgroup.nontrivial_iff_ne_bot _).mp hZ))
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hmem : (z : T) ∈ CFSG.omegaOneCenter (⊤ : Subgroup T) := by
    rw [mem_omegaOneCenter_top_iff]
    refine ⟨z.2, ?_⟩
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  rw [hbot, Subgroup.mem_bot] at hmem
  have : z = 1 := Subtype.ext hmem
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)


omit [Finite G] in
theorem higherElemThompson_characteristic {S : Type*} [Group S] [Finite S] (j : ℕ) :
    (CFSG.higherElemThompson S j).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro ϕ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ?_
  rw [CFSG.mem_higherElemThompsonFamily_iff] at hA ⊢
  obtain ⟨hAe, hAc⟩ := hA
  have := hAe
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsElementaryAbelian.map ϕ.toMonoidHom,
    by rw [Subgroup.card_map_of_injective ϕ.injective, hAc]⟩

omit [Finite G] in
theorem higherElemThompson_zero_characteristic {S : Type*} [Group S] [Finite S] :
    (CFSG.higherElemThompson S 0).Characteristic :=
  higherElemThompson_characteristic 0

omit [Finite G] in
theorem mem_omegaOneCenter_iff' {S : Type*} [Group S] (J : Subgroup S) (z : S) :
    z ∈ CFSG.omegaOneCenter J ↔ z ∈ J ∧ (∀ y ∈ J, y * z = z * y) ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩), hz⟩
  · rintro ⟨hzJ, hc, hz⟩
    exact ⟨⟨⟨z, hzJ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hc y y.2), rfl⟩, hz⟩

omit [Finite G] in
theorem omegaOneCenter_characteristic_of {S : Type*} [Group S] {J : Subgroup S}
    (hJ : J.Characteristic) : (CFSG.omegaOneCenter J).Characteristic := by
  have hJ' := Subgroup.characteristic_iff_map_le.mp hJ
  rw [Subgroup.characteristic_iff_map_le]
  rintro ϕ _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_iff'] at hz
  rw [mem_omegaOneCenter_iff']
  obtain ⟨hzJ, hzc, hz2⟩ := hz
  refine ⟨hJ' ϕ ⟨z, hzJ, rfl⟩, fun y hy => ?_, ?_⟩
  · have hy' : ϕ.symm y ∈ J := hJ' ϕ.symm ⟨y, hy, rfl⟩
    have h2 := congrArg ϕ (hzc _ hy')
    simpa using h2
  · change ϕ z ^ 2 = 1
    rw [← map_pow, hz2, map_one]

omit [Finite G] in
theorem fourChar_le (S : Subgroup G) (i : Fin 4) : Sec18.fourChar S i ≤ S := by
  fin_cases i <;> exact Subgroup.map_subtype_le _

theorem normalizer_le_normalizer_fourChar (S : Subgroup G) (i : Fin 4) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Sec18.fourChar S i : Set G) := by
  fin_cases i
  · have : (CFSG.omegaOneCenter (⊤ : Subgroup S)).Characteristic :=
      omegaOneCenter_top_characteristic
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  · have : (CFSG.higherElemThompson S 0).Characteristic := higherElemThompson_characteristic 0
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  · have : (CFSG.higherElemThompsonOmega S 1).Characteristic :=
      omegaOneCenter_characteristic_of (higherElemThompson_characteristic 1)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  · have : (CFSG.higherElemThompsonOmega S 2).Characteristic :=
      omegaOneCenter_characteristic_of (higherElemThompson_characteristic 2)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem mem_pCoreOf_of_forall_commute {X : Subgroup G}
    (hF : CFSG.generalizedFitting X = CFSG.pCore 2 X) {x : G} (hxX : x ∈ X)
    (hx : ∀ y ∈ CFSG.Open.pCoreOf 2 X, x * y = y * x) : x ∈ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF
  have hmem : (⟨x, hxX⟩ : X) ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact (hx y ⟨y, hy, rfl⟩).symm
  have h1 := hc hmem
  exact ⟨_, h1, rfl⟩

theorem omegaZOf_le_omegaZOf_pCoreOf {X T : Subgroup G}
    (hF : CFSG.generalizedFitting X = CFSG.pCore 2 X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) :
    Sec3.omegaZOf T ≤ Sec3.omegaZOf (CFSG.Open.pCoreOf 2 X) := by
  have hQT : CFSG.Open.pCoreOf 2 X ≤ T := pCoreOf_le_of_isSylowOf hT
  rintro _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hz
  have hcomm : ∀ y ∈ CFSG.Open.pCoreOf 2 X, (z : G) * y = y * z := by
    intro y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.1 ⟨y, hQT hy⟩)).symm
  have hzQ := mem_pCoreOf_of_forall_commute hF (hT.le z.2) hcomm
  refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff]
  refine ⟨Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcomm y y.2).symm, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hz.2
  simpa using this

theorem isSylowOf_map_conj {p : ℕ} [Fact p.Prime] {T M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) {k : G} (hk : k ∈ M) :
    CFSG.ABGLocalTools.IsSylowOf p (T.map (MulAut.conj k).toMonoidHom) M := by
  apply CFSG.ABGLocalTools.isSylowOf_of_card
  · rintro _ ⟨t, ht, rfl⟩
    exact M.mul_mem (M.mul_mem hk (hT.le ht)) (M.inv_mem hk)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hT.card_eq

omit [Finite G] in
theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {S X : Subgroup G} (hS : IsPGroup p S)
    (hSX : S ≤ X) : ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p T X ∧ S ≤ T := by
  obtain ⟨Q, hQ⟩ := (hS.comap_subtype (K := X)).exists_le_sylow
  refine ⟨(Q : Subgroup X).map X.subtype, ⟨Q, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hSX]
  exact Subgroup.map_mono hQ

theorem isSylowOf_of_le_of_not_dvd {p : ℕ} [Fact p.Prime] {T Y M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T Y) (hYM : Y ≤ M) (hidx : ¬ p ∣ Y.relIndex M) :
    CFSG.ABGLocalTools.IsSylowOf p T M := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT ⊢
  refine ⟨hT.1.trans hYM, hT.2.1, fun h => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T Y M hT.1 hYM] at h
  exact ((Nat.Prime.dvd_mul (Fact.out)).mp h).elim hT.2.2 hidx

theorem not_dvd_relIndex_of_isSylowOf_le {p : ℕ} [Fact p.Prime] {T Y M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hTY : T ≤ Y) (hYM : Y ≤ M) :
    ¬ p ∣ Y.relIndex M := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT
  intro h
  apply hT.2.2
  rw [← Subgroup.relIndex_mul_relIndex T Y M hTY hYM]
  exact h.mul_left _

theorem mem_normalizer_of_map_conj_le {g : G} {Y : Subgroup G}
    (h : Y.map (MulAut.conj g).toMonoidHom ≤ Y) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {c : G} (hc : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := by
  rintro ⟨g, hg⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

end CFSG.RankThree.PartTwo.Sec20
