module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz
public import CFSG.Quasithin.Vol2.Ch5Sec1L34J2Aut
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.RankThree.ThinCatalog.FiveModels
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertTitsBridge
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsDSSz

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms

section SzOrder

theorem le_card_sz {a : ℕ} (ha : 1 ≤ a) :
    29120 ≤ Nat.card ↥(Sz a) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  have hq : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have h1 : 64 ≤ q ^ 2 := by nlinarith
  have h2 : 7 ≤ q - 1 := by omega
  calc 29120 = 64 * (64 + 1) * 7 := by norm_num
    _ ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) h2

theorem le_card_sz_two {a : ℕ} (ha : 2 ≤ a) :
    32537600 ≤ Nat.card ↥(Sz a) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  have hq : 32 ≤ 2 ^ (2 * a + 1) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have h1 : 1024 ≤ q ^ 2 := by nlinarith
  have h2 : 31 ≤ q - 1 := by omega
  calc 32537600 = 1024 * (1024 + 1) * 31 := by norm_num
    _ ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) h2

theorem card_sz_one : Nat.card ↥(Sz 1) = 29120 := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  norm_num

theorem five_dvd_card_sz (a : ℕ) : 5 ∣ Nat.card ↥(Sz a) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
  apply Dvd.dvd.mul_right
  apply Dvd.dvd.mul_left
  have : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [this]
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem oddPart_dvd_of_card_sz_dvd (a : ℕ) {k m : ℕ}
    (h : Nat.card ↥(Sz a) ∣ 2 ^ k * m) :
    ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) ∣ m := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz] at h
  have h1 : ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) ∣ 2 ^ k * m := by
    rw [mul_assoc] at h
    exact (Dvd.intro_left _ rfl).trans h
  have hodd : Odd (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) := by
    have he : Even (2 ^ (2 * a + 1)) := (Nat.even_pow' (by omega)).mpr even_two
    have h2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine Nat.odd_mul.mpr ⟨?_, ?_⟩
    · have he2 : Even ((2 ^ (2 * a + 1)) ^ 2) := (Nat.even_pow' (by norm_num)).mpr he
      exact he2.add_one
    · obtain ⟨r, hr⟩ := he
      exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact hcop.dvd_of_dvd_mul_left h1

end SzOrder

section Section

theorem card_sz_dvd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite Y] {M : Subgroup Y}
    (e : X ≃* ↥M) {a : ℕ} (L : Subgroup X) (f : oTwoQuot ↥L ≃* ↥(Sz a)) :
    Nat.card ↥(Sz a) ∣ Nat.card Y := by
  let L' : Subgroup Y := (L.map e.toMonoidHom).map M.subtype
  have e1 : ↥L ≃* ↥L' := (L.equivMapOfInjective _ e.injective).trans
    ((L.map e.toMonoidHom).equivMapOfInjective _ M.subtype_injective)
  have f' : oTwoQuot ↥L' ≃* ↥(Sz a) := (oTwoQuotCongr e1.symm).trans f
  rw [← Nat.card_congr f'.toEquiv]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L')

theorem exists_vertex_mulEquiv {α : RankTwoAmalgam.{0}} {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup α P ∨ IsParabolicAmalgamOfGroup α P) :
    ∃ (Y : Type) (_ : Group Y), P Y ∧ ∃ M₁ M₂ : Subgroup Y,
      Nonempty (α.G1 ≃* ↥M₁) ∧ Nonempty (α.G2 ≃* ↥M₂) := by
  rcases h with ⟨Y, _, hP, T, M₁, M₂, -, ⟨e⟩⟩ | ⟨Y, _, hP, T, M₁, M₂, -, ⟨e₁⟩, -, ⟨e₂⟩⟩
  · exact ⟨Y, inferInstance, hP, M₁, M₂, ⟨e.φ1⟩, ⟨e.φ2⟩⟩
  · exact ⟨Y, inferInstance, hP, M₁, M₂, ⟨e₁⟩, ⟨e₂⟩⟩

theorem noSz_of_amalgam {α : RankTwoAmalgam.{0}} {P : ∀ (Y : Type) [Group Y], Prop} {a : ℕ}
    (h : IsAmalgamOfGroup α P ∨ IsParabolicAmalgamOfGroup α P)
    (hP : ∀ (Y : Type) [Group Y], P Y → Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y) :
    (∀ L : Subgroup α.G1, IsEmpty (oTwoQuot ↥L ≃* ↥(Sz a))) ∧
      ∀ L : Subgroup α.G2, IsEmpty (oTwoQuot ↥L ≃* ↥(Sz a)) := by
  obtain ⟨Y, _, hPY, M₁, M₂, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_vertex_mulEquiv h
  obtain ⟨hfin, hndvd⟩ := hP Y hPY
  exact ⟨fun L => ⟨fun f => hndvd (card_sz_dvd_of_mulEquiv e₁ L f)⟩,
    fun L => ⟨fun f => hndvd (card_sz_dvd_of_mulEquiv e₂ L f)⟩⟩

theorem not_card_sz_dvd_of_lt {a N : ℕ} (ha : 1 ≤ a)
    (hN : 0 < N) (h : N < 29120) : ¬ Nat.card ↥(Sz a) ∣ N := fun hd =>
  absurd (Nat.le_of_dvd hN hd) (by have := le_card_sz ha; omega)

theorem not_card_sz_dvd_of_five {a N : ℕ} (h : ¬ 5 ∣ N) :
    ¬ Nat.card ↥(Sz a) ∣ N := fun hd => h ((five_dvd_card_sz a).trans hd)

theorem not_card_sz_dvd_of_lt_two {a N : ℕ} (ha : 1 ≤ a)
    (hN : 0 < N) (h : N < 32537600) (h8 : ¬ 29120 ∣ N) : ¬ Nat.card ↥(Sz a) ∣ N := by
  intro hd
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have ha1 : a = 1 := by omega
    subst ha1
    rw [card_sz_one] at hd
    exact h8 hd
  · exact absurd (Nat.le_of_dvd hN hd) (by have := le_card_sz_two ha2; omega)

end Section

section Aut

theorem finite_mulAut_of_finite (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective

theorem finite_psu3_three_one : Finite ↥(CFSG.Open.PSU3 3 1) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 3 (2 * 1))) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 3 (2 * 1)) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem card_mulAut_eq {X : Type*} [Group X] [Finite X] :
    ∃ i : ℕ, i ∣ Nat.card X ∧ Nat.card (MulAut X) = i * Nat.card (Outer X) := by
  refine ⟨Nat.card (inner X), ?_, ?_⟩
  · exact Subgroup.card_range_dvd (MulAut.conj : X →* MulAut X)
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X), mul_comm]

end Aut


section Twelve

theorem noSz_psl32
    {a : ℕ} (ha : 1 ≤ a) {Y : Type} [Group Y]
    (hY : IsLieOverTwo .PSL 3 1 Y) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  have hc := (CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hY).2
  have h168 : Nat.card Y = 168 := by
    rw [hc]
    decide
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt ha (by omega) (by omega)⟩

theorem noSz_psu42
    {a : ℕ} (ha : 1 ≤ a) {Y : Type} [Group Y]
    (hY : IsLieOverTwo .PSU 4 1 Y) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  have hc := (CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hY).2
  have h1 : Nat.card Y = 25920 := by
    rw [hc]
    decide
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt ha (by omega) (by omega)⟩

theorem noSz_d42
    {a : ℕ} {Y : Type} [Group Y]
    (hY : IsLieOverTwo .trialityD4 0 1 Y) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  have hc := (CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hY).2
  have h1 : Nat.card Y = 211341312 := by
    rw [hc]
    decide
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_five (by rw [h1]; decide)⟩

theorem noSz_sp42 {a : ℕ} (ha : 1 ≤ a) {Y : Type} [Group Y]
    (hY : IsSp4Over 1 Y) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h, -⟩
  · have h720 : Nat.card Y = 720 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
        show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    exact ⟨Nat.finite_of_card_ne_zero (by omega),
      not_card_sz_dvd_of_lt ha (by omega) (by omega)⟩
  · exact absurd h (by norm_num)

theorem noSz_g22
    {a : ℕ} (ha : 1 ≤ a)
    {Y : Type} [Group Y] (hY : IsG2Over 1 Y) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h, -⟩
  · have hle := CFSG.Quasithin.card_mulAut_psu3_le
    have := finite_psu3_three_one
    have hfin : Finite (MulAut (CFSG.Open.PSU3 3 1)) := finite_mulAut_of_finite _
    have hpos : 0 < Nat.card (MulAut (CFSG.Open.PSU3 3 1)) := Nat.card_pos
    rw [← Nat.card_congr e.toEquiv] at hle hpos
    exact ⟨Finite.of_equiv _ e.symm.toEquiv, not_card_sz_dvd_of_lt ha hpos (by omega)⟩
  · exact absurd h (by norm_num)

theorem noSz_u33 {a : ℕ} (ha : 1 ≤ a) {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.PSU3 3 1)) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have := finite_psu3_three_one
  have hle := CFSG.Quasithin.card_psu3_three_one_le
  have hpos : 0 < Nat.card ↥(CFSG.Open.PSU3 3 1) := Nat.card_pos
  rw [← Nat.card_congr e.toEquiv] at hle hpos
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, not_card_sz_dvd_of_lt ha hpos (by omega)⟩

theorem noSz_tits {a : ℕ}
    (ha : 1 ≤ a) {Y : Type} [Group Y] (hY : Nonempty (Y ≃* CFSG.Open.quasithinTits)) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have h1 : Nat.card Y = 17971200 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.card_quasithinTits]
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt_two ha (by omega) (by omega) (by rw [h1]; decide)⟩

theorem noSz_f42
    {a : ℕ} (ha : 1 ≤ a)
    {Y : Type} [Group Y]
    (hY : IsTwistedF4Over 1 Y) : Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h, -⟩
  · have : Finite CFSG.Open.quasithinTits := Nat.finite_of_card_ne_zero
      (by rw [CFSG.Quasithin.card_quasithinTits]; norm_num)
    have hfin : Finite (MulAut CFSG.Open.quasithinTits) := finite_mulAut_of_finite _
    refine ⟨Finite.of_equiv _ e.symm.toEquiv, fun hd => ?_⟩
    rw [Nat.card_congr e.toEquiv] at hd
    obtain ⟨i, hi, hcard⟩ := card_mulAut_eq (X := CFSG.Open.quasithinTits)
    have h2 : IsPGroup 2 (Outer CFSG.Open.quasithinTits) :=
      (CFSG.Sporadic.Schreier.Tits.AT_Tits_derived_group_Schreier).1.of_equiv
        (equivalence CFSG.Quasithin.quasithinTitsEquivD).symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfo : Finite (Outer CFSG.Open.quasithinTits) := inferInstance
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    rw [CFSG.Quasithin.card_quasithinTits] at hi
    have hdiv : i * 2 ^ k ∣ 2 ^ (11 + k) * 8775 := by
      have e2 : 2 ^ (11 + k) * 8775 = 17971200 * 2 ^ k := by ring
      rw [e2]
      exact Nat.mul_dvd_mul_right hi _
    have hd' : Nat.card ↥(Sz a) ∣ 2 ^ (11 + k) * 8775 := by
      rw [hcard, hk] at hd
      exact hd.trans hdiv
    have hodd := oddPart_dvd_of_card_sz_dvd a hd'
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have ha1 : a = 1 := by omega
      subst ha1
      revert hodd
      decide
    · have hq : 32 ≤ 2 ^ (2 * a + 1) := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle := Nat.le_of_dvd (by norm_num) hodd
      generalize 2 ^ (2 * a + 1) = q at hq hle
      have h1 : 1024 ≤ q ^ 2 := by nlinarith
      have h3 : 1025 * 31 ≤ (q ^ 2 + 1) * (q - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  · exact absurd h (by norm_num)


theorem noSz_j2 {a : ℕ}
    (ha : 1 ≤ a) {Y : Type} [Group Y] (hY : Nonempty (Y ≃* CFSG.Open.quasithinJ2)) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have h1 : Nat.card Y = 604800 := by
    rw [Nat.card_congr (e.trans CFSG.Quasithin.quasithinJ2MulEquivNative).toEquiv,
      CFSG.Sporadic.J2.card_J2]
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt_two ha (by omega) (by omega) (by rw [h1]; decide)⟩

theorem noSz_autJ2
    {a : ℕ} (ha : 1 ≤ a) {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* MulAut CFSG.Open.quasithinJ2)) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have h1 : Nat.card Y = 1209600 := by
    rw [Nat.card_congr e.toEquiv, card_mulAut_quasithinJ2]
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt_two ha (by omega) (by omega) (by rw [h1]; decide)⟩

theorem noSz_m12 {a : ℕ}
    (ha : 1 ≤ a) {Y : Type} [Group Y] (hY : Nonempty (Y ≃* CFSG.Open.quasithinM12)) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have h1 : Nat.card Y = 95040 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.quasithinM12_eq_native,
      CFSG.Sporadic.Mathieu.card_M12]
  exact ⟨Nat.finite_of_card_ne_zero (by omega),
    not_card_sz_dvd_of_lt_two ha (by omega) (by omega) (by rw [h1]; decide)⟩

theorem noSz_autM12
    {a : ℕ} (ha : 1 ≤ a)
    {Y : Type} [Group Y] (hY : Nonempty (Y ≃* MulAut CFSG.Open.quasithinM12)) :
    Finite Y ∧ ¬ Nat.card ↥(Sz a) ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have hX : Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 = 95040 :=
    CFSG.Sporadic.Mathieu.card_M12
  have : Finite ↥CFSG.Blueprint.NativeSporadic.M12 :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hfin : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M12) := finite_mulAut_of_finite _
  have e' : Y ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12 := e
  obtain ⟨i, hi, hcard⟩ := card_mulAut_eq (X := ↥CFSG.Blueprint.NativeSporadic.M12)
  have hout := (CFSG.Sporadic.Schreier.at_m12_schreier).1
  have hopos : 0 < Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M12) := Nat.card_pos
  rw [hX] at hi
  have hipos : 0 < i := Nat.pos_of_dvd_of_pos hi (by norm_num)
  have hile : i ≤ 95040 := Nat.le_of_dvd (by norm_num) hi
  have hY1 : Nat.card Y = i * Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M12) := by
    rw [Nat.card_congr e'.toEquiv, hcard]
  refine ⟨Finite.of_equiv _ e'.symm.toEquiv, ?_⟩
  rw [hY1]
  refine not_card_sz_dvd_of_lt_two ha (Nat.mul_pos hipos hopos)
    (by nlinarith) (fun h8 => ?_)
  have h7 : 7 ∣ i * Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M12) :=
    (show 7 ∣ 29120 by norm_num).trans h8
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · have := h.trans hi
    norm_num at this
  · have := Nat.le_of_dvd hopos h
    omega

end Twelve


section Fact

theorem sz_simple_facts {a : ℕ} (ha : 1 ≤ a) :
    IsSimpleGroup ↥(Sz a) ∧ (∃ x y : ↥(Sz a), x * y ≠ y * x) ∧ ¬ 3 ∣ Nat.card ↥(Sz a) := by
  have hSM : CFSG.Blueprint.SuzukiModel ↥(Sz a) 2 (2 * a + 1) :=
    ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
      GaloisField.card 2 (2 * a + 1) (by omega),
      CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a⟩
  have hs := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 (2 * a + 1) hSM).2
  have h3 := CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hSM
  refine ⟨hs, ?_, h3⟩
  by_contra hall
  push Not at hall
  have hge := le_card_sz ha
  have : Finite ↥(Sz a) := Nat.finite_of_card_ne_zero (by omega)
  let _ : CommGroup ↥(Sz a) := { (inferInstance : Group ↥(Sz a)) with mul_comm := hall }
  have hp : (Nat.card ↥(Sz a)).Prime := IsSimpleGroup.prime_card
  have h2 : 2 ∣ Nat.card ↥(Sz a) := by
    rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
    apply Dvd.dvd.mul_right
    apply Dvd.dvd.mul_right
    exact Dvd.dvd.pow (dvd_pow_self 2 (by omega)) (by norm_num)
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

theorem noSz_of_section {a : ℕ} (ha : 1 ≤ a) {X : Type*}
    [Group X] {L : Subgroup X}
    (h : ∀ (N : Subgroup ↥L) [N.Normal], IsSimpleGroup (↥L ⧸ N) →
      (∃ x y : ↥L ⧸ N, x * y ≠ y * x) → 3 ∣ Nat.card (↥L ⧸ N)) :
    IsEmpty (oTwoQuot ↥L ≃* ↥(Sz a)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨hs, ⟨x, y, hxy⟩, h3⟩ := sz_simple_facts ha
  have hsL : IsSimpleGroup (oTwoQuot ↥L) := e.isSimpleGroup
  have hnab : ∃ x y : oTwoQuot ↥L, x * y ≠ y * x := by
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    have := congrArg e hc
    simpa using this
  have h3L := h (CFSG.Open.pCore 2 ↥L) hsL hnab
  exact h3 (by rw [← Nat.card_congr e.toEquiv]; exact h3L)

theorem f112SecondNoSzFact_of
    (hU4 : U4ExtTwoVertexFact) : F112SecondNoSzFact := by
  intro α halt a ha
  rcases halt with h | h | h | h | h | h | h | h | h | h | h | h | ⟨f, hf, hU⟩
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_psl32 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_sp42 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_g22 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_d42 hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_f42 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_tits ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_psu42 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_u33 ha hY
  · exact noSz_of_amalgam (Or.inr h) fun Y _ hY => noSz_j2 ha hY
  · exact noSz_of_amalgam (Or.inr h) fun Y _ hY => noSz_autJ2 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_m12 ha hY
  · exact noSz_of_amalgam (Or.inl h) fun Y _ hY => noSz_autM12 ha hY
  · obtain ⟨h1, h2⟩ := hU4 f α hf hU
    exact ⟨fun L => noSz_of_section ha (h1 L), fun L => noSz_of_section ha (h2 L)⟩

end Fact

end CFSG.Quasithin.H13
