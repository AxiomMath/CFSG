module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.PartOne.KE.SuzukiPlane
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover

namespace NbrInnerNine

theorem card_lt_of_not_pow_dvd {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (hG : ¬ p ^ k ∣ Nat.card G) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E < p ^ k := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hE)
  have hdvd : p ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card E
  rw [hn]
  by_contra h
  have hkn : k ≤ n := (Nat.pow_le_pow_iff_right hp.one_lt).mp (not_lt.mp h)
  exact hG ((pow_dvd_pow p hkn).trans hdvd)

theorem not_pow_three_dvd_su33 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 6048 := by
  intro h
  have h' : p ^ 3 ∣ 2 ^ 5 * 3 ^ 3 * 7 := by norm_num; exact h
  have hd : p ∣ 2 ^ 5 * 3 ^ 3 * 7 := (dvd_pow_self p (by norm_num)).trans h'
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))
  · have h7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp hd
    subst h7
    norm_num at h

theorem not_pow_three_dvd_tits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 35942400 := by
  intro h
  have h' : p ^ 3 ∣ 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num; exact h
  have hd : p ∣ 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := (dvd_pow_self p (by norm_num)).trans h'
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))
    · have h5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow hd)
      subst h5
      norm_num at h
  · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp hd
    subst h13
    norm_num at h

theorem dvd_two_pow_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) :
    p ∣ (2 ^ m) ^ (p - 1) - 1 := by
  have := Fact.mk hp
  have h2 : ((2 ^ m : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have h1 : 1 ≤ (2 ^ m) ^ (p - 1) := Nat.one_le_pow _ _ (by positivity)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, ZMod.pow_card_sub_one_eq_one h2,
    Nat.cast_one, sub_self]

theorem baseChangeGL_mem_adjointGroup
    {K K' : Type} [Field K] [Field K'] {τ : Tag} (f : K →+* K')
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) : baseChangeGL f g ∈ adjointGroup τ K' := by
  have h1 : baseChangeGL f g ∈ (adjointGroup τ K).map (baseChangeGL f) := ⟨g, hg, rfl⟩
  rw [map_baseChangeGL_adjointGroup] at h1
  refine (Subgroup.closure_le _).mpr ?_ h1
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact Subgroup.subset_closure ⟨i, f c, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨i, f c, Or.inr rfl⟩


section G2

variable {K : Type} [Field K]

theorem card_lt_cube_G2_all [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (adjointGroup .G2 K)} (hE : IsElemAbelian p E) :
    Nat.card E < p ^ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero (p - 1) := ⟨by have := hp.two_le; omega⟩
  let K' := FiniteField.Extension K 2 (p - 1)
  have : CharP K' 2 := charP_of_injective_algebraMap (algebraMap K K').injective 2
  let f : K →+* K' := algebraMap K K'
  have hpK' : p ∣ Nat.card K' - 1 := by
    rw [FiniteField.natCard_extension, hK]
    exact dvd_two_pow_pow_sub_one hp hp2 m
  let ψ : adjointGroup .G2 K →* adjointGroup .G2 K' :=
    ((baseChangeGL f).comp (adjointGroup .G2 K).subtype).codRestrict _
      fun g => baseChangeGL_mem_adjointGroup f g.2
  have hψ : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val hxy))
  have h1 := TableBExc.card_lt_cube_G2 hp hp2 hpK' (TableB.isElemAbelian_map hE ψ)
  rwa [Subgroup.card_map_of_injective hψ] at h1

theorem largeEvenLabelAll_card_lt_G2_all {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : lab.tag = .G2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  have := TableBExc.finite_recipeGroup .G2 K
  have hI := TableBExc.idImage_subset_inn_of_top .G2 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn
    (TableBExc.center_recipeGroup_eq_bot .G2 K) (fun φ hφ => hI (hXI hφ)) hX
  have h1 := card_lt_cube_G2_all hK hp hp2 (E := A.map (TableBExc.recipeEquiv .G2 K).toMonoidHom)
    (TableB.isElemAbelian_map hA _)
  rw [Subgroup.card_map_of_injective (TableBExc.recipeEquiv .G2 K).injective, hAc] at h1
  exact h1

end G2

section Order

open TableBExcSmallRest CFSG.Quasithin.G2U CFSG.Assembly.LowTwoRank

theorem largeEvenLabelAll_card_lt_G2der_ne_three
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (ht : lab.tag = .G2der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  obtain ⟨e⟩ := nonempty_g2der_equiv_su3 K hK
  have : Finite (StatedSU 3 3 F9) := Nat.finite_of_card_ne_zero (by
    rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9]; norm_num)
  have : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanG2)
    (LargeEvenChevH LargeEvenCartanG2 K true)
  refine card_lt_of_subset_inn (center_eq_bot_of_mulEquiv e center_su3_eq_bot)
    (fun A hA => card_lt_of_mulEquiv e (fun E hE => card_lt_of_not_pow_dvd hp ?_ hE) hA)
    (fun φ hφ => ?_) hX
  · rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9]
    exact not_pow_three_dvd_su33 hp hp2 hp3
  · obtain ⟨r, hr⟩ := hI (hXI hφ)
    exact ⟨r, hr⟩

section Tits


theorem card_titsD_dvd : Nat.card CFSG.Sporadic.Schreier.Tits.titsD ∣ 35942400 := by
  rw [← Nat.card_congr (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)).toEquiv]
  exact CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd (Nat.card_zmod 2)

theorem largeEvenLabelAll_card_lt_twF4der_ne_three {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : n = 1 := hlab.2.2
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hm : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have : Finite CFSG.Sporadic.Schreier.Tits.titsD :=
    Nat.finite_of_card_ne_zero fun h => by have := card_titsD_dvd; rw [h] at this; norm_num at this
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) := Finite.of_equiv _ e.symm.toEquiv
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4)
    (LargeEvenTwF4H 0 K)
  refine card_lt_of_subset_inn
    (center_eq_bot_of_mulEquiv e CFSG.Sporadic.Schreier.Tits.titsD_center)
    (fun A hA => card_lt_of_mulEquiv e (fun E hE => card_lt_of_not_pow_dvd hp
      (fun h => not_pow_three_dvd_tits hp hp2 hp3 (h.trans card_titsD_dvd)) hE) hA)
    (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end Tits

theorem not_pow_three_dvd_GL_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 20160 := by
  intro h
  have h' : p ^ 3 ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  have hd : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := (dvd_pow_self p (by norm_num)).trans h'
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))
    · have h5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hd
      subst h5
      norm_num at h
  · have h7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp hd
    subst h7
    norm_num at h

theorem largeEvenLabelAll_card_lt_b2der_ne_three {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (ht : lab.tag = .B2der) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  obtain ⟨K, i1, i2, hK, hQ⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ, fun X hXI hX => TwoThree.card_lt_of_not_dvd hp
    (TwoThree.gsp_subset_normalizer hK) ?_ hX hXI⟩
  rw [TwoThree.card_GL_four hK]
  exact not_pow_three_dvd_GL_four hp hp2 hp3

end Order

section Suzuki

open CFSG.ComponentClassification.UnbalancedCatalog Matrix

theorem minorJ_alt {K : Type} [Field K] [CharP K 2] (v : Fin 4 → K) :
    v ⬝ᵥ (SpChain.minorJ K *ᵥ v) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, SpChain.minorJ_apply]
  linear_combination (v 0 * v 3 + v 1 * v 2) * h2

theorem card_le_sq_of_le_antiSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Subgroup (GL (Fin 4) K)} (hH : H ≤ SpChain.antiSp K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup H} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  classical
  set E' : Subgroup (GL (Fin 4) K) := E.map H.subtype with hE'def
  have hE' : IsElemAbelian p E' := TableB.isElemAbelian_map hE _
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective H.subtype_injective
  have h := CFSG.RankThree.PartOne.LIT.card_le_pow_half_of_form_gl hp
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2) (SpChain.minorJ K)
    SpChain.det_minorJ_ne_zero minorJ_alt E'
    (fun g hg h hh => TableB.IsElemAbelian.comm hE' hg hh) (fun g hg => hE'.2 g hg)
    (fun g hg => by
      obtain ⟨g', -, rfl⟩ := hg
      exact SpChain.mem_antiSp.mp (hH g'.2))
  rw [hcard] at h
  simpa using h

theorem largeEvenLabelAll_card_lt_twB2_all {p : ℕ}
    {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twB2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  subst ht
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hn3 : 3 ≤ n := hlab.2.2.2
  have hk' : n = 2 * k + 1 := hk
  have ha : 1 ≤ (n - 1) / 2 := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  have hZ : Subgroup.center (LargeEvenSzGroup ((n - 1) / 2) K) = ⊥ := by
    rw [largeEvenSzGroup_eq]
    exact CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  let e : LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K) ≃*
      LargeEvenSzGroup ((n - 1) / 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Finite (LargeEvenSzGroup ((n - 1) / 2) K) := Subtype.finite
  have : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hH : LargeEvenSzGroup ((n - 1) / 2) K ≤ SpChain.antiSp K := by
    rw [largeEvenSzGroup_eq]
    exact SpChain.suzukiGroup_le_antiSp hK
  exact TableBExcSmallRest.card_lt_of_subset_inn
    (TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZ)
    (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e (fun E hE =>
      (card_le_sq_of_le_antiSp hH hp hp2 hE).trans_lt
        (Nat.pow_lt_pow_right hp.one_lt (by norm_num))) hA) hXI hX

end Suzuki

section TriD4


theorem largeEvenLabelAll_card_lt_triD4_of {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4)
    (hpq : p = 3 ∨ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hI := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK
  have hbound : ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian p E → Nat.card E < p ^ 3 := by
    intro E hE
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 hn K hK σ hσ hE
    · have hd : p ∣ (2 ^ n) ^ 2 - 1 := hpq.resolve_left hp3
      have hp2 : p ≠ 2 := by
        rintro rfl
        have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
        omega
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        omega
      exact (TableBExcSmallRest.card_le_sq_D4_split hn K hK σ hσ hp hp5 hd hE).trans_lt
        (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  refine TableBExcSmallRest.card_lt_of_subset_inn
    (TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZC)
    (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e hbound hA) (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end TriD4

end NbrInnerNine

end CFSG.StandardType

end
