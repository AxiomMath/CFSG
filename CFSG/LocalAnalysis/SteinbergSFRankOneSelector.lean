module

public import CFSG.LocalAnalysis.SteinbergSFRankOneSelectorSmall
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.SteinbergSFLinearUnitaryThreeBaseField

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RankOneSelector

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSUEquiv)
open PrincipalLayers (statedProjEquivProjectiveSL statedProjSLTwoEquiv charP_two_of_card)

theorem card_le_of_card_eq {D : Type*} [Group D] [Finite D] {k m : ℕ} (hm : Odd m)
    (hD : Nat.card D = 2 ^ k * m) {P : Subgroup D} (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ k := by
  refine card_le_of_not_dvd ?_ hP
  rw [hD, pow_succ]
  intro h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)

theorem odd_sq_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd ((2 ^ k) ^ 2 - 1) := by
  have h1 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have he : Even ((2 ^ k) ^ 2) :=
    (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩)
  obtain ⟨r, hr⟩ := he
  refine ⟨r - 1, ?_⟩
  have : 1 ≤ r := by nlinarith
  omega

theorem card_le_of_SL_two {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k)
    (hF : Nat.card F = 2 ^ k) {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ k :=
  card_le_of_card_eq (odd_sq_sub_one hk)
    (by rw [LinearUnitaryThree.card_SL_two, hF]) hP

theorem select_simple (hSel : FixedRootSelector fun D _ => Catalog D)
    {D : Type} [Group D] [Finite D] [IsSimpleGroup D] (hnab : ∃ a b : D, a * b ≠ b * a)
    (hcat : Catalog D) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2 ^ n) {α : MulAut D} (hα : orderOf α = 2) {S : Subgroup D}
    (hSα : S ≤ fixedSubgroup α) (hSn : (S.subgroupOf (fixedSubgroup α)).Normal)
    (κ : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) (hr : FixedRootRankOne α S)
    {V : Subgroup D} (hV : IsPGroup 2 V) (hαV : V.map α.toMonoidHom ≤ V)
    (hCV : V ⊓ fixedSubgroup α ≤ S) :
    ((2 ^ n) ^ 3 ≤ Nat.card V →
        StatedClassicalModel D .PSL 3 2 n ∨ StatedClassicalModel D .PSU 3 2 n) ∧
      ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ x ∈ V, x * x = 1) → Nat.card V = (2 ^ n) ^ 2 →
        StatedClassicalModel D .PSL 2 2 (2 * n)) := by
  have hKn : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_two_of_card hKn
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := LinearUnitaryThree.isSimpleGroup_SL_two (k := K) hK4
  have : IsSimpleGroup S := κ.isSimpleGroup
  have hSnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := LinearUnitaryThree.exists_mul_ne_SL_two (k := K)
    exact ⟨κ.symm a, κ.symm b, fun h => hab (κ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hScard : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr κ.toEquiv, LinearUnitaryThree.card_SL_two, hKn]
  have hclass : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {d p f : ℕ}, d ≠ 0 →
      LieModel D t d p f → StatedClassicalModel D t d p f := by
    intro t d p f hd h
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 hd
  have hsurv := hSel D inferInstance hcat n hn K hK α hα S hSα hSn ⟨κ⟩ hr
  have hn1 : 1 ≤ n := by omega
  have hq : 2 ^ n < (2 ^ n) ^ 2 := by
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    nlinarith
  rcases hsurv with h | h | h | h | h
  ·
    have hm := hclass (by norm_num) h
    refine ⟨fun h3 => ?_, fun _ _ _ => hm⟩
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
    have : CharP F 2 := charP_two_of_card hF
    let η := e.trans (statedProjSLTwoEquiv F)
    have h1 := card_le_of_SL_two (by omega) hF (hV.map η.toMonoidHom)
    rw [Subgroup.card_map_of_injective η.injective] at h1
    have h2 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
    have h3' : 2 ^ (2 * n) < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  ·
    have hm := hclass (by norm_num) h
    refine ⟨fun _ => Or.inr hm, fun hc hs h2 => ?_⟩
    obtain ⟨⟨-, hm1, -⟩, F, _, _, hF, ⟨e⟩⟩ := hm
    have hu : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hm1, by rw [hF, ← pow_mul, mul_comm]⟩
    let η := e.trans (unitaryPSUEquiv hu (n := 3) (by norm_num)).symm
    obtain ⟨-, -, -, -, -, hel, -⟩ :=
      LinearUnitaryThree.unitary_three_fixed_normal_SL_two hKn hn hu η α hα S hSα hSn κ
    have := hel V (isElementaryAbelian_of hc hs)
    omega
  ·
    have hm := hclass (by norm_num) h
    refine ⟨fun _ => Or.inl hm, fun hc hs h2 => ?_⟩
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
    let η := e.trans (statedProjEquivProjectiveSL 3 F)
    obtain ⟨-, -, -, -, -, hel, -⟩ :=
      LinearUnitaryThree.linear_three_fixed_normal_SL_two hKn hn hF η α hα S hSα hSn κ
    exact (hel V (isElementaryAbelian_of hc hs) h2 hαV).elim
  ·
    refine ⟨fun h3 => ?_, fun hc hs h2 => ?_⟩
    · exact (false_of_small_survivor hnab hn hα hSα hSnab hScard hr hV hαV hCV (Or.inl h)
        (Or.inl h3)).elim
    · exact (false_of_small_survivor hnab hn hα hSα hSnab hScard hr hV hαV hCV (Or.inl h)
        (Or.inr ⟨hc, hs, h2⟩)).elim
  ·
    refine ⟨fun h3 => ?_, fun hc hs h2 => ?_⟩
    · exact (false_of_small_survivor hnab hn hα hSα hSnab hScard hr hV hαV hCV (Or.inr h)
        (Or.inl h3)).elim
    · exact (false_of_small_survivor hnab hn hα hSα hSnab hScard hr hV hαV hCV (Or.inr h)
        (Or.inr ⟨hc, hs, h2⟩)).elim

theorem not_two_dvd_relIndex {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (hC : ∀ S : Sylow 2 C, Nat.card S = 2) {a : X} (ha : orderOf a = 2) (haC : a ∈ C) :
    ¬ 2 ∣ (zpowers a).relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (zpowers a).subgroupOf C with hP
  have hcard : Nat.card P = 2 := by
    rw [hP, Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).2 haC)).toEquiv,
      Nat.card_zpowers, ha]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  have hPQ : P = Q := Subgroup.eq_of_le_of_card_ge hQ (by rw [hC Q, hcard])
  rw [Subgroup.relIndex, ← hP, hPQ]
  exact Q.not_dvd_index

theorem rankOne_layer_select (hSel : FixedRootSelector fun D _ => Catalog D)
    {X : Type} [Group X] [Finite X] (hX : CFSG.SectionRank.IsKGroupCat X)
    (hO : CFSG.Open.standardComponentOddCore X = ⊥) {n : ℕ} {A : Subgroup X}
    (hA : StdLinearData X A n) (hsyl : ∀ S : Sylow 2 (centralizer (A : Set X)), Nat.card S = 2)
    {a : X} (ha : orderOf a = 2) (haA : a ∈ centralizer (A : Set X)) {V : Subgroup X}
    (hVD : V ≤ normalClosure (A : Set X)) (hV : IsPGroup 2 V) (haV : a ∈ normalizer (V : Set X))
    (hCV : V ⊓ centralizer ({a} : Set X) ≤ A) :
    CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayerConclusion A a ∧
      ((2 ^ n) ^ 3 ≤ Nat.card V → IsSimpleGroup (normalClosure (A : Set X)) ∧
        (StatedClassicalModel (normalClosure (A : Set X)) .PSL 3 2 n ∨
          StatedClassicalModel (normalClosure (A : Set X)) .PSU 3 2 n)) ∧
      ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ x ∈ V, x * x = 1) → Nat.card V = (2 ^ n) ^ 2 →
        IsSimpleGroup (normalClosure (A : Set X)) →
          StatedClassicalModel (normalClosure (A : Set X)) .PSL 2 2 (2 * n)) := by
  set D := normalClosure (A : Set X) with hDdef
  have hlay := oneOrTwoLayer_of_stdLinearData hO hA ha haA (not_two_dvd_relIndex hsyl ha haA)
  have halt := hlay.2.2.2.2.2.1
  obtain ⟨hCt, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hA.isStandard
      haA ha
  have hn := hA.1
  obtain ⟨-, -, -, k, _, _, hk, ⟨φ⟩⟩ := hA
  have hkn : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
  have : CharP k 2 := charP_two_of_card hkn
  have hAD : A ≤ D := le_normalClosure
  set V' := V.subgroupOf D with hV'
  have hV'card : Nat.card V' = Nat.card V := Nat.card_congr (subgroupOfEquivOfLe hVD).toEquiv
  have hV'2 : IsPGroup 2 V' := hV.of_equiv (subgroupOfEquivOfLe hVD).symm
  have hq3 : 2 ^ (2 * n) < (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨hlay, ?_⟩
  rcases halt with ⟨⟨hDs, hDnab, -, hnt⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, -⟩, -⟩
  ·
    have d := fixedRootDatum_of_normal hAD ha haA hCt hnt
      (fun P hPC hP => card_le_two_of_sylow hsyl hPC hP) hn hk φ
    have hcat : Catalog D :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hX D (MonoidHom.id D)
        Function.surjective_id
    obtain ⟨κ⟩ := d.nonempty_mulEquiv
    have hαV : V'.map (MulAut.conjNormal a : MulAut D).toMonoidHom ≤ V' := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := mem_map.1 hy
      rw [mem_subgroupOf] at hv ⊢
      change ((MulAut.conjNormal a v : D) : X) ∈ V
      rw [MulAut.conjNormal_apply]
      exact (mem_normalizer_iff.1 haV v).1 hv
    have hCV' : V' ⊓ fixedSubgroup (MulAut.conjNormal a : MulAut D) ≤ A.subgroupOf D := by
      intro v hv
      obtain ⟨hvV, hvfix⟩ := mem_inf.1 hv
      rw [mem_subgroupOf] at hvV ⊢
      exact hCV (mem_inf.2 ⟨hvV, mem_centralizer_of_mem_eqLocus hvfix⟩)
    obtain ⟨h1, h2⟩ := select_simple hSel hDnab hcat hn hk d.orderOf_eq d.le_fixed d.normal κ
      d.rankOne hV'2 hαV hCV'
    refine ⟨fun h3 => ⟨hDs, h1 (by rw [hV'card]; exact h3)⟩, fun hc hs h2' _ => ?_⟩
    exact h2 (fun x hx y hy => Subtype.ext (hc x hx y hy)) (fun x hx => Subtype.ext (hs x hx))
      (by rw [hV'card, h2'])
  ·
    have hAcard : Nat.card A = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr φ.toEquiv, LinearUnitaryThree.card_SL_two, hkn]
    have hDcard : Nat.card D = 2 ^ (2 * n) * ((2 ^ n) ^ 2 - 1) ^ 2 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, hAcard]
      ring
    have hodd : Odd (((2 ^ n) ^ 2 - 1) ^ 2) := (odd_sq_sub_one (by omega)).pow
    refine ⟨fun h3 => ?_, fun _ _ _ hDs => ?_⟩
    · have := card_le_of_card_eq hodd hDcard hV'2
      omega
    · exfalso
      have : IsSimpleGroup (A × A) := ψ.symm.isSimpleGroup
      have hA1 : ∃ x : A, x ≠ 1 := by
        have : 1 < Nat.card A := by
          rw [hAcard]
          have h4 : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          have h15 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
            have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
            omega
          nlinarith
        obtain ⟨x, y, hxy⟩ := Finite.one_lt_card_iff_nontrivial.1 this
        by_cases hx : x = 1
        · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
        · exact ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hA1
      set N : Subgroup (A × A) := (⊤ : Subgroup A).prod ⊥ with hN
      have hNn : N.Normal := by
        rw [hN]
        exact Subgroup.prod_normal _ _
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
      · have : ((x, 1) : A × A) ∈ N := Subgroup.mem_prod.2 ⟨mem_top x, one_mem _⟩
        rw [h, mem_bot] at this
        exact hx (congrArg Prod.fst this)
      · have : ((1, x) : A × A) ∈ N := h ▸ mem_top _
        exact hx ((mem_bot).1 (Subgroup.mem_prod.1 this).2)

end RankOneSelector

end CFSG.LocalAnalysis.SymplecticFourStandard
