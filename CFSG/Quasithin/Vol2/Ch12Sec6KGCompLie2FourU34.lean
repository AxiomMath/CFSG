module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigCov
public import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open Matrix

section Y


theorem eq_one_of_commute_t0 {t : Y} (ht : t * t = 1) (hc : t * t0 = t0 * t) : t = 1 := by
  have hm : mat t * diagonal ![om, 1, om * om] = diagonal ![om, 1, om * om] * mat t := by
    rw [← t0Mat_eq_diagonal, ← mat_t0, ← mat_mul, ← mat_mul, hc]
  have hd : ∀ i j : Fin 3, i ≠ j → (![om, 1, om * om] : Fin 3 → GF16) i ≠ ![om, 1, om * om] j := by
    decide
  have hoff : ∀ i j, i ≠ j → mat t i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hm i) j
    rw [mul_diagonal, diagonal_mul] at h1
    have h0 : ((![om, 1, om * om] : Fin 3 → GF16) j - ![om, 1, om * om] i) * mat t i j = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (hd j i (Ne.symm hij)))
  have hdiag : mat t = diagonal fun i => mat t i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have h2 : (2 : GF16) = 0 := by decide
  have hsq : ∀ i, mat t i i = 1 := by
    intro i
    have hm2 : mat t * mat t = 1 := by rw [← mat_mul, ht, mat_one]
    rw [hdiag, diagonal_mul_diagonal] at hm2
    have h := congrFun (congrFun hm2 i) i
    rw [diagonal_apply_eq, one_apply_eq] at h
    have h3 : (mat t i i - 1) * (mat t i i - 1) = 0 := by
      linear_combination h + (1 - mat t i i) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  apply mat_injective
  rw [mat_one, hdiag]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, hsq, one_apply_eq]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem mul_ne_mul_Y {a t : Y} (ha : orderOf a = 3) (ht : t * t = 1) (ht1 : t ≠ 1) :
    a * t ≠ t * a := by
  intro hat
  obtain ⟨g, hg⟩ := exists_eq_map_conj (Subgroup.zpowers a) (by rw [Nat.card_zpowers, ha])
  have haT : a ∈ (Subgroup.zpowers t0).map (MulAut.conj g).toMonoidHom :=
    hg ▸ Subgroup.mem_zpowers a
  obtain ⟨x, hx, hxa⟩ := haT
  have hxa' : g * x * g⁻¹ = a := hxa
  have hx3 : orderOf x = 3 := by
    rw [← hxa', show g * x * g⁻¹ = MulAut.conj g x from rfl, MulEquiv.orderOf_eq] at ha
    exact ha
  have hzp : Subgroup.zpowers x = Subgroup.zpowers t0 := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_t0, hx3]
  have hcx : (g⁻¹ * t * g) * x = x * (g⁻¹ * t * g) := by
    have : x = g⁻¹ * a * g := by rw [← hxa']; group
    rw [this]
    calc g⁻¹ * t * g * (g⁻¹ * a * g) = g⁻¹ * (t * a) * g := by group
      _ = g⁻¹ * (a * t) * g := by rw [hat]
      _ = g⁻¹ * a * g * (g⁻¹ * t * g) := by group
  have hct : (g⁻¹ * t * g) * t0 = t0 * (g⁻¹ * t * g) := by
    have hmem : t0 ∈ Subgroup.zpowers x := hzp ▸ Subgroup.mem_zpowers t0
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk]
    exact (Commute.zpow_right hcx k)
  have h1 := eq_one_of_commute_t0 (t := g⁻¹ * t * g)
    (by calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [ht]; group) hct
  apply ht1
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Y

theorem mul_ne_mul_u34 {M : Type} [Group M]
    (hM : StatedClassicalModel M .PSU 3 2 2) {a t : M} (ha : orderOf a = 3) (ht : t * t = 1)
    (ht1 : t ≠ 1) : a * t ≠ t * a := by
  obtain ⟨φ⟩ := nonempty_equiv_Y hM
  intro hat
  refine mul_ne_mul_Y (a := φ a) (t := φ t) (by rwa [MulEquiv.orderOf_eq])
    (by rw [← map_mul, ht, map_one]) (fun h => ht1 (φ.injective (by rw [h, map_one]))) ?_
  rw [← map_mul, ← map_mul, hat]

theorem false_of_autConf_u34
    {M : Type} [Group M] (hM : StatedClassicalModel M .PSU 3 2 2) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨φ⟩ := nonempty_equiv_Y hM
  have : Finite M := Finite.of_equiv _ φ.symm.toEquiv
  have hZ : Subgroup.center M = ⊥ := by
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := id hM
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 2 hF 3 le_rfl
      (by decide)
    have hs : IsSimpleGroup M := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨S, hS, -⟩ := h.sylow
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : 2 ∣ Nat.card M := by
        rw [Nat.card_congr φ.toEquiv, card_Y]
        norm_num
      have h3 : 3 ∣ Nat.card M := by
        rw [Nat.card_congr φ.toEquiv, card_Y]
        norm_num
      obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, ha3⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; norm_num at ht2
      have htt : t * t = 1 := by
        rw [← sq]
        exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ht2])
      refine mul_ne_mul_u34 hM ha3 htt ht1 ?_
      exact Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top t) a
  have hcj := conj_injective_of_center_eq_bot hZ
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.Ch1.evenUnitaryAutInner M 2 le_rfl hM S hS ν hSν
  have hν : ν = MulAut.conj x⁻¹ := MulEquiv.ext fun y => by
    rw [hx, MulAut.conj_apply, inv_inv]
  subst hν
  have hz2 : x⁻¹ * x⁻¹ = 1 := hcj (by rw [map_mul, ← sq, h.sq, map_one])
  have hz1 : x⁻¹ ≠ 1 := fun h1 => h.ne_one (by rw [h1, map_one])
  have hO := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := M) (Or.inr rfl) le_rfl Nat.prime_two (by norm_num) hM).1
  have hO3 : ¬ 3 ∣ Nat.card (Outer M) := fun h3 => by
    have h4 := h3.trans hO
    norm_num [CFSG.RankThree.OuterOrder.determinantParameter] at h4
  obtain ⟨c, hc, hc3⟩ := h.exists_innerPart_three hZ fun α hα =>
    CFSG.AGLEmbedding.mem_inner_of_pow_eq_one_of_not_dvd Nat.prime_three hO3 hα
  have hfix := h.fix_of_mem_innerPart hZ hc
  rw [MulAut.conj_apply] at hfix
  refine mul_ne_mul_u34 hM hc3 hz2 hz1 ?_
  calc c * x⁻¹ = x⁻¹ * c * x⁻¹⁻¹ * x⁻¹ := by rw [hfix]
    _ = x⁻¹ * c := by group

theorem false_of_autConf_su34
    {M : Type} [Group M] (hM : IsSU3 4 M) {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}
    (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hM
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  obtain ⟨hq, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K)
    (p := 2) (f := 2) (n := 3) hK' le_rfl (fun h2 => by simp only [Prod.mk.injEq] at h2; omega)
  have : Group.IsPerfect (StatedSU 3 (2 ^ 2) K) := hq.1
  have hZ : Odd (Nat.card (Subgroup.center (StatedSU 3 (2 ^ 2) K))) :=
    odd_card_of_pow_three fun z => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_three_of_mem_center_su3 hZc z.2, Subgroup.coe_one])
  have hadm : StatedLieAdmissible .PSU 3 2 2 :=
    ⟨Nat.prime_two, by omega, le_rfl, fun h2 => by simp only [Prod.mk.injEq] at h2; omega⟩
  have hmod : StatedClassicalModel (StatedSU 3 (2 ^ 2) K ⧸ Subgroup.center (StatedSU 3 (2 ^ 2) K))
      .PSU 3 2 2 :=
    ⟨hadm, K, inferInstance, inferInstance, hK', ⟨QuotientGroup.quotientMulEquivOfEq hZc⟩⟩
  exact false_of_autConf_u34 hmod ((h.map e).descend le_rfl hZ)

theorem not_psu34
    {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q} (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) : ¬ StatedClassicalModel ↥K .PSU 3 2 2 := fun hK => by
  have := hQ.finite
  exact false_of_autConf_u34 hK h.autConf

theorem not_su34
    {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q} (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) : ¬ IsSLEps3 false 4 ↥K := fun hK => by
  have := hQ.finite
  exact false_of_autConf_su34 hK h.autConf

end CFSG.Quasithin.H13.S126C
