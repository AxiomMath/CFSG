module

public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.Q1327T.Item2L3U3
public import CFSG.RankThree.PartOne.Q1327T.Item5Alt
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.RankThree.PartOne.KF.ClsTits
public import CFSG.RankThree.PartOne.KFR4.At
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.GorensteinWalter CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
  CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.Q1327T
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Assembly.LowTwoRank TauCeti

theorem row8OddItem_zero : Row8OddItem 0 := by
  classical
  intro Q _ _ p g Ē hp11 _ hX h
  exfalso
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, x, K, hc1, hcp, hKc, hKmodel, hxK, hxo, hEel, hEcard⟩ := h.exists_T
  obtain ⟨q, hq2, -, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e : (Q ⧸ Subgroup.center Q) ≃* PSL2 (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  by_cases hpr : p = q.p
  · subst hpr
    have hec1 : e c ≠ 1 := fun h1 => hc1 (e.injective (by rw [h1, map_one]))
    have hecp : e c ^ q.p = 1 := by rw [← map_pow, hcp, map_one]
    have hPg : IsPGroup q.p K := by
      intro k
      refine ⟨1, ?_⟩
      have hcomm : e c * e (k : Q ⧸ Subgroup.center Q) = e (k : Q ⧸ Subgroup.center Q) * e c := by
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subgroup.mem_centralizer_singleton_iff.1 (hKc k.2)).symm
      have := K133.psl2_centralizer_pow (F := GaloisField q.p q.exponent) hp2 (e c)
        (e (k : Q ⧸ Subgroup.center Q)) hec1 hecp hcomm
      apply Subtype.ext
      apply e.injective
      simpa [← map_pow] using this
    have : Group.IsNilpotent K := hPg.isNilpotent
    have hsol : Group.IsSolvable K := inferInstance
    obtain ⟨hKs, a, b, hab⟩ := simple_nonab_of_model hKmodel
    have := hKs
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)
  · have hne : ((p : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p] at h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 h0).symm
    have : NeZero ((p : ℕ) : GaloisField q.p q.exponent) := ⟨hne⟩
    have hA : IsElementaryAbelian p ↥((Subgroup.zpowers c ⊔ Subgroup.zpowers x).map
        e.toMonoidHom) := by
      have := hEel
      exact IsElementaryAbelian.map e.toMonoidHom
    have hcard := K133.psl2_elemAb_card_le hp hp2 _ hA
    rw [Subgroup.card_map_of_injective e.injective, hEcard] at hcard
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem row8OddItem_one : Row8OddItem 1 := by
  classical
  intro Q _ _ p g Ē hp11 _ hX h
  exfalso
  obtain ⟨c, x, K, hc1, hcp, hKc, hKmodel, hxK, hxo, hEel, hEcard⟩ := h.exists_T
  obtain ⟨q, hq2, he3, ⟨hv, ⟨e0⟩⟩ | ⟨hv, ⟨e0⟩⟩⟩ := hX
  · have : Fact q.p.Prime := ⟨q.prime_p⟩
    let Kf := GaloisField q.p q.exponent
    have e1 : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSL 3 Kf) :=
      (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 Kf)
    have h2 : (2 : Kf) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff Kf q.p 2).1 (by simpa using h0)
      exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 this)
    exact no_L2_centralizer_of_equiv h2 (StatedSL 3 Kf) e1 hc1 hKc hKmodel
  · have : Fact q.p.Prime := ⟨q.prime_p⟩
    have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
    have h2 : (2 : GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)) ≠ 0 := by
      intro h0
      have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p := by
        simp [ValidLieTypeIndex.characteristic]
      have := (CharP.cast_eq_zero_iff _ (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
        2).1 (by simpa using h0)
      rw [hℓ] at this
      exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 this)
    exact no_L2_centralizer_of_equiv h2 _ e1 hc1 hKc hKmodel

theorem not_sq_dvd_of_primeFactors_eleven {N : ℕ} (hN : N ≠ 0) (S : Finset ℕ)
    (hS : N.primeFactors = S) (h2 : ∀ p ∈ S, 11 ≤ p → ¬ p ^ 2 ∣ N) {p : ℕ} (hp : p.Prime)
    (h11 : 11 ≤ p) : ¬ p ^ 2 ∣ N := by
  intro h
  have hpN : p ∣ N := (dvd_pow_self p (by norm_num)).trans h
  have : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpN, hN⟩
  rw [hS] at this
  exact h2 p this h11 h

theorem Row8OddAt.of_no_plane {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∀ p : ℕ, 11 ≤ p → p.Prime →
      ∀ A : Subgroup X, IsElementaryAbelian p A → Nat.card A = p ^ 2 → False) :
    Row8OddAt P := by
  intro Q _ _ p g Ē hp11 _ hX h
  exfalso
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  exact hP _ hX p hp11 h.prime A hAel hAcard

theorem Row8OddAt.of_card {P : (X : Type) → [Group X] → Prop} {N : ℕ} (S : Finset ℕ)
    (hN : N ≠ 0) (hS : N.primeFactors = S) (h2 : ∀ p ∈ S, 11 ≤ p → ¬ p ^ 2 ∣ N)
    (hcard : ∀ (X : Type) [Group X] [Finite X], P X → Nat.card X = N) : Row8OddAt P :=
  Row8OddAt.of_no_plane fun X _ _ hX _ hp11 hp A _ hAcard =>
    not_sq_dvd_of_primeFactors_eleven hN S hS h2 hp hp11
      (hcard X hX ▸ hAcard ▸ Subgroup.card_subgroup_dvd_card A)

theorem row8OddItem_four : Row8OddItem 4 :=
  Row8OddAt.of_no_plane fun X _ _ hX p hp11 hp A _ hAcard => by
    obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := hX
    have h1 : p ^ 2 ∣ Nat.card X := hAcard ▸ Subgroup.card_subgroup_dvd_card A
    rw [Nat.card_congr e.toEquiv] at h1
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have hdvd : p ^ 2 ∣ n.factorial :=
      h1.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega)))
    have hple : p ≤ n := (hp.dvd_factorial).1 (dvd_trans (dvd_pow_self p two_ne_zero) hdvd)
    have := prime_sq_dvd_factorial n (by omega) p (by omega) hn5 (by omega) hp hdvd
    omega

theorem row8OddAt_leaf7_zero : Row8OddAt (K133.leaf7 0) :=
  Row8OddAt.of_no_plane fun X _ _ hX p hp11 hp A hAel hAcard => by
    obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
    have hp2 : p ≠ 2 := by omega
    have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A (r := 1) hv e0
    rw [hq2] at hmod
    obtain ⟨-, F, _, _, _, -, ⟨e⟩⟩ := S15K.exists_mulEquiv_sl2_of_model hmod
    have hrk := KFR4.pRank_le_one_of_equiv_sl2 hp hp2 e
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt A hAel hAcard
    omega

theorem row8OddAt_leaf7_one :
    Row8OddAt (K133.leaf7 1) :=
  Row8OddAt.of_no_plane fun X _ _ hX p hp11 hp A hAel hAcard => by
    obtain ⟨m, hiso⟩ := hX
    have hp2 : p ≠ 2 := by omega
    have : Fact p.Prime := ⟨hp⟩
    have hmodel := CTP.suzukiModel_of_isoLie m hiso
    obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
    have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
    have e' : X ≃* CFSG.Open.GLASzGroup a F :=
      e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
    have hsyl :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
        a ha hF' e'
    have hodd : Odd (Nat.card A) := by
      rw [hAcard]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hc : IsCyclic A :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic A
        hodd hAel.toIsMulCommutative hsyl
    have hle := card_le_of_isCyclic_elemAb hp A hAel
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem row8OddAt_leaf9_zero : Row8OddAt (K133.leaf9 0) :=
  Row8OddAt.of_card (N := 9999360) {2, 3, 5, 7, 31} (by norm_num) (by decide +kernel)
    (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl]
    decide +kernel

theorem row8OddAt_leaf9_one : Row8OddAt (K133.leaf9 1) :=
  Row8OddAt.of_card (N := 20158709760) {2, 3, 5, 7, 31} (by norm_num) (by decide +kernel)
    (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl]
    decide +kernel

theorem row8OddAt_leaf9_two : Row8OddAt (K133.leaf9 2) :=
  Row8OddAt.of_card (N := 163849992929280) {2, 3, 5, 7, 31, 127} (by norm_num)
    (by decide +kernel) (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl]
    decide +kernel

theorem row8OddAt_leaf9_three : Row8OddAt (K133.leaf9 3) :=
  Row8OddAt.of_card (N := 9196830720) {2, 3, 5, 7, 11} (by norm_num) (by decide +kernel)
    (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl]
    decide +kernel

theorem row8OddAt_leaf9_four : Row8OddAt (K133.leaf9 4) :=
  Row8OddAt.of_card (N := 47377612800) {2, 3, 5, 7, 17} (by norm_num) (by decide +kernel)
    (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2
      (by omega) e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.1 rfl]
    decide +kernel

theorem row8OddAt_leaf9_five : Row8OddAt (K133.leaf9 5) :=
  Row8OddAt.of_card (N := 174182400) {2, 3, 5, 7} (by norm_num) (by decide +kernel)
    (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hq2 e0
    rw [hq2, hq1] at hmod
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.2.1 rfl]
    decide +kernel

section F4

theorem row8OddAt_leaf9_six : Row8OddAt (K133.leaf9 6) :=
  Row8OddAt.of_card (N := 3311126603366400) {2, 3, 5, 7, 13, 17} (by norm_num)
    (by decide +kernel) (by decide +kernel) fun X _ _ hX => by
    obtain ⟨q, hq2, hq1, hiso⟩ := hX
    obtain ⟨Y, _, _, hY2, ⟨θ⟩⟩ := SEITZX.exists_adjointF4_two_model hq2 hq1 hiso
    have hY3 := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := Y)
    rw [hY2] at hY3
    rw [Nat.card_congr θ.toEquiv]
    exact hY3.trans (by norm_num [CFSG.Open.ordF4])

end F4

section Tits

open CFSG.Sporadic.Schreier.Tits

theorem row8OddAt_leaf7_ten : Row8OddAt (K133.leaf7 10) :=
  Row8OddAt.of_no_plane fun X _ _ hX p hp11 hp A _ hAcard => by
    have hX' := hX
    obtain ⟨eS⟩ := titsModelEquiv X 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hX')
    have hdvd : p ^ 2 ∣ 17971200 := by
      rw [← card_titsD, ← Nat.card_congr eS.toEquiv, ← hAcard]
      exact Subgroup.card_subgroup_dvd_card A
    exact KFU.not_sq_dvd_card_titsD hp (by omega) hdvd

end Tits

section Ree

theorem row8OddItem_two : Row8OddItem 2 := by
  intro Q _ _ p g Ē hp11 _ hX h
  exfalso
  have hp := h.prime
  have h5 := h.five_le
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.quasisimple.2.1
  have hZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ :=
    center_eq_bot_of_simple_nonabelian h.quasisimple.2.2
  obtain ⟨k, hk⟩ := CTP.card_mulAut_dvd_smallRee (ℓ := 3) rfl (CTP.reeTitsModel_reeG2 1 hX)
  have hinj : Function.Injective (MulAut.conj : (Q ⧸ Subgroup.center Q) →* _) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hx z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * x = x * z * x⁻¹ * x * 1 := by rw [h1]; group
        _ = x * z := by group
    rwa [hZ, Subgroup.mem_bot] at hxc
  have h1 : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card (MulAut (Q ⧸ Subgroup.center Q)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : p ^ 2 ∣ Nat.card (Q ⧸ Subgroup.center Q) := hAcard ▸ Subgroup.card_subgroup_dvd_card A
  exact CTP.not_sq_dvd_smallRee_aut hp h5 (h2.trans (h1.trans hk))

end Ree

end CFSG.RankThree.PartOne.K133B
