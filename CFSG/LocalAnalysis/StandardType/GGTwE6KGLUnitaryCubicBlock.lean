module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial Module
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.CanonU3

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {N : ℕ}

theorem selfDual_natDegree_one_of_card_ordTwistedA
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x) (hN : N ≤ 6)
    {a : primaryFactors (x : Module.End K (Fin N → K))} (ha : IsGoodBlock h x a)
    {k : ℕ} (hk : Odd k)
    (hcard : Nat.card (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X]))) =
      CFSG.Open.ordTwistedA 2 (2 ^ k)) :
    dualPoly h.bar (a : K[X]) = a ∧ (a : K[X]).natDegree = 1 := by
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  let SB := specialBlock (idForm h N) x (a : K[X])
  let Comp := unitaryBlockComponent h (x := x) (a : K[X])
  let F := unitaryPreimageBlock h (x := x) (a : K[X])
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h N)) F
  have hπF := subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a
  let ε : ↥F ≃* ↥SB := specialBlockEquiv h H a hq ha
  let πSB : ↥SB →* ↥Comp := πF.comp ε.symm.toMonoidHom
  have hπSB : Function.Surjective πSB := hπF.1.comp ε.symm.surjective
  have hkerSB : πSB.ker ≤ Subgroup.center ↥SB := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hπF.2).trans (Subgroup.comap_center_le_center ε.symm.injective)
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfr : Module.finrank K (primaryComponent (x : Module.End K (Fin N → K)) (a : K[X])) =
      (a : K[X]).natDegree *
        primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) := by
    rw [finrank_primaryComponent]
  have hdm : (a : K[X]).natDegree *
      primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]) ≤ 6 := by
    have hle := Submodule.finrank_le
      (primaryComponent (x : Module.End K (Fin N → K)) (a : K[X]))
    rw [hfr, Module.finrank_fin_fun] at hle
    omega
  obtain ⟨r, hr, hord⟩ := CFSG.Quasithin.Vol2.Ch11.SecB.exists_odd_ordTwistedA_two (k := k)
    (by obtain ⟨j, rfl⟩ := hk; omega)
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  swap
  · exact (false_of_paired_goodBlock (n := k) H ⟨a, ha⟩ hself hN hk hπSB hkerSB hr hord
      hcard).elim
  refine ⟨hself, ?_⟩
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos h.one_le hd
  rcases exists_field_factor_of_selfDual hq H a hself ha with
    ⟨F', hF, hFt, -, hFcard, h4, ⟨eSL2⟩⟩ | ⟨E, hE, hEt, -, hEcard, hm3, hne, ⟨eSU⟩⟩
  · letI : Field F' := hF
    letI : Fintype F' := hFt
    exact (false_of_sl2_centralQuotient (f := f) (d := (a : K[X]).natDegree) (n := k)
      hFcard h4 eSL2 πSB hπSB hkerSB hr hk hord hcard).elim
  letI : Field E := hE
  letI : Fintype E := hEt
  have hperf : commutator ↥(CFSG.Open.StatedSU
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]))
      (2 ^ (f * (a : K[X]).natDegree)) E) = ⊤ :=
    (suFactorFacts_holds E (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]))
      (2 ^ (f * (a : K[X]).natDegree)) hEcard hm3 hne).perfect
  obtain ⟨g, hg, hker⟩ := exists_central_surjection_of_mulEquiv eSU πSB hπSB hkerSB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEnat : Nat.card E = (2 ^ (f * (a : K[X]).natDegree)) ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hEcard
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2)
    (f := f * (a : K[X]).natDegree) hEnat
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := E) (p := 2) (f := f * (a : K[X]).natDegree)
    (n := primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X])) hEnat hm3 hne
  have hZcard : Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]))
      (2 ^ (f * (a : K[X]).natDegree)) E)) =
      Nat.gcd (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]))
        (2 ^ (f * (a : K[X]).natDegree) + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := f * (a : K[X]).natDegree)
      (n := primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X])) hEnat (by omega)
  have hZodd : Odd (Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU
      (primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X]))
      (2 ^ (f * (a : K[X]).natDegree)) E))) := by
    rw [hZcard]
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
    simpa using CFSG.Timmesfeld.Orders.odd_pow_add_one (f := f * (a : K[X]).natDegree)
      (a := 1) (by omega) (by norm_num)
  have hpad := CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_statedSU
    (K := E) (a := f * (a : K[X]).natDegree)
    (d := primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X])) (by omega)
    (by omega) hEnat
  have hp2 := padicValNat_two_of_central_surjective hperf g hg hker hcard hZodd hr hord
  rw [hpad] at hp2
  rcases su_block_solution (f := f) (d := (a : K[X]).natDegree)
    (m := primaryMultiplicity (x : Module.End K (Fin N → K)) (a : K[X])) (n := k)
    h.one_le hd hm3 hdm hk hp2 with ⟨-, hd1, -⟩ | ⟨-, hd1, -⟩ <;> exact hd1

theorem specialBlockEquiv_symm_sesqSUConj_of_model
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x)
    (a : primaryFactors (x : Module.End K (Fin N → K))) (hq : 2 ≤ 2 ^ f)
    (ha : IsGoodBlock h x a) {ℓ' f' : ℕ}
    {hE : UnitaryFieldData ℓ' f' (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K (Fin N → K)) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K (Fin N → K)) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    {Y : primeFormUnitary h (idGram K N)}
    {Φ : ↥(specialBlock (idForm h N) x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)}
    (hΦ : ∀ (s : ↥(specialBlock (idForm h N) x (a : K[X]))) (v : Fin N → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin N → K)) (a : K[X])),
      blockApply (Φ s : blockGL (x : Module.End K (Fin N → K)) (a : K[X])) v hv =
        ((s : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v)
    {g : ↥(sesqUnitaryGroup Hf)}
    (hm : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin N) K) ∈
      unitaryCentralizer (idForm h N) x)
    (hg : ∀ (v : Fin N → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin N → K)) (a : K[X])),
      blockApply g v hv =
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin N) K) : Module.End K (Fin N → K)) v)
    (u : ↥(unitaryPreimageBlock h (x := x) (a : K[X])))
    (hYmem : primeFormConjSU h (idGram K N) Y u ∈
      unitaryPreimageBlock h (x := x) (a : K[X])) :
    (specialBlockEquiv h H a hq ha).symm
      (Φ.symm (sesqSUConj g (Φ (specialBlockEquiv h H a hq ha u)))) =
      (⟨primeFormConjSU h (idGram K N) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
  classical
  let ε := specialBlockEquiv h H a hq ha
  let w : ↥(specialBlock (idForm h N) x (a : K[X])) :=
    ⟨Matrix.GeneralLinearGroup.toLin (Y : GL (Fin N) K) *
      ((ε u : ↥(specialBlock (idForm h N) x (a : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) *
      (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin N) K))⁻¹,
      conj_mem_specialBlock hm (ε u).2⟩
  have hU2 := blockApply_conj_specialBlock (B := idForm h N) (x := x) (a := a)
    (G := sesqSpecialUnitaryGroup Hf) (Φ := Φ) hΦ hm hg (ε u)
  have hU2' : Φ w = sesqSUConj g (Φ (ε u)) := by
    apply Subtype.ext
    rw [sesqSUConj_apply]
    exact hU2
  have hεw : ε (⟨primeFormConjSU h (idGram K N) Y u, hYmem⟩ :
      ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) = w := by
    apply Subtype.ext
    rw [specialBlockEquiv_apply_coe, toLinSU_primeFormConjSU,
      ← specialBlockEquiv_apply_coe h H a hq ha u]
  calc ε.symm (Φ.symm (sesqSUConj g (Φ (ε u))))
      = ε.symm (Φ.symm (Φ w)) := by rw [← hU2']
    _ = ε.symm w := by rw [Φ.symm_apply_apply]
    _ = (⟨primeFormConjSU h (idGram K N) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
      rw [← hεw, ε.symm_apply_apply]

end CFSG.StandardType.SCFourCover

end
