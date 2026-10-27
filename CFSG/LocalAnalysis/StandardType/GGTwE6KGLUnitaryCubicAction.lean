module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubicBlock

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial Module
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem centerQuotientHom_mem_innAutDerived_of_ordTwistedA {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {A Y : primeFormUnitary h (idGram K n)} {β x : MulAut (primeFormP h (idGram K n))}
    (hAβ : primeFormConjHom h (idGram K n) A = β) (hYx : primeFormConjHom h (idGram K n) Y = x)
    (hβ3 : β ^ 3 = 1) (hx3 : x ^ 3 = 1) (hβx : Commute β x)
    {Kc : Subgroup (primeFormP h (idGram K n))}
    (hKc : CFSG.Open.IsComponentOf Kc (fixSubgroup β)) {k : ℕ} (hk : Odd k)
    (hcard : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) = CFSG.Open.ordTwistedA 2 (2 ^ k))
    (hstab : x ∈ CFSG.GroupActions.subgroupStabAut Kc) :
    centerQuotientHom ↥Kc (CFSG.GroupActions.subgroupStabRestrict Kc ⟨x, hstab⟩) ∈
      innAutDerived (↥Kc ⧸ Subgroup.center ↥Kc) := by
  classical
  subst hAβ hYx
  have hA1 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by rw [map_pow, hβ3]
  obtain ⟨c, -, hA3⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_idGram hn hA1
  rw [Subgroup.coe_pow] at hA3
  obtain ⟨μ, hYA⟩ := eq_scalar_commutator_of_commute_primeFormConjHom (h := h) hn hβx
  have H : UnitaryPrimaryData h.bar (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA3
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  obtain ⟨a, hT⟩ := exists_good_primaryFactor_of_component (h := h) (n := n)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) hq2 A rfl H Kc hKc
  let SB := specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (a.1 : K[X])
  let Comp := unitaryBlockComponent h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X])
  let F := unitaryPreimageBlock h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X])
  have hT' : Kc = Comp := hT
  have hstabComp : primeFormConjHom h (idGram K n) Y ∈
      CFSG.GroupActions.subgroupStabAut Comp := hT' ▸ hstab
  have hcardComp : Nat.card (↥Comp ⧸ Subgroup.center ↥Comp) =
      CFSG.Open.ordTwistedA 2 (2 ^ k) := hT' ▸ hcard
  obtain ⟨hself, hdeg⟩ := selfDual_natDegree_one_of_card_ordTwistedA h H hn6 a.2 hk hcardComp
  have hmonic : (a.1 : K[X]).Monic := monic_of_mem_primaryFactors a.1.2
  obtain ⟨lam, hlam⟩ : ∃ lam : K, (a.1 : K[X]) = Polynomial.X - C lam :=
    ⟨-(a.1 : K[X]).coeff 0, by rw [map_neg, sub_neg_eq_add]; exact hmonic.eq_X_add_C hdeg⟩
  have hself_lam : dualPoly h.bar (Polynomial.X - C lam) = Polynomial.X - C lam := by
    rw [← hlam]
    exact hself
  have ha_mem_lam : Polynomial.X - C lam ∈ primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) := by
    rw [← hlam]
    exact a.1.2
  have hS : SelfDualPrimaryBlock h (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a.1 :=
    selfDualPrimaryBlock H a.1 hself
  have hnorm := map_conj_specialBlock_eq_self (h := h) (H := H) (a := a.1) hq2 a.2 hstabComp
  have hnorm_lam : (specialBlock (idForm h n)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (Polynomial.X - C lam)).map
        (MulAut.conj (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))).toMonoidHom =
      specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
        (Polynomial.X - C lam) := by
    rw [← hlam]
    exact hnorm
  have hQSB : CFSG.IsQuasisimple ↥SB :=
    (specialBlockFacts_of_good H hq2 a.1 a.2).quasisimple a.2.1
  have hne : specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (Polynomial.X - C lam) ≠ ⊥ := by
    rw [← hlam]
    exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hQSB)
  have hscalar : (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin n) μ) :
      Module.End K (Fin n → K)) = μ • 1 := by
    ext v i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def]
  have hYA_end : (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) :
        Module.End K (Fin n → K)) *
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) =
      μ • ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) *
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) : Module.End K (Fin n → K))) := by
    have h1 := congrArg (fun T : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (T : Module.End K (Fin n → K)))
      (congrArg (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)) hYA)
    simp only [Units.val_mul, map_mul] at h1
    rw [hscalar] at h1
    simpa only [smul_mul_assoc, one_mul] using h1
  have hμ : μ = 1 := Units.ext
    (smul_eq_one_of_normalizes_specialBlock (hK := h) H ha_mem_lam hself_lam hYA_end
      hnorm_lam hne)
  have hcomm : Commute (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) :
        Module.End K (Fin n → K))
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) := by
    rw [hμ, one_smul] at hYA_end
    exact hYA_end
  have hm : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) ∈
      unitaryCentralizer (idForm h n)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    mem_unitaryCentralizer.mpr
      ⟨(toLin_mem_sesqUnitaryGroup_iff (h := h) (n := n) (Y : GL (Fin n) K)).mpr Y.2, hcomm⟩
  obtain ⟨hE, Hf, hHf, hHfl, Φ, hΦ, hisoG⟩ :=
    exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary (hK := h) H hself hS
  obtain ⟨g, hg⟩ := hisoG (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K)) hm
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n)) F
  have hπF := subgroupMap_mk'_surjective_ker_le_center (h := h)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a.1
  let ε : ↥F ≃* ↥SB := specialBlockEquiv (h := h) H a.1 hq2 a.2
  let π' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥Comp :=
    πF.comp (ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom)
  have hπ' : Function.Surjective π' :=
    hπF.1.comp (ε.symm.surjective.comp Φ.symm.surjective)
  have hker' : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup Hf) := by
    rw [← MonoidHom.comap_ker]
    refine (Subgroup.comap_mono hπF.2).trans ?_
    have hinj : Function.Injective ⇑(ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom) :=
      fun _ _ hxy => Φ.symm.injective (ε.symm.injective hxy)
    exact Subgroup.comap_center_le_center hinj
  let γ : MulAut ↥Comp :=
    CFSG.GroupActions.subgroupStabRestrict Comp ⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩
  have hγ : ∀ s : ↥(sesqSpecialUnitaryGroup Hf), γ (π' s) = π' (sesqSUConj g s) := by
    intro s
    let u : ↥F := ε.symm (Φ.symm s)
    have hεu : ε u = Φ.symm s := ε.apply_symm_apply _
    have hΦu : Φ (ε u) = s := by simpa only [hεu] using Φ.apply_symm_apply s
    have hcYmem : primeFormConjSU h (idGram K n) Y u ∈ F := by
      show toLinSU h n (primeFormConjSU h (idGram K n) Y u) ∈ SB
      rw [toLinSU_primeFormConjSU]
      have h2 : toLinSU h n u ∈ SB := u.2
      have h4 := Subgroup.mem_map_of_mem (MulAut.conj
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))).toMonoidHom h2
      rwa [hnorm] at h4
    have hL : γ (π' s) = πF (⟨primeFormConjSU h (idGram K n) Y u, hcYmem⟩ : ↥F) := by
      have hπ's : π' s = πF u := rfl
      rw [hπ's]
      apply Subtype.ext
      rw [CFSG.GroupActions.subgroupStabRestrict_apply]
      exact primeFormConjHom_mk h (idGram K n) Y (u : ↥(gramSU h (idGram K n)))
    have hR : π' (sesqSUConj g s) =
        πF (⟨primeFormConjSU h (idGram K n) Y u, hcYmem⟩ : ↥F) := by
      have hπ'c : π' (sesqSUConj g s) = πF (ε.symm (Φ.symm (sesqSUConj g s))) := rfl
      rw [hπ'c]
      have harg : ε.symm (Φ.symm (sesqSUConj g s)) =
          ε.symm (Φ.symm (sesqSUConj g (Φ (ε u)))) :=
        congrArg (fun t => ε.symm (Φ.symm (sesqSUConj g t))) hΦu.symm
      rw [harg, specialBlockEquiv_symm_sesqSUConj_of_model h H a.1 hq2 a.2 hΦ hm hg u hcYmem]
    exact hL.trans hR.symm
  have hSUperf : commutator ↥(sesqSpecialUnitaryGroup Hf) = ⊤ := by
    haveI : Group.IsPerfect ↥SB := hQSB.1
    haveI : Group.IsPerfect ↥(sesqSpecialUnitaryGroup Hf) :=
      @Group.IsPerfect.ofSurjective ↥SB ↥(sesqSpecialUnitaryGroup Hf) _ _
        Φ.toMonoidHom hQSB.1 Φ.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hγ3 : γ ^ 3 = 1 := by
    change ((CFSG.GroupActions.subgroupStabRestrict Comp
      ⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩) ^ 3) = 1
    rw [← map_pow]
    have h1 : (⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩ :
        CFSG.GroupActions.subgroupStabAut Comp) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hx3
    rw [h1, map_one]
  have hγp : centerQuotientHom ↥Comp γ ^ 3 = 1 := by
    rw [← map_pow, hγ3, map_one]
  have hgoal : centerQuotientHom ↥Comp γ ∈ innAutDerived (↥Comp ⧸ Subgroup.center ↥Comp) :=
    centerQuotientHom_mem_innAutDerived_of_sesqSUConj (hE := hE) hHf hHfl hSUperf
      Nat.prime_three (by norm_num) g π' hπ' hker' hγ hγp
  subst hT'
  exact hgoal

end CFSG.StandardType.SCFourCover

end
