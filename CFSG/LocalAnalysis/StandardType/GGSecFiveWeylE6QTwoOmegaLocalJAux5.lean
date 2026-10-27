module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux4

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open Polynomial Module
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_mem_supportedFixedDerived_of_fixedSpace_eq_six
    (hK : Nat.card K = 2)
    {n x' : ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4))}
    (hx3 : orderOf x' = 3) (hn : Commute n x')
    (h6 : Module.finrank K
      (fixedSpace (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 6) :
    ∃ j : ℕ, (n * (x' ^ j)⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived
        (TableBOrth.qPlusForm K 4))) ∈
      (supportedFixedDerived (TableBOrth.qPlusForm K 4)
        (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4)) := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  let Q : QuadraticForm K (Fin 4 ⊕ Fin 4 → K) := TableBOrth.qPlusForm K 4
  let xV : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := x'
  have hQ : Q.polarBilin.Nondegenerate := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  have hdim : finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by simp
  have hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even 4 := by
    constructor
    · intro _; norm_num
    · intro _; simpa [Q, TableBOrth.qPlusForm] using
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 4)
  obtain ⟨hx, hpq, hmem, s, hs, hsm, htype⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.dims_of_orderOf_three (Or.inl hK) hQ hdim hV
      x' hx3
  have hmem' : (X ^ 2 + X + 1 : K[X]) ∈
      primaryFactors (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toLinearMap := by
    simpa [xV] using hmem
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨irreducible_of_mem_primaryFactors hmem'⟩
  have hs3 : s = 3 := by rw [hs] at h6; omega
  have hsm' : s + primaryMultiplicity xV.toLinearMap (X ^ 2 + X + 1) = 4 := by
    simpa [xV] using hsm
  have hm1 : primaryMultiplicity xV.toLinearMap (X ^ 2 + X + 1) = 1 := by omega
  let U : Submodule K (Fin 4 ⊕ Fin 4 → K) := primaryComponent xV.toLinearMap (X ^ 2 + X + 1)
  have hUdim : finrank K U = 2 := by
    rw [show U = primaryComponent xV.toLinearMap (X ^ 2 + X + 1) from rfl,
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.finrank_phi (by simpa [xV] using hmem'), hm1]
  have hothersU : othersSpace xV.toLinearMap (X - 1) = U := by
    rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_eq hx hpq hmem']
  have hX1 : (X - 1 : K[X]) ∈ primaryFactors xV.toLinearMap := by
    by_contra hX
    have hbot := fixedSpace_eq_bot_of_not_mem hX
    rw [hbot, finrank_bot] at h6
    omega
  have hnEnd : Commute (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) xV := by
    have h := congrArg (fun e : ↥(CFSG.RankThree.Classical2.orthDerived Q) =>
      (e : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) hn.eq
    apply LinearEquiv.ext
    intro v
    have h2 := congrArg (fun e : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => e v) h
    simpa [xV, LinearEquiv.mul_apply] using h2
  have hnEnd' : Commute (n : Module.End K (Fin 4 ⊕ Fin 4 → K))
      (xV : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
    rw [Commute]
    apply LinearMap.ext
    intro w
    exact LinearEquiv.congr_fun hnEnd.eq w
  have hyU : ∀ u ∈ U, xV u ∈ U := fun u hu =>
    apply_mem_primaryComponent (Commute.refl xV.toLinearMap) hu
  have hbU : ∀ u ∈ U, (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) u ∈ U :=
    fun u hu => apply_mem_primaryComponent hnEnd' hu
  have hxV3 : xV ^ 3 = 1 := by
    have h := pow_orderOf_eq_one xV
    rwa [show orderOf xV = 3 from by simpa [xV] using hx3] at h
  have hneg : ∀ z : (Fin 4 ⊕ Fin 4 → K), -z = z :=
    CFSG.ClassicalGroups.Orthogonal.neg_eq_self_of_two_eq_zero (by simpa using CharP.cast_eq_zero K 2)
  have hy2 : ∀ u ∈ U, xV (xV u) = xV u + u := by
    intro u hu
    have hu' : aeval (xV : Module.End K (Fin 4 ⊕ Fin 4 → K)) (X ^ 2 + X + 1 : K[X]) u = 0 := by
      rw [← mem_primaryComponent]
      exact hu
    have h : xV (xV u) + xV u + u = 0 := by
      simpa [Polynomial.aeval_X, pow_two, map_add, map_mul] using hu'
    have h' : xV (xV u) + (xV u + u) = 0 := by
      simpa [add_assoc] using h
    have h2 := eq_neg_of_add_eq_zero_left h'
    rw [hneg] at h2
    exact h2
  have hpow := exists_pow_of_commute_of_finrank_two (K := K)
    (V := Fin 4 ⊕ Fin 4 → K) hK (y := xV)
    (b := (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)))
    hxV3 hnEnd hyU hbU hy2 hUdim
  obtain ⟨j, hj⟩ := hpow
  have hxpowU : ∀ k : ℕ, ∀ u ∈ U, (xV ^ k) u ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
        intro u hu
        rw [pow_succ, LinearEquiv.mul_apply]
        exact ih (xV u) (hyU u hu)
  have hxj3 : (xV ^ j) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hxV3, one_pow]
  have hxjinv : (xV ^ j)⁻¹ = (xV ^ j) ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    calc (xV ^ j) * (xV ^ j) ^ 2 = (xV ^ j) ^ 3 := by group
      _ = 1 := hxj3
  have hinvU : ∀ u ∈ U, ((xV ^ j)⁻¹) u ∈ U := by
    intro u hu
    rw [hxjinv]
    simpa [pow_mul, mul_comm] using hxpowU (2 * j) u hu
  have hgU : ∀ u ∈ U,
      (((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹) u = u) := by
    intro u hu
    rw [LinearEquiv.mul_apply, hj ((xV ^ j)⁻¹ u) (hinvU u hu)]
    simp
  have hgcomm : Commute ((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *
      (xV ^ j)⁻¹) xV := by
    have h2 : Commute ((xV ^ j)⁻¹) xV := by
      have h := (Commute.refl xV).pow_left j
      exact h.inv_left
    exact hnEnd.mul_left h2
  have hgmem : (((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹)) ∈
      isometryCentralizer Q xV := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have hnO : (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup n.2
      have hxO : xV ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hx.mem
      have hxjO : (xV ^ j) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.pow_mem _ hxO j
      have hgO : ((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.mul_mem _ hnO (Subgroup.inv_mem _ hxjO)
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
    · exact LinearEquiv.congr_fun hgcomm.eq v
  have hgsupp : ((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹) ∈
      supportedBlock Q xV (X - 1) := by
    refine mem_supportedBlock.mpr ⟨hgmem, fun v hv => ?_⟩
    rw [hothersU] at hv
    exact hgU v hv
  have hgorth : ((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹) ∈
      CFSG.RankThree.Classical2.orthDerived Q := by
    have hxorth : xV ∈ CFSG.RankThree.Classical2.orthDerived Q := x'.2
    exact Subgroup.mul_mem _ n.2 (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxorth j))
  have hD := hx.dicksonHom_eq_restrict_of_mem_supportedBlock (p := 3) (by norm_num) hQ hX1 hgsupp
  have h1 := dicksonHom_eq_one_of_mem_orthDerived hQ hgorth
  have hD1 : dicksonHom (Q.comp (fixedSpace xV).subtype) hx.polarBilin_fixed_nondegenerate
      ⟨isometryRestrictFixed Q xV ⟨_, supportedBlock_le_isometryCentralizer (X - 1) hgsupp⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
    rw [← hD, h1]
  have hts : ∀ W : Submodule K ↥(fixedSpace xV), finrank K W = 3 →
      ∃ w ∈ W, (Q.comp (fixedSpace xV).subtype) w ≠ 0 := by
    intro W hW
    by_contra h
    push Not at h
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace xV).subtype) := by
      refine ⟨W, ?_, fun w hw => h w hw⟩
      rw [hW, h6]
    have htype3 := htype (by omega)
    have hev : Even s := htype3.mp hplus
    rw [hs3] at hev
    rcases hev with ⟨k, hk⟩
    omega
  have hW : (omegaGroup (Q.comp (fixedSpace xV).subtype)
      hx.polarBilin_fixed_nondegenerate) ≤
      CFSG.RankThree.Classical2.orthDerived (Q.comp (fixedSpace xV).subtype) :=
    CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six
      hx.polarBilin_fixed_nondegenerate h6 hts
  let xO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xV).subtype)) :=
    ⟨isometryRestrictFixed Q xV ⟨_, supportedBlock_le_isometryCentralizer (X - 1) hgsupp⟩,
      isometryRestrictFixed_mem_orthogonalGroup _⟩
  have homega : (xO : ↥(fixedSpace xV) ≃ₗ[K] ↥(fixedSpace xV)) ∈
      omegaGroup (Q.comp (fixedSpace xV).subtype)
        hx.polarBilin_fixed_nondegenerate := by
    have hmemker : xO ∈ (dicksonHom (Q.comp (fixedSpace xV).subtype)
        hx.polarBilin_fixed_nondegenerate).ker := by
      rw [MonoidHom.mem_ker]
      simpa [xO] using hD1
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker] at hmemker
    exact Subgroup.mem_subgroupOf.mp hmemker
  have hfixed : restrictFixed Q xV ⟨_, hgsupp⟩ ∈
      CFSG.RankThree.Classical2.orthDerived (Q.comp (fixedSpace xV).subtype) := by
    have h := hW homega
    simpa [restrictFixed, isometryRestrictFixed, xO] using h
  refine ⟨j, Subgroup.mem_subgroupOf.mpr ?_⟩
  exact mem_supportedFixedDerived.mpr
    ⟨by simpa [xV] using hgsupp, by simpa [xV] using hfixed⟩

end CFSG.StandardType.E6QTwo

end
