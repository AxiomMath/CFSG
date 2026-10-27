module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus
public import Mathlib.Algebra.Group.Submonoid.BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.StandardType.USixTwo.MainProof

open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.StandardType.USixTwo.TorHyperplanes
open CFSG.StandardType.USixTwo.TorConj
open CFSG.StandardType.USixTwo.OrbitProof

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

@[expose] def threeAVec : Fin 6 → ZMod 3 := ![1, 2, 0, 0, 0, 0]

theorem sum_threeAVec : ∑ i, threeAVec i = 0 := by
  norm_num [threeAVec, Fin.sum_univ_six]
  decide

@[expose] def threeAArg : ↥sumZeroSubgroup :=
  ⟨Multiplicative.ofAdd threeAVec, sum_threeAVec⟩

theorem coeffVec_threeAArg :
    coeffVec hK hω (threeAArg : Multiplicative (Fin 6 → ZMod 3)) =
      ![unitOmega hω, unitOmega hω ^ 2, 1, 1, 1, 1] := by
  funext i
  fin_cases i <;> simp [threeAArg, threeAVec, coeffVec, coeffEquiv_one]
  · have h2 : Multiplicative.ofAdd (2 : ZMod 3) =
        Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd (1 : ZMod 3) := by
      rw [← ofAdd_add]
      norm_num
    rw [h2, map_mul, coeffEquiv_one, pow_two]

theorem torLift_threeAArg_eq :
    torLift hK hω threeAArg = threeASU hω := by
  apply Subtype.ext
  change (TauCeti.diagGL (coeffVec hK hω (threeAArg : Multiplicative (Fin 6 → ZMod 3))) :
      GL (Fin 6) K) =
    ((threeASU hω : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K)
  ext i j
  rw [TauCeti.diagGL_coe, coe_threeASU, coeffVec_threeAArg]
  fin_cases i <;> fin_cases j <;> simp [threeAMatrix, unitOmega]

theorem torHom_threeAArg :
    torHom hK hω threeAArg = threeA hω := by
  change LargeEvenProjMk _ (torLift hK hω threeAArg) =
    LargeEvenProjMk _ (threeASU hω)
  rw [torLift_threeAArg_eq]

theorem fS_threeAArg_eq_one_iff (u : T4) :
    fS u threeAArg = 1 ↔ u.1 = u.2.1 := by
  rw [fS_apply]
  change Multiplicative.ofAdd (∑ i, expLift u i * threeAVec i) = 1 ↔ u.1 = u.2.1
  have hsum : ∑ i, expLift u i * threeAVec i = u.1 - u.2.1 := by
    obtain ⟨u0, u1, u2, u3⟩ := u
    fin_cases u0 <;> fin_cases u1 <;>
      simp [threeAVec, expLift, Fin.sum_univ_six] <;> decide
  rw [hsum]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one] at h'
    exact sub_eq_zero.mp h'
  · intro h
    rw [sub_eq_zero.mpr h, ofAdd_zero]

@[expose] def deltaS (i : Fin 5) : ↥sumZeroSubgroup :=
  ⟨Multiplicative.ofAdd (delta i), delta_mem i⟩

@[expose] def deltaB (i : Fin 5) : Fin 6 → ZMod 3 :=
  fun j => if j = i.castSucc then 1 else if j = 5 then -1 else 0

theorem sum_deltaB (i : Fin 5) : ∑ j, deltaB i j = 0 := by
  fin_cases i <;> simp [deltaB, Fin.sum_univ_six] <;> decide

@[expose] def deltaSB (i : Fin 5) : ↥sumZeroSubgroup :=
  ⟨Multiplicative.ofAdd (deltaB i), by
    rw [mem_sumZeroSubgroup_iff]
    exact sum_deltaB i⟩

theorem deltaB_eq_delta (i : Fin 5) : deltaB i = delta i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [deltaB, delta, delta0, delta1, delta2, delta3, delta4] <;> rfl

theorem deltaSB_eq_deltaS (i : Fin 5) : deltaSB i = deltaS i := by
  apply Subtype.ext
  simp [deltaSB, deltaS, deltaB_eq_delta]

theorem sum_smul_delta {y : Fin 6 → ZMod 3} (hy : ∑ i, y i = 0) :
    y = ∑ i : Fin 5, y i.castSucc • deltaB i := by
  funext j
  fin_cases j
  · simp [deltaB, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  · simp [deltaB, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  · simp [deltaB, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  · simp [deltaB, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  · simp [deltaB, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  · rw [Fin.sum_univ_six] at hy
    have hy' : y 5 = - (y 0 + y 1 + y 2 + y 3 + y 4) := by
      linear_combination hy
    simp [deltaB, Fin.sum_univ_five, hy', Pi.smul_apply, smul_eq_mul]
    abel

theorem eq_prod_deltaS_amb (x : ↥sumZeroSubgroup) :
    (x : Multiplicative (Fin 6 → ZMod 3)) =
      ∏ i : Fin 5, (deltaSB i : Multiplicative (Fin 6 → ZMod 3)) ^
        (x.1.toAdd i.castSucc).val := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp only [toAdd_pow, toAdd_ofAdd, deltaSB, Subgroup.coe_mk]
  have hsum : (∑ i : Fin 5, (x.1.toAdd i.castSucc).val • deltaB i) =
      ∑ i : Fin 5, (x.1.toAdd i.castSucc) • deltaB i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [hsum]
  exact sum_smul_delta (mem_sumZeroSubgroup_iff.mp x.2)

theorem eq_prod_deltaS (x : ↥sumZeroSubgroup) :
    x = (∏ i : Fin 5, deltaSB i ^ (x.1.toAdd i.castSucc).val : ↥sumZeroSubgroup) := by
  apply Subtype.ext
  simpa [Subgroup.coe_prod, Subgroup.coe_pow] using eq_prod_deltaS_amb x

theorem closure_deltaS_eq_top :
    Submonoid.closure (Set.range deltaS) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [eq_prod_deltaS x]
  simp_rw [deltaSB_eq_deltaS]
  simpa using Submonoid.prod_mem (Submonoid.closure (Set.range deltaS))
    (fun i _ => Submonoid.pow_mem (Submonoid.closure (Set.range deltaS))
      (Submonoid.subset_closure (Set.mem_range_self i))
      ((x.1.toAdd i.castSucc).val))

theorem torHom_mem_Hfun_iff (u : T4) (x : ↥sumZeroSubgroup) :
    torHom hK hω x ∈ Hfun hK hω u ↔ fS u x = 1 := by
  rw [Hfun, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqeq⟩
    rw [MonoidHom.mem_ker] at hq
    have hq' : q = QuotientGroup.mk x := by
      apply (torChart hK hω).injective
      change (torChart hK hω).toMonoidHom q =
        (torChart hK hω).toMonoidHom (QuotientGroup.mk x)
      rw [hqeq]
      exact (torChart_mk hK hω x).symm
    subst hq'
    rw [fQ, QuotientGroup.lift_mk] at hq
    exact hq
  · intro hx
    refine ⟨QuotientGroup.mk x, ?_, torChart_mk hK hω x⟩
    rw [MonoidHom.mem_ker, fQ, QuotientGroup.lift_mk]
    exact hx

noncomputable def threeAElt (hω : ω ^ 2 + ω + 1 = 0) : ↥(torU K) :=
  ⟨threeA hω, threeA_mem_torU hω⟩

theorem threeA_mem_Hfun_iff {u : T4} :
    threeAElt hω ∈ Hfun hK hω u ↔ u.1 = u.2.1 := by
  rw [show threeAElt hω = torHom hK hω threeAArg from by
    apply Subtype.ext
    exact (torHom_threeAArg hK hω).symm]
  rw [torHom_mem_Hfun_iff hK hω u threeAArg, fS_threeAArg_eq_one_iff u]

theorem Hfun_zero : Hfun hK hω 0 = ⊤ := by
  rw [Hfun]
  have hexp0 : expLift (0 : T4) = 0 := by
    funext i
    fin_cases i <;> simp [expLift] <;> decide
  have hfS0 : fS 0 = 1 := by
    ext x
    rw [fS_apply, hexp0]
    simp
  have hfQ : fQ hK hω 0 = 1 := by
    ext x
    have hx : fS 0 x = 1 := by rw [hfS0]; rfl
    simpa [fQ] using hx
  rw [hfQ]
  simp

theorem fQ_mk_delta (u : T4) (i : Fin 5) :
    fQ hK hω u (QuotientGroup.mk (deltaS i)) =
      Multiplicative.ofAdd (expLift u i.castSucc) := by
  rw [fQ, QuotientGroup.lift_mk, fS_apply]
  congr 1
  fin_cases i <;>
    simp [deltaS, delta, expLift_delta0, expLift_delta1, expLift_delta2,
      expLift_delta3, expLift_delta4]

theorem fS_delta (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (u : T4) (i : Fin 5) :
    fS u (deltaS i) = Multiplicative.ofAdd (expLift u i.castSucc) := by
  simpa [fQ, QuotientGroup.lift_mk] using fQ_mk_delta hK hω u i

theorem exists_Hfun_eq_of_index_eq_three (H : Subgroup ↥(torU K)) (hH : H.index = 3) :
    ∃ u : T4, u ≠ 0 ∧ H = Hfun hK hω u := by
  classical
  let Q := ↥(torU K) ⧸ H
  have hQcard : Nat.card Q = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hH
  let e : Q ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq (p := 3) hQcard (by simp)
  let χq : (↥sumZeroSubgroup ⧸ (torHom hK hω).ker) →* Multiplicative (ZMod 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' H).comp (torChart hK hω).toMonoidHom)
  let χ : ↥sumZeroSubgroup →* Multiplicative (ZMod 3) :=
    χq.comp (QuotientGroup.mk' (torHom hK hω).ker)
  have hχker : (torHom hK hω).ker ≤ χ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxq : (QuotientGroup.mk x : ↥sumZeroSubgroup ⧸ (torHom hK hω).ker) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hx
    simp [χ, hxq]
  let u : T4 :=
    (Multiplicative.toAdd (χ (deltaS 0)),
     Multiplicative.toAdd (χ (deltaS 1)),
     Multiplicative.toAdd (χ (deltaS 2)),
     Multiplicative.toAdd (χ (deltaS 3)))
  have h0 : χ (deltaS 0) = Multiplicative.ofAdd (expLift u 0) := by
    simp [u, expLift]
  have h1 : χ (deltaS 1) = Multiplicative.ofAdd (expLift u 1) := by
    simp [u, expLift]
  have h2 : χ (deltaS 2) = Multiplicative.ofAdd (expLift u 2) := by
    simp [u, expLift]
  have h3 : χ (deltaS 3) = Multiplicative.ofAdd (expLift u 3) := by
    simp [u, expLift]
  let oneVec : Fin 6 → ZMod 3 := fun _ => 1
  have hOneSum : ∑ i, oneVec i = 0 := by
    simp [oneVec, Fin.sum_univ_six]
    decide
  let oneS : ↥sumZeroSubgroup := ⟨Multiplicative.ofAdd oneVec, hOneSum⟩
  have hOneKer : oneS ∈ (torHom hK hω).ker := by
    rw [MonoidHom.mem_ker]
    rw [CFSG.StandardType.USixTwo.TorHomKernel.torHom_eq_one_iff]
    refine ⟨1, fun i => ?_⟩
    simp [oneS, oneVec]
  have hprod : deltaS 0 * deltaS 1 * deltaS 2 * deltaS 3 * deltaS 4 = oneS := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;>
      simp [deltaS, delta, delta0, delta1, delta2, delta3, delta4, oneS, oneVec,
        Fin.sum_univ_six] <;> decide
  have hχone : χ oneS = 1 := MonoidHom.mem_ker.mp (hχker hOneKer)
  have hχprod :
      χ (deltaS 0) * χ (deltaS 1) * χ (deltaS 2) * χ (deltaS 3) * χ (deltaS 4) = 1 := by
    have h := congrArg χ hprod
    simp only [map_mul] at h
    simpa [hχone] using h
  have h4 : χ (deltaS 4) =
      (χ (deltaS 0) * χ (deltaS 1) * χ (deltaS 2) * χ (deltaS 3))⁻¹ :=
    eq_inv_of_mul_eq_one_right hχprod
  have h4' : χ (deltaS 4) = Multiplicative.ofAdd (expLift u 4) := by
    rw [h4, h0, h1, h2, h3]
    rw [← ofAdd_add, ← ofAdd_add, ← ofAdd_add, ← ofAdd_neg]
    congr 1
  have hχdelta : ∀ i : Fin 5, χ (deltaS i) = Multiplicative.ofAdd (expLift u i.castSucc) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4'
  have hχ_eq : ∀ x : ↥sumZeroSubgroup, χ x = fS u x := by
    have heq : χ.eqLocusM (fS u) = ⊤ := by
      rw [eq_top_iff, ← closure_deltaS_eq_top]
      exact Submonoid.closure_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact MonoidHom.mem_eqLocusM.mpr (by rw [hχdelta i, fS_delta hK hω u i]))
    intro x
    have hx : x ∈ χ.eqLocusM (fS u) := by
      rw [heq]
      exact Submonoid.mem_top x
    exact MonoidHom.mem_eqLocusM.mp hx
  have hH_eq : H = Hfun hK hω u := by
    ext a
    obtain ⟨x, rfl⟩ := CFSG.StandardType.USixTwo.TorHomKernel.torHom_surjective hK hω a
    rw [torHom_mem_Hfun_iff, ← hχ_eq x]
    have hχx : χ x = e (QuotientGroup.mk' H (torHom hK hω x)) := by
      change e (QuotientGroup.mk' H (torChart hK hω (QuotientGroup.mk x))) =
        e (QuotientGroup.mk' H (torHom hK hω x))
      rw [torChart_mk hK hω]
    rw [hχx]
    constructor
    · intro hx
      have h1' : QuotientGroup.mk' H (torHom hK hω x) = 1 := by
        change (QuotientGroup.mk (torHom hK hω x) : ↥(torU K) ⧸ H) = 1
        rw [QuotientGroup.eq_one_iff]
        exact hx
      rw [h1', map_one]
    · intro hx
      have h1' : QuotientGroup.mk' H (torHom hK hω x) = 1 := by
        apply e.injective
        simpa using hx
      change (QuotientGroup.mk (torHom hK hω x) : ↥(torU K) ⧸ H) = 1 at h1'
      rwa [QuotientGroup.eq_one_iff] at h1'
  refine ⟨u, ?_, hH_eq⟩
  intro hu0
  have htop : H = ⊤ := by rw [hH_eq, hu0, Hfun_zero]
  have hindex : H.index = 1 := by rw [htop, Subgroup.index_top]
  omega

theorem lineCanon_eq_smul {u : T4} (hu : u ≠ 0) :
    ∃ c : ZMod 3, c ≠ 0 ∧ lineCanon u = smulT4 c u := by
  by_cases h1 : u.1 ≠ 0
  · exact ⟨u.1⁻¹, inv_ne_zero h1, by simp [lineCanon, h1]⟩
  · by_cases h2 : u.2.1 ≠ 0
    · exact ⟨u.2.1⁻¹, inv_ne_zero h2, by simp [lineCanon, h1, h2]⟩
    · by_cases h3 : u.2.2.1 ≠ 0
      · exact ⟨u.2.2.1⁻¹, inv_ne_zero h3, by simp [lineCanon, h1, h2, h3]⟩
      · by_cases h4 : u.2.2.2 ≠ 0
        · exact ⟨u.2.2.2⁻¹, inv_ne_zero h4, by simp [lineCanon, h1, h2, h3, h4]⟩
        · exfalso
          apply hu
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp_all

theorem Hfun_lineCanon (u : T4) : Hfun hK hω (lineCanon u) = Hfun hK hω u := by
  by_cases hu : u = 0
  · subst hu
    rw [show lineCanon 0 = 0 by decide +kernel]
  · obtain ⟨c, hc, hcu⟩ := lineCanon_eq_smul hu
    rw [hcu, Hfun_smul hK hω hc]

theorem lineCanon_eq_self_of_mem_lineReps :
    ∀ u : T4, u ∈ lineReps → lineCanon u = u := by
  decide +kernel

theorem lineCanon_smul_eq :
    ∀ (c : ZMod 3) (u : T4), c ≠ 0 → lineCanon (smulT4 c u) = lineCanon u := by
  decide +kernel

theorem zero_not_mem_lineReps : (0 : T4) ∉ lineReps := by
  decide +kernel

theorem ne_zero_of_mem_lineReps {u : T4} (hu : u ∈ lineReps) : u ≠ 0 :=
  fun h0 => zero_not_mem_lineReps (h0 ▸ hu)

theorem Hfun_injOn_lineReps {u u' : T4} (hu : u ∈ lineReps) (hu' : u' ∈ lineReps)
    (h : Hfun hK hω u = Hfun hK hω u') : u = u' := by
  classical
  have hu0 : u ≠ 0 := ne_zero_of_mem_lineReps hu
  have hu0' : u' ≠ 0 := ne_zero_of_mem_lineReps hu'
  have hker : (fQ hK hω u).ker = (fQ hK hω u').ker := by
    apply Subgroup.map_injective (f := (torChart hK hω).toMonoidHom)
      (fun a b hab => (torChart hK hω).injective hab)
    simpa [Hfun] using h
  let A := ↥sumZeroSubgroup ⧸ (torHom hK hω).ker
  let f : A →* Multiplicative (ZMod 3) := fQ hK hω u
  let g : A →* Multiplicative (ZMod 3) := fQ hK hω u'
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    exact fQ_range_eq_top hK hω hu0
  have hg : Function.Surjective g := by
    rw [← MonoidHom.range_eq_top]
    exact fQ_range_eq_top hK hω hu0'
  let φ : A ⧸ f.ker ≃* Multiplicative (ZMod 3) :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  let hl : A ⧸ f.ker →* Multiplicative (ZMod 3) :=
    QuotientGroup.lift f.ker g (by rw [hker])
  have hl_surj : Function.Surjective hl := by
    intro y
    obtain ⟨x, hx⟩ := hg y
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [show hl (QuotientGroup.mk x) = g x by
      dsimp only [hl]
      rw [QuotientGroup.lift_mk]]
    exact hx
  have hl_inj : Function.Injective hl := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    have hgx : g x = 1 := by
      rw [show hl (QuotientGroup.mk x) = g x by
        dsimp only [hl]
        rw [QuotientGroup.lift_mk]] at hq
      exact hq
    have hxker : x ∈ g.ker := by simpa [MonoidHom.mem_ker] using hgx
    rw [← hker] at hxker
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hxker
  let hlE : A ⧸ f.ker ≃* Multiplicative (ZMod 3) :=
    MulEquiv.ofBijective hl ⟨hl_inj, hl_surj⟩
  let e : Multiplicative (ZMod 3) ≃* Multiplicative (ZMod 3) := φ.symm.trans hlE
  have hφ : ∀ x : A, φ (QuotientGroup.mk x) = f x := by
    intro x
    change QuotientGroup.kerLift f (QuotientGroup.mk x) = f x
    rw [QuotientGroup.kerLift_mk]
  have he : ∀ x : A, g x = e (f x) := by
    intro x
    have h1 : hlE (QuotientGroup.mk x) = g x := by
      change hl (QuotientGroup.mk x) = g x
      dsimp only [hl]
      rw [QuotientGroup.lift_mk]
    have h2 : φ.symm (f x) = QuotientGroup.mk x := by
      rw [← hφ x, MulEquiv.symm_apply_apply]
    calc
      g x = hlE (QuotientGroup.mk x) := h1.symm
      _ = e (f x) := by
        rw [show e (f x) = hlE (φ.symm (f x)) from rfl, h2]
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic e.toMonoidHom
  have hcoord : ∀ i : Fin 5, expLift u' i.castSucc = (m : ZMod 3) * expLift u i.castSucc := by
    intro i
    have hx := he (QuotientGroup.mk (deltaS i))
    have hgi : g (QuotientGroup.mk (deltaS i)) = Multiplicative.ofAdd (expLift u' i.castSucc) := by
      change fQ hK hω u' (QuotientGroup.mk (deltaS i)) = _
      exact fQ_mk_delta hK hω u' i
    have hfi : f (QuotientGroup.mk (deltaS i)) = Multiplicative.ofAdd (expLift u i.castSucc) := by
      change fQ hK hω u (QuotientGroup.mk (deltaS i)) = _
      exact fQ_mk_delta hK hω u i
    rw [hgi, hfi, show e (Multiplicative.ofAdd (expLift u i.castSucc)) =
      (Multiplicative.ofAdd (expLift u i.castSucc)) ^ m from hm _] at hx
    have hx' := congrArg Multiplicative.toAdd hx
    simp only [toAdd_ofAdd] at hx'
    rw [toAdd_zpow] at hx'
    rw [zsmul_eq_mul] at hx'
    exact hx'
  have hsmul : u' = smulT4 (m : ZMod 3) u := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · have := hcoord 0; simpa [expLift, smulT4] using this
    · have := hcoord 1; simpa [expLift, smulT4] using this
    · have := hcoord 2; simpa [expLift, smulT4] using this
    · have := hcoord 3; simpa [expLift, smulT4] using this
  have hk : (m : ZMod 3) ≠ 0 := by
    intro hk0
    apply hu0'
    rw [hsmul, hk0]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [smulT4]
  have hu_can : lineCanon u = u := lineCanon_eq_self_of_mem_lineReps u hu
  have hu'_can : lineCanon u' = u' := lineCanon_eq_self_of_mem_lineReps u' hu'
  calc
    u = lineCanon u := hu_can.symm
    _ = lineCanon (smulT4 (m : ZMod 3) u) := (lineCanon_smul_eq (m : ZMod 3) u hk).symm
    _ = lineCanon u' := by rw [← hsmul]
    _ = u' := hu'_can

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (ρ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* (V ≃ₗ[ZMod 2] V))

open CFSG.StandardType.USixTwo.ModuleProof

theorem map_conjAutTor_eq (σ : Equiv.Perm (Fin 6)) (H : Subgroup ↥(torU K)) :
    (H.map (conjAutTor hK hω σ).toMonoidHom).map (torU K).subtype =
      (H.map (torU K).subtype).map
        (MulAut.conj (Psigma (K := K) hK σ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem Hfun_permU_eq_map_conj {σ : Equiv.Perm (Fin 6)} {v : T4}
    (hconj : ((Hfun hK hω v).map (torU K).subtype).map
        (MulAut.conj (Psigma (K := K) hK σ)).toMonoidHom =
      (Hfun hK hω (CFSG.StandardType.USixTwo.TorConj.permU σ v)).map (torU K).subtype) :
    Hfun hK hω (CFSG.StandardType.USixTwo.TorConj.permU σ v) =
      (Hfun hK hω v).map (conjAutTor hK hω σ).toMonoidHom := by
  apply Subgroup.map_injective (f := (torU K).subtype)
    (fun a b hab => Subgroup.subtype_injective (torU K) hab)
  rw [map_conjAutTor_eq hK hω σ (Hfun hK hω v)]
  exact hconj.symm

theorem finrank_Hfun_lineStep (σ : Equiv.Perm (Fin 6)) {v : T4}
    (hconj : ((Hfun hK hω v).map (torU K).subtype).map
        (MulAut.conj (Psigma (K := K) hK σ)).toMonoidHom =
      (Hfun hK hω (CFSG.StandardType.USixTwo.TorConj.permU σ v)).map (torU K).subtype) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep σ v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) := by
  rw [lineStep, Hfun_lineCanon,
    Hfun_permU_eq_map_conj hK hω hconj,
    CFSG.StandardType.USixTwo.ModuleProof.finrank_weightSpace_conj hK hω ρ σ
      (Hfun hK hω v)]

theorem finrank_Hfun_lineStep_s01 (v : T4) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep s01 v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) :=
  finrank_Hfun_lineStep hK hω ρ s01 (Hfun_conj_s01 hK hω v)

theorem finrank_Hfun_lineStep_s12 (v : T4) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep s12 v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) :=
  finrank_Hfun_lineStep hK hω ρ s12 (Hfun_conj_s12 hK hω v)

theorem finrank_Hfun_lineStep_s23 (v : T4) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep s23 v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) :=
  finrank_Hfun_lineStep hK hω ρ s23 (Hfun_conj_s23 hK hω v)

theorem finrank_Hfun_lineStep_s34 (v : T4) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep s34 v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) :=
  finrank_Hfun_lineStep hK hω ρ s34 (Hfun_conj_s34 hK hω v)

theorem finrank_Hfun_lineStep_s45 (v : T4) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω (lineStep s45 v))) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω v)) :=
  finrank_Hfun_lineStep hK hω ρ s45 (Hfun_conj_s45 hK hω v)

theorem finrank_Hfun_mem_reach (base : T4) :
    ∀ (n : ℕ) {u : T4}, u ∈ reach base n →
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) =
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base)) := by
  intro n
  induction n with
  | zero =>
    intro u hu
    simp only [reach, Finset.mem_singleton] at hu
    subst hu
    rfl
  | succ n ih =>
    intro u hu
    simp only [reach, Finset.mem_union, Finset.mem_biUnion, stepSet, Finset.mem_insert,
      Finset.mem_singleton] at hu
    rcases hu with hu | ⟨v, hv, hu | hu | hu | hu | hu⟩
    · exact ih hu
    · rw [hu]; exact (finrank_Hfun_lineStep_s01 hK hω ρ v).trans (ih hv)
    · rw [hu]; exact (finrank_Hfun_lineStep_s12 hK hω ρ v).trans (ih hv)
    · rw [hu]; exact (finrank_Hfun_lineStep_s23 hK hω ρ v).trans (ih hv)
    · rw [hu]; exact (finrank_Hfun_lineStep_s34 hK hω ρ v).trans (ih hv)
    · rw [hu]; exact (finrank_Hfun_lineStep_s45 hK hω ρ v).trans (ih hv)

theorem finrank_Hfun_mem_O1 {u : T4} (hu : u ∈ O₁) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) :=
  finrank_Hfun_mem_reach hK hω ρ base₁ 6 hu

theorem finrank_Hfun_mem_O2 {u : T4} (hu : u ∈ O₂) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) :=
  finrank_Hfun_mem_reach hK hω ρ base₂ 6 hu

theorem finrank_Hfun_mem_O3 {u : T4} (hu : u ∈ O₃) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) :=
  finrank_Hfun_mem_reach hK hω ρ base₃ 6 hu

theorem sum_weightSpace_eq_sum_lineReps
    [Fintype (Hyperplane ↥(torU K) 3)] :
    (∑ H : Hyperplane ↥(torU K) 3,
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1)) =
      ∑ u ∈ lineReps,
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) := by
  classical
  exact (Finset.sum_bij
    (s := lineReps) (t := (Finset.univ : Finset (Hyperplane ↥(torU K) 3)))
    (f := fun u => Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)))
    (g := fun H => Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1))
    (fun u hu => ⟨Hfun hK hω u, Hfun_index hK hω (ne_zero_of_mem_lineReps hu)⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun u hu u' hu' heq => Hfun_injOn_lineReps hK hω hu hu' (congrArg Subtype.val heq))
    (by
      intro H _
      obtain ⟨u, hu0, hHu⟩ := exists_Hfun_eq_of_index_eq_three hK hω H H.2
      refine ⟨lineCanon u, ?_, ?_⟩
      · show lineCanon u ∈ lineReps
        rw [lineReps]
        exact Finset.mem_image.mpr
          ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0⟩, rfl⟩
      · apply Subtype.ext
        change Hfun hK hω (lineCanon u) = (H : Subgroup ↥(torU K))
        rw [Hfun_lineCanon]
        exact hHu.symm)
    (fun _ _ => rfl)).symm

theorem finrank_eq_fixedSpace_add_orbits :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) +
        10 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) +
        15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) +
        15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
  classical
  haveI : Finite ↥(torU K) := Nat.finite_of_card_ne_zero (by rw [card_torU hK]; norm_num)
  haveI : Finite (Subgroup ↥(torU K)) :=
    Finite.of_injective (fun H : Subgroup ↥(torU K) => (H : Set ↥(torU K)))
      SetLike.coe_injective
  haveI : Finite (Hyperplane ↥(torU K) 3) :=
    Finite.of_injective (fun H : Hyperplane ↥(torU K) 3 =>
      (H.1 : Subgroup ↥(torU K))) (fun a b h => Subtype.ext h)
  haveI : Fintype (Hyperplane ↥(torU K) 3) := Fintype.ofFinite _
  have h := finrank_eqLocus_eq hK hω (ρ := ρ) (a := (1 : ↥(torU K)))
    (T := Finset.univ.filter (fun H : Hyperplane ↥(torU K) 3 =>
      weightSpace (repTor ρ) H.1 ≠ ⊥)) (by intro H; simp)
  have hleft : Module.finrank (ZMod 2)
      (LinearMap.eqLocus (ρ (1 : ↥(torU K)) : V →ₗ[ZMod 2] V) LinearMap.id) =
      Module.finrank (ZMod 2) V := by
    have htop : LinearMap.eqLocus (ρ (1 : ↥(torU K)) : V →ₗ[ZMod 2] V) LinearMap.id = ⊤ := by
      rw [LinearMap.eqLocus_eq_top]
      ext v
      simp
    rw [htop, finrank_top]
  rw [hleft] at h
  have hfilter : (Finset.univ.filter (fun H : Hyperplane ↥(torU K) 3 =>
      weightSpace (repTor ρ) H.1 ≠ ⊥)).filter
      (fun H => (1 : ↥(torU K)) ∈ H.1) =
      Finset.univ.filter (fun H : Hyperplane ↥(torU K) 3 =>
        weightSpace (repTor ρ) H.1 ≠ ⊥) := by
    apply Finset.filter_true_of_mem
    intro H _
    exact Subgroup.one_mem H.1
  have hsupp : (∑ H ∈ Finset.univ.filter (fun H : Hyperplane ↥(torU K) 3 =>
      weightSpace (repTor ρ) H.1 ≠ ⊥),
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1)) =
      ∑ H : Hyperplane ↥(torU K) 3,
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro H _
    by_cases hH : weightSpace (repTor ρ) H.1 = ⊥
    · rw [hH, finrank_bot]
      simp
    · simp [hH]
  rw [hfilter, hsupp] at h
  rw [h, sum_weightSpace_eq_sum_lineReps hK hω ρ, lineReps_partition]
  set f : T4 → ℕ := fun u =>
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) with hf
  have hsplit : (∑ u ∈ O₁ ∪ O₂ ∪ O₃, f u) =
      (∑ u ∈ O₁, f u) + (∑ u ∈ O₂, f u) + (∑ u ∈ O₃, f u) := by
    rw [Finset.union_assoc]
    rw [Finset.sum_union]
    · rw [Finset.sum_union]
      · ac_rfl
      · exact O₂_disjoint_O₃
    · exact Finset.disjoint_union_right.mpr ⟨O₁_disjoint_O₂, O₁_disjoint_O₃⟩
  rw [hsplit]
  have hO1 : (∑ u ∈ O₁, f u) =
      10 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) := by
    calc
      (∑ u ∈ O₁, f u) = ∑ _u ∈ O₁,
          Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) :=
        Finset.sum_congr rfl (fun u hu => finrank_Hfun_mem_O1 hK hω ρ hu)
      _ = 10 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) := by
        rw [Finset.sum_const, O₁_card, nsmul_eq_mul]
        push_cast
        norm_num
  have hO2 : (∑ u ∈ O₂, f u) =
      15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) := by
    calc
      (∑ u ∈ O₂, f u) = ∑ _u ∈ O₂,
          Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) :=
        Finset.sum_congr rfl (fun u hu => finrank_Hfun_mem_O2 hK hω ρ hu)
      _ = 15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) := by
        rw [Finset.sum_const, O₂_card, nsmul_eq_mul]
        push_cast
        norm_num
  have hO3 : (∑ u ∈ O₃, f u) =
      15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
    calc
      (∑ u ∈ O₃, f u) = ∑ _u ∈ O₃,
          Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) :=
        Finset.sum_congr rfl (fun u hu => finrank_Hfun_mem_O3 hK hω ρ hu)
      _ = 15 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
        rw [Finset.sum_const, O₃_card, nsmul_eq_mul]
        push_cast
        norm_num
  rw [hO1, hO2, hO3]
  ring

theorem sum_filter_weightSpace_threeA
    [Fintype (Hyperplane ↥(torU K) 3)]
    [DecidablePred (fun H : Hyperplane ↥(torU K) 3 => threeAElt hω ∈ H.1)] :
    (∑ H ∈ (Finset.univ : Finset (Hyperplane ↥(torU K) 3)).filter
        (fun H => threeAElt hω ∈ H.1),
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1)) =
      ∑ u ∈ lineReps.filter (fun u => u.1 = u.2.1),
        Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) := by
  classical
  exact (Finset.sum_bij
    (s := lineReps.filter (fun u => u.1 = u.2.1))
    (t := (Finset.univ : Finset (Hyperplane ↥(torU K) 3)).filter
      (fun H => threeAElt hω ∈ H.1))
    (f := fun u => Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)))
    (g := fun H => Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1))
    (fun u hu => ⟨Hfun hK hω u,
      Hfun_index hK hω (ne_zero_of_mem_lineReps (Finset.mem_filter.mp hu).1)⟩)
    (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (threeA_mem_Hfun_iff hK hω).mpr (Finset.mem_filter.mp hu).2⟩)
    (fun u hu u' hu' heq => Hfun_injOn_lineReps hK hω
      (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 (congrArg Subtype.val heq))
    (by
      intro H hH
      have h3 : threeAElt hω ∈ H.1 := (Finset.mem_filter.mp hH).2
      obtain ⟨u, hu0, hHu⟩ := exists_Hfun_eq_of_index_eq_three hK hω H H.2
      refine ⟨lineCanon u, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · exact Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0⟩, rfl⟩
        · have h3' : threeAElt hω ∈ Hfun hK hω u := by
            rw [← hHu]
            exact h3
          rw [← threeA_mem_Hfun_iff (hK := hK) (hω := hω) (u := lineCanon u),
            Hfun_lineCanon]
          exact h3'
      · apply Subtype.ext
        change Hfun hK hω (lineCanon u) = (H : Subgroup ↥(torU K))
        rw [Hfun_lineCanon]
        exact hHu.symm)
    (fun _ _ => rfl)).symm

theorem finrank_eqLocus_threeA_eq :
    Module.finrank (ZMod 2)
        (LinearMap.eqLocus (ρ (threeA hω) : V →ₗ[ZMod 2] V) LinearMap.id) =
      Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) +
        4 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) +
        6 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) +
        3 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
  classical
  haveI : Finite ↥(torU K) := Nat.finite_of_card_ne_zero (by rw [card_torU hK]; norm_num)
  haveI : Finite (Subgroup ↥(torU K)) :=
    Finite.of_injective (fun H : Subgroup ↥(torU K) => (H : Set ↥(torU K)))
      SetLike.coe_injective
  haveI : Fintype (Hyperplane ↥(torU K) 3) := Fintype.ofFinite _
  let T : Finset (Hyperplane ↥(torU K) 3) :=
    Finset.univ.filter (fun H => weightSpace (repTor ρ) H.1 ≠ ⊥)
  have hT : ∀ H : Hyperplane ↥(torU K) 3,
      H ∈ T ↔ weightSpace (repTor ρ) H.1 ≠ ⊥ := by
    intro H
    simp [T]
  have h := finrank_eqLocus_eq hK hω (ρ := ρ) (a := threeAElt hω) T hT
  have hsupp3 : (∑ H ∈ T.filter (fun H => threeAElt hω ∈ H.1),
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1)) =
      ∑ H ∈ (Finset.univ : Finset (Hyperplane ↥(torU K) 3)).filter
        (fun H => threeAElt hω ∈ H.1),
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1) := by
    simp only [Finset.sum_filter]
    apply Finset.sum_subset (Finset.subset_univ T)
    intro a _ haT
    have hp : weightSpace (repTor ρ) a.1 = ⊥ := by
      by_contra hp
      exact haT ((hT a).mpr hp)
    simp [hp]
  rw [hsupp3, sum_filter_weightSpace_threeA hK hω ρ, lineReps_partition] at h
  simp only [threeAElt, Subtype.coe_mk] at h
  rw [Finset.sum_filter] at h
  set f : T4 → ℕ := fun u =>
    Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω u)) with hf
  have hsplit : (∑ u ∈ O₁ ∪ O₂ ∪ O₃, (if u.1 = u.2.1 then f u else 0)) =
      (∑ u ∈ O₁, (if u.1 = u.2.1 then f u else 0)) +
        (∑ u ∈ O₂, (if u.1 = u.2.1 then f u else 0)) +
        (∑ u ∈ O₃, (if u.1 = u.2.1 then f u else 0)) := by
    rw [Finset.union_assoc]
    rw [Finset.sum_union]
    · rw [Finset.sum_union]
      · ac_rfl
      · exact O₂_disjoint_O₃
    · exact Finset.disjoint_union_right.mpr ⟨O₁_disjoint_O₂, O₁_disjoint_O₃⟩
  rw [hsplit] at h
  have hO1 : (∑ u ∈ O₁, (if u.1 = u.2.1 then f u else 0)) =
      4 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) := by
    rw [← Finset.sum_filter]
    calc
      (∑ u ∈ O₁.filter (fun u => u.1 = u.2.1), f u) =
          ∑ _u ∈ O₁.filter (fun u => u.1 = u.2.1),
            Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) :=
        Finset.sum_congr rfl (fun u hu =>
          finrank_Hfun_mem_O1 hK hω ρ (Finset.mem_filter.mp hu).1)
      _ = 4 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) := by
        rw [Finset.sum_const, O₁_threeA_count, nsmul_eq_mul]
        norm_num
  have hO2 : (∑ u ∈ O₂, (if u.1 = u.2.1 then f u else 0)) =
      6 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) := by
    rw [← Finset.sum_filter]
    calc
      (∑ u ∈ O₂.filter (fun u => u.1 = u.2.1), f u) =
          ∑ _u ∈ O₂.filter (fun u => u.1 = u.2.1),
            Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) :=
        Finset.sum_congr rfl (fun u hu =>
          finrank_Hfun_mem_O2 hK hω ρ (Finset.mem_filter.mp hu).1)
      _ = 6 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) := by
        rw [Finset.sum_const, O₂_threeA_count, nsmul_eq_mul]
        norm_num
  have hO3 : (∑ u ∈ O₃, (if u.1 = u.2.1 then f u else 0)) =
      3 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
    rw [← Finset.sum_filter]
    calc
      (∑ u ∈ O₃.filter (fun u => u.1 = u.2.1), f u) =
          ∑ _u ∈ O₃.filter (fun u => u.1 = u.2.1),
            Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) :=
        Finset.sum_congr rfl (fun u hu =>
          finrank_Hfun_mem_O3 hK hω ρ (Finset.mem_filter.mp hu).1)
      _ = 3 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
        rw [Finset.sum_const, O₃_threeA_count, nsmul_eq_mul]
        norm_num
  rw [hO1, hO2, hO3] at h
  calc
    Module.finrank (ZMod 2)
        (LinearMap.eqLocus (ρ (threeA hω) : V →ₗ[ZMod 2] V) LinearMap.id) =
        Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) +
          (4 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) +
            6 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) +
            3 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃))) := h
    _ = Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) +
          4 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) +
        6 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) +
      3 * Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) := by
      ac_rfl

theorem twenty_le_finrank_of_faithful (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hρ : Function.Injective ρ) :
    20 ≤ Module.finrank (ZMod 2) V := by
  classical
  haveI : Finite ↥(torU K) := Nat.finite_of_card_ne_zero (by rw [card_torU hK]; norm_num)
  have hformula := finrank_eq_fixedSpace_add_orbits hK hω ρ
  have hex : (Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) ≠ 0) ∨
      (Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) ≠ 0) ∨
      (Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) ≠ 0) := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    have hV : Module.finrank (ZMod 2) V =
        Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) := by
      rw [hformula, h1, h2, h3]
      omega
    have htop : fixedSpace (repTor ρ) ⊤ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hV]
    have htriv : ∀ a ∈ torU K, ρ a = 1 := by
      intro a ha
      ext v
      have hv : v ∈ fixedSpace (repTor ρ) ⊤ := by rw [htop]; exact Submodule.mem_top
      let a' : ↥(torU K) := ⟨a, ha⟩
      have hfix := Iff.mp (CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt.mem_fixedSpace (repTor ρ)) hv
        a' (Subgroup.mem_top a')
      rw [repTor_apply] at hfix
      simpa [a'] using hfix
    have htor_bot : torU K = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have h1' : a ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        exact htriv a ha
      rwa [(MonoidHom.ker_eq_bot_iff ρ).mpr hρ] at h1'
    have hcard := card_torU hK
    rw [htor_bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  rcases hex with h1 | h2 | h3
  · obtain ⟨k, hk⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₁)
    omega
  · obtain ⟨k, hk⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₂)
    omega
  · obtain ⟨k, hk⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₃)
    omega

theorem finrank_eq_twenty_of_fixed (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0)
    (htor : ∀ v : V, (∀ x ∈ torU K, ρ x v = v) → v = 0)
    (h8 : Module.finrank (ZMod 2)
      (LinearMap.eqLocus (ρ (threeA hω) : V →ₗ[ZMod 2] V) LinearMap.id) = 8) :
    Module.finrank (ZMod 2) V = 20 := by
  classical
  haveI : Finite ↥(torU K) := Nat.finite_of_card_ne_zero (by rw [card_torU hK]; norm_num)
  have hCbot : fixedSpace (repTor ρ) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    apply htor v
    intro x hx
    let x' : ↥(torU K) := ⟨x, hx⟩
    have hfix := Iff.mp (CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt.mem_fixedSpace (repTor ρ)) hv
      x' (Subgroup.mem_top x')
    rw [repTor_apply] at hfix
    simpa [x'] using hfix
  have hCfin : Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) = 0 := by
    rw [hCbot, finrank_bot]
  have h6 := finrank_eqLocus_threeA_eq hK hω ρ
  rw [hCfin, h8] at h6
  obtain ⟨k1, hk1⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₁)
  obtain ⟨k2, hk2⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₂)
  obtain ⟨k3, hk3⟩ := even_finrank_weightSpace hK hω ρ (Hfun hK hω base₃)
  have hd1 : Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₁)) = 2 := by
    omega
  have hd2 : Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₂)) = 0 := by
    omega
  have hd3 : Module.finrank (ZMod 2) (weightSpace (repTor ρ) (Hfun hK hω base₃)) = 0 := by
    omega
  have h5 := finrank_eq_fixedSpace_add_orbits hK hω ρ
  rw [hCfin, hd1, hd2, hd3] at h5
  omega

end CFSG.StandardType.USixTwo.MainProof

end
