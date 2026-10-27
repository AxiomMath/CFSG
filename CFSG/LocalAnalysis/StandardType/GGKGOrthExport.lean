module

public import CFSG.LocalAnalysis.StandardType.GGKGOmegaNoSp
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Assembly.LowTwoRank

private def kgx_Data (ℓ q : ℕ) (X : Type) [Group X] : Prop :=
  KGOrthFactor ℓ q X ∧ LieFactorProperty ℓ X

private theorem kgx_paired (hSL : SLFactorFacts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (h : K[X]) (hirr : Irreducible h)
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (kgx_Data (ringChar K) (Nat.card K)) ↥(specialBlock Q x h) := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have h4 : 4 ≤ Fintype.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    rw [Fintype.card_eq_nat_card]
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    ((MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv b).symm)
  have hX := hSL (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) hm (fun _ => h4)
  have hchar : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
  rw [hchar] at hX
  have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h
  have hdpos : 1 ≤ h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hfac : KGOrthFactor (ringChar K) (Nat.card K)
      (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h))
        (AdjoinRoot h)) :=
    Or.inl ⟨primaryMultiplicity x.toLinearMap h, h.natDegree, AdjoinRoot h, inferInstance,
      inferInstance, hm, hdpos, hchar, by rw [← Nat.card_eq_fintype_card]; exact hcardE,
      (fun _ => h4), ⟨MulEquiv.refl _⟩⟩
  refine OrthCompData.of_model ⟨hfac, hX, fun hA6 _ _ hℓ3 => ⟨fun e6 => ?_⟩⟩ e₁.symm
  obtain ⟨-, h9⟩ := hA6 (AdjoinRoot h) _ hm ⟨e6⟩
  exact hℓ3 (hchar ▸ ringChar_eq_three_of_card_eq_nine' h9)

private theorem kgx_selfDual (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (h : K[X])
    (hirr : Irreducible h) (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthCompData (kgx_Data (ringChar K) (Nat.card K)) ↥(specialBlock Q x h) := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hdpos : 1 ≤ d := by
    have := (Fact.out : Irreducible h).natDegree_pos
    omega
  obtain ⟨ℓ, f, hU, hq0, hbar⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_unitaryFieldData (K := K) (E := AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hK : Fintype.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
    rw [Fintype.card_eq_nat_card, hE]
  have hchar : ringChar (AdjoinRoot h) = ringChar K := (Algebra.ringChar_eq K (AdjoinRoot h)).symm
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have hfinV : Finite ↥(sesqSpecialUnitaryGroup B) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e₁.toEquiv
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with hm3 | hm3
  ·
    have hm2 : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
      have : primaryMultiplicity x.toLinearMap h = 2 := by omega
      exact this
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBsymm
      hBl hm2
    letI : Fintype ↥hU.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card ↥hU.fixedField = ℓ ^ (f * d) := by
      rw [Fintype.card_eq_nat_card, hU.card_fixedField]
    have h4 : 4 ≤ Fintype.card ↥hU.fixedField := by
      by_contra hlt
      refine false_of_isQuasisimple_of_isSolvable' hq ?_
      haveI := isSolvable_sl_two_of_card_lt_four' (E := ↥hU.fixedField)
        (by rw [Nat.card_eq_fintype_card]; omega)
      exact Group.isSolvable_of_isSolvable_injective (f := (e₁.trans φ).toMonoidHom)
        (e₁.trans φ).injective
    have hX := hSL ↥hU.fixedField 2 le_rfl (fun _ => h4)
    have hcharF : ringChar ↥hU.fixedField = ringChar K := by
      rw [← hchar]
      exact Algebra.ringChar_eq ↥hU.fixedField (AdjoinRoot h)
    rw [hcharF] at hX
    have hcardNat : Nat.card ↥hU.fixedField = Nat.card K ^ d := by
      rw [Nat.card_eq_fintype_card, hcardF, hq0, ← pow_mul]
    have hfac : KGOrthFactor (ringChar K) (Nat.card K)
        (Matrix.SpecialLinearGroup (Fin 2) ↥hU.fixedField) :=
      Or.inl ⟨2, d, ↥hU.fixedField, inferInstance, inferInstance, le_rfl, hdpos, hcharF,
        by rw [← Nat.card_eq_fintype_card]; exact hcardNat, (fun _ => h4),
        ⟨MulEquiv.refl _⟩⟩
    refine OrthCompData.of_model ⟨hfac, hX, fun hA6 _ _ hℓ3 => ⟨fun e6 => ?_⟩⟩
      (φ.symm.trans e₁.symm)
    obtain ⟨-, h9⟩ := hA6 ↥hU.fixedField 2 le_rfl ⟨e6⟩
    exact hℓ3 (hcharF ▸ ringChar_eq_three_of_card_eq_nine' h9)
  ·
    by_cases hexc : primaryMultiplicity x.toLinearMap h = 3 ∧ ℓ ^ (f * d) = 2
    · exfalso
      refine false_of_isQuasisimple_of_isSolvable' hq ?_
      haveI : Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := by
        refine isSolvable_of_card_primeFactors_le_two ?_
        have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
          (n := primaryMultiplicity x.toLinearMap h) rfl (by omega)).2.1
        obtain ⟨hm3', hq2⟩ := hexc
        rw [hm3', hq2] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
        have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
          exact_mod_cast hcard.trans e
        rw [h216]
        decide +kernel
      exact Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective
    · have hmq : (primaryMultiplicity x.toLinearMap h, ℓ ^ (f * d)) ≠ (3, 2) := fun e =>
        hexc ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      have hX := hSU (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d)) hK hm3 hmq
      rw [hchar] at hX
      have hq' : ℓ ^ (f * d) = Nat.card K ^ d := by rw [hq0, ← pow_mul]
      obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
      obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
        e₀ he₀
      have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
          (primaryMultiplicity x.toLinearMap h) =
          CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
            (AdjoinRoot h) := by
        rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
        exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
      let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
          (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
        (e₂.trans (MulEquiv.subgroupCongr hS)).symm
      have hfac : KGOrthFactor (ringChar K) (Nat.card K)
          ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
            (AdjoinRoot h)) :=
        Or.inr (Or.inl ⟨primaryMultiplicity x.toLinearMap h, d, ℓ ^ (f * d), AdjoinRoot h,
          inferInstance, inferInstance, hm3, hdpos, hchar, hq', hK, hmq,
          ⟨MulEquiv.refl _⟩⟩)
      exact OrthCompData.of_model ⟨hfac, hX,
        (fun _ hSU6 _ _ =>
          hSU6 (AdjoinRoot h) (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d)) hK hm3)⟩
        (e₃.trans e₁.symm)

private theorem kgx_fixedFactor {p : ℕ} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (F : Subgroup (V ≃ₗ[K] V))
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    OrthCompData (kgx_Data (ringChar K) (Nat.card K)) ↥F :=
  orthCompData_fixedFactor_of (P := kgx_Data (ringChar K) (Nat.card K))
    (hprov := fun L hLn hLq => by
      have hQW := hx.polarBilin_fixed_nondegenerate
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨X, _, _, hX, hfac, f, hf, hfk⟩ :=
        kgOmegaFactor_holds K hK2 (fixedSpace x) (Q.comp (fixedSpace x).subtype) hQW L hLn hLq
      refine ⟨X, inferInstance, inferInstance, ⟨hfac, ⟨hX, fun _ _ hOm6 hℓ3 => ?_⟩⟩, f, hf, hfk⟩
      refine ⟨fun e6 => ?_⟩
      obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
      obtain ⟨h3, -⟩ := hOm6 (K := K) (V := fixedSpace x)
        (Q := Q.comp (fixedSpace x).subtype) hQW L hLn hLq ⟨e'.symm.trans e6⟩
      exact hℓ3 h3)
    hx F hFq hFle hFn

private theorem kgx_component (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    OrthCompData (kgx_Data (ringChar K) (Nat.card K)) ↥J :=
  orthCompData_component_of (P := kgx_Data (ringChar K) (Nat.card K)) (hp := hp)
    (hp2 := hp2) (hQ := hQ) (hT := hT) (hpℓ := hpℓ)
    (hperfP := fun _ _ h => h.2.1.perfect)
    (hpaired := fun hx h hirr hh hne1 hne hq =>
      kgx_paired hSL hp hp2 hx h hirr hh hne1 hne hq)
    (hself := fun hx h hirr hh hne1 hself hq =>
      kgx_selfDual hSL hSU hp hp2 hx h hirr hh hne1 hself hq)
    (hfixed := fun hx F hFq hFle hFn => kgx_fixedFactor hK2 hx F hFq hFle hFn)
    (a := a) (ha := ha) (J := J) (hJ := hJ)

theorem kgOrth_lieFactor {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] {n f : ℕ}
    (hG : StatedClassicalModel G t n 2 f) (a : G) (ha : a ^ p = 1) (J : Subgroup G)
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X),
      LieFactorData 2 X ∧ KGOrthFactor 2 (2 ^ f) X ∧
      ∃ g : X →* ↥J, Function.Surjective g ∧ g.ker ≤ Subgroup.center X := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcardK, hring, ⟨e⟩⟩ :=
    exists_projOrth_model_card (Or.inr ht) hG
  have hfix : HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.congr e (MulAut.conj a)) =
      (HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)).map
        (e : G →* ProjOrthDerived Q) := by
    ext x
    rw [HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    show e (MulAut.conj a (e.symm x)) = x ↔ MulAut.conj a (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
      (Subgroup.centralizer ({e a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
    rw [← hfix, congr_conj, fixSubgroup_conj_eq_centralizer] at h1
    exact h1
  have hpℓ : p ≠ ringChar K := by rw [hring]; exact hp2
  obtain ⟨X, _, _, fX, hP, hf, hfk⟩ :=
    kgx_component slFactorFacts_holds suFactorFacts_holds hp hp2 hring hQ hT hpℓ
      (e a) (by rw [← map_pow, ha, map_one]) _ hJ'
  let g : ↥(J.map (e : G →* ProjOrthDerived Q)) ≃* ↥J :=
    (J.equivMapOfInjective (e : G →* ProjOrthDerived Q) e.injective).symm
  have hfac : KGOrthFactor 2 (2 ^ f) X := by
    rw [← hcardK, ← hring]
    exact hP.1
  have hX : LieFactorData 2 X := by
    rw [← hring]
    exact hP.2.1
  refine ⟨X, inferInstance, inferInstance, hX, hfac, g.toMonoidHom.comp fX,
    g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

end CFSG.StandardType.KG
