module

public import CFSG.GroupTheory.AutomorphismFixedSubgroupSimple
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTri
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTD4
import CFSG.RankThree.PartOne.KD4L.TriDescent
import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.HardMathSupport.Lang.Coordinator

section


theorem fieldAutOdd_twistedE6 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f r : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .twistedE6 n p f)
    (hX : LieModel X .twistedE6 n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ CFSG.Open.signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨-, hchev⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  let α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := MulAut.congr e' θ
  have hαord : orderOf α = r :=
    (orderOf_injective (MulAut.congr e').toMonoidHom (MulAut.congr e').injective θ).trans hθ
  have hαr : α ^ r = 1 := hαord ▸ pow_orderOf_eq_one α
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := fun hin =>
    hout ((congr_mem_inner_iff e' θ).mp hin)
  have hK2f : Nat.card K = p ^ (2 * f) := by
    rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      hp hf K hcard σ hσ
  have hpg : ¬ r ∣ Nat.gcd 3 (p ^ f + 1) := by
    intro h
    have h1 : r ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
    have h2 : r ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hη1 : Θ α ≠ 1 := by
    intro h1
    have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hαin (mem_inner_of_mem_inn_sup_diag hr hcard hσ hpg hcube hαr hmem)
  have hr2 : r ≠ 2 := by omega
  obtain ⟨d, hd, hd1, r₀, s, T, ε, hT, hε, hrs, ψ, hψpow, _hψlast⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order
      hp hf K hK2f σ hσ Θ hΘ hr hr2 α hαr hη1
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hp (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ p ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = p ^ (2 * d * r) := by
    rw [hK2f, hd]
    congr 1
    ring
  have hσdp : ∀ c, σ c = c ^ p ^ (d * r) := fun c => by
    rw [hσ c, hd, mul_comm r d]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ p ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ r := by omega
  have hpodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨-, hkcard, hJC, -, hder, hsimpleJ, -, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hp hd1 hm3 hpodd K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
    (fixSubfieldRestrict T κ) with hJdef
  have hder' : ⁅fixedSubgroup δ, fixedSubgroup δ⁆ =
      J.subgroupOf (twistedE6RootGroup K σ) := hder
  have hJΓ : J.subgroupOf (twistedE6RootGroup K σ) ≤ fixedSubgroup δ := by
    rw [← hder']
    exact Subgroup.commutator_le_self _
  have hσ₀' : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ) c = c ^ (p ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hkcard' : Nat.card (fixSubfield κ) = (p ^ d) ^ TwistTag.E6.order := by
    rw [hkcard, ← pow_mul, mul_comm]
    rfl
  have hmodel := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.twistedModel_graphFixedRootGroup
    (t := TwistTag.E6) hp hd1 (fixSubfield κ) hkcard' (fixSubfieldRestrict T κ) hσ₀'
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6
      (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)) :=
    CFSG.SectionRank.four_le_pRank_of_twistedE6Model hd1 hmodel
  let eJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) ≃* ↥J :=
    Subgroup.equivMapOfInjective
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)
      (baseChangeGL (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)
      (baseChangeGL_injective _)
  let eJC : ↥(J.subgroupOf (twistedE6RootGroup K σ)) ≃* ↥J :=
    Subgroup.subgroupOfEquivOfLe hJC
  have hYrank : 2 ≤ CFSG.pRank p (↥J) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p (↥J)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eJ]
    exact le_trans (by norm_num : 2 ≤ 4) h4
  let ιJ : ↥J →* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (Subgroup.subtype (J.subgroupOf (twistedE6RootGroup K σ))).comp eJC.symm.toMonoidHom
  have hιJ : Function.Injective ιJ :=
    (Subgroup.subtype_injective (J.subgroupOf (twistedE6RootGroup K σ))).comp
      eJC.symm.injective
  have hfixJ : ∀ y, δ (ιJ y) = ιJ y := fun y => hJΓ (eJC.symm y).2
  have : IsSimpleGroup ↥J := hsimpleJ
  obtain ⟨S, hS, hSsimple, hSrank⟩ :=
    CFSG.exists_simple_subgroup_le_fixed_of_injective ιJ hιJ δ hfixJ hYrank
  have : IsSimpleGroup ↥S := hSsimple
  have hψcongr : MulAut.congr ψ (α ^ r₀) = δ := by
    have heq : MulAut.congr ψ (α ^ r₀) = ψ * α ^ r₀ * ψ⁻¹ := by
      ext x
      rfl
    exact heq.trans hψpow
  let Sα : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    S.map ψ.symm.toMonoidHom
  have hSα₀le : Sα ≤ CFSG.Open.signalizerFixedSubgroup (α ^ r₀) := by
    change S.map ψ.symm.toMonoidHom ≤ signalizerFixedSubgroup (α ^ r₀)
    rw [← CFSG.SignalizerFunctorTheorem.McBride.congr_symm_congr ψ (α ^ r₀),
      CFSG.SignalizerFunctorTheorem.McBride.signalizerFixedSubgroup_congr, hψcongr]
    exact Subgroup.map_mono hS
  have hpow_le : CFSG.Open.signalizerFixedSubgroup (α ^ r₀) ≤
      CFSG.Open.signalizerFixedSubgroup α := by
    intro x hx
    have hx' : (α ^ r₀) x = x := hx
    rw [← hrs]
    exact (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.fixedSubgroup_le_pow'
      (α ^ r₀) s) hx'
  have hSαle : Sα ≤ CFSG.Open.signalizerFixedSubgroup α := le_trans hSα₀le hpow_le
  have hSαsimple : IsSimpleGroup Sα :=
    (Subgroup.equivMapOfInjective S ψ.symm.toMonoidHom ψ.symm.injective).symm.isSimpleGroup
  have : IsSimpleGroup ↥Sα := hSαsimple
  have hSαrank : 2 ≤ CFSG.pRank p Sα := by
    rw [← CFSG.pRank_congr_of_mulEquiv
      (S.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective) p]
    exact hSrank
  let S' : Subgroup X := Sα.map e'.symm.toMonoidHom
  have hS'le : S' ≤ CFSG.Open.signalizerFixedSubgroup θ := by
    change Sα.map e'.symm.toMonoidHom ≤ signalizerFixedSubgroup θ
    rw [← CFSG.SignalizerFunctorTheorem.McBride.congr_symm_congr e' θ,
      CFSG.SignalizerFunctorTheorem.McBride.signalizerFixedSubgroup_congr]
    exact Subgroup.map_mono hSαle
  have hS'simple : IsSimpleGroup S' :=
    (Subgroup.equivMapOfInjective Sα e'.symm.toMonoidHom e'.symm.injective).symm.isSimpleGroup
  have hS'rank : 2 ≤ CFSG.pRank p S' := by
    rw [← CFSG.pRank_congr_of_mulEquiv
      (Sα.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective) p]
    exact hSαrank
  exact ⟨⟨d, hd⟩, S', hS'le, hS'simple, hS'rank⟩


theorem fieldAutOdd_trialityD4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f r : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : LieModel X .trialityD4 n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ CFSG.Open.signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨-, hchev⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hchev.2
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  let α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e' θ
  have hαord : orderOf α = r :=
    (orderOf_injective (MulAut.congr e').toMonoidHom (MulAut.congr e').injective θ).trans hθ
  have hαr : α ^ r = 1 := hαord ▸ pow_orderOf_eq_one α
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun hin =>
    hout ((congr_mem_inner_iff e' θ).mp hin)
  obtain ⟨f₀, k₀, _, _, σ₀, hf_eq, hk₀, hσ₀, hmod, ⟨eFix⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.FR.trialityD4_outer_fixed_equiv
      hp hf hr hr5 K hcard σ hσ α hαr hαin
  have hd1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h, mul_zero] at hf_eq
      omega
    · exact h
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hmod' : r % 3 = 1 ∨ r % 3 = 2 := by omega
  have hσ₀_or : (∀ c, σ₀ c = c ^ (p ^ f₀)) ∨
      (∀ c, σ₀ c = c ^ (p ^ f₀) ^ 2) := by
    rcases hmod' with h | h
    · left
      intro c
      rw [hσ₀ c, h, pow_one]
    · right
      intro c
      rw [hσ₀ c, h]
  have hYsimple : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) :=
    (CFSG.RankThree.PartOne.KD4L.isSimple_graphFixedRootGroup_triality
      hp hd1 hk₀ (r % 3) hmod' σ₀.toRingHom hσ₀).1
  have hYrank : 2 ≤ CFSG.pRank p (↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p
      (↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom))]
    have h4 :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.four_le_pRank_graphFixedRootGroup_D4
        hp hd1 k₀ hk₀ σ₀ hσ₀_or
    exact le_trans (by norm_num : 2 ≤ 4) h4
  let ι : ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.subtype (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α)).comp
      eFix.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α)).comp
      eFix.symm.injective
  have hfix : ∀ y, α (ι y) = ι y := fun y => (eFix.symm y).2
  have : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) := hYsimple
  obtain ⟨S, hS, hSsimple, hSrank⟩ :=
    CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι α hfix hYrank
  have : IsSimpleGroup ↥S := hSsimple
  let S' : Subgroup X := S.map e'.symm.toMonoidHom
  have hS'le : S' ≤ CFSG.Open.signalizerFixedSubgroup θ := by
    change S.map e'.symm.toMonoidHom ≤ signalizerFixedSubgroup θ
    rw [← CFSG.SignalizerFunctorTheorem.McBride.congr_symm_congr e' θ,
      CFSG.SignalizerFunctorTheorem.McBride.signalizerFixedSubgroup_congr]
    exact Subgroup.map_mono hS
  have hS'simple : IsSimpleGroup S' :=
    (Subgroup.equivMapOfInjective S e'.symm.toMonoidHom e'.symm.injective).symm.isSimpleGroup
  have hS'rank : 2 ≤ CFSG.pRank p S' := by
    rw [← CFSG.pRank_congr_of_mulEquiv
      (S.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective) p]
    exact hSrank
  exact ⟨⟨f₀, hf_eq⟩, S', hS'le, hS'simple, hS'rank⟩

end

end CFSG.LocalAnalysis.UniquenessCase.UC22
