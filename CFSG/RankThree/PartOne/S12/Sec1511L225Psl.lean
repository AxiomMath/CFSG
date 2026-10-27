module

public import CFSG.RankThree.PartOne.S12.Sec1511L225Abs
public import CFSG.RankThree.PartOne.S12.Sec1511Y2Aut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Adapters.LinearCatalog
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP CFSG.GorensteinWalter Matrix Projectivization
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Sec1511

namespace L225

section Fixed

theorem unipotent_fixed_iff {K : Type} [Field K] {t : K} (ht : t ≠ 0) (p : PSL2ProjectiveLine K) :
    psl2QuotientMap K (sl2UpperUnipotent t) • p = p ↔ p = psl2ProjectiveInfinity K := by
  constructor
  · induction p using Projectivization.ind with
    | h v hv =>
        intro hfix
        rw [psl2QuotientMap_smul, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hfix
        obtain ⟨a, ha⟩ := hfix
        have hUv : sl2UpperUnipotent t • v = ![v 0 + t * v 1, v 1] := by
          change (sl2UpperUnipotent t).val *ᵥ v = _
          ext i
          fin_cases i <;>
            simp [sl2UpperUnipotent, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
        rw [hUv] at ha
        by_cases hv1 : v 1 = 0
        · rw [psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff']
          refine ⟨v 0, ?_⟩
          ext i
          fin_cases i <;> simp [hv1]
        · have ha1 : (a : K) = 1 := by
            apply mul_right_cancel₀ hv1
            simpa [Units.smul_def] using congrFun ha 1
          have h0 : v 0 = v 0 + t * v 1 := by
            simpa [Units.smul_def, ha1] using congrFun ha 0
          have h1 : t * v 1 = 0 := by
            apply add_left_cancel (a := v 0)
            simpa using h0.symm
          exact absurd (mul_eq_zero.1 h1) (by simp [ht, hv1])
  · rintro rfl
    have hu : psl2QuotientMap K (sl2UpperUnipotent t) ∈ psl2UpperUnipotentSubgroup K :=
      (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨t, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp (psl2UpperUnipotent_le_borel hu)

theorem psl2_fix5 {K : Type} [Field K] [Finite K] {f : ℕ} (hKcard : Nat.card K = 5 ^ f)
    {a : PSL2 K} (ha : orderOf a = 5) : ∃! x : PSL2ProjectiveLine K, a • x = x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hKcard
  have hUs : IsSylowOf 5 (psl2UpperUnipotentSubgroup K) ⊤ := by
    refine ⟨le_top, by rw [← hQ]; exact Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hQ]
    exact Q.not_dvd_index
  have hap : a ^ 5 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  obtain ⟨g, hg⟩ := StrongP.exists_conj_le_sylow hUs (StrongP.isPGroup_zpowers_of_pow_eq_one hap)
  have hmem : g * a * g⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    hg ⟨a, Subgroup.mem_zpowers a, by simp [MulAut.conj_apply]⟩
  obtain ⟨t, ht⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 hmem
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    omega
  have ht0 : t ≠ 0 := by
    intro h0
    apply ha1
    rw [h0, sl2UpperUnipotent_zero, map_one] at ht
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, ht]
    group
  have hfix := (unipotent_fixed_iff ht0 (psl2ProjectiveInfinity K)).2 rfl
  rw [← ht] at hfix
  refine ⟨g⁻¹ • psl2ProjectiveInfinity K, ?_, ?_⟩
  · show a • (g⁻¹ • psl2ProjectiveInfinity K) = g⁻¹ • psl2ProjectiveInfinity K
    calc a • (g⁻¹ • psl2ProjectiveInfinity K) = (g⁻¹ * (g * a * g⁻¹)) • psl2ProjectiveInfinity K := by
          rw [← mul_smul]
          congr 1
          group
      _ = g⁻¹ • ((g * a * g⁻¹) • psl2ProjectiveInfinity K) := mul_smul _ _ _
      _ = g⁻¹ • psl2ProjectiveInfinity K := by rw [hfix]
  · intro y hy
    have h1 : (g * a * g⁻¹) • (g • y) = g • y := by
      calc (g * a * g⁻¹) • (g • y) = (g * a * g⁻¹ * g) • y := (mul_smul _ _ _).symm
        _ = (g * a) • y := by rw [show g * a * g⁻¹ * g = g * a by group]
        _ = g • (a • y) := mul_smul _ _ _
        _ = g • y := by rw [hy]
    rw [ht] at h1
    have := (unipotent_fixed_iff ht0 (g • y)).1 h1
    exact eq_inv_smul_iff.2 this

theorem psl2_fix3 {K : Type} [Field K] [Finite K] {a : PSL2 K} (ha : a ≠ 1)
    {x y z : PSL2ProjectiveLine K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : a • x = x) (hy : a • y = y) (hz : a • z = z) : False := by
  have h := psl2_fixedPoint_card_le_two K a ha
  have hmem : ∀ i : Fin 3, a • (![x, y, z] i) = ![x, y, z] i := by
    intro i
    fin_cases i <;> assumption
  have hinj : Function.Injective
      (fun i : Fin 3 => (⟨![x, y, z] i, hmem i⟩ : {w : PSL2ProjectiveLine K // a • w = w})) := by
    intro i j hij
    have := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h3 := Nat.card_le_card_of_injective _ hinj
  simp at h3
  omega

end Fixed

section Borel

variable {K : Type} [Field K]

theorem sl2Borel_diag_ne_zero {A : SL(2, K)} (hA : A ∈ sl2Borel K) : A.val 0 0 ≠ 0 := by
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).1 hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  exact left_ne_zero_of_mul_eq_one hdet

noncomputable def borelDiag : sl2Borel K →* Kˣ where
  toFun A := Units.mk0 (A.1.val 0 0) (sl2Borel_diag_ne_zero A.2)
  map_one' := by
    apply Units.ext
    simp
  map_mul' A B := by
    apply Units.ext
    have hB : (B : SL(2, K)).val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff _).1 B.2
    simp [Matrix.mul_apply, Fin.sum_univ_two, hB]

theorem sl2UpperUnipotent_mem_borel (x : K) : sl2UpperUnipotent x ∈ sl2Borel K :=
  (sl2_mem_stabilizer_infinity_iff _).2 (by simp [sl2UpperUnipotent])

theorem isSolvable_sl2Borel : Group.IsSolvable (sl2Borel K) := by
  let f : Multiplicative K →* sl2Borel K :=
    { toFun := fun t => ⟨sl2UpperUnipotent t.toAdd, sl2UpperUnipotent_mem_borel _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  refine Group.isSolvable_of_ker_le_range f borelDiag ?_
  intro A hA
  have h00 : A.1.val 0 0 = 1 := by
    have := congrArg Units.val ((MonoidHom.mem_ker).1 hA)
    simpa [borelDiag] using this
  have h10 : A.1.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff _).1 A.2
  have h11 : A.1.val 1 1 = 1 := by
    have h := A.1.property
    rw [Matrix.det_fin_two, h10, h00] at h
    simpa using h
  refine ⟨Multiplicative.ofAdd (A.1.val 0 1), Subtype.ext (Subtype.ext ?_)⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f, sl2UpperUnipotent, h00, h10, h11]

theorem isSolvable_psl2Borel : Group.IsSolvable (psl2Borel K) := by
  have := isSolvable_sl2Borel (K := K)
  rw [psl2Borel_eq_map]
  exact Group.isSolvable_of_surjective
    (MonoidHom.subgroupMap_surjective (psl2QuotientMap K) (sl2Borel K))

theorem psl2_stab_solvable [Finite K] (x : PSL2ProjectiveLine K) :
    Group.IsSolvable ↥(MulAction.stabilizer (PSL2 K) x) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 K) (psl2ProjectiveInfinity K) x
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have h1 : Group.IsSolvable (psl2Borel K) := isSolvable_psl2Borel
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (psl2Borel K) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.toMonoidHom) (MulEquiv.injective _)

end Borel

section Cards

variable {K : Type} [Field K] [Finite K]

theorem card_proj : Nat.card (PSL2ProjectiveLine K) = Nat.card K + 1 :=
  Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)

theorem isOddPrimePower_of_card {K : Type} [Field K] (hK : Nat.card K = 5 ^ 2) :
    IsOddPrimePower (Nat.card K) :=
  ⟨5, 2, by norm_num, by decide, by norm_num, hK⟩

theorem card_psl2 (hK : Nat.card K = 5 ^ 2) : Nat.card (PSL2 K) = 7800 := by
  rw [psl2_card_formula K (isOddPrimePower_of_card hK), hK]
  norm_num

theorem card_aut_psl2 (hK : Nat.card K = 5 ^ 2) : Nat.card (MulAut (PSL2 K)) = 31200 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hodd := isOddPrimePower_of_card hK
  have h4 : 3 < Nat.card K := by rw [hK]; norm_num
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hK hodd h4
  let eAut := pGammaL2EquivMulAutPSL2 K hodd h4 hsurj
  rw [← Nat.card_congr eAut.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hpgl : Nat.card (PGL2 K) = 15600 := by
    have := pgl2_card_formula K
    rw [hK] at this
    exact this
  have hAut : Nat.card (K ≃+* K) = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 5) (n := 2) (by norm_num) (by norm_num) hK
    exact h
  rw [hpgl, hAut]

end Cards

section Instance

theorem exists_setting {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ 2) (e : ↥S ≃* PSL2 K) :
    ∃ (Ω : Type) (_ : MulAction H Ω), Setting S Ω := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let ρ₀ : H →* MulAut (PSL2 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := S))
  have hρ₀ : Function.Injective ρ₀ :=
    (MulAut.congr e).injective.comp (CTP.conjNormal_injective_of_centralizer S hSc)
  let ρ : H →* Equiv.Perm (PSL2ProjectiveLine K) := (psl2MulAutProjectiveLine K hK).comp ρ₀
  have hρ : Function.Injective ρ := (psl2MulAutProjectiveLine_injective K hK).comp hρ₀
  let _ : MulAction H (PSL2ProjectiveLine K) := MulAction.compHom _ ρ
  have hsmul : ∀ (h : H) (x : PSL2ProjectiveLine K), h • x = ρ h x := fun _ _ => rfl
  have hcompat : ∀ (s : ↥S) (x : PSL2ProjectiveLine K), (s : H) • x = e s • x := by
    intro s x
    have h1 : MulAut.conjNormal (H := S) (s : H) = MulAut.conj s := by
      ext y
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    rw [hsmul]
    show psl2MulAutProjectiveLine K hK (MulAut.congr e (MulAut.conjNormal (H := S) (s : H))) x = _
    rw [h1, ComponentClassification.OuterAutomorphisms.congr_conj, psl2MulAutProjectiveLine_conj]
  refine ⟨PSL2ProjectiveLine K, inferInstance, ?_⟩
  exact
  { faithful := fun g hg => hρ (by
      refine Equiv.ext fun x => ?_
      rw [map_one]
      exact hg x)
    card_Ω := by rw [card_proj, hK]; norm_num
    card_S := by rw [Nat.card_congr e.toEquiv, card_psl2 hK]
    trans := fun x y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 K) x y
      refine ⟨(e.symm g : H), (e.symm g).2, ?_⟩
      rw [hcompat (e.symm g) x, e.apply_symm_apply]
      exact hg
    coatom := by
      intro x Z hZS hsub
      let Z' : Subgroup (PSL2 K) := (Z.subgroupOf S).map e.toMonoidHom
      have hstab : MulAction.stabilizer (PSL2 K) x ≤ Z' := by
        intro g hg
        have hg' : g • x = x := MulAction.mem_stabilizer_iff.1 hg
        refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
        change ((e.symm g : ↥S) : H) ∈ Z
        apply hsub
        refine Subgroup.mem_inf.2 ⟨(e.symm g).2, MulAction.mem_stabilizer_iff.2 ?_⟩
        rw [hcompat, e.apply_symm_apply]
        exact hg'
      by_cases hZ' : MulAction.stabilizer (PSL2 K) x = Z'
      · left
        refine le_antisymm (fun z hz => ?_) hsub
        have hzS : z ∈ S := hZS hz
        refine Subgroup.mem_inf.2 ⟨hzS, MulAction.mem_stabilizer_iff.2 ?_⟩
        have hmem : e ⟨z, hzS⟩ ∈ Z' := ⟨⟨z, hzS⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
        rw [← hZ'] at hmem
        have := MulAction.mem_stabilizer_iff.1 hmem
        rw [← hcompat ⟨z, hzS⟩ x] at this
        exact this
      · right
        have htop : Z' = ⊤ :=
          (Glauberman.Dickson.MaxStructure.isCoatom_stabilizer x).2 Z' (lt_of_le_of_ne hstab hZ')
        refine le_antisymm hZS (fun s hs => ?_)
        have hmem : e ⟨s, hs⟩ ∈ Z' := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨z, hz, hze⟩ := hmem
        have hzs : z = ⟨s, hs⟩ := e.injective hze
        have hz' : (z : H) ∈ Z := Subgroup.mem_subgroupOf.1 hz
        rw [hzs] at hz'
        exact hz'
    solv := by
      intro x
      have := psl2_stab_solvable (K := K) x
      let ι : ↥(S ⊓ MulAction.stabilizer H x) →* ↥(MulAction.stabilizer (PSL2 K) x) :=
        ((e.toMonoidHom).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (fun h => by
          rw [MulAction.mem_stabilizer_iff]
          have h1 := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h.2).2
          show e (Subgroup.inclusion inf_le_left h) • x = x
          rw [← hcompat]
          exact h1)
      refine Group.isSolvable_of_isSolvable_injective (f := ι) ?_
      intro a b hab
      have h1 := congrArg Subtype.val hab
      have h2 : (Subgroup.inclusion inf_le_left a : ↥S) = Subgroup.inclusion inf_le_left b :=
        e.injective h1
      exact Subgroup.inclusion_injective inf_le_left h2
    fix5 := fun a ha hord => by
      have hord' : orderOf (e ⟨a, ha⟩) = 5 := by
        have h1 : orderOf (e ⟨a, ha⟩) = orderOf (⟨a, ha⟩ : ↥S) :=
          orderOf_injective e.toMonoidHom e.injective ⟨a, ha⟩
        rw [h1, ← Subgroup.orderOf_coe ⟨a, ha⟩]
        exact hord
      obtain ⟨x, hx, huniq⟩ := psl2_fix5 hK hord'
      refine ⟨x, ?_, fun y hy => huniq y ?_⟩
      · show a • x = x
        rw [show a • x = e ⟨a, ha⟩ • x from hcompat ⟨a, ha⟩ x]
        exact hx
      · show e ⟨a, ha⟩ • y = y
        rw [← show a • y = e ⟨a, ha⟩ • y from hcompat ⟨a, ha⟩ y]
        exact hy
    fix3 := fun a ha ha1 x y z hxy hxz hyz hx hy hz => by
      have ha1' : e ⟨a, ha⟩ ≠ 1 := by
        intro h
        apply ha1
        have : (⟨a, ha⟩ : ↥S) = 1 := e.injective (by rw [h, map_one])
        exact congrArg Subtype.val this
      rw [hcompat ⟨a, ha⟩] at hx hy hz
      exact psl2_fix3 ha1' hxy hxz hyz hx hy hz
    card_H := by
      have h1 : Nat.card H ∣ Nat.card (MulAut (PSL2 K)) := Subgroup.card_dvd_of_injective ρ₀ hρ₀
      rwa [card_aut_psl2 hK] at h1
    quot := by
      have hcomm : ∀ a b : ComponentClassification.OuterAutomorphisms.Outer ↥S, a * b = b * a :=
        fun a b => (ComponentClassification.OuterAutomorphisms.equivalence e).injective (by
          rw [map_mul, map_mul]
          exact LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K _ _)
      have : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer ↥S) :=
        Group.isSolvable_of_comm hcomm
      exact CTP.solvable_quotient_of_outer S hSc }

theorem kfL225 : KFL225 := by
  intro H _ _ S hSn hSc hiso Y₀ hY P hP hPel hPcard
  have := hSn
  obtain ⟨q, hqp, hq2, hv, ⟨e0⟩⟩ := hiso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e := e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hK : Nat.card (GaloisField q.p q.exponent) = 5 ^ 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hqp, hq2]
  obtain ⟨Ω, _, hS⟩ := exists_setting S hSc hK e
  exact kfL225_of_setting hS Y₀ hY P hP hPel hPcard

end Instance

end L225

end Sec1511

end CFSG.RankThree.PartOne
