module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedRange
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
public import CFSG.RankThree.PartOne.S11d.OrthLayer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4N2ChartCommute
import CFSG.LocalAnalysis.StandardType.GGF4N2Rank
import CFSG.LocalAnalysis.StandardType.GGF4N2ActualH0
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
import CFSG.LieType.SeitzGeneration.OrthManyRank
import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualModel
import CFSG.RankThree.PartOne.S11d.OrthCyclic
import CFSG.RankThree.PartOne.S15K.OrthMult
import CFSG.ClassicalInvolution.WeakCT.Center

public section

namespace CFSG.StandardType.N2GoodLine

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

omit [CharP F 2] in
theorem natDegree_eq_three (hF : Nat.card F = 4) {x : V ≃ₗ[F] V} (hx : x ^ 7 = 1) {h : F[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) : h.natDegree = 3 := by
  rw [CFSG.LieType.SeitzGeneration.natDegree_eq_orderOf (by norm_num) hx hh hne, hF]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

omit [CharP F 2] in
theorem ne_reciprocalPolynomial (hF : Nat.card F = 4) {x : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q 7 x) {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ X - 1) : h ≠ reciprocalPolynomial h := by
  intro hself
  obtain ⟨d, hd, -⟩ := hx.selfDualModel ⟨3, rfl⟩ hh hne hself
  rw [natDegree_eq_three hF hx.pow_eq_one hh hne] at hd
  omega

omit [CharP F 2] in
theorem primaryMultiplicity_le_one_and_finrank_fixedSpace_le_two (hF : Nat.card F = 4)
    (hV : finrank F V = 8) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q 7 x) (hx1 : x ≠ 1) :
    (∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → primaryMultiplicity x.toLinearMap h ≤ 1) ∧
      finrank F (fixedSpace x) ≤ 2 := by
  classical
  have hsq := hx.squarefree_minpoly
  have hsum : ∑ a : primaryFactors x.toLinearMap,
      finrank F (primaryComponent x.toLinearMap (a : F[X])) = 8 := by
    rw [← hV]
    exact (finrank_eq_sum_primaryComponent (x := x.toLinearMap) hsq).symm
  have hle2 : ∀ a ∈ primaryFactors x.toLinearMap, ∀ b ∈ primaryFactors x.toLinearMap, a ≠ b →
      finrank F (primaryComponent x.toLinearMap a) +
        finrank F (primaryComponent x.toLinearMap b) ≤ 8 := by
    intro a ha b hb hab
    calc _ = ∑ c ∈ ({⟨a, ha⟩, ⟨b, hb⟩} : Finset (primaryFactors x.toLinearMap)),
          finrank F (primaryComponent x.toLinearMap (c : F[X])) :=
          (Finset.sum_pair fun e => hab (congrArg Subtype.val e)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 8 := hsum
  have hle3 : ∀ a ∈ primaryFactors x.toLinearMap, ∀ b ∈ primaryFactors x.toLinearMap,
      ∀ c ∈ primaryFactors x.toLinearMap, a ≠ b → a ≠ c → b ≠ c →
      finrank F (primaryComponent x.toLinearMap a) + finrank F (primaryComponent x.toLinearMap b) +
        finrank F (primaryComponent x.toLinearMap c) ≤ 8 := by
    intro a ha b hb c hc hab hac hbc
    have hbc' : (⟨b, hb⟩ : primaryFactors x.toLinearMap) ≠ ⟨c, hc⟩ :=
      fun e => hbc (congrArg Subtype.val e)
    have hnot : (⟨a, ha⟩ : primaryFactors x.toLinearMap) ∉
        ({⟨b, hb⟩, ⟨c, hc⟩} : Finset (primaryFactors x.toLinearMap)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
      tauto
    calc _ = ∑ d ∈ ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Finset (primaryFactors x.toLinearMap)),
          finrank F (primaryComponent x.toLinearMap (d : F[X])) := by
          rw [Finset.sum_insert hnot, Finset.sum_pair hbc', add_assoc]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 8 := hsum
  have hdim : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      finrank F (primaryComponent x.toLinearMap h) = 3 * primaryMultiplicity x.toLinearMap h ∧
        1 ≤ primaryMultiplicity x.toLinearMap h := by
    intro h hh hne
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have h3 : finrank F (primaryComponent x.toLinearMap h) =
        3 * primaryMultiplicity x.toLinearMap h := by
      rw [finrank_primaryComponent (x := x.toLinearMap) (a := h),
        natDegree_eq_three hF hx.pow_eq_one hh hne]
    have hne0 : finrank F (primaryComponent x.toLinearMap h) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact primaryComponent_ne_bot hsq hh
    exact ⟨h3, by omega⟩
  have hpair : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      reciprocalPolynomial h ∈ primaryFactors x.toLinearMap ∧ h ≠ reciprocalPolynomial h ∧
        reciprocalPolynomial h ≠ X - 1 := by
    intro h hh hne
    refine ⟨hx.reciprocalPolynomial_mem hh, ne_reciprocalPolynomial hF hx hh hne, fun he => ?_⟩
    have h3 : (reciprocalPolynomial h).natDegree = 3 := by
      rw [natDegree_reciprocalPolynomial (hx.coeff_zero_ne hh),
        natDegree_eq_three hF hx.pow_eq_one hh hne]
    have h1 : (X - 1 : F[X]).natDegree = 1 := by compute_degree!
    rw [he] at h3
    omega
  refine ⟨fun h hh hne => ?_, ?_⟩
  · obtain ⟨hh', hself, hne'⟩ := hpair h hh hne
    have h12 := hle2 h hh _ hh' hself
    obtain ⟨h₁, -⟩ := hdim h hh hne
    obtain ⟨h₂, h₂'⟩ := hdim _ hh' hne'
    omega
  · obtain ⟨h₀, hh₀, hne₀⟩ := CFSG.AGLEmbedding.exists_primaryFactor_ne_X_sub_one hsq
      (fun h1 => hx1 (LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun h1 v))
    have hne₀' : h₀ ≠ X - 1 := by rwa [← C_1]
    obtain ⟨hh₀', hself₀, hne₀''⟩ := hpair h₀ hh₀ hne₀'
    by_cases hX1 : (X - 1 : F[X]) ∈ primaryFactors x.toLinearMap
    · have h3 := hle3 _ hX1 _ hh₀ _ hh₀' hne₀'.symm hne₀''.symm hself₀
      obtain ⟨h₁, h₁'⟩ := hdim h₀ hh₀ hne₀'
      obtain ⟨h₂, h₂'⟩ := hdim _ hh₀' hne₀''
      rw [fixedSpace_eq_primaryComponent]
      omega
    · rw [fixedSpace_eq_bot_of_not_mem hX1, finrank_bot]
      norm_num

theorem isSolvable_isometryCentralizer (hF : Nat.card F = 4) (hQ : (polarBilin Q).Nondegenerate)
    (hV : finrank F V = 8) {x : V ≃ₗ[F] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx7 : orderOf x = 7) : Group.IsSolvable ↥(isometryCentralizer Q x) := by
  have hpl : 7 ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hx : OddOrderIsometry Q 7 x :=
    S15K.oddOrderIsometry_of_order hQ (by norm_num) hpl hxO hx7
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx7
    norm_num at hx7
  obtain ⟨hmult, hW⟩ := primaryMultiplicity_le_one_and_finrank_fixedSpace_le_two hF hV hx hx1
  have hfix : ∀ g ∈ (isometryRestrictFixed Q x).ker, ∀ w ∈ fixedSpace x,
      (g : V ≃ₗ[F] V) w = w := by
    intro g hg w hw
    have h1 := congrArg (fun e : fixedSpace x ≃ₗ[F] fixedSpace x => ((e ⟨w, hw⟩ : fixedSpace x) : V))
      (MonoidHom.mem_ker.mp hg)
    simpa [coe_isometryRestrictFixed] using h1
  have : Group.IsSolvable ↥(isometryRestrictFixed Q x).ker := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hx.commute_of_fixes_fixedSpace hmult (Subgroup.mem_inf.mp a.1.2).2
      (Subgroup.mem_inf.mp b.1.2).2 (hfix a.1 a.2) (hfix b.1 b.2)))
  have hle : (isometryRestrictFixed Q x).range ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
    rintro _ ⟨g, rfl⟩
    exact isometryRestrictFixed_mem_orthogonalGroup g
  have : Group.IsSolvable
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
      hx.polarBilin_fixed_nondegenerate hW
  have : Group.IsSolvable ↥(isometryRestrictFixed Q x).range :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_ker_le_range (isometryRestrictFixed Q x).ker.subtype
    (isometryRestrictFixed Q x).rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem isSolvable_centralizer_projOrthDerived (hF : Nat.card F = 4)
    (hQ : (polarBilin Q).Nondegenerate) (hV : finrank F V = 8) {t : ProjOrthDerived Q}
    (ht : orderOf t = 7) :
    Group.IsSolvable ↥(Subgroup.centralizer ({t} : Set (ProjOrthDerived Q))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨y, rfl⟩ := piOrth_surjective (Q := Q) t
  have hy7 : orderOf (y : V ≃ₗ[F] V) = 7 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective (piOrth Q) (piOrth_injective hQ) y]
    exact ht
  have hyO : (y : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    N2Chart.commutator_le_self _ y.2
  have := isSolvable_isometryCentralizer hF hQ hV hyO hy7
  let ι : ↥((isometryCentralizer Q (y : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) →*
      ↥(isometryCentralizer Q (y : V ≃ₗ[F] V)) :=
    ((orthDerived Q).subtype.comp (Subgroup.subtype _)).codRestrict _ fun g =>
      Subgroup.mem_subgroupOf.mp g.2
  have : Group.IsSolvable ↥((isometryCentralizer Q (y : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :=
    solvable_of_solvable_injective (f := ι) fun a b hab => Subtype.ext (Subtype.ext (by
      have h := congrArg Subtype.val hab
      exact h))
  rw [← centralizerImage_eq hQ y, centralizerImage]
  exact solvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)

theorem isSolvable_inf_centralizer_of_mulEquiv {G : Type} [Group G] {L : Subgroup G}
    (hF : Nat.card F = 4) (hQ : (polarBilin Q).Nondegenerate) (hV : finrank F V = 8)
    (θ : ↥L ≃* ProjOrthDerived Q) {S : Set G} {m : G} (hmS : m ∈ S) (hmL : m ∈ L)
    (hm7 : orderOf m = 7) : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer S) := by
  have ht : orderOf (θ ⟨m, hmL⟩) = 7 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hm7
  have := isSolvable_centralizer_projOrthDerived hF hQ hV ht
  let f : ↥(L ⊓ Subgroup.centralizer S) →* ProjOrthDerived Q :=
    θ.toMonoidHom.comp (Subgroup.inclusion inf_le_left)
  have hf : ∀ g, f g ∈ Subgroup.centralizer ({θ ⟨m, hmL⟩} : Set (ProjOrthDerived Q)) := by
    intro g
    have hc : Subgroup.inclusion inf_le_left g * (⟨m, hmL⟩ : L) =
        ⟨m, hmL⟩ * Subgroup.inclusion inf_le_left g :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp g.2).2 m hmS).symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (map_mul θ (Subgroup.inclusion inf_le_left g) ⟨m, hmL⟩).symm.trans
      ((congrArg θ hc).trans (map_mul θ ⟨m, hmL⟩ (Subgroup.inclusion inf_le_left g)))
  have hinj : Function.Injective f := θ.injective.comp (Subgroup.inclusion_injective inf_le_left)
  exact solvable_of_solvable_injective (f := f.codRestrict _ hf) fun a b hab =>
    hinj (congrArg Subtype.val hab)

end CFSG.StandardType.N2GoodLine

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.Open CFSG.RankThree.Classical2 CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggF4N2_exists_orderSeven_mem_blockSL
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) :
    ∃ m ∈ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ, orderOf m = 7 := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2), orderOf A = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    exact exists_prime_orderOf_dvd_card' 7 (by rw [N2Chart.card_SL3_four]; norm_num)
  have hinj := comp_blockSL_injective hψ (by norm_num : 0 + 3 ≤ 6) (by norm_num)
  exact ⟨ψ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num) A),
    Subgroup.mem_map_of_mem ψ (MonoidHom.mem_range.mpr ⟨A, rfl⟩),
    (orderOf_injective _ hinj A).trans hA⟩

section OriginalLines

theorem ggF4N2_goodLines_isSolvable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (ψ₁ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ₁ : ψ₁.ker ≤ Subgroup.center _)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer
      (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G)) ∧
    ∀ t ∈ Subgroup.centralizer (J : Set G),
      Group.IsSolvable ↥(L.map (MulAut.conj t).toMonoidHom ⊓ Subgroup.centralizer
        (((blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ : Subgroup G) : Set G)) := by
  classical
  have hJL : J ≤ L := hR.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hMJ : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ₁ ≤ J := by
    rw [← hJ₁, MonoidHom.range_comp]
    exact Subgroup.map_mono ggN2_blockSL30_le_blockSL40
  obtain ⟨m, hmM, hm7⟩ := ggF4N2_exists_orderSeven_mem_blockSL ψ₁ hψ₁
  have hmL : m ∈ L := hJL (hMJ hmM)
  have hZ := ggN2Center_eq_bot_of_centralImage hL
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := ggN2Model_of_centralImage hL eQ
  have hF4 : Nat.card F = 4 := by simpa using hF
  have : CharP F 2 := by
    let : Fintype F := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 2) (by simpa using hF4)
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus 4 F b c)
  let θ : ↥L ≃* ProjOrthDerived (quadMinus 4 F b c) := e.trans e₂
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 F hbc
  have hdim : finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  refine ⟨N2GoodLine.isSolvable_inf_centralizer_of_mulEquiv hF4 hQ hdim θ hmM hmL hm7,
    fun t ht => ?_⟩
  have hmt : t * m * t⁻¹ = m := by
    rw [← Subgroup.mem_centralizer_iff.mp ht m (hMJ hmM), mul_inv_cancel_right]
  let θ' : ↥(L.map (MulAut.conj t).toMonoidHom) ≃* ProjOrthDerived (quadMinus 4 F b c) :=
    (L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans θ
  exact N2GoodLine.isSolvable_inf_centralizer_of_mulEquiv hF4 hQ hdim θ' hmM
    (Subgroup.mem_map.mpr ⟨m, hmL, hmt⟩) hm7

end OriginalLines

end CFSG.StandardType

end
