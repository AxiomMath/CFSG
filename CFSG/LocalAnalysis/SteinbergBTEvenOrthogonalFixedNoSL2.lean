module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.SteinbergBTEvenHigherLinearFixedNoSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBT

open Subgroup Matrix QuadraticMap Module CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (isometryGroup)

variable {K : Type} [Field K] {d : ℕ}

theorem inner_le_matrixProjectiveImage (Q : QuadraticForm K (Fin d → K)) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨h, rfl⟩ := matrixProjectiveProjection_surjective Q y
  exact ⟨_, matrixProjectiveConjugationHom_derived Q h⟩

theorem orthogonal_fixed_field_orderOf_four [Finite K] {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hαE : α ∈ matrixProjectiveImage Q)
    (hα : orderOf α = 2) {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hSα : matrixProjectiveConjugationHom Q S = α) (hσ : S.val.right ≠ 1)
    {L : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hL : CFSG.Assembly.IsComponentOf L
      (OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ centralizer {α})) :
    ∃ x : L, orderOf x = 4 := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, hk, hJs, -, ext, -, -, hextinj, hextInn, hextC, hextN, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hαE hα S hS hSα hσ
  set N := (extKappa Q ext).range with hNdef
  have hInnE := inner_le_matrixProjectiveImage Q
  have : Finite (MulAut (matrixProjectiveDerived Q)) := finite_mulAut
  have hLN : CFSG.Assembly.IsComponentOf L N := by
    refine isComponentOf_of_normal_of_comm (le_inf hextInn (hextC.trans inf_le_right))
      (fun y hy => mem_normalizer_of_normal_subgroupOf hextC hextN
        (mem_inf.2 ⟨hInnE hy.1, hy.2⟩)) ?_ hL
    intro x hx hxc y hy hyc
    have hx' : x ∈ matrixProjectiveImage Q ⊓ centralizer {α} ⊓
        centralizer ((extKappa Q ext).range : Set (MulAut (matrixProjectiveDerived Q))) :=
      mem_inf.2 ⟨mem_inf.2 ⟨hInnE hx.1, hx.2⟩, hxc⟩
    have hy' : y ∈ matrixProjectiveImage Q ⊓ centralizer {α} ⊓
        centralizer ((extKappa Q ext).range : Set (MulAut (matrixProjectiveDerived Q))) :=
      mem_inf.2 ⟨mem_inf.2 ⟨hInnE hy.1, hy.2⟩, hyc⟩
    rw [hcent] at hx' hy'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy'
    exact (Commute.zpow_zpow_self α i j).eq
  have : IsSimpleGroup N := (MonoidHom.ofInjective hextinj).symm.isSimpleGroup
  have hLeq : L = N := eq_of_isComponentOf_simple ‹IsSimpleGroup N› hLN
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ :=
    UnitaryHigher.evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  obtain ⟨hSS, hTT, -⟩ := hinv _ hαE hα S hS hSα
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfeven, -, -⟩ := card_descentField hf hK hσσ hσ
  obtain ⟨hfin, -, -, hQ₀, -⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField S.val.right) 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hk2 hk
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨Qc, ⟨ψ⟩, -, ⟨Tc, hTc3, hTcs⟩, -⟩ :=
    exists_coordinate_isometry hn (pairDescentForm hS) hQ₀ hdim
  have hT₀ : ∃ T₀ : Submodule (descentField S.val.right) (pairFix S),
      Module.finrank (descentField S.val.right) T₀ = 3 ∧ ∀ x ∈ T₀, pairDescentForm hS x = 0 := by
    refine ⟨Tc.map (ψ.toLinearEquiv.symm : (Fin (2 * n) → descentField S.val.right) →ₗ[_] _),
      ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hTc3]
    · rintro x ⟨y, hy, rfl⟩
      rw [← ψ.map_app]
      change Qc (ψ.toLinearEquiv (ψ.toLinearEquiv.symm y)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hTcs y hy
  obtain ⟨P, r, hr3, hP, hA, hAdim⟩ := CFSG.RankThree.Classical.exists_hypPair_tail_decomposition
    (Q := pairDescentForm hS) hQ₀ hT₀
  obtain ⟨g, hg, hg4⟩ := SteinbergCD.exists_orderOf_eq_four_orthogonal hQ₀ hP hr3 hA hAdim
  refine ⟨⟨extKappa Q ext ⟨g, hg⟩, hLeq ▸ ⟨⟨g, hg⟩, rfl⟩⟩, ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_injective _ hextinj, Subgroup.orderOf_mk, hg4]

theorem orthogonal_fixed_symmetry_orderOf_four [Finite K] {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin (2 * n) → K} (hv : Q v = 1)
    (hvH : symmetryGL Q v ∉ matrixDerived Q)
    {L : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hL : CFSG.Assembly.IsComponentOf L
      (OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ centralizer {symmetryAut Q v})) :
    ∃ x : L, orderOf x = 4 := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hd : 1 ≤ 2 * n := by omega
  have hd3 : 3 ≤ 2 * n := by omega
  have hInnE := inner_le_matrixProjectiveImage Q
  set Y := OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓
    centralizer {symmetryAut Q v} with hY
  have hle : derivedSymmetryCentralizer Q v ≤ matrixIsometries Q := fun g hg => hg.2.1
  set ψ : derivedSymmetryCentralizer Q v →* MulAut (matrixProjectiveDerived Q) :=
    (matrixProjectiveConjugationHom Q).comp
      ((matrixIsometryInclusion Q).comp (Subgroup.inclusion hle)) with hψ
  have hψinj : Function.Injective ψ :=
    (kappa_inclusion_injective hQ hT hE hd).comp (Subgroup.inclusion_injective hle)
  have hNY : ψ.range ≤ Y := by
    rintro _ ⟨g, rfl⟩
    have hgD : (g : GL (Fin (2 * n)) K) ∈ matrixDerived Q := g.2.1
    refine ⟨⟨matrixProjectiveProjection Q
      (⟨(g : GL (Fin (2 * n)) K), hgD⟩ : matrixDerived Q), ?_⟩, ?_⟩
    · exact (kappa_derived_eq_conj (⟨(g : GL (Fin (2 * n)) K), hgD⟩ : matrixDerived Q)).symm
    · have hc : Commute (Subgroup.inclusion hle g) (symmetryIsometry Q v) :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2.2)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hc.map (matrixIsometryInclusion Q)).map (matrixProjectiveConjugationHom Q)).eq
  have hNnormal : (ψ.range.subgroupOf Y).Normal := by
    constructor
    intro x hx y
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨g, hg⟩ := hx
    obtain ⟨S, hS, hSy⟩ := exists_unit_rep (hInnE y.2.1)
    have hα : Commute (matrixProjectiveConjugationHom Q S) (symmetryAut Q v) := by
      rw [hSy]
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    have hSv := conj_inclusion_eq_of_commute hQ hT hE hd hS hα
    refine ⟨⟨_, conjIsometry_mem hSv (g := Subgroup.inclusion hle g) g.2⟩, ?_⟩
    change matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (conjIsometry S (Subgroup.inclusion hle g))) =
      (y : MulAut (matrixProjectiveDerived Q)) * x * (y : MulAut (matrixProjectiveDerived Q))⁻¹
    rw [← conj_kappa_inclusion, hSy, ← hg]
    rfl
  have hkey : ∀ x ∈ Y, x ∈ centralizer (ψ.range : Set (MulAut (matrixProjectiveDerived Q))) →
      x = 1 ∨ x = symmetryAut Q v := by
    intro x hx hxc
    obtain ⟨S, hS, hSx⟩ := exists_unit_rep (hInnE hx.1)
    have hα : Commute (matrixProjectiveConjugationHom Q S) (symmetryAut Q v) := by
      rw [hSx]
      exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hNc : ∀ g : matrixIsometries Q,
        (g : GL (Fin (2 * n)) K) ∈ derivedSymmetryCentralizer Q v →
        Commute (matrixProjectiveConjugationHom Q S)
          (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g)) := by
      intro g hg
      have h1 := Subgroup.mem_centralizer_iff.mp hxc (ψ ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
      rw [← hSx] at h1
      exact h1.symm
    rcases eq_one_or_eq_of_commute hQ hT hE hd3 hv hS hα hNc with h | h
    · left
      rw [← hSx, h, map_one]
    · right
      rw [← hSx, h]
  have hcomm : ∀ x ∈ Y, x ∈ centralizer (ψ.range : Set (MulAut (matrixProjectiveDerived Q))) →
      ∀ y ∈ Y, y ∈ centralizer (ψ.range : Set (MulAut (matrixProjectiveDerived Q))) →
        x * y = y * x := by
    intro x hx hxc y hy hyc
    rcases hkey x hx hxc with rfl | rfl <;> rcases hkey y hy hyc with rfl | rfl <;> simp
  have : Finite (MulAut (matrixProjectiveDerived Q)) := finite_mulAut
  have hLN : CFSG.Assembly.IsComponentOf L ψ.range :=
    isComponentOf_of_normal_of_comm hNY
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNY hNnormal hy) hcomm hL
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hle' : derivedSymmetryCentralizer Q v ≤ symmetryCentralizer Q v := fun g hg => hg.2
  set φ : derivedSymmetryCentralizer Q v →* bilinIsometryGroup (vQuotForm Q v) :=
    ((symmetryRestrict hQ hv).comp (Subgroup.inclusion hle')).codRestrict _
      (fun g => symmetryRestrict_mem hQ hv _) with hφ
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg, hgy⟩ : y.val ∈ ((derivedSymmetryCentralizer Q v).subgroupOf
        (symmetryCentralizer Q v)).map (symmetryRestrict hQ hv) := by
      rw [map_derived_symmetryRestrict hQ hv hE]
      exact y.2
    exact ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, Subtype.ext hgy⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : symmetryRestrict hQ hv (Subgroup.inclusion hle' x) = 1 :=
      congrArg Subtype.val hx
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hx1 with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ x.2.1) hvH
  let eO : derivedSymmetryCentralizer Q v ≃* isometryGroup (vQuotForm Q v) :=
    (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).trans (bilinIsometryGroupEquiv _)
  have hdimU : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by
    have := finrank_vQuot hQ hv
    omega
  have : Finite (GL (Fin (2 * n)) K) := Finite.of_injective Units.val Units.val_injective
  rcases symplectic_component_dichotomy hψinj hLN hK (by omega : 1 ≤ n - 1) (by omega)
      (vQuotForm Q v) (vQuotForm_isAlt Q v) (vQuotForm_nondegenerate hQ hv0) hdimU eO with
    ⟨-, -, -, -, ⟨eX⟩⟩ | ⟨-, -, hXc, -, -, ⟨eA⟩⟩
  · obtain ⟨y, hy, -⟩ := SteinbergCD.exists_orderOf_eq_four_statedSp (k := K)
      CharTwo.two_eq_zero (by omega : 2 ≤ n - 1)
    exact ⟨eX.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  · obtain ⟨y, hy⟩ := exists_orderOf_eq_four_alternating_six
    exact ⟨((MulEquiv.subgroupCongr hXc).trans eA).symm y, by rw [MulEquiv.orderOf_eq, hy]⟩

theorem orthogonal_fixed_linear_false [Finite K] {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : orderOf α = 2) {S : similarityPairs Q}
    (hSα : matrixProjectiveConjugationHom Q S = α) (hσ : S.val.right = 1)
    {L : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hL : CFSG.Assembly.IsComponentOf L
      (OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ centralizer {α}))
    (h4 : ∀ x : L, orderOf x ≠ 4) : False := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
    UnitaryHigher.evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
      F.ker := by
    rw [MonoidHom.mem_ker, hF, hσ]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = α :=
    (show matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
      matrixProjectiveConjugationHom Q S from hs).trans hSα
  rw [← hs'] at hL hα
  have hss : s * s = 1 := by
    apply isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
    have h2 := pow_orderOf_eq_one (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    rw [hα] at h2
    rw [← pow_two]
    exact h2
  have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    rw [h1, map_one, map_one, orderOf_one] at hα
    exact absurd hα (by norm_num)
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · exact no_component_of_two_le_rank hQ hT hE _ le_rfl (inner_le_matrixProjectiveImage Q) s hα
      hr _ ((isComponentOf_iff_isComponent_subgroupOf hL.1).mp hL)
  · obtain ⟨v, hv, hsv⟩ := exists_symmetry_of_rank_le_one hQ s.2
      (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry Q v := Subtype.ext hsv
    subst hincl
    have hvH : symmetryGL Q v ∉ matrixDerived Q := fun hmemD => hr
      (two_le_rank_of_mem_derived hQ hT hE ⟨symmetryGL Q v, hmemD⟩
        (fun h => hs1 (congrArg Subtype.val h)) (Subtype.ext (symmetryGL_mul_self Q v)))
    obtain ⟨x, hx⟩ := orthogonal_fixed_symmetry_orderOf_four hf hK hn hQ hT hE hv hvH hL
    exact h4 x hx

end CFSG.LocalAnalysis.SteinbergBT
