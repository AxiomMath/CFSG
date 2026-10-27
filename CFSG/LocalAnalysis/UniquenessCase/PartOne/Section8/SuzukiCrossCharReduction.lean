module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.RepresentationTheory.MinimalLinearCover
public import CFSG.RepresentationTheory.SmallPermutationOfMinimalDegree
public import CFSG.RepresentationTheory.NormalAbelianScalarOfSmallPermutation
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiCrossCharKernel
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound
public import CFSG.Quasithin.Background.KnownMultOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiCrossCharBorel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.GroupTheory.SteinbergBKMinimalCoverPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open
open scoped TensorProduct commutatorElement

theorem exists_minimal_perfect_linear_cover
    {F W Q : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] [Group Q] [Group.IsPerfect Q]
    (Γ : Subgroup (W ≃ₗ[F] W)) (π : Γ →* Q) (hπ : Function.Surjective π) :
    ∃ H : Subgroup Γ, H.map π = ⊤ ∧
      (∀ J : Subgroup H, J.map (π.comp H.subtype) = ⊤ → J = ⊤) ∧
      Group.IsPerfect H ∧ Group.IsNilpotent (π.comp H.subtype).ker := by
  classical
  have : Finite W := Module.finite_of_finite F
  have : Finite (W ≃ₗ[F] W) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  obtain ⟨H, hH, hmin⟩ := CFSG.RankThree.GroupTheory.SteinbergBK.exists_minimal_cover π hπ
  have hπH : Function.Surjective (π.comp H.subtype) := by
    intro q
    have hq : q ∈ H.map π := by rw [hH]; exact Subgroup.mem_top q
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨⟨h, hh⟩, rfl⟩
  have hminH : ∀ J : Subgroup H, J.map (π.comp H.subtype) = ⊤ → J = ⊤ := by
    intro J hJ
    have heq : J.map H.subtype = H :=
      hmin _ (Subgroup.map_subtype_le J) (by rw [Subgroup.map_map]; exact hJ)
    apply le_antisymm le_top
    intro h _
    have hh : (h : Γ) ∈ J.map H.subtype := heq.symm ▸ h.2
    obtain ⟨j, hj, hjh⟩ := hh
    rwa [Subtype.ext hjh] at hj
  refine ⟨H, hH, hminH, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.isPerfect_of_minimal
      hπH hminH inferInstance
  · exact CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.isNilpotent_ker_of_minimal hπH hminH

theorem exists_minimal_suzuki_linear_system
    {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (Γ : Subgroup (W ≃ₗ[F] W)) (N : Subgroup Γ) [N.Normal]
    {n : ℕ} (_hn : 3 ≤ n) (hSz : UC22.IsSz (Γ ⧸ N) n) :
    ∃ H : Subgroup Γ, H.map (QuotientGroup.mk' N) = ⊤ ∧
      (∀ J : Subgroup H, J.map ((QuotientGroup.mk' N).comp H.subtype) = ⊤ → J = ⊤) ∧
      Group.IsPerfect H ∧ Group.IsNilpotent ((QuotientGroup.mk' N).comp H.subtype).ker ∧
      ((Subgroup.center (W ≃ₗ[F] W)).comap (Γ.subtype.comp H.subtype)) ≤
        ((QuotientGroup.mk' N).comp H.subtype).ker := by
  have hQ := hSz.suzukiModel.2
  have : Group.IsPerfect (Γ ⧸ N) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.isPerfect_of_suzukiModel hQ
  obtain ⟨H, hH, hmin, hperf, hnil⟩ := exists_minimal_perfect_linear_cover Γ
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hπ : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
    intro q
    have hq : q ∈ H.map (QuotientGroup.mk' N) := by rw [hH]; exact Subgroup.mem_top q
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨⟨h, hh⟩, rfl⟩
  have hZ : Subgroup.center (Γ ⧸ N) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.center_eq_bot_of_isSz hSz
  refine ⟨H, hH, hmin, hperf, hnil, ?_⟩
  have hc : (Subgroup.center (W ≃ₗ[F] W)).comap (Γ.subtype.comp H.subtype) ≤
      Subgroup.center H := Subgroup.comap_center_le_center
        (f := Γ.subtype.comp H.subtype) (Γ.subtype_injective.comp H.subtype_injective)
  exact hc.trans (((QuotientGroup.mk' N).comp H.subtype).center_le_ker hπ hZ)

theorem exists_faithful_baseChange_linear_action
    {F k W : Type} [Field F] [Field k] [Algebra F k]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    (Γ : Subgroup (W ≃ₗ[F] W)) :
    ∃ ρ : Γ →* ((k ⊗[F] W) ≃ₗ[k] (k ⊗[F] W)), Function.Injective ρ ∧
      Module.finrank k (k ⊗[F] W) = Module.finrank F W := by
  let σ : Representation F Γ W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp Γ.subtype
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply Γ.subtype_injective
    apply LinearEquiv.toLinearMap_injective
    exact hxy
  let τ := CFSG.Theory.Representation.extendScalars k σ
  let ρ := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (k ⊗[F] W)).toMonoidHom.comp
    τ.asGroupHom
  refine ⟨ρ, ?_, Module.finrank_baseChange⟩
  intro x y hxy
  apply (CFSG.Theory.Representation.extendScalars_faithful_iff k σ).mp hσ
  have hu := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (k ⊗[F] W)).injective hxy
  exact congrArg Units.val hu

theorem fourteen_le_finrank_of_faithful_suzuki
    {Q k V : Type} [Group Q]
    [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (hQ : UC22.IsSz Q n) (h2 : (2 : k) ≠ 0)
    (ρ : Q →* (V ≃ₗ[k] V)) (hρ : Function.Injective ρ) :
    14 ≤ Module.finrank k V := by
  obtain ⟨_, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hQ.suzukiModel.2
  let σ : CFSG.Blueprint.suzukiGroup a K →* Module.End k V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.comp e.symm.toMonoidHom)
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply e.symm.injective
    apply hρ
    exact LinearEquiv.toLinearMap_injective hxy
  have hbound := suzuki_borel_cross_char_degree_two_mul ha hK h2 σ hσ
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    change 2 ^ 3 ≤ 2 ^ (2 * a + 1)
    exact Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 2 * a + 1)
  omega

theorem exists_minimal_suzuki_irreducible_linear_system
    {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (hF : ringChar F ≠ 2)
    (Γ : Subgroup (W ≃ₗ[F] W)) (N : Subgroup Γ) [N.Normal]
    {n : ℕ} (hn : 3 ≤ n) (hSz : UC22.IsSz (Γ ⧸ N) n) :
    ∃ (V L : Type) (_ : AddCommGroup V) (_ : Module (AlgebraicClosure F) V)
      (_ : Module.Finite (AlgebraicClosure F) V) (_ : Group L) (_ : Finite L)
      (π : L →* (Γ ⧸ N)) (ρ : Representation (AlgebraicClosure F) L V),
      Function.Surjective π ∧
      (∀ J : Subgroup L, J.map π = ⊤ → J = ⊤) ∧
      Group.IsPerfect L ∧ Group.IsNilpotent π.ker ∧
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Module.finrank (AlgebraicClosure F) V ≤ Module.finrank F W ∧
      (∀ (r : ℕ) (μ : L →* Matrix.GeneralLinearGroup (Fin r) (AlgebraicClosure F)),
        μ ≠ 1 → Module.finrank (AlgebraicClosure F) V ≤ r) ∧
      (∀ (Ω : Type) [Finite Ω], Nat.card Ω ≤ Module.finrank (AlgebraicClosure F) V →
        ∀ φ : L →* Equiv.Perm Ω, φ = 1) := by
  classical
  have : IsSimpleGroup (Γ ⧸ N) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  obtain ⟨H, hH, hmin, hperf, hnil, _⟩ :=
    exists_minimal_suzuki_linear_system Γ N hn hSz
  let πH := (QuotientGroup.mk' N).comp H.subtype
  have hπH : Function.Surjective πH := by
    intro q
    have hq : q ∈ H.map (QuotientGroup.mk' N) := by rw [hH]; exact Subgroup.mem_top q
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨⟨h, hh⟩, rfl⟩
  have : Finite W := Module.finite_of_finite F
  have : Finite (W ≃ₗ[F] W) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have : Finite H := inferInstance
  obtain ⟨τ, hτ, hdim⟩ := exists_faithful_baseChange_linear_action
    (k := AlgebraicClosure F) Γ
  let σH : Representation (AlgebraicClosure F) H ((AlgebraicClosure F) ⊗[F] W) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (τ.comp H.subtype)
  have hσH : Function.Injective σH := by
    intro x y hxy
    exact H.subtype_injective (hτ (LinearEquiv.toLinearMap_injective hxy))
  have hminH : ∀ J : Subgroup H, J ≠ ⊤ → J.map πH ≠ ⊤ := by
    intro J hJ htop
    exact hJ (hmin J htop)
  obtain ⟨m, V, _, _, _, σ, hmd, hdimV, hirr, _, _, _, hLperf, hLfin,
    π, hfac, hπ, hnilπ, hminL, hminDegree⟩ :=
    CFSG.RepresentationTheory.exists_minimal_linear_constituent_image
      hperf πH hπH hnil hminH σH hσH
  let L := σ.asGroupHom.range
  let ρ : Representation (AlgebraicClosure F) L V :=
    (Units.coeHom (Module.End (AlgebraicClosure F) V)).comp L.subtype
  let q : H →* L := σ.asGroupHom.rangeRestrict
  have hq : Function.Surjective q := σ.asGroupHom.rangeRestrict_surjective
  have hcomp : ρ.comp q = σ := by
    ext h v
    rfl
  have hρirr : ρ.IsIrreducible := by
    apply (TauCeti.isIrreducible_comp_surjective_iff q hq ρ).mp
    rwa [hcomp]
  have hρ : Function.Injective ρ := Units.val_injective.comp L.subtype_injective
  have hFbar : ringChar (AlgebraicClosure F) ≠ 2 := by
    rwa [← Algebra.ringChar_eq F (AlgebraicClosure F)]
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, hLfin,
    π, ρ, hπ, ?_, hLperf, hnilπ, hρ, hρirr, ?_, ?_, ?_⟩
  · intro J hJ
    by_contra hne
    exact hminL J hne hJ
  · rw [hdimV]
    rwa [hdim] at hmd
  · intro r μ hμ
    rw [hdimV]
    exact hminDegree r μ hμ
  · intro Ω _ hΩ φ
    apply CFSG.RepresentationTheory.perm_eq_one_of_minimal_linear_degree
      (Ring.two_ne_zero hFbar) hminDegree (m := m)
    rwa [hdimV] at hΩ

theorem minimal_linear_system_scalar_bounds
    {k L V : Type} [Field k] [IsAlgClosed k] [Group L] [Finite L]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (h2 : (2 : k) ≠ 0) (ρ : Representation k L V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (hmin : ∀ (r : ℕ) (μ : L →* Matrix.GeneralLinearGroup (Fin r) k),
      μ ≠ 1 → Module.finrank k V ≤ r) :
    (∀ (A : Subgroup L), A.Normal → IsMulCommutative A →
      A ≤ Subgroup.center L ∧ IsCyclic A) ∧
    (∀ (Q : Subgroup L), Q.Normal →
      (∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) →
      Nat.card (Q ⧸ Subgroup.center Q) ≤ Module.finrank k V ^ 2) := by
  have : Nontrivial V := hirr.nontrivial
  have hperm : ∀ (Ω : Type) [Finite Ω], Nat.card Ω ≤ Module.finrank k V →
      ∀ φ : L →* Equiv.Perm Ω, φ = 1 := by
    intro Ω _ hΩ φ
    exact CFSG.RepresentationTheory.perm_eq_one_of_minimal_linear_degree h2 hmin hΩ φ
  have hA : ∀ (A : Subgroup L) [A.Normal], IsMulCommutative A →
      ∀ a ∈ A, ∃ c : k, ρ a = c • (1 : Module.End k V) := by
    intro A _ hcomm a ha
    exact CFSG.RepresentationTheory.normal_abelian_scalar_of_small_permutation
      ρ hirr hperm A hcomm ⟨a, ha⟩
  constructor
  · intro A hAn hcomm
    have : A.Normal := hAn
    exact CFSG.RepresentationTheory.scalar_subgroup_le_center_and_isCyclic ρ hρ A (hA A hcomm)
  · intro Q hQn hclass
    have : Q.Normal := hQn
    exact CFSG.RepresentationTheory.card_quotient_center_le_finrank_sq_of_scalar ρ hρ hA Q hclass

theorem minimal_suzuki_linear_kernel_le_center
    {k L V Q : Type} [Field k] [IsAlgClosed k] [Group L] [Finite L] [Group.IsPerfect L]
    [Group Q] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (h2 : (2 : k) ≠ 0) (ρ : Representation k L V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (hminDegree : ∀ (r : ℕ) (μ : L →* Matrix.GeneralLinearGroup (Fin r) k),
      μ ≠ 1 → Module.finrank k V ≤ r)
    (hd : Module.finrank k V ≤ 13) (π : L →* Q) (hπ : Function.Surjective π)
    (hmin : ∀ J : Subgroup L, J.map π = ⊤ → J = ⊤)
    {n : ℕ} (hQ : UC22.IsSz Q n) (hn : 3 ≤ n) :
    π.ker ≤ Subgroup.center L := by
  obtain ⟨hA, hB⟩ := minimal_linear_system_scalar_bounds h2 ρ hρ hirr hminDegree
  apply minimal_suzuki_kernel_le_center_of_scalar_bounds π hπ hmin hQ.suzukiModel.2 hn
    (fun A hAn hAc => (hA A hAn hAc).1)
  intro R _ hRn hRcl
  exact (hB R hRn hRcl).trans (by nlinarith)

theorem exists_suzuki_perfect_central_linear_cover
    {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (hF : ringChar F ≠ 2)
    (Γ : Subgroup (W ≃ₗ[F] W)) (N : Subgroup Γ) [N.Normal]
    {n : ℕ} (hn : 3 ≤ n) (hSz : UC22.IsSz (Γ ⧸ N) n) (hd : Module.finrank F W ≤ 13) :
    ∃ (V L : Type) (_ : AddCommGroup V) (_ : Module (AlgebraicClosure F) V)
      (_ : Module.Finite (AlgebraicClosure F) V) (_ : Group L) (_ : Finite L)
      (π : L →* (Γ ⧸ N)) (ρ : Representation (AlgebraicClosure F) L V),
      Function.Surjective π ∧ Group.IsPerfect L ∧ π.ker ≤ Subgroup.center L ∧
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Module.finrank (AlgebraicClosure F) V ≤ Module.finrank F W := by
  obtain ⟨V, L, _, _, _, _, hLfin, π, ρ, hπ, hmin, hperf, _, hρ, hirr, hdim, hminD, _⟩ :=
    exists_minimal_suzuki_irreducible_linear_system hF Γ N hn hSz
  have : Finite L := hLfin
  have : Group.IsPerfect L := hperf
  have hFbar : ringChar (AlgebraicClosure F) ≠ 2 := by
    rwa [← Algebra.ringChar_eq F (AlgebraicClosure F)]
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, hLfin,
    π, ρ, hπ, hperf, ?_, hρ, hirr, hdim⟩
  exact minimal_suzuki_linear_kernel_le_center (Ring.two_ne_zero hFbar) ρ hρ hirr hminD
    (hdim.trans hd) π hπ hmin hSz hn

theorem isPGroup_two_ker_of_perfect_central_suzuki_cover
    {L Q : Type} [Group L] [Finite L] [Group.IsPerfect L] [Group Q]
    (π : L →* Q) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center L)
    {n : ℕ} (hQ : UC22.IsSz Q n) : IsPGroup 2 π.ker := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel
    hQ.suzukiModel.2
  let eQ : L ⧸ π.ker ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).trans e
  exact CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow π.ker hcen eQ
    (fun p hp hp2 _ P => CFSG.SectionRank.suzuki_sylow_isCyclic a (by omega) hp2 P)

theorem fourteen_le_finrank_of_suzuki_quotient_of_ne_three
    {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (hF : ringChar F ≠ 2)
    (Γ : Subgroup (W ≃ₗ[F] W)) (N : Subgroup Γ) [N.Normal]
    {n : ℕ} (hn : 3 ≤ n) (hSz : UC22.IsSz (Γ ⧸ N) n) (hn3 : n ≠ 3) :
    14 ≤ Module.finrank F W := by
  by_contra hlt
  have hd : Module.finrank F W ≤ 13 := by omega
  obtain ⟨V, L, _, _, _, _, hLfin, π, ρ, hπ, hperf, hcen, hρ, hirr, hdim⟩ :=
    exists_suzuki_perfect_central_linear_cover hF Γ N hn hSz hd
  have : Finite L := hLfin
  have : Group.IsPerfect L := hperf
  have : Finite (Γ ⧸ N) := Finite.of_surjective π hπ
  have h2 := isPGroup_two_ker_of_perfect_central_suzuki_cover π hπ hcen hSz
  have hker : π.ker = ⊥ :=
    (CFSG.LocalAnalysis.ComponentInitial.even_Suzuki_catalog_perfect_central_two_kernel_bound
      π hπ hcen h2 hSz).2.1 hn3
  let e : L ≃* (Γ ⧸ N) := MulEquiv.ofBijective π
    ⟨(MonoidHom.ker_eq_bot_iff π).mp hker, hπ⟩
  let τ := (LinearMap.GeneralLinearGroup.generalLinearEquiv (AlgebraicClosure F) V).toMonoidHom.comp
    ρ.asGroupHom
  have hτ : Function.Injective τ := by
    intro x y hxy
    apply hρ
    exact congrArg Units.val
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (AlgebraicClosure F) V).injective hxy)
  have hFbar : ringChar (AlgebraicClosure F) ≠ 2 := by
    rwa [← Algebra.ringChar_eq F (AlgebraicClosure F)]
  have h14 := fourteen_le_finrank_of_faithful_suzuki hSz (Ring.two_ne_zero hFbar)
    (τ.comp e.symm.toMonoidHom) (hτ.comp e.symm.injective)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
