module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverInvariants
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.Models.BenderSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups

universe u

theorem suzukiCover_matrix_nontrivial_Sylow_centralizer
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (a : ℕ) (ha : 1 ≤ a) (η : E →* SuzukiMatrixGroup a)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hp : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥) :
    (∀ P : Sylow 2 E, Subgroup.centralizer (P : Set E) = η.ker) ∧
      η.ker = Subgroup.center E := by
  have ha0 : 0 < a := by omega
  let Q : Sylow 2 (SuzukiMatrixGroup a) := suzukiCoverSylow a ha0
  let : IsElementaryAbelian 2 (commutator (Q : Subgroup (SuzukiMatrixGroup a))) :=
    (suzukiCoverRoot_layers_elementary a ha0).1
  let : IsElementaryAbelian 2 (Abelianization (Q : Subgroup (SuzukiMatrixGroup a))) :=
    (suzukiCoverRoot_layers_elementary a ha0).2
  have hclass : commutator (Q : Subgroup (SuzukiMatrixGroup a)) ≤
      Subgroup.center (Q : Subgroup (SuzukiMatrixGroup a)) :=
    (suzukiCoverRoot_structure a ha0).2.2.1.le
  exact central_two_cover_irreducible_derived_Sylow_centralizer η hsurj hcentral hp hne
    Q hclass (suzukiCoverDerived_ne_bot a ha0) (suzukiCoverRoot_centralizer a ha0)
    (suzukiCoverTorus a) (suzukiCoverTorus_le_normalizer a)
    (suzukiCoverTorus_odd a ha0) (suzukiCoverDerived_irreducible a ha0)
    (suzukiCoverAbelian_invariant_eq_zero a ha0)

@[expose] def suzukiCoverNativeEquiv (a : ℕ) : Sz a ≃* SuzukiMatrixGroup a := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  exact (MulEquiv.subgroupCongr hmodel).symm.trans
    (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))

theorem suzukiCover_native_nontrivial_Sylow_centralizer
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (a : ℕ) (ha : 1 ≤ a) (η : E →* Sz a)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hp : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥) :
    (∀ P : Sylow 2 E, Subgroup.centralizer (P : Set E) = η.ker) ∧
      η.ker = Subgroup.center E := by
  let e := suzukiCoverNativeEquiv a
  let φ := e.toMonoidHom.comp η
  have hker : φ.ker = η.ker :=
    MonoidHom.ker_comp_of_injective η e.toMonoidHom e.injective
  have h := suzukiCover_matrix_nontrivial_Sylow_centralizer a ha φ
    (e.surjective.comp hsurj) (hker.symm ▸ hcentral) (hker.symm ▸ hp)
    (hker.symm ▸ hne)
  exact hker ▸ h

theorem suzuki_nontrivial_central_two_cover_Sylow_centralizer
    {K : Type} [Field K] [Finite K]
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (a : ℕ) (ha : 1 ≤ a) (hcard : Nat.card K = 2 ^ (2 * a + 1))
    (η : E →* GLASzGroup a K) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker)
    (hne : η.ker ≠ ⊥) :
    (∀ P : Sylow 2 E, Subgroup.centralizer (P : Set E) = η.ker) ∧
      η.ker = Subgroup.center E := by
  let e := glaSzEquivNative a ha hcard
  let φ := e.toMonoidHom.comp η
  have hker : φ.ker = η.ker :=
    MonoidHom.ker_comp_of_injective η e.toMonoidHom e.injective
  have h := suzukiCover_native_nontrivial_Sylow_centralizer a ha φ
    (e.surjective.comp hsurj) (hker.symm ▸ hcentral) (hker.symm ▸ hp)
    (hker.symm ▸ hne)
  exact hker ▸ h

end CFSG.ShultStronglyClosedTI
