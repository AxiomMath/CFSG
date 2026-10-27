module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHullClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverUnitary

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.FixedPointModel CFSG.ShultStronglyClosedTI.OvergroupHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped LinearAlgebra.Projectivization

theorem exists_unitary_cover_point
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} (hNM : CFSG.oddCore L ≤ M)
    {q : ℕ} (hmodel : IsModelCosetAction L M q 3) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (J : HermitianForm 3 k)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (f : ℕ), 2 ≤ f ∧ q = 2 ^ f ∧
      Nat.card k = (2 ^ f) ^ 2 ∧ Nat.card {x : k // J.conj x = x} = 2 ^ f ∧
      ∃ (C : Subgroup J.specialSubgroup) (_ : C.Normal) (hC : C ≤ scalarCenter J)
        (θ : J.specialSubgroup ⧸ C ≃* L),
        ∀ x, θ x ∈ M ↔ coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 =
          unitaryCoordinatePoint 0 := by
  rcases hmodel with ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨-, f, hf, hq, -, k, _, _, J, hJ, hk, hfix, e, -, hM, -, -⟩
  · omega
  · omega
  subst hq
  let : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hk, ← pow_mul])
  let η : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L))
  have hker : η.ker = CFSG.oddCore L := by ext x; simp [η]
  obtain ⟨-, φ, hφη, -, -, hφker, -, ⟨θ, hθ⟩, -⟩ :=
    PerfectOddCover.perfect_odd_cover_unitary J f hf hk hfix hJ η
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ hZ)
      (hker ▸ CFSG.ComponentClassification.OddCore.odd_card L)
  have hC : φ.ker ≤ scalarCenter J := hφker.trans (scalarCenter_eq_ker J hJ).ge
  refine ⟨k, inferInstance, inferInstance, inferInstance, J, hJ, f, hf, rfl, hk, hfix, φ.ker,
    inferInstance, hC, θ, fun x => ?_⟩
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective φ.ker x
  have hθA : θ (QuotientGroup.mk' φ.ker A) = φ A := (hθ A).1
  have hηA : η (φ A) = PerfectOddCover.unitaryProj J A := by
    rw [← MonoidHom.comp_apply, hφη]
  have hmem : ∀ l : L, l ∈ M ↔ η l ∈ unitaryCoordinateStabilizer J 0 := by
    intro l
    rw [← hM]
    constructor
    · intro hl
      exact ⟨QuotientGroup.mk' _ l, ⟨l, hl, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨m, hm, rfl⟩, hy⟩
      have hmk : QuotientGroup.mk' (CFSG.oddCore L) m = QuotientGroup.mk' (CFSG.oddCore L) l :=
        e.injective hy
      rw [QuotientGroup.mk'_eq_mk'] at hmk
      obtain ⟨c, hc, hmc⟩ := hmk
      rw [← hmc]
      exact M.mul_mem hm (hNM hc)
  rw [hθA, hmem, hηA]
  rfl

variable {G : Type} [Group G] [Finite G]

theorem exists_unitaryHullFrame
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    (hdeg : Nat.card {ω : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1) :
    Nonempty (UnitaryHullFrame H t (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))
      (Nat.card (minimalLocalFailurePairActionPointHull H z))) := by
  set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) with hLdef
  set q := Nat.card (minimalLocalFailurePairActionPointHull H z) with hqdef
  have hL : L = Subgroup.closure (conjugacyWithin Y z) :=
    congrArg Subgroup.closure (overgroup_class_eq h hcomm hbeta ht hproper hKY)
  obtain ⟨-, hKL, -, hperfect, -, hstrong, hcenter, hcoreM, hmodel, hinvM, horbit⟩ :=
    overgroup_hull_structure h hcomm hsmallerR1 hbeta ht hproper hY hKY hL
  obtain ⟨ι, hιinj, hιrange, -, -⟩ := orbit_coset_embedding H L
  obtain ⟨-, -, j, hj, hindex⟩ :=
    fixed_point_model_recognition hstrong hcoreM hcenter hmodel hinvM
  obtain ⟨-, -, -, -, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hidx : (H.subgroupOf L).index = q ^ 3 + 1 := by
    rw [← hdeg, horbit, ← hιrange, Nat.card_range_of_injective hιinj]
    rfl
  rw [← hqdef] at hindex
  have hj3 : j = 3 := Nat.pow_right_injective (by omega : 2 ≤ q) (by
    change q ^ j = q ^ 3
    omega)
  subst hj3
  have : Group.IsPerfect L := hperfect
  obtain ⟨k, _, _, _, J, hJ, f, hf, hq, hk, hfix, C, _, hC, θ₀, hθ₀⟩ :=
    exists_unitary_cover_point hcenter hcoreM hj
  have htL : t ∈ L := hKL (minimalLocalFailureProperPair_flip_mem H z beta t)
  set τ₀ := θ₀.symm ⟨t, htL⟩
  have hP : coverToPGL J C hJ hC τ₀ • unitaryCoordinatePoint (K := k) 0 ≠
      unitaryCoordinatePoint 0 := by
    intro hfix0
    have hmemH := (hθ₀ τ₀).mpr hfix0
    rw [MulEquiv.apply_symm_apply] at hmemH
    exact CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry.pair_flip_not_mem_point hbeta ht hmemH
  set w : J.specialSubgroup ⧸ C := QuotientGroup.mk' C (hermitianWeylSU J hJ)
  have hw : coverToPGL J C hJ hC w • unitaryCoordinatePoint (K := k) 0 =
      unitaryCoordinatePoint 2 :=
    UnitaryModel.hermitianWeylPSU_smul_zero J hJ
  have hw0 : coverToPGL J C hJ hC w • unitaryCoordinatePoint (K := k) 0 ≠
      unitaryCoordinatePoint 0 := by
    rw [hw]
    exact UnitaryModel.unitaryCoordinatePoint_two_ne_zero
  obtain ⟨z₀, hz₀, -⟩ := heisL_regular hf hk hfix hJ hC hP hw0
  set c := heisL J C hJ z₀
  have hc0 : coverToPGL J C hJ hC c • unitaryCoordinatePoint (K := k) 0 =
      unitaryCoordinatePoint 0 := heisL_smul_zero hJ hC z₀
  let θ : J.specialSubgroup ⧸ C ≃* L := (MulAut.conj c⁻¹).trans θ₀
  have hmem : ∀ x, ((θ x : L) : G) ∈ H ↔
      coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 0 := by
    intro x
    change θ₀ (c⁻¹ * x * c⁻¹⁻¹) ∈ H.subgroupOf L ↔ _
    rw [hθ₀, inv_inv, map_mul, map_mul, mul_smul, mul_smul, hc0, map_inv, inv_smul_eq_iff, hc0]
  have hflip : ∀ x, ((θ x : L) : G) = t →
      coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 2 := by
    intro x hx
    have hx' : θ₀ (c⁻¹ * x * c⁻¹⁻¹) = θ₀ τ₀ := by
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hx
    have hxτ : c⁻¹ * x * c⁻¹⁻¹ = τ₀ := θ₀.injective hx'
    have hxeq : x = c * τ₀ * c⁻¹ := by
      rw [← hxτ]
      group
    rw [hxeq, map_mul, map_mul, mul_smul, mul_smul, map_inv, inv_smul_eq_iff.mpr hc0.symm, hz₀,
      hw]
  exact ⟨{
    k := k, J := J, hJ := hJ, f := f, hf := hf, hq := hq, hcard := hk, hfixed := hfix,
    C := C, hC := hC, θ := θ, mem_point := hmem, flip := hflip }⟩

end CFSG.ShultStronglyClosedTI.UnitaryHulls
