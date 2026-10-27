module

public import CFSG.Quasithin.Background.Harris.G2.Setup
public import CFSG.Quasithin.Background.SmithB45G2Out
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply]

section Aut


variable {K : Type} [Field K] [Finite K] [CharP K 2]

set_option quotPrecheck false in
local notation "Inn" =>
  CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K)

omit [CharP K 2] in
theorem conj_injective_adjoint : Function.Injective
    (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) := by
  intro g g' e
  have hc : g'⁻¹ * g ∈ Subgroup.center ↥(adjointGroup .G2 K) :=
    Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut ↥(adjointGroup .G2 K) => α x) e
      simp only [MulAut.conj_apply] at h1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = g'⁻¹ * g * x := by group
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem card_le_of_mulAut {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (B : Subgroup (MulAut ↥(adjointGroup .G2 K))) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ (3 * f) := by
  classical
  set C := ↥(adjointGroup .G2 K) with hC
  have hinj := conj_injective_adjoint (K := K)
  set Γ := (B ⊓ Inn).comap
    (MulAut.conj : C →* MulAut C) with hΓdef
  have hmap : Γ.map MulAut.conj = B ⊓ Inn :=
    Subgroup.map_comap_eq_self (inf_le_right.trans (le_of_eq rfl))
  have hcardΓ : Nat.card Γ = Nat.card (B ⊓ Inn :
      Subgroup (MulAut C)) := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hΓ1 : ∀ g ∈ Γ, g * g = 1 := fun g hg => hinj (by
    rw [map_mul, map_one]
    exact hsq _ (Subgroup.mem_inf.1 hg).1)
  have hΓc : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g := fun g hg h hh => hinj (by
    rw [map_mul, map_mul]
    exact hc _ (Subgroup.mem_inf.1 hg).1 _ (Subgroup.mem_inf.1 hh).1)
  have hbound := CFSG.Quasithin.B45G2.card_le_cube_adjointGroup hK (by omega) hΓ1 hΓc
  rw [hK, ← pow_mul, mul_comm f 3] at hbound
  by_cases hBL : B ≤ Inn
  · rw [inf_eq_left.2 hBL] at hcardΓ
    exact hcardΓ ▸ hbound
  obtain ⟨y, hyB, hyL⟩ := Set.not_subset.1 hBL
  have hy1 : y ≠ 1 := fun h => hyL (h ▸ one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hsq y hyB) hy1
  have hfix : ∀ g ∈ Γ, y g = g := fun g hg => by
    have hc' : y * MulAut.conj g = MulAut.conj g * y :=
      hc _ hyB _ (Subgroup.mem_inf.1 hg).1
    have := mulAut_mul_conj_mul_inv y g
    rw [hc', mul_inv_cancel_right] at this
    exact hinj this.symm
  have hsqΓ := CFSG.Quasithin.B45G2.card_sq_le_of_outer_fixed hf hK y hyo hyL hfix hΓ1 hΓc
  obtain ⟨-, Θ, -, -, hker, hinv⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hmemker : ∀ x, x ∈ Inn ↔ Θ x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, hker]
    rfl
  have hval : ∀ x ∈ B, x ∉ Inn → ∀ c, Θ x c = c ^ 2 ^ (f / 2) :=
    fun x hx hxL c => by
      rcases hinv x (by rw [pow_two]; exact hsq x hx) with h | ⟨-, h, -⟩
      · exact absurd ((hmemker x).2 h) hxL
      · exact h c
  have hidx : ∀ x ∈ B, x ∉ Inn → y⁻¹ * x ∈ Inn := by
    intro x hx hxL
    have hΘ : Θ x = Θ y := RingEquiv.ext fun c => by rw [hval x hx hxL, hval y hyB hyL]
    rw [hmemker, map_mul, map_inv, hΘ, inv_mul_cancel]
  have hcard2 : Nat.card B ≤ 2 * Nat.card (B ⊓ Inn :
      Subgroup (MulAut C)) := by
    let g : B → (B ⊓ Inn : Subgroup (MulAut C)) ⊕
        (B ⊓ Inn : Subgroup (MulAut C)) := fun x =>
      if hx : (x : MulAut C) ∈ Inn then Sum.inl ⟨x, x.2, hx⟩
      else Sum.inr ⟨y⁻¹ * x, B.mul_mem (B.inv_mem hyB) x.2, hidx x x.2 hx⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      by_cases hx : (x : MulAut C) ∈ Inn <;>
        by_cases hx' : (x' : MulAut C) ∈ Inn
      · simp only [g, hx, hx', dite_true, Sum.inl.injEq] at hxx
        exact Subtype.ext (congrArg (fun z : ↥(B ⊓ Inn) => (z : MulAut C))
          hxx)
      · simp [g, hx, hx'] at hxx
      · simp [g, hx, hx'] at hxx
      · simp only [g, hx, hx', dite_false, Sum.inr.injEq] at hxx
        exact Subtype.ext (mul_left_cancel
          (congrArg (fun z : ↥(B ⊓ Inn) => (z : MulAut C)) hxx))
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_sum] at this
    omega
  rw [← hcardΓ] at hcard2
  have h1 : Nat.card B ^ 2 ≤ 4 * 2 ^ (3 * f) := by
    calc Nat.card B ^ 2 ≤ (2 * Nat.card Γ) ^ 2 := Nat.pow_le_pow_left hcard2 2
      _ = 4 * Nat.card Γ ^ 2 := by ring
      _ ≤ 4 * 2 ^ (3 * f) := Nat.mul_le_mul_left 4 hsqΓ
  have h2 : 4 * 2 ^ (3 * f) < (2 ^ (3 * f)) ^ 2 := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ((Nat.pow_lt_pow_iff_left two_ne_zero).1 (h1.trans_lt h2)).le

end Aut


section Full


theorem m_le_of_g2 [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m)
    {f : ℕ} (hf : 2 ≤ f) (e : ↥L ≃* ↥(CFSG.Quasithin.Explicit.cayleyGroup (GaloisField 2 f))) :
    m ≤ 3 * f := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ψ, -, hsurj, hker⟩ :=
    CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hK hf
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, center_adjointGroup_eq_bot]
  exact m_le_of_autRank hs (e.trans (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm)
    fun B hc hsq => card_le_of_mulAut hf hK B hc hsq

end Full

end CFSG.Quasithin.G11.Harris.G2
