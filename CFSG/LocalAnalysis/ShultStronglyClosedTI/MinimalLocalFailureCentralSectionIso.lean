module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionSinger

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def sectionCommutatorHom {A Q M : Subgroup G}
    (hAQ : ∀ a ∈ A, ∀ y ∈ Q, a * y = y * a) (hQab : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' = y' * y)
    (hcomm : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q) {j : G} (hj : j ∈ M) : A →* Q :=
  MonoidHom.mk' (fun a => ⟨a * j * (a : G)⁻¹ * j⁻¹, hcomm a a.2 j hj⟩) (fun a b => by
    apply Subtype.ext
    have hca := hcomm a a.2 j hj
    have hcb := hcomm b b.2 j hj
    have h1 : (a : G) * (b * j * (b : G)⁻¹ * j⁻¹) = (b * j * (b : G)⁻¹ * j⁻¹) * a :=
      hAQ a a.2 _ hcb
    have h2 := hQab _ hca _ hcb
    change ((a : G) * b) * j * ((a : G) * b)⁻¹ * j⁻¹ =
      (a * j * (a : G)⁻¹ * j⁻¹) * (b * j * (b : G)⁻¹ * j⁻¹)
    calc ((a : G) * b) * j * ((a : G) * b)⁻¹ * j⁻¹
        = (a : G) * (b * j * (b : G)⁻¹ * j⁻¹) * j * (a : G)⁻¹ * j⁻¹ := by group
      _ = (b * j * (b : G)⁻¹ * j⁻¹) * a * j * (a : G)⁻¹ * j⁻¹ := by rw [h1]
      _ = (b * j * (b : G)⁻¹ * j⁻¹) * (a * j * (a : G)⁻¹ * j⁻¹) := by group
      _ = (a * j * (a : G)⁻¹ * j⁻¹) * (b * j * (b : G)⁻¹ * j⁻¹) := h2.symm)

omit [Finite G] in
theorem sectionCommutatorHom_apply {A Q M : Subgroup G}
    (hAQ : ∀ a ∈ A, ∀ y ∈ Q, a * y = y * a) (hQab : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' = y' * y)
    (hcomm : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q) {j : G} (hj : j ∈ M) (a : A) :
    (sectionCommutatorHom hAQ hQab hcomm hj a : G) = a * j * (a : G)⁻¹ * j⁻¹ :=
  rfl

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem section_centralizer_X_eq_bot
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) {x : G}
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1) :
    A ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  obtain ⟨-, -, -, hAM, -⟩ := d.section_basic hA
  rw [d.section_centralizer_X hAM hx hx1, d.section_inf_J hA]

theorem section_quotient_fixed
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) {x : G}
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1)
    {a : G} (ha : a ∈ A) (hfix : a⁻¹ * (x * a * x⁻¹) ∈ minimalLocalFailurePairActionPointHull H z) :
    a ∈ minimalLocalFailurePairActionPointHull H z := by
  obtain ⟨hAH, hAN, hQA, -⟩ := d.section_basic hA
  obtain ⟨hQH, hQn, -, -, -, hBH, hXB, -⟩ := d.point_data
  have hC := d.section_centralizer_X_eq_bot hA hx hx1
  have hxH : x ∈ H := hBH (hXB hx)
  set Q := minimalLocalFailurePairActionPointHull H z
  let f : G → G := fun b => b⁻¹ * (x * b * x⁻¹)
  have hinj : ∀ b ∈ A, ∀ c ∈ A, f b = f c → b = c := by
    intro b hb c hc hbc
    have hmem : c * b⁻¹ ∈ A ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem hc (inv_mem hb), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h' : c * (b⁻¹ * (x * b * x⁻¹)) = c * (c⁻¹ * (x * c * x⁻¹)) := by
        rw [show b⁻¹ * (x * b * x⁻¹) = f b from rfl, hbc]
      calc c * b⁻¹ * x = (c * (b⁻¹ * (x * b * x⁻¹))) * (x * b * x⁻¹)⁻¹ * x := by group
        _ = (c * (c⁻¹ * (x * c * x⁻¹))) * (x * b * x⁻¹)⁻¹ * x := by rw [h']
        _ = x * (c * b⁻¹) := by group
    rw [hC, Subgroup.mem_bot] at hmem
    exact (mul_inv_eq_one.mp hmem).symm
  have hfQ : ∀ b ∈ Q, f b ∈ Q := by
    intro b hb
    have := hQn.conj_mem ⟨b, hQH hb⟩ hb ⟨x, hxH⟩
    exact mul_mem (inv_mem hb) this
  have himage : f '' (Q : Set G) = Q := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨b, hb, rfl⟩
      exact hfQ b hb
    · rw [Set.InjOn.ncard_image fun b hb c hc hbc => hinj b (hQA hb) c (hQA hc) hbc]
    · exact Set.toFinite _
  have hfa : f a ∈ f '' (Q : Set G) := himage.symm ▸ hfix
  obtain ⟨b, hb, hba⟩ := hfa
  rw [← hinj b (hQA hb) a ha hba]
  exact hb

theorem section_commutator_hom
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    ∃ φ : A →* minimalLocalFailurePairActionPointHull H z,
      (∀ a : A, (φ a : G) = (a : G) * j * (a : G)⁻¹ * j⁻¹) ∧
      φ.ker = (minimalLocalFailurePairActionPointHull H z).subgroupOf A ∧
      ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), ∀ a a' : A,
        (a' : G) = x * a * x⁻¹ → (φ a' : G) = x * φ a * x⁻¹ := by
  obtain ⟨hAH, hAN, hQA, hAM, hAQ, -⟩ := d.section_basic hA
  have hcomm := hA.2.2.2.2.2.1
  obtain ⟨-, -, hQ, -⟩ := d.point_data
  obtain ⟨-, -, -, hJM, -⟩ := d.core_data
  have hQab : ∀ y ∈ minimalLocalFailurePairActionPointHull H z,
      ∀ y' ∈ minimalLocalFailurePairActionPointHull H z, y * y' = y' * y :=
    fun y hy y' hy' => congrArg Subtype.val (isMulCommutative_iff.mp hQ.1 ⟨y, hy⟩ ⟨y', hy'⟩)
  refine ⟨sectionCommutatorHom hAQ hQab hcomm (hJM hj), fun a => rfl, ?_, ?_⟩
  · ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hCj := d.section_centralizer_J hQA hAM hj hj1
    rw [d.section_inf_J hA, sup_bot_eq] at hCj
    constructor
    · intro h1
      have h1' : (a : G) * j * (a : G)⁻¹ * j⁻¹ = 1 := congrArg Subtype.val h1
      have hmem : (a : G) ∈ A ⊓ Subgroup.centralizer ({j} : Set G) := by
        refine ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc (a : G) * j = ((a : G) * j * (a : G)⁻¹ * j⁻¹) * j * a := by group
          _ = j * a := by rw [h1']; group
      rwa [hCj] at hmem
    · intro haQ
      have hmem : (a : G) ∈ A ⊓ Subgroup.centralizer ({j} : Set G) := hCj ▸ haQ
      apply Subtype.ext
      change (a : G) * j * (a : G)⁻¹ * j⁻¹ = 1
      rw [Subgroup.mem_centralizer_singleton_iff.mp hmem.2]
      group
  · intro x hx a a' ha'
    change (a' : G) * j * (a' : G)⁻¹ * j⁻¹ = x * ((a : G) * j * (a : G)⁻¹ * j⁻¹) * x⁻¹
    have hxj := d.X_commute_J hx hj
    have hjx : j = x * j * x⁻¹ := by rw [hxj, mul_inv_cancel_right]
    rw [ha']
    conv_lhs => rw [hjx]
    group

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
