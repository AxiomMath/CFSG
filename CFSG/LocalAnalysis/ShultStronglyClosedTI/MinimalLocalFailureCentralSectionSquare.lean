module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionOrder

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem section_involutions
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    {a : G | a ∈ A ∧ orderOf a = 2} = (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} :=
  (d.card_involutions hA.1 hA.2.1 hA.2.2.1.le hA.2.2.2.1).2 (d.section_inf_J hA)

theorem section_square_eq
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A)
    (φ : A →* minimalLocalFailurePairActionPointHull H z)
    (hker : φ.ker = (minimalLocalFailurePairActionPointHull H z).subgroupOf A)
    (hequiv : ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), ∀ a a' : A,
      (a' : G) = x * a * x⁻¹ → (φ a' : G) = x * φ a * x⁻¹) :
    ∃ x₀ : rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
      ∀ a : A, (a : G) ^ 2 = (x₀ : G) * φ a * (x₀ : G)⁻¹ := by
  obtain ⟨hAH, hAN, hQA, hAM, hAQ, -⟩ := d.section_basic hA
  have hQltA := hA.2.2.1
  have hsq := hA.2.2.2.2.2.2
  obtain ⟨hQH, hQn, hQ, -, -, hBH, hXB, -, hXcyc, -⟩ := d.point_data
  have hinv := d.section_involutions hA
  have hφ1 : ∀ a : A, φ a = 1 ↔ (a : G) ∈ minimalLocalFailurePairActionPointHull H z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := IsConcreteLE.exists_of_lt hQltA
  have ha₀sq : a₀ ^ 2 ≠ 1 := by
    intro h2
    have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀Q (h1 ▸ (minimalLocalFailurePairActionPointHull H z).one_mem)
    have : a₀ ∈ {a : G | a ∈ A ∧ orderOf a = 2} := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ⟨ha₀A, orderOf_eq_prime_iff.mpr ⟨h2, ha₀1⟩⟩
    rw [hinv] at this
    exact ha₀Q this.1
  have hφa₀ : (φ ⟨a₀, ha₀A⟩ : G) ≠ 1 := by
    intro h1
    exact ha₀Q ((hφ1 ⟨a₀, ha₀A⟩).mp (Subtype.ext h1))
  obtain ⟨x₀, hx₀, -⟩ := d.X_regular _ (φ ⟨a₀, ha₀A⟩).2 hφa₀ _ (hsq a₀ ha₀A) ha₀sq
  refine ⟨x₀, fun a => ?_⟩
  by_cases haQ : (a : G) ∈ minimalLocalFailurePairActionPointHull H z
  · rw [(hφ1 a).mpr haQ, OneMemClass.coe_one, mul_one, mul_inv_cancel]
    exact hQ.2 _ haQ
  · have hφa : (φ a : G) ≠ 1 := fun h1 => haQ ((hφ1 a).mp (Subtype.ext h1))
    obtain ⟨x, hx, -⟩ := d.X_regular _ (φ ⟨a₀, ha₀A⟩).2 hφa₀ _ (φ a).2 hφa
    have hxH : (x : G) ∈ H := hBH (hXB x.2)
    have ha₁A : (x : G) * a₀ * (x : G)⁻¹ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (hAN hxH) a₀).mp ha₀A
      exact this
    let a₁ : A := ⟨(x : G) * a₀ * (x : G)⁻¹, ha₁A⟩
    have hφa₁ : (φ a₁ : G) = φ a := by
      rw [hequiv x x.2 ⟨a₀, ha₀A⟩ a₁ rfl, hx]
    have hy : (a₁⁻¹ * a : A) ∈ (minimalLocalFailurePairActionPointHull H z).subgroupOf A := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφa₁, inv_mul_cancel, OneMemClass.coe_one]
    set y : G := ((a₁⁻¹ * a : A) : G) with hydef
    have hyQ : y ∈ minimalLocalFailurePairActionPointHull H z := hy
    have ha : (a : G) = a₁ * y := by
      rw [hydef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hcomm : (a₁ : G) * y = y * a₁ := hAQ _ a₁.2 y hyQ
    have hy2 : y ^ 2 = 1 := hQ.2 y hyQ
    have hxx₀ : (x : G) * x₀ = x₀ * x :=
      congrArg Subtype.val (isMulCommutative_iff.mp (IsCyclic.isMulCommutative) x x₀)
    calc (a : G) ^ 2 = (a₁ : G) ^ 2 * y ^ 2 := by
          rw [ha]
          calc ((a₁ : G) * y) ^ 2 = (a₁ : G) * (y * a₁) * y := by rw [sq]; group
            _ = (a₁ : G) * (a₁ * y) * y := by rw [← hcomm]
            _ = (a₁ : G) ^ 2 * y ^ 2 := by rw [sq, sq]; group
      _ = (x : G) * (a₀ ^ 2) * (x : G)⁻¹ := by
          rw [hy2, mul_one]
          change ((x : G) * a₀ * (x : G)⁻¹) ^ 2 = _
          rw [sq, sq]
          group
      _ = (x : G) * ((x₀ : G) * φ ⟨a₀, ha₀A⟩ * (x₀ : G)⁻¹) * (x : G)⁻¹ := by rw [hx₀]
      _ = (x₀ : G) * ((x : G) * φ ⟨a₀, ha₀A⟩ * (x : G)⁻¹) * (x₀ : G)⁻¹ := by
          calc (x : G) * ((x₀ : G) * φ ⟨a₀, ha₀A⟩ * (x₀ : G)⁻¹) * (x : G)⁻¹
              = ((x : G) * x₀) * φ ⟨a₀, ha₀A⟩ * ((x : G) * x₀)⁻¹ := by group
            _ = ((x₀ : G) * x) * φ ⟨a₀, ha₀A⟩ * ((x₀ : G) * x)⁻¹ := by rw [hxx₀]
            _ = _ := by group
      _ = (x₀ : G) * φ a * (x₀ : G)⁻¹ := by rw [hx]

theorem section_square_hom
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    (∃ ψ : A →* minimalLocalFailurePairActionPointHull H z,
      (∀ a : A, (ψ a : G) = (a : G) ^ 2) ∧
      ψ.ker = (minimalLocalFailurePairActionPointHull H z).subgroupOf A ∧
      Function.Surjective ψ ∧
      ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), ∀ a a' : A,
        (a' : G) = x * a * x⁻¹ → (ψ a' : G) = x * ψ a * x⁻¹) ∧ IsMulCommutative A := by
  obtain ⟨hAH, hAN, hQA, hAM, hAQ, -⟩ := d.section_basic hA
  have hsq := hA.2.2.2.2.2.2
  obtain ⟨hQH, hQn, hQ, -, -, hBH, hXB, -⟩ := d.point_data
  obtain ⟨-, -, hJne, -⟩ := d.J_data
  obtain ⟨j, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJne
  obtain ⟨-, φ, -, hker, hsurj, hequiv⟩ :=
    d.section_commutator_iso hA j.2 (fun h => hj1 (Subtype.ext h))
  obtain ⟨x₀, hkey⟩ := d.section_square_eq hA φ hker hequiv
  have hx₀H : (x₀ : G) ∈ H := hBH (hXB x₀.2)
  let ψ : A →* minimalLocalFailurePairActionPointHull H z :=
    MonoidHom.mk' (fun a => ⟨(a : G) ^ 2, hsq a a.2⟩) (fun a b => by
    apply Subtype.ext
    change (((a * b : A)) : G) ^ 2 = (a : G) ^ 2 * (b : G) ^ 2
    rw [hkey, hkey, hkey, map_mul, Subgroup.coe_mul]
    group)
  have hψ : ∀ a : A, (ψ a : G) = (a : G) ^ 2 := fun a => rfl
  have hψker : ψ.ker = (minimalLocalFailurePairActionPointHull H z).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : (a : G) ^ 2 = 1 := congrArg Subtype.val h1
      rw [hkey] at h2
      apply Subtype.ext
      rw [OneMemClass.coe_one]
      calc (φ a : G) = (x₀ : G)⁻¹ * ((x₀ : G) * φ a * (x₀ : G)⁻¹) * x₀ := by group
        _ = (x₀ : G)⁻¹ * 1 * x₀ := by rw [h2]
        _ = 1 := by group
    · intro h1
      apply Subtype.ext
      change (a : G) ^ 2 = 1
      rw [hkey, h1, OneMemClass.coe_one, mul_one, mul_inv_cancel]
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy' : (x₀ : G)⁻¹ * y * x₀ ∈ minimalLocalFailurePairActionPointHull H z := by
      have h3 : (x₀ : G)⁻¹ * y * ((x₀ : G)⁻¹)⁻¹ ∈ minimalLocalFailurePairActionPointHull H z :=
        hQn.conj_mem ⟨y, hQH y.2⟩ y.2 ⟨(x₀ : G)⁻¹, H.inv_mem hx₀H⟩
      rwa [inv_inv] at h3
    obtain ⟨a, ha⟩ := hsurj ⟨_, hy'⟩
    refine ⟨a, Subtype.ext ?_⟩
    rw [hψ, hkey, ha]
    group
  have hψequiv : ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), ∀ a a' : A,
      (a' : G) = x * a * x⁻¹ → (ψ a' : G) = x * ψ a * x⁻¹ := by
    intro x _ a a' ha'
    rw [hψ, hψ, ha', sq, sq]
    group
  refine ⟨⟨ψ, hψ, hψker, hψsurj, hψequiv⟩, isMulCommutative_iff.mpr fun a b => ?_⟩
  have h := congrArg Subtype.val (map_mul ψ a b)
  simp only [Subgroup.coe_mul, hψ] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc (a : G) * b = (a : G)⁻¹ * ((a : G) ^ 2 * (b : G) ^ 2) * (b : G)⁻¹ := by
        rw [sq, sq]; group
    _ = (a : G)⁻¹ * (((a : G) * b) ^ 2) * (b : G)⁻¹ := by rw [h]
    _ = (b : G) * a := by rw [sq]; group

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
