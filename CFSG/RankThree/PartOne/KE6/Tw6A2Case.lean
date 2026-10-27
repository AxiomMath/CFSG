module

public import CFSG.RankThree.PartOne.KE6.Phi3A2Case
public import CFSG.RankThree.PartOne.KE6.Phi6A2
public import CFSG.RankThree.PartOne.KE6.Tw6Transport

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_unitary)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

section Case

variable {Fr : Ω →+* Ω}

theorem tw6_A2_layer_gen {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 ∧
    Finite ↥(rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S ⊓
      (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    e6Commutant (((rootSpan Tag.E6 Ω S ⊓
        (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) ∧
    ∃ h₀ : ModGL Tag.E6 Ω, ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω (e6Index 0) (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) *
        h₀⁻¹ ∈ rootSpan Tag.E6 Ω S ⊓
          (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      tw6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π j) (π i)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_tw6Theta_pinnedX (Fr := Fr) w
      (chainRoot13_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ, ← chainRoot_swap]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (tw6ThetaConj Ω Fr w) (tw6ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, hfin, hq⟩ := sl3_root_permuting_frobenius_fixed_unitary hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  set P := rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) with hPdef
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup_gen (tw6Theta Ω Fr) (tw6ThetaConj Ω Fr w)
    (tw6ThetaConj_conj w) hQ hmaps Φ hΦ₀
  have hmemQ₁ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfinP : Finite ↥P := Finite.of_equiv _ e.symm.toEquiv
  have hqsP : CFSG.IsQuasisimple ↥P :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm (hq (by omega)).1
  have hA2 := isA2Layer_a2Inv₁ (Ω := Ω)
  have hconj : ((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω)) =
      unitaryLayer (a2Inv₁ Ω) (ℓ ^ f) (Matrix.SpecialLinearGroup.toGL H') := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz := hmemQ₁ y hy.1
      obtain ⟨Y, hY, hXY⟩ := (hH' (e ⟨y, hy⟩ : SL(3, Ω))).1 (e ⟨y, hy⟩).2
      have h1 : a2Inv₁ Ω (e ⟨y, hy⟩ : SL(3, Ω)) = n * y * n⁻¹ :=
        (a2Inv₁_eq_iff hz).2 (he ⟨y, hy⟩)
      exact ⟨(e ⟨y, hy⟩ : SL(3, Ω)), ⟨Y, hY, hXY.symm⟩, h1⟩
    · rintro ⟨X, ⟨Y, hY, hXY⟩, rfl⟩
      have hX : X ∈ fixSubgroup Φ := (hH' X).2 ⟨Y, hY, hXY.symm⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨X, hX⟩
      have hz := hmemQ₁ y y.2.1
      have h1 := he y
      rw [hy] at h1
      have h2 : a2Inv₁ Ω X = n * y * n⁻¹ := (a2Inv₁_eq_iff hz).2 h1
      exact ⟨y, y.2, h2.symm⟩
  have hcommP : e6Commutant (((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) := by
    rw [hconj]
    exact hA2.e6Commutant_unitaryLayer hℓ hf hK hq3 _
  obtain ⟨m, hmQ, hsl⟩ := hA2.exists_conj_simpleRootSL2_mem_unitaryLayer hℓ hf hK
    (Matrix.SpecialLinearGroup.toGL H')
  refine ⟨hQ, hfinP, hqsP, hcommP, n⁻¹ * m, fun B => ?_⟩
  have hmem : m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ ∈
        ((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
          Set (ModGL Tag.E6 Ω)) := by
    rw [hconj]
    exact hsl B
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hyeq' : n * y * n⁻¹ = m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ := hyeq
  have this : n⁻¹ * m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * (n⁻¹ * m)⁻¹ = y := by
    have h3 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [h3, hyeq']
    group
  rw [this]
  exact hy

end Case

end CFSG.RankThree.PartOne.KE6
