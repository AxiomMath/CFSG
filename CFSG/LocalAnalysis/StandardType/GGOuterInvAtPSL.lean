module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvModelData
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Open (IsElemAbelian)

@[expose] def PSLFieldNone : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ n →
    ∀ (A B : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε < 2 → σ ≠ 1 →
      let α := conjAut n K A * (fieldAut n K σ * AutPSL.graphAut ^ ε)
      α * α = 1 → Odd (orderOf (conjAut n K B)) → α * conjAut n K B = conjAut n K B * α →
      (∀ g, conjAut n K B g = g → α g = g) →
      ∀ L₁ : Subgroup (projectiveSL n K), (∀ g ∈ L₁, conjAut n K B g = g) → Group.IsSolvable L₁

@[expose] def PSLGraphNone : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ n →
    ∀ (A B : GL (Fin n) K),
      let α := conjAut n K A * AutPSL.graphAut
      α * α = 1 → Odd (orderOf (conjAut n K B)) → α * conjAut n K B = conjAut n K B * α →
      (∀ g, conjAut n K B g = g → α g = g) →
      ∀ L₁ : Subgroup (projectiveSL n K), (∀ g ∈ L₁, conjAut n K B g = g) → Group.IsSolvable L₁

theorem ggOuterInv_pslMarking (m f : ℕ) {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G)
    (hker : ψ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hdiag : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ c) :
    ∃ φ ∈ (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) (GaloisField 2 f)))),
      ∀ u u', c * ψ u * c⁻¹ = ψ u' →
        φ (proj (m + 1) (GaloisField 2 f) u) = proj (m + 1) (GaloisField 2 f) u' := by
  have hπker : (proj (m + 1) (GaloisField 2 f)).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := by
    rw [ker_proj, scalars_eq_center]
  obtain ⟨s, hs⟩ := ClassicalPosition.exists_isGLLift_PSL m (GaloisField 2 f) ψ hker.le hc hdiag
  refine ⟨conjAut (m + 1) (GaloisField 2 f) s⁻¹, ⟨s⁻¹, rfl⟩, fun u u' h => ?_⟩
  obtain ⟨v, hv, hvψ⟩ := hs u'
  have hψ : ψ v = ψ u := by
    rw [← hvψ, ← h]
    group
  have hvu : proj (m + 1) (GaloisField 2 f) v = proj (m + 1) (GaloisField 2 f) u := by
    rw [MonoidHom.eq_iff, hπker, ← hker, ← MonoidHom.eq_iff]
    exact hψ
  rw [← hvu, conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hv]
  group

theorem ggOuterInvModelDataAt_PSL_of
    (hA : PSLFieldNone) (hB : PSLGraphNone) :
    GGOuterInvModelDataAt .PSL := by
  intro n f hadm hrank
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 2 ≤ m := hrank
  have hn : 3 ≤ m + 1 := by omega
  have hπker : (proj (m + 1) (GaloisField 2 f)).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := by
    rw [ker_proj, scalars_eq_center]
  refine ⟨projectiveSL (m + 1) (GaloisField 2 f), inferInstance, proj (m + 1) (GaloisField 2 f),
    AutPSL.inndiag, proj_surjective _ _, hπker, AutPSL.inn_le_inndiag,
    AutPSL.odd_relIndex_inn_inndiag, ?_, ?_⟩
  · intro G _ ψ hker c hc hdiag
    exact ggOuterInv_pslMarking m f ψ hker hc hdiag
  · intro p β α E hp hp2 _ hβE hEI hEab _ hEα hα2 hαI hL hfix
    obtain ⟨L₁, hL₁β, hL₁⟩ := hL
    obtain ⟨B, rfl⟩ := hEI hβE
    have hodd : Odd (orderOf (conjAut (m + 1) (GaloisField 2 f) B)) := by
      have h1 : orderOf (conjAut (m + 1) (GaloisField 2 f) B) ∣ p :=
        orderOf_dvd_of_pow_eq_one (hEab.2 _ hβE)
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · rw [h]
        exact odd_one
      · rw [h]
        exact hp.odd_of_ne_two hp2
    have hcomm : α * conjAut (m + 1) (GaloisField 2 f) B =
        conjAut (m + 1) (GaloisField 2 f) B * α := by
      have := hEα hβE
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    obtain ⟨i, ⟨A, rfl⟩, c, ⟨σ, hc⟩, rfl⟩ := AutPSL.exists_mul_compl hn α
    apply hL₁
    by_cases hσ : σ = 1
    · subst hσ
      rcases hc with rfl | rfl
      · exact absurd (by rw [map_one, mul_one]; exact ⟨A, rfl⟩) hαI
      · rw [map_one, one_mul] at hα2 hcomm hfix
        exact hB (m + 1) (GaloisField 2 f) hn A B hα2 hodd hcomm hfix L₁ hL₁β
    · rcases hc with rfl | rfl
      · have e : conjAut (m + 1) (GaloisField 2 f) A *
            (fieldAut (m + 1) (GaloisField 2 f) σ * AutPSL.graphAut ^ 0) =
            conjAut (m + 1) (GaloisField 2 f) A * fieldAut (m + 1) (GaloisField 2 f) σ := by
          rw [pow_zero, mul_one]
        have key := hA (m + 1) (GaloisField 2 f) hn A B σ 0 (by norm_num) hσ
        simp only [e] at key
        exact key hα2 hodd hcomm hfix L₁ hL₁β
      · have e : conjAut (m + 1) (GaloisField 2 f) A *
            (fieldAut (m + 1) (GaloisField 2 f) σ * AutPSL.graphAut ^ 1) =
            conjAut (m + 1) (GaloisField 2 f) A *
              (fieldAut (m + 1) (GaloisField 2 f) σ * AutPSL.graphAut) := by
          rw [pow_one]
        have key := hA (m + 1) (GaloisField 2 f) hn A B σ 1 (by norm_num) hσ
        simp only [e] at key
        exact key hα2 hodd hcomm hfix L₁ hL₁β

theorem ggOuterInvAt_PSL_of
    (h2 : GGO2CentralizerG0At .PSL) (hA : PSLFieldNone)
    (hB : PSLGraphNone) : GGOuterInvAt .PSL :=
  ggOuterInvAt_of_modelData ggSteinbergCorrectionAt_PSL h2 (ggOuterInvModelDataAt_PSL_of hA hB)

end CFSG.StandardType
