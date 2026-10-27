module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsCent
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.StandardType

namespace SUFacts

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.UnitaryPilot (IsPairRadical pairRadical isPGroup_pairRadical
  card_pairRadical_ge aSpanTop zSpan)

variable {F : Type} [Field F] {a : ℕ}

theorem coord_eq_zero_of_mem_sup {w : Module.Basis (HypIndex 1 1) F (Fin 3 → F)} {y : Fin 3 → F}
    (hy : y ∈ Submodule.span F {w (.inr (.inr 0))} ⊔ Submodule.span F {w (.inr (.inl 0))}) :
    w.repr y (.inl 0) = 0 := by
  have hle : Submodule.span F {w (.inr (.inr 0))} ⊔ Submodule.span F {w (.inr (.inl 0))} ≤
      LinearMap.ker ((Finsupp.lapply (.inl 0)).comp w.repr.toLinearMap) := by
    refine sup_le ?_ ?_ <;> rw [Submodule.span_le, Set.singleton_subset_iff] <;>
      simp [Module.Basis.repr_self]
  exact hle hy

theorem span_inl_eq {ε : ℕ} (w : HypIndex 1 ε → (Fin 3 → F)) :
    aSpanTop F w = Submodule.span F {w (.inl 0)} := by
  rw [aSpanTop]
  congr 1
  ext v
  simp [eq_comm]

theorem span_z_eq {r : ℕ} (w : HypIndex r 1 → (Fin 3 → F)) :
    zSpan F w = Submodule.span F {w (.inr (.inl 0))} := by
  rw [zSpan]
  congr 1
  ext v
  simp [eq_comm]

@[expose] def hypSwap : Equiv.Perm (HypIndex 1 1) :=
  Function.Involutive.toPerm hypPartner hypPartner_involutive

theorem hypSwap_symm_apply (x : HypIndex 1 1) : hypSwap.symm x = hypPartner x := rfl

theorem gram_reindex_hypSwap (h : UnitaryFieldData 2 a F)
    {w : Module.Basis (HypIndex 1 1) F (Fin 3 → F)}
    (hw : ∀ x y, CFSG.LinearGroups.stdHermForm h 3 (w x) (w y) = hypGram 1 1 F x y) (x y) :
    CFSG.LinearGroups.stdHermForm h 3 (w.reindex hypSwap x) (w.reindex hypSwap y) =
      hypGram 1 1 F x y := by
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hypSwap_symm_apply,
    hypSwap_symm_apply, hw, hypGram_apply, hypGram_apply, hypPartner_hypPartner]
  by_cases hxy : y = hypPartner x
  · rw [ite_eq_left (by rw [hxy, hypPartner_hypPartner]), ite_eq_left hxy]
  · rw [ite_eq_right (fun h' => hxy (by rw [← h', hypPartner_hypPartner])), ite_eq_right hxy]

theorem eq_one_of_mulVec_basis {ι : Type*} [Fintype ι] (w : Module.Basis ι F (Fin 3 → F))
    {G : Matrix (Fin 3) (Fin 3) F} (hG : ∀ i, G *ᵥ w i = w i) : G = 1 := by
  have hlin : Matrix.toLin' G = LinearMap.id := w.ext fun i => by
    rw [Matrix.toLin'_apply, hG, LinearMap.id_apply]
  rw [← Matrix.toLin'_one] at hlin
  exact Matrix.toLin'.injective hlin

theorem exists_transverse_sylow_pair [CharP F 2] (h : UnitaryFieldData 2 a F) :
    ∃ S₁ S₂ : Subgroup (unitarySU 2 a F 3), IsPGroup 2 S₁ ∧ IsPGroup 2 S₂ ∧
      2 ^ (3 * a) ≤ Nat.card S₁ ∧ 2 ^ (3 * a) ≤ Nat.card S₂ ∧
      ∀ g₁ ∈ S₁, ∀ g₂ ∈ S₂, ∀ z ∈ Subgroup.center (unitarySU 2 a F 3), g₁ = g₂ * z → g₁ = 1 := by
  obtain ⟨w, hw, -⟩ : ∃ w : Module.Basis (HypIndex 1 1) F (Fin 3 → F),
      (∀ x y, CFSG.LinearGroups.stdHermForm h 3 (w x) (w y) = hypGram 1 1 F x y) ∧
        (⊥ : Submodule F (Fin 3 → F)) ≤ aSpanTop F ⇑w :=
    CFSG.SeitzReduction.UnitaryPilot.exists_wittBasis_le_aSpanTop h (n := 3) ⊥ (by simp)
  set w' := w.reindex hypSwap with hw'def
  have hw' := gram_reindex_hypSwap h hw
  have hw'a : w' (.inl 0) = w (.inr (.inr 0)) := by
    rw [hw'def, Module.Basis.reindex_apply, hypSwap_symm_apply]; rfl
  have hw'z : w' (.inr (.inl 0)) = w (.inr (.inl 0)) := by
    rw [hw'def, Module.Basis.reindex_apply, hypSwap_symm_apply]; rfl
  refine ⟨pairRadical 2 a (aSpanTop F ⇑w) (aSpanTop F ⇑w ⊔ zSpan F ⇑w),
    pairRadical 2 a (aSpanTop F ⇑w') (aSpanTop F ⇑w' ⊔ zSpan F ⇑w'),
    isPGroup_pairRadical 2 a _ _, isPGroup_pairRadical 2 a _ _, ?_, ?_, ?_⟩
  · have := card_pairRadical_ge h w hw
    rwa [show a * (1 * (1 + 2 * 1)) = 3 * a by ring] at this
  · have := card_pairRadical_ge h w' hw'
    rwa [show a * (1 * (1 + 2 * 1)) = 3 * a by ring] at this
  intro g₁ hg₁ g₂ hg₂ z hz hg
  rw [span_inl_eq, span_z_eq] at hg₁
  rw [span_inl_eq, span_z_eq, hw'a, hw'z] at hg₂
  obtain ⟨h11, h12, h13⟩ := hg₁
  obtain ⟨h21, h22, h23⟩ := hg₂
  set a₀ := w (.inl 0) with ha₀
  set z₀ := w (.inr (.inl 0)) with hz₀
  set b₀ := w (.inr (.inr 0)) with hb₀
  set G₁ := ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  set G₂ := ((g₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  obtain ⟨c, -, -, hzc⟩ := mem_unitaryScalars.mp
    (CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_le_unitaryScalars h 3 hz)
  have hZ : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) := by
    rw [hzc]
    rfl
  have hG : G₁ = G₂ * Matrix.scalar (Fin 3) (c : F) := by
    rw [← hZ]
    exact congrArg (fun x : unitarySU 2 a F 3 => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hg
  have ha₁ : G₁ *ᵥ a₀ = a₀ := h11 _ (Submodule.mem_span_singleton_self _)
  have hy := h23 a₀
  have hc1 : (c : F) = 1 := by
    have e : (1 - (c : F)) • a₀ = (c : F) • (G₂ *ᵥ a₀ - a₀) := by
      have : G₁ *ᵥ a₀ = (c : F) • (G₂ *ᵥ a₀) := by
        have hs : Matrix.scalar (Fin 3) (c : F) *ᵥ a₀ = (c : F) • a₀ := by
          ext i
          rw [Matrix.scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        rw [hG, ← mulVec_mulVec, hs, mulVec_smul]
      rw [ha₁] at this
      rw [smul_sub, sub_smul, one_smul, ← this]
    have hcoord := congrArg (fun v => w.repr v (.inl 0)) e
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, ha₀, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one] at hcoord
    rw [coord_eq_zero_of_mem_sup hy, mul_zero] at hcoord
    exact (sub_eq_zero.mp hcoord).symm
  have hG12 : G₁ = G₂ := by
    rw [hG, hc1, Matrix.scalar_apply, diagonal_one, Matrix.mul_one]
  have hb₁ : G₁ *ᵥ b₀ = b₀ := by
    rw [hG12]
    exact h21 _ (Submodule.mem_span_singleton_self _)
  have hz₁ : G₁ *ᵥ z₀ = z₀ := by
    have m1 : G₁ *ᵥ z₀ - z₀ ∈ Submodule.span F {a₀} :=
      h12 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    have m2 : G₁ *ᵥ z₀ - z₀ ∈ Submodule.span F {b₀} := by
      rw [hG12]
      exact h22 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp m1
    obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp m2
    have hcoord := congrArg (fun v => w.repr v (.inl 0)) (hμ.trans hν.symm)
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, ha₀, hb₀, Module.Basis.repr_self] at hcoord
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by simp), mul_one, mul_zero] at hcoord
    rw [← sub_eq_zero, ← hμ, hcoord, zero_smul]
  have h1 : G₁ = 1 := eq_one_of_mulVec_basis w fun i => by
    rcases i with i | i | i
    · rw [show i = 0 from Subsingleton.elim _ _]; exact ha₁
    · rw [show i = 0 from Subsingleton.elim _ _]; exact hz₁
    · rw [show i = 0 from Subsingleton.elim _ _]; exact hb₁
  exact Subtype.ext (Units.ext h1)

end SUFacts

end CFSG.StandardType
