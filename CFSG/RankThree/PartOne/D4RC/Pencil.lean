module

public import CFSG.RankThree.PartOne.D4RC.RootGroups
public import CFSG.RankThree.PartOne.D4RC.Transport
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec8Projection
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
open CFSG.Timmesfeld.ARS (conjSub Commuting)
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Pencil

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}

theorem rcq_le_fix (D : RclAlgData F i) :
    rclA0AlgOf L (fixSubfield σ) D.H' ≤ fixSubgroup D.Φ' := by
  rw [rclA0AlgOf_eq_range]
  rintro _ ⟨t, rfl⟩
  exact D.a0 (Multiplicative.toAdd t)

abbrev rcqTheta (sp : RclSpecial F x i) (D : RclAlgData F i) : ↥(fixSubgroup D.Φ') →* 𝒞[K, σ] :=
  (rclPx sp).subtype.comp (rcaTheta sp D).toMonoidHom

theorem rcqTheta_injective (sp : RclSpecial F x i) (D : RclAlgData F i) :
    Function.Injective (rcqTheta sp D) :=
  (Subgroup.subtype_injective _).comp (rcaTheta sp D).injective

theorem rcq_rcaA0_eq_map (sp : RclSpecial F x i) (D : RclAlgData F i) :
    rcaA0 sp D = ((rclA0AlgOf L (fixSubfield σ) D.H').subgroupOf (fixSubgroup D.Φ')).map
      (rcqTheta sp D) := by
  rw [rcaA0, Subgroup.map_map]

theorem rcq_pencil (sp : RclSpecial F x i) (D : RclAlgData F i) (h1 : ε = 1) :
    ∃ g₁ ∈ rclPx sp, ∃ g₂ ∈ rclPx sp,
      Commuting (rcaA0 sp D) (conjSub (rcaA0 sp D) g₁) ∧
      Commuting (rcaA0 sp D) (conjSub (rcaA0 sp D) g₂) ∧
      ¬ Commuting (conjSub (rcaA0 sp D) g₁) (conjSub (rcaA0 sp D) g₂) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have h2 : (2 : fixSubfield σ) = 0 := by
    have h := CharP.cast_eq_zero L ℓ
    rw [F.hℓ2] at h
    apply (algebraMap (fixSubfield σ) L).injective
    rw [map_ofNat, map_zero]
    exact_mod_cast h
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ
  have : Finite (fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hkc]; exact (pow_pos hℓ.pos _).ne')
  obtain ⟨g₁, hg₁, g₂, hg₂, hc1, hc2, b₁, hb₁, b₂, hb₂, hne⟩ :=
    rcl_phi3_split h2 D.Φ' D.H (D.split h1)
  rw [← D.H'_split h1] at hc1 hc2 hb₁ hb₂
  set A'' := rclA0AlgOf L (fixSubfield σ) D.H' with hA''
  set A' := A''.subgroupOf (fixSubgroup D.Φ') with hA'
  set φ := rcqTheta sp D with hφ
  have hle := rcq_le_fix D
  have hcomm : ∀ g (hg : g ∈ fixSubgroup D.Φ'), (∀ a ∈ A'',
      ∀ b ∈ A''.map (MulAut.conj g).toMonoidHom, a * b = b * a) →
        Commuting A' (conjSub A' ⟨g, hg⟩) := by
    intro g hg hc
    rintro a ha _ ⟨y, hy, rfl⟩
    exact Subtype.ext (hc a ha _ ⟨y, hy, rfl⟩)
  refine ⟨φ ⟨g₁, hg₁⟩, (rcaTheta sp D ⟨g₁, hg₁⟩).2, φ ⟨g₂, hg₂⟩, (rcaTheta sp D ⟨g₂, hg₂⟩).2,
    ?_, ?_, ?_⟩
  · rw [rcq_rcaA0_eq_map, ← hφ, rcm_conjSub_map]
    exact rcm_commuting_map φ (hcomm g₁ hg₁ hc1)
  · rw [rcq_rcaA0_eq_map, ← hφ, rcm_conjSub_map]
    exact rcm_commuting_map φ (hcomm g₂ hg₂ hc2)
  · rw [rcq_rcaA0_eq_map, ← hφ, rcm_conjSub_map, rcm_conjSub_map,
      rcm_commuting_map_iff (rcqTheta_injective sp D)]
    intro hC
    obtain ⟨y₁, hy₁, rfl⟩ := hb₁
    obtain ⟨y₂, hy₂, rfl⟩ := hb₂
    have h := hC _ ⟨⟨y₁, hle hy₁⟩, hy₁, rfl⟩ _ ⟨⟨y₂, hle hy₂⟩, hy₂, rfl⟩
    exact hne (congrArg Subtype.val h)

end Pencil

end CFSG.RankThree.PartOne.D4RC
