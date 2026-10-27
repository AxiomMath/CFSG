module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityNonOrthBasic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Aut

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open scoped commutatorElement

namespace NonOrthSocle

theorem nonempty_mulEquiv_of_commutator_le {Y : Type} [Group Y]
    {S : Subgroup (Y ⧸ Subgroup.center Y)} (hS : NonOrthSocle _ S) {A : Type} [Group A]
    {N P : Subgroup A} (hPN : P ≤ N) (hkey : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ P) (φ : Y →* ↥N)
    (hφ : Function.Surjective φ) {U : Type} [Group U] [IsSimpleGroup U]
    (hU : commutator U = ⊤) (ρ : ↥P →* U) (hρ : Function.Surjective ρ) :
    Nonempty (↥S ≃* U) := by
  let f : Y →* A := N.subtype.comp φ
  have hD : commutator Y ≤ P.comap f := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hkey _ (φ a).2 _ (φ b).2
  let φP : ↥(commutator Y) →* ↥P :=
    (f.comp (commutator Y).subtype).codRestrict P fun d => hD d.2
  let σ := ρ.comp φP
  have hσ : Function.Surjective σ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hU, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨p, rfl⟩ := hρ a
    obtain ⟨q, rfl⟩ := hρ b
    obtain ⟨y, hy⟩ := hφ ⟨p, hPN p.2⟩
    obtain ⟨z, hz⟩ := hφ ⟨q, hPN q.2⟩
    refine MonoidHom.mem_range.mpr ⟨⟨⁅y, z⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top y) (Subgroup.mem_top z)⟩, ?_⟩
    rw [← map_commutatorElement]
    change ρ (φP _) = ρ ⁅p, q⁆
    congr 1
    apply Subtype.ext
    change ((φ ⁅y, z⁆ : ↥N) : A) = _
    rw [map_commutatorElement, hy, hz]
    simp [commutatorElement_def]
  have hDS : (commutator Y).map (QuotientGroup.mk' (Subgroup.center Y)) = S := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def]
    exact hS.commutator_eq
  let α : ↥(commutator Y) →* ↥S :=
    (MulEquiv.subgroupCongr hDS).toMonoidHom.comp
      ((QuotientGroup.mk' (Subgroup.center Y)).subgroupMap (commutator Y))
  have hα : Function.Surjective α :=
    (MulEquiv.subgroupCongr hDS).surjective.comp (MonoidHom.subgroupMap_surjective _ _)
  have hcomm : ∀ x ∈ α.ker, ∀ y ∈ α.ker, x * y = y * x := by
    intro x hx y _
    have h1 : QuotientGroup.mk' (Subgroup.center Y) (x : Y) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext (Subgroup.mem_center_iff.mp h1 y).symm
  have hUnc : ¬ ∀ a b : U, a * b = b * a := by
    intro hc
    obtain ⟨u, hu⟩ := exists_ne (1 : U)
    have hmem : u ∈ commutator U := by
      rw [hU]
      exact Subgroup.mem_top u
    rw [commutator_def] at hmem
    have hle : ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc a b
    exact hu (Subgroup.mem_bot.mp (hle hmem))
  have := hS.simple
  exact nonempty_mulEquiv_of_surjective_of_comm_ker α σ hα hσ hcomm hUnc

end NonOrthSocle

theorem exists_surjective_quotient_center {Ω Ω' P : Type*} [Group Ω] [Group Ω'] [Group P]
    (e : Ω ≃* Ω') (ψ : Ω →* P) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center Ω) :
    ∃ ρ : P →* Ω' ⧸ Subgroup.center Ω', Function.Surjective ρ := by
  let g : Ω →* Ω' ⧸ Subgroup.center Ω' := (QuotientGroup.mk' _).comp e.toMonoidHom
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hle : ψ.ker ≤ g.ker := by
    intro x hx
    have h1 : e x ∈ Subgroup.center Ω' := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hx) y']
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' _ (e x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1
  refine ⟨ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨g, hle⟩, fun u => ?_⟩
  obtain ⟨x, rfl⟩ := hg u
  exact ⟨ψ x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩

theorem exists_psu_four_three_of_projOmegaMinus {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ (U : Type) (_ : Group U), IsSimpleGroup U ∧ commutator U = ⊤ ∧
      CFSG.Blueprint.LieModel U .PSU 4 3 1 ∧
      ∃ ρ : ↥(CFSG.PGLModel.projOmegaMinus 2 F b c) →* U, Function.Surjective ρ := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hbc
  have hdim : Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hno : ¬ ∃ T : Submodule F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      Module.finrank F T = 3 ∧ ∀ x ∈ T, quadMinus 3 F b c x = 0 := by
    rintro ⟨T, hT, hTQ⟩
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num) hbc
      ⟨T, by omega, hTQ⟩
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd (quadMinus 3 F b c)
      hQ hdim hno
  have hmodel :=
    (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_six
      (p := 3) (e := 1) Nat.prime_three (by norm_num) le_rfl (by rw [hF3]; norm_num)
      (quadMinus 3 F b c) hQ hdim hno ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩).2
  refine ⟨_, inferInstance, hq.2.1, ?_, hmodel, ?_⟩
  · have := hq.1
    exact @Group.IsPerfect.commutator_eq_top _ _
      (Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center _)))
  ·
    let e₁ : ↥(StatedOmega (StatedQuadMinus 3 F b c)) ≃*
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c)⁆ :=
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ F).subgroupMap _).trans
        (MulEquiv.subgroupCongr (by
          rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadMinus 3 F b c)]
          exact Subgroup.map_comap_eq_self_of_surjective
            (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ F).surjective _))
    let eΩ := e₁.trans
      ((MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _).symm).trans
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm)
    let ψ : ↥(StatedOmega (StatedQuadMinus 3 F b c)) →*
        ↥(CFSG.PGLModel.projOmegaMinus 2 F b c) :=
      (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedOmegaMinus 3 F b c)).toMonoidHom.comp
        (Matrix.ProjGenLinGroup.mk.subgroupMap _)
    have hψ : Function.Surjective ψ :=
      (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedOmegaMinus 3 F b c)).surjective.comp
        (MonoidHom.subgroupMap_surjective _ _)
    refine exists_surjective_quotient_center eΩ ψ hψ fun x hx => ?_
    have h1 : Matrix.ProjGenLinGroup.mk
        (x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ∈ Subgroup.center _ := by
      rw [← Matrix.ProjGenLinGroup.ker_mk]
      exact h1
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp h2 y)

namespace NonOrthSocle

theorem false_of_isOrth63Reflection {Y₀ : Type} [Group Y₀]
    {S : Subgroup (Y₀ ⧸ Subgroup.center Y₀)} (hS : NonOrthSocle _ S) {s₀ : Y₀}
    (hO : IsOrth63Reflection Y₀ s₀) : False := by
  obtain ⟨F, _, _, hF3, b, c, hbc, N, hPN, hNO, φ, hφ, -, -, -⟩ := hO
  obtain ⟨U, _, hU, hUperf, hmodel, ρ, hρ⟩ := exists_psu_four_three_of_projOmegaMinus hF3 hbc
  have hkey : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ CFSG.PGLModel.projOmegaMinus 2 F b c := by
    intro x hx y hy
    obtain ⟨g₁, hg₁, rfl⟩ := hNO hx
    obtain ⟨g₂, hg₂, rfl⟩ := hNO hy
    rw [← map_commutatorElement Matrix.ProjGenLinGroup.mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.commutator_mem_commutator hg₁ hg₂)
  obtain ⟨ι⟩ := hS.nonempty_mulEquiv_of_commutator_le hPN hkey φ hφ hUperf ρ hρ
  exact hS.not_card_outer_dvd 3 (CFSG.OddStandard.SmallF3.Omega.aor_card_outer_dvd_of_psu_four
    (CFSG.Blueprint.LieModel.of_mulEquiv ι.symm hmodel))

end NonOrthSocle

end CFSG.OddTranspositions.PartFour
