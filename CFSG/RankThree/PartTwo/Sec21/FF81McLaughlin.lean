module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesSym
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes
import CFSG.LargeExtraspecial.S12DWCount

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSp StatedProj)

theorem mcLaughlin_six {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 6)
    (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (∀ t ∈ S, IsF2Transvection t) ∧ G = Subgroup.closure S)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    G = ⊤ ∨ Nonempty (G ≃* StatedSp 3 (ZMod 2)) ∨ Nat.card G = 51840 ∨ Nat.card G = 40320 ∨
      Nat.card G = 5040 := by
  rcases mclaughlin_transvection_groups_F2 (by omega) G hgen hirr with
    hG | ⟨-, f, hnd, halt, hG⟩ | ⟨-, Q, hQ, hG⟩ | ⟨-, ⟨β, hβ⟩ | ⟨β, hβ⟩⟩
  · exact Or.inl hG
  · obtain ⟨m, hm, ⟨e⟩⟩ := mclt_exists_bilinIsometryGroup_equiv_statedSp hnd halt
    have hm3 : m = 3 := by omega
    subst hm3
    exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hG).trans e⟩)
  · right; right
    have : Finite V := Module.finite_of_finite (ZMod 2)
    have hV' : finrank (ZMod 2) V = 2 * 3 := by rw [hV]
    have hO : Nat.card G = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hG]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).surjective _))).toEquiv
    have h1 := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_mul_ncard_eq hQ hV'
    have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
    rw [h2] at h1
    have h64 := CFSG.LargeExtraspecial.S12DW.natCard_eq_four_pow hV'
    have hz := CFSG.LargeExtraspecial.S12DW.ncard_eq_zero_eq Q
    have hq := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
      (CFSG.LargeExtraspecial.S12DW.polar_eq_zero_imp hQ) h64
    rw [h64] at hz
    have h43 : (4 : ℕ) ^ 3 = 64 := by norm_num
    have h23 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h43, h23] at hq
    rw [h43] at hz
    rw [← hO] at h1
    rcases hq with hq | hq
    · right; left
      have h36 : {x | Q x = 0}.ncard = 36 := by omega
      rw [h36] at h1
      omega
    · left
      have h28 : {x | Q x = 0}.ncard = 28 := by omega
      rw [h28] at h1
      omega
  · right; right; right; right
    obtain ⟨e⟩ := mclt_nonempty_equiv_perm β
      (mclt_sumZeroRep_injective (m := finrank (ZMod 2) V + 1) (by rw [hV]; norm_num)) hβ
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, hV]
    rfl
  · right; right; right; left
    obtain ⟨e⟩ := mclt_nonempty_equiv_perm β
      (mclt_heartRep_injective (m := finrank (ZMod 2) V + 2) (by rw [hV]; norm_num)) hβ
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, hV]
    rfl

theorem finrank_range_id_add_toLin {n : ℕ} (g : GL (Fin n) (ZMod 2)) :
    finrank (ZMod 2) (LinearMap.range (LinearMap.id +
      (Matrix.GeneralLinearGroup.toLin g : (Fin n → ZMod 2) →ₗ[ZMod 2] _))) =
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1).rank := by
  have h : LinearMap.id + (Matrix.GeneralLinearGroup.toLin g : (Fin n → ZMod 2) →ₗ[ZMod 2] _) =
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1).mulVecLin := by
    refine LinearMap.ext fun w => funext fun i => ?_
    simp only [LinearMap.add_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply]
    rw [CharTwo.sub_eq_add, add_comm]
    rfl
  rw [h]
  rfl

local instance instModuleGF2Six :
    @Module (ZMod 2) (Fin 6 → ZMod 2) _ AddCommGroup.toAddCommMonoid :=
  Pi.module _ _ _

local instance instFiniteDimensionalGF2Six : FiniteDimensional (ZMod 2) (Fin 6 → ZMod 2) := by
  exact (inferInstance : FiniteDimensional (ZMod 2) (Fin 6 → ZMod 2))

theorem kf_mcLaughlin6 : KF_McLaughlin6 := by
  intro X hirr hgen
  set e : GL (Fin 6) (ZMod 2) ≃* LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2) :=
    Matrix.GeneralLinearGroup.toLin with he
  set X' := X.map e.toMonoidHom with hX'
  have hXX' : X ≃* X' := X.equivMapOfInjective _ e.injective
  have hS : X' = Subgroup.closure
      (e.toMonoidHom '' {g | g ∈ X ∧ ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1}) := by
    have h := congrArg (Subgroup.map e.toMonoidHom) hgen
    rwa [MonoidHom.map_closure] at h
  have hne : ∀ g : GL (Fin 6) (ZMod 2), ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1 →
      e g ≠ 1 := fun g hg h1 => by
    have hg1 : g = 1 := e.injective (h1.trans e.map_one.symm)
    simp [hg1] at hg
  have hirr' : ∀ W : Submodule (ZMod 2) (Fin 6 → ZMod 2),
      (∀ g ∈ X', ∀ w ∈ W, (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] _) w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun g hg w hw => hW (e g) ⟨g, hg, rfl⟩ w hw
  have hfin : finrank (ZMod 2) (Fin 6 → ZMod 2) = 6 := by
    exact (by simp : finrank (ZMod 2) (Fin 6 → ZMod 2) = 6)
  have key := mcLaughlin_six (V := Fin 6 → ZMod 2) hfin X'
  have hgen' : ∃ S, (∀ t ∈ S, IsF2Transvection t) ∧ X' = Subgroup.closure S := by
    refine ⟨_, fun t ht => ?_, hS⟩
    obtain ⟨g, ⟨-, hg⟩, rfl⟩ := ht
    exact ⟨hne g hg, (finrank_range_id_add_toLin g).trans hg⟩
  rcases key hgen' hirr' with hG | he₂ | h | h | h
  · left
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨g', hg', hgg⟩ := (Subgroup.eq_top_iff' X').mp hG (e g)
    rwa [e.injective hgg] at hg'
  · right; left
    obtain ⟨e₂⟩ := he₂
    have hZ : Subgroup.center (StatedSp 3 (ZMod 2)) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    have e₃ : StatedSp 3 (ZMod 2) ⧸ Subgroup.center (StatedSp 3 (ZMod 2)) ≃* X :=
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        e₂.symm).trans hXX'.symm
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₃
      (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 3 (ZMod 2)
        ⟨Nat.prime_two, le_rfl, by decide, by decide⟩ (by rw [Nat.card_zmod]; rfl))
  · exact Or.inr (Or.inr (Or.inl ((Nat.card_congr hXX'.toEquiv).trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.card_congr hXX'.toEquiv).trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.card_congr hXX'.toEquiv).trans h))))

end CFSG.RankThree.PartTwo.Sec21.FF81
