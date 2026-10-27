module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Open.PGLModelStated
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG.Open (StatedOmega StatedQuadMinus StatedProj StatedScalars)
open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjEquivProjImage)
open Matrix

abbrev Om8 : Type := ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1))

@[expose] noncomputable def gf2EquivZMod : GaloisField 2 1 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

theorem gf2_eq_zero_or_one (r : GaloisField 2 1) : r = 0 ∨ r = 1 := by
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases key (gf2EquivZMod r) with h | h
  · exact Or.inl (gf2EquivZMod.injective (by rw [h, map_zero]))
  · exact Or.inr (gf2EquivZMod.injective (by rw [h, map_one]))

theorem gf2_one_add_one : (1 : GaloisField 2 1) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharP.cast_eq_zero (GaloisField 2 1) 2

theorem eq_one_of_irreducible_gf2 {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  rcases gf2_eq_zero_or_one c with rfl | rfl
  · exact (hbc 0 (by simp)).elim
  · rcases gf2_eq_zero_or_one b with rfl | rfl
    · exact (hbc 1 (by rw [one_pow, zero_mul, add_zero, gf2_one_add_one])).elim
    · exact ⟨rfl, rfl⟩

theorem subsingleton_units_gf2 : Subsingleton (GaloisField 2 1)ˣ := by
  refine ⟨fun u v => Units.ext ?_⟩
  rcases gf2_eq_zero_or_one (u : GaloisField 2 1) with h | h
  · exact absurd h u.ne_zero
  · rcases gf2_eq_zero_or_one (v : GaloisField 2 1) with h' | h'
    · exact absurd h' v.ne_zero
    · rw [h, h']

theorem statedScalars_gf2_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (GaloisField 2 1) = ⊥ := by
  haveI := subsingleton_units_gf2
  rw [eq_bot_iff]
  intro x hx
  rw [StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Subsingleton.elim c 1, map_one, Subgroup.mem_bot]

theorem statedScalars_subgroupOf_gf2_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (GaloisField 2 1))) :
    (StatedScalars ι (GaloisField 2 1)).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgZ
  rw [Subgroup.mem_subgroupOf, statedScalars_gf2_eq_bot, Subgroup.mem_bot] at hgZ
  rw [Subgroup.mem_bot]
  exact Subtype.ext hgZ

@[expose] noncomputable def statedProjEquivSelf {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (GaloisField 2 1))) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_gf2_eq_bot H)).trans
    QuotientGroup.quotientBot

theorem map_omega_gf2 :
    (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) 1 1)).map
        (glCongr (ι := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) gf2EquivZMod).toMonoidHom =
      StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1) :=
  CFSG.ClassicalInvolution.Upgrade.map_statedOmega
    (QK := StatedQuadMinus 4 (GaloisField 2 1) 1 1) (QL := StatedQuadMinus 4 (ZMod 2) 1 1)
    gf2EquivZMod
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp gf2EquivZMod
      (map_one gf2EquivZMod) (map_one gf2EquivZMod) v)

theorem nonempty_projOmegaMinus_equiv_om8 {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (projOmegaMinus 3 (GaloisField 2 1) b c ≃* Om8) := by
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible_gf2 hbc
  have hP : CFSG.PGLModel.projImage (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) 1 1)) =
      projOmegaMinus 3 (GaloisField 2 1) 1 1 :=
    CFSG.PGLModel.projImage_statedOmegaMinus 4 (GaloisField 2 1) 1 1
  exact ⟨((statedProjEquivProjImage _ hP).symm.trans
    (statedProjEquivSelf (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) 1 1)))).trans
    ((MulEquiv.subgroupMap (glCongr (ι := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) gf2EquivZMod) _).trans
      (MulEquiv.subgroupCongr map_omega_gf2))⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
