module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.Adapters.LieModelSimple
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin U54InvRank
open CFSG.Blueprint (LieModel)

theorem U54InvRank.twelve_le_rkIdx_fixV {S : Type} [Group S] (hS : LieModel S .PSU 5 2 2)
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1) (ρ : S →* MulAut U) {l : S}
    (hl : orderOf l = 2) (hρl : ρ l ≠ 1) : 12 ≤ rkIdx (fixV (Subgroup.zpowers (ρ l))) := by
  obtain ⟨φS, gS, hrel, hs1, hinv⟩ := exists_torusPackage hS
  have hsimple : IsSimpleGroup S :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exact absurd (ρ.mem_ker.mp (h ▸ Subgroup.mem_top l)) hρl
  have hφ : (ρ.comp φS) (.ofAdd cS) ≠ 1 := by
    intro h
    apply hs1
    apply hinj
    simpa using h
  have h24 := twentyFour_le_rkIdx hU (ρ.comp φS) hφ (fun i => ρ (gS i)) (fun i c => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, ← map_inv, ← map_mul, hrel])
  obtain ⟨x, hx⟩ := hinv l hl
  have hc5 : (Multiplicative.ofAdd cS) ^ 5 = 1 := by decide
  set y : S := x * φS (.ofAdd cS) * x⁻¹ with hy
  have hy5 : (ρ y) ^ 5 = 1 := by
    rw [← map_pow, hy, conj_pow, ← map_pow, hc5, map_one, mul_one, mul_inv_cancel, map_one]
  have hl2 : ρ l * ρ l = 1 := by
    rw [← map_mul, ← pow_two, ← hl, pow_orderOf_eq_one, map_one]
  have hly : ρ l * ρ y * (ρ l)⁻¹ = (ρ y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hx, map_inv]
  have hsq := CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.index_fixV_le_sq_of_inverts
    (W := U) (p := 5) ⟨2, rfl⟩ hy5 hl2 hly
  have hconj : (fixV (Subgroup.zpowers (ρ y))).index =
      (fixV (Subgroup.zpowers ((ρ.comp φS) (.ofAdd cS)))).index := by
    rw [hy, map_mul, map_mul, map_inv]
    exact FixVLat.index_fixV_zpowers_conj _ _
  rw [hconj, CFSG.Quasithin.B1.index_eq_two_pow hU, CFSG.Quasithin.B1.index_eq_two_pow hU,
    ← pow_mul] at hsq
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hsq
  omega

theorem k146U54InvRank_holds : K146U54InvRank := fun _ _ _ hS _ _ _ hU ρ _ _ hl hρl =>
  le_trans (by norm_num) (U54InvRank.twelve_le_rkIdx_fixV hS hU ρ hl hρl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
