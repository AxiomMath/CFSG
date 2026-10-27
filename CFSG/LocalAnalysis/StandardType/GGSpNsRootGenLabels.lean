module

public import CFSG.LocalAnalysis.StandardType.GGRootGenSpOrthSplitAvoid
public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenAsm
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftSp
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open CFSG.LieType.Steinberg.CentralExt
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

theorem statedSp_injective_of_cover
    {K : Type} [Field K] [Finite K]
    {f n : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 2 ≤ n) (L' : Type) [Group L']
    [Finite L'] (ψ : L' →* LargeEvenSpGroup K n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) : Function.Injective ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card hK
  set Z := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars n K
  have hZc : Z ≤ Subgroup.center (StatedSp n K) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Group.IsPerfect (StatedSp n K) := SpClosed.isPerfect_statedSp' (Or.inl h4)
  obtain ⟨σ, hσ⟩ := CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (SpClosed.psp_two_cover_trivial hK (by omega) hn fun _ => hf)
    (fun E _ _ π hπ hcen hc => SpClosed.sp_exists_section_of_coprime E π hπ hcen hc) L' ψ hψ hker
  have : Group.IsPerfect L' := ⟨hperf⟩
  exact (MonoidHom.ker_eq_bot_iff ψ).mp (SL2Closed.ker_eq_bot_of_section ψ hker σ hσ)

theorem ggTorusRootGenAvoidKG_symplecticNs
    {K : Type} [Field K] [Finite K]
    {f n p : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSpGroup K n))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K n)) (LargeEvenGSpSet K n)) := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero n := ⟨by omega⟩
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let e : LargeEvenProj (LargeEvenSpGroup K n) ≃* Gsp (spForm n K) :=
    spProjEquivSp.trans spEquiv
  have hZ : Subgroup.center (Gsp (spForm n K)) = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have hz' : (spEquiv : StatedSp n K ≃* Gsp (spForm n K)).symm z ∈
        Subgroup.center (StatedSp n K) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have h := Subgroup.mem_center_iff.mp hz (spEquiv g)
      apply (spEquiv : StatedSp n K ≃* Gsp (spForm n K)).injective
      simp only [map_mul, MulEquiv.apply_symm_apply, h]
    rw [center_statedSp_eq_bot_of_charP_two (by omega : 1 ≤ n), Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← (spEquiv : StatedSp n K ≃* Gsp (spForm n K)).apply_symm_apply z, hz',
      map_one]
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (fun φ hφ => ?_)
    (SpNsRootGen.ggTorusRootGenAvoidKG_gsp spForm_isAlt spForm_nondegenerate hp hp2 hpq h4
      finrank_spSpace hn (fun L' _ _ ψ hψ hker hperf => ?_) hZ r)
  · obtain ⟨x, rfl⟩ := sp_I_subset_inn hφ
    refine ⟨e x, MulEquiv.ext fun y => ?_⟩
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  · have h := statedSp_injective_of_cover hK hf (by omega) L'
      ((spEquiv : StatedSp n K ≃* Gsp (spForm n K)).symm.toMonoidHom.comp ψ)
      (spEquiv.symm.surjective.comp hψ)
      (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf
    exact fun x y hxy => h (congrArg spEquiv.symm hxy)

end CFSG.StandardType

end
