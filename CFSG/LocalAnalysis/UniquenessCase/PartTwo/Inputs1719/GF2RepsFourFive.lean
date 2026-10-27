module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourFiveDefs
import CFSG.Quasithin.Background.E3Gen
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.HDefs
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E1Inherit
public import CFSG.Quasithin.Background.E1Residual
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup

theorem w4Lem4_5K_holds : W4Lem4_5K := by
  intro W _ _ _ Y H T A K Ω j hHY hS hΩ hΩa hAΩ hAT hK
  rw [commSub_eq_bot_iff]
  intro v hv
  rw [mem_fixV] at hv ⊢
  have hAin : A ∈ E3.aSet (j + 1) Y := hΩa A hAΩ
  have hAab : IsElemAbelian 2 A := CFSG.Quasithin.H.isElemAbelian2_iff.mp hAin.2.2.1
  obtain ⟨-, hAcard⟩ := E3.card_le_of_isE hS hAT hAab hK
  have hmA : E3.mQuot A (A ⊓ pCoreOf 2 K) ≤ j := by
    have h1 := E3.card_eq_two_pow_mul (E3.isPGroup_of_isElemAbelian2 hAin.2.2.1)
      (inf_le_left : A ⊓ pCoreOf 2 K ≤ A)
    rw [h1] at hAcard
    have h2 : 2 ^ E3.mQuot A (A ⊓ pCoreOf 2 K) ≤ 2 ^ j :=
      Nat.le_of_mul_le_mul_right hAcard Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hO2T : pCoreOf 2 K ≤ T := (E1.pCoreOf_two_le_of_isSylowIn hK.2.2.1).trans inf_le_left
  have hkey : ∀ h ∈ K, ∀ a ∈ A.map (MulAut.conj h).toMonoidHom, a v = v := by
    intro h hhK a ha
    let Ah : Subgroup (MulAut W) := A.map (MulAut.conj h).toMonoidHom
    have hAh_eq : Ah = A.map (MulAut.conj h).toMonoidHom := rfl
    have hhY : h ∈ Y := hHY (hK.1 hhK)
    have hAhΩ : Ah ∈ Ω := hΩ A hAΩ h hhY
    have hAhA : Ah ∈ E3.aSet (j + 1) Y := hΩa Ah hAhΩ
    have hAhAb : IsElemAbelian 2 Ah := CFSG.Quasithin.H.isElemAbelian2_iff.mp hAhA.2.2.1
    have hAh2 : IsPGroup 2 ↥Ah := E3.isPGroup_of_isElemAbelian2 hAhA.2.2.1
    have hpCore : (pCoreOf 2 K).map (MulAut.conj h).toMonoidHom = pCoreOf 2 K := by
      rw [show (pCoreOf 2 K).map (MulAut.conj h).toMonoidHom =
          conjSubgroup (pCoreOf 2 K) h⁻¹ from by simp only [conjSubgroup, inv_inv]]
      exact RonanE42.conjSubgroup_pCoreOf (H := K) (g := h⁻¹) (K.inv_mem hhK)
    have hmconj : E3.mQuot Ah ((A ⊓ pCoreOf 2 K).map (MulAut.conj h).toMonoidHom) =
        E3.mQuot A (A ⊓ pCoreOf 2 K) := by
      unfold E3.mQuot
      rw [hAh_eq,
        Subgroup.relIndex_map_map_of_injective (A ⊓ pCoreOf 2 K) A (MulAut.conj h).injective]
    have hCeq : (A ⊓ pCoreOf 2 K).map (MulAut.conj h).toMonoidHom = Ah ⊓ pCoreOf 2 K := by
      rw [hAh_eq, Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hpCore]
    have hmAh : E3.mQuot Ah (Ah ⊓ pCoreOf 2 K) ≤ j := by
      rw [← hCeq, hmconj]
      exact hmA
    have hmAhT : E3.mQuot Ah (Ah ⊓ T) ≤ j :=
      (E3.mQuot_mono (inf_le_inf_left Ah hO2T)).trans hmAh
    have hAh_rk : j + 1 ≤ rk ↥Ah := by
      have h1 := E3.le_mQuot_bot_of_mem_aSet hAhA
      rwa [E3.mQuot_bot_eq_rk] at h1
    let B : Subgroup (MulAut W) := Ah ⊓ T
    have hB_eq : B = Ah ⊓ T := rfl
    have hBT : B ≤ T := hB_eq.le.trans inf_le_right
    have hBAh : B ≤ Ah := hB_eq.le.trans inf_le_left
    have hB2 : IsPGroup 2 ↥B := E3.isPGroup_of_isElemAbelian2 (B6.isElemAbelian2_mono
      hAhA.2.2.1 hBAh)
    have hmB : E3.mQuot Ah B ≤ j := hmAhT
    have hrk : rk ↥Ah = E3.mQuot Ah B + rk ↥B := by
      have h1 := E3.card_eq_two_pow_mul hAh2 hBAh
      rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAh2,
        CFSG.Quasithin.card_eq_two_pow_of_isPGroup hB2, ← pow_add] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    obtain ⟨D, hDB, -, hmD⟩ := E3.exists_mem_le_mQuot_eq (B2F.isElemAbelian_mono hBAh hAhAb)
      (c := j - E3.mQuot Ah B) (by omega) (b := 1) B.one_mem
    have hDAh : D ≤ Ah := hDB.trans hBAh
    have hDT : D ≤ T := hDB.trans hBT
    have hmAD : E3.mQuot Ah D = j := by
      have hadd := E3.mQuot_add (V := Ah) hDB hBAh
      omega
    have hDWk : D ≤ Wk j T Ω := by
      rw [show Wk j T Ω = ⨆ (U : Subgroup (MulAut W)) (_ : U ≤ T)
          (_ : ∃ V ∈ Ω, U ≤ V ∧ E3.mQuot V U = j), U from rfl]
      exact le_iSup_of_le (f := fun U : Subgroup (MulAut W) =>
          ⨆ (_ : U ≤ T), ⨆ (_ : ∃ V ∈ Ω, U ≤ V ∧ E3.mQuot V U = j), U) D <|
        le_iSup_of_le hDT <| le_iSup_of_le ⟨Ah, hAhΩ, hDAh, hmAD⟩ le_rfl
    have hvD : v ∈ fixV D := fun d hd => hv d (hDWk hd)
    have hfix : fixV D = fixV Ah := hAhA.2.2.2 D hDAh (by omega)
    rw [hfix] at hvD
    exact (mem_fixV.mp hvD) a ha
  intro x hx
  have hsub : twoResidual K ≤ conjClosure A K :=
    E1.twoResidual_le_conjClosure (H := H) (T := T) (A := A) (K := K) ⟨j, hK⟩
  have hx' : x ∈ conjClosure A K := hsub hx
  have hle : conjClosure A K ≤ fixingSubgroup (MulAut W) ({v} : Set W) := by
    refine conjClosure_le ?_
    intro h hh z hz
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hz' : h * z * h⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hz
      simpa [MulAut.conj_apply] using h1
    simpa using hkey h hh _ hz'
  have hmem := (mem_fixingSubgroup_iff (MulAut W) (s := ({v} : Set W))).mp (hle hx')
  simpa using hmem v rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
