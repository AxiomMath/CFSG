module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4TorusDiag
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoF4Transport

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU)

theorem isDiag_of_conj_torusSU_eq_smul {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {w : GL (Fin 6) K}
    (hw : ∀ d ∈ CFSG.RankThree.PartOne.KFU.torusSU 3 6 K, ∃ c : K,
      ((w * d * w⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        c • (d : Matrix (Fin 6) (Fin 6) K)) :
    (w : Matrix (Fin 6) (Fin 6) K).IsDiag := by
  classical
  let e : K ≃+* F4 := ringEquivF4 hK
  let w' : GL (Fin 6) F4 := Matrix.GeneralLinearGroup.map (e : K →+* F4) w
  have hw' : ∀ d' ∈ torusSU 3 6 F4, ∃ c : F4,
      ((w' * d' * w'⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • (d' : Matrix (Fin 6) (Fin 6) F4) := by
    intro d' hd'
    let d : GL (Fin 6) K := Matrix.GeneralLinearGroup.map (e.symm : F4 →+* K) d'
    obtain ⟨c, hc⟩ := hw d ((mem_torusSU_map_iff e.symm d').mp hd')
    have hmapd : Matrix.GeneralLinearGroup.map (e : K →+* F4) d = d' := glMap_glMap_symm e d'
    refine ⟨e c, ?_⟩
    have hGL : (w' * d' * w'⁻¹ : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.map (e : K →+* F4) (w * d * w⁻¹) := by
      rw [map_mul, map_mul, map_inv, hmapd]
    have hmat : ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map (e : K → F4) =
        (d' : Matrix (Fin 6) (Fin 6) F4) := by
      simpa [Matrix.GeneralLinearGroup.val_map_apply] using
        congrArg (fun g : GL (Fin 6) F4 => ((g : Matrix (Fin 6) (Fin 6) F4))) hmapd
    calc ((w' * d' * w'⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
        = ((Matrix.GeneralLinearGroup.map (e : K →+* F4) (w * d * w⁻¹) : GL (Fin 6) F4) :
            Matrix (Fin 6) (Fin 6) F4) := by rw [hGL]
      _ = (((w * d * w⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).map (e : K → F4) :=
            Matrix.GeneralLinearGroup.val_map_apply _ _
      _ = (c • ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).map (e : K → F4) := by rw [hc]
      _ = e c • (((d : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).map (e : K → F4) :=
            Matrix.map_smul' (e : K → F4) c _ (fun a b => map_mul e a b)
      _ = e c • (d' : Matrix (Fin 6) (Fin 6) F4) := by rw [hmat]
  have hdiag' : ((w : Matrix (Fin 6) (Fin 6) K).map (e : K → F4)).IsDiag :=
    CFSG.GGQ2Prime.isDiag_of_conj_torusSU_eq_smul hw'
  intro i j hij
  have h2 : e ((w : Matrix (Fin 6) (Fin 6) K) i j) = 0 := hdiag' hij
  exact e.injective (by rw [h2, map_zero])

end CFSG.StandardType.USixTwo

end
