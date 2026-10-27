module

public import CFSG.LocalAnalysis.StandardType.GGTPRowDataDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTP_su_le_ker_det (n : ℕ) (K : Type) [Field K] :
    LargeEvenSUGroup (Fin 7) K (2 ^ n) ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin 7) K →* Kˣ).ker := by
  change CFSG.MatrixModel.unitaryCore (Fin 7) K (2 ^ n) ≤ _
  unfold CFSG.MatrixModel.unitaryCore
  refine (Subgroup.closure_le _).mpr ?_
  rintro B ⟨hB1, -⟩
  show Matrix.GeneralLinearGroup.det B = 1
  exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hB1]; rfl)

private theorem ggTP_subgroupOf_scalars_pow_seven {K : Type} [Field K]
    {H : Subgroup (GL (Fin 7) K)}
    (hdet : H ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 7) K →* Kˣ).ker)
    (z : (LargeEvenScalars (Fin 7) K).subgroupOf H) : z ^ 7 = 1 := by
  obtain ⟨c, hc⟩ := z.2
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 7) c ∈
      (Matrix.GeneralLinearGroup.det : GL (Fin 7) K →* Kˣ).ker := by
    rw [hc]
    exact hdet z.1.2
  have hc7 : c ^ 7 = 1 := by
    rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.det_scalar] at hmem
    simpa using hmem
  have hA : ((z.1 : H) : GL (Fin 7) K) = Matrix.GeneralLinearGroup.scalar (Fin 7) c :=
    hc.symm
  have hd : ((z.1 : H) : GL (Fin 7) K) ^ 7 = 1 := by
    calc ((z.1 : H) : GL (Fin 7) K) ^ 7
        = (Matrix.GeneralLinearGroup.scalar (Fin 7) c) ^ 7 := by rw [hA]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 7) (c ^ 7) := by rw [map_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 7) 1 := by rw [hc7]
      _ = 1 := by rw [map_one]
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hd

theorem ggTPRowData_twA {n : ℕ} {Y : Type} [Group Y] (hY : GGHasLabel ⟨.twA, 6, n⟩ Y) :
    GGTPRowDatum Y := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hY
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard2 : Fintype.card K = 2 ^ (n * 2) := by
    rw [← Nat.card_eq_fintype_card, hKcard, pow_mul]
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow hcard2
  have hSUdet : LargeEvenSUGroup (Fin 7) K (2 ^ n) ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin 7) K →* Kˣ).ker :=
    ggTP_su_le_ker_det n K
  refine ⟨Fin 7, inferInstance, inferInstance, K, inferInstance, inferInstance,
    LargeEvenSUGroup (Fin 7) K (2 ^ n), ⟨e⟩, by decide, hchar, ?_⟩
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hz7 : z ^ 7 = 1 := ggTP_subgroupOf_scalars_pow_seven hSUdet z
  have hdvd : orderOf z ∣ 7 := orderOf_dvd_of_pow_eq_one hz7
  rw [hz] at hdvd
  exact absurd hdvd (by decide)

end CFSG.StandardType

end
