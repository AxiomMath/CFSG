module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3Defs
public import CFSG.Open.StatedAPI
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG.Open CFSG.Open.StatedAPI CFSG.Open.StatedCenterThree Matrix

theorem exists_scalar_of_mem_center_statedSL {K : Type} [Field K] {w : StatedSL 3 K}
    (hw : w ∈ Subgroup.center (StatedSL 3 K)) :
    ∃ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c := by
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_transvectionStruct
    (M := ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) fun t => by
      have ht : (⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩ : GL (Fin 3) K) ∈
          StatedSL 3 K := mem_statedSL_of_det t.det
      have h := Subgroup.mem_center_iff.mp hw ⟨_, ht⟩
      exact congrArg (fun g : StatedSL 3 K => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  exact ⟨c, hc.symm⟩

private theorem cyc3_mul_diagonal_mul_transpose {K : Type} [Field K] {c : K} (hc : c ^ 3 = 1) :
    (cyc3 : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, c, c ^ 2] * cyc3ᵀ =
      scalar (Fin 3) c * diagonal ![1, c, c ^ 2] := by
  have h3 : c * c ^ 2 = 1 := by rw [← pow_succ']; exact hc
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cyc3, diagonal_apply, h3] <;> ring

private theorem conj_eq_mul_of_eigen {G : Type*} [Group G] {a P D C Z : G}
    (hD : P⁻¹ * a * P = D) (hC : C * D * C⁻¹ = Z * D) (hZ : ∀ g : G, g * Z = Z * g) :
    (P * C * P⁻¹) * a * (P * C * P⁻¹)⁻¹ = a * Z := by
  have e : a = P * D * P⁻¹ := by rw [← hD]; group
  subst e
  calc P * C * P⁻¹ * (P * D * P⁻¹) * (P * C * P⁻¹)⁻¹
      = P * (C * D * C⁻¹) * P⁻¹ := by group
    _ = P * (Z * D) * P⁻¹ := by rw [hC]
    _ = (P * Z) * D * P⁻¹ := by group
    _ = (Z * P) * D * P⁻¹ := by rw [hZ P]
    _ = Z * (P * D * P⁻¹) := by group
    _ = P * D * P⁻¹ * Z := (hZ _).symm

theorem not_l143Config_statedSL (heig : L143EigProp) {K : Type} [Field K]
    (a w : StatedSL 3 K) : ¬ L143Config a w := by
  intro h
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_statedSL h.w_mem
  have hc3 : c ^ 3 = 1 := by
    have h1 := det_of_mem_statedSL w.2
    rwa [hc, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact h.w_ne (Subtype.ext (Units.ext (by simpa using hc)))
  have ha3 : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have h1 := congrArg (fun g : StatedSL 3 K => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      h.a_pow
    simpa using h1
  have ha_ns : ∀ r : K, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ scalar (Fin 3) r := by
    intro r hr
    refine h.a_not_mem (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Units.ext ?_))
    have hg := scalar_comm r (Commute.all r) ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← hr] at hg
    exact hg.symm
  obtain ⟨P, hPdet, hAP⟩ := heig K c hc3 hc1 _ ha3 (det_of_mem_statedSL a.2) ha_ns
  obtain ⟨Pg, hPg⟩ := (isUnit_iff_isUnit_det P).mpr hPdet
  obtain ⟨Dg, hDg⟩ : ∃ Dg : GL (Fin 3) K, Pg⁻¹ * (a : GL (Fin 3) K) * Pg = Dg := ⟨_, rfl⟩
  have hDval : ((Dg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, c, c ^ 2] := by
    have hQP : ((Pg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P = 1 := by
      rw [← hPg]
      exact Units.inv_mul Pg
    rw [← hDg, Units.val_mul, Units.val_mul, hPg, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hQP,
      Matrix.one_mul]
  have hZ : ∀ g : GL (Fin 3) K, g * (w : GL (Fin 3) K) = (w : GL (Fin 3) K) * g := fun g => by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hc]
    exact (scalar_comm c (Commute.all c) _).symm
  have hCD : (cyc3GL : GL (Fin 3) K) * Dg * cyc3GL⁻¹ = (w : GL (Fin 3) K) * Dg := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hDval, hc]
    exact cyc3_mul_diagonal_mul_transpose hc3
  have hC : (cyc3GL : GL (Fin 3) K) ∈ StatedSL 3 K :=
    mem_statedSL_of_det (by simp [cyc3GL, cyc3, det_fin_three])
  have hN : (StatedSL 3 K).Normal := by
    rw [statedSL_eq_ker_det]
    infer_instance
  have hy : Pg * cyc3GL * Pg⁻¹ ∈ StatedSL 3 K := hN.conj_mem _ hC Pg
  exact h.not_conj ⟨_, hy⟩ (Subtype.ext (conj_eq_mul_of_eigen hDg hCD hZ))

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
