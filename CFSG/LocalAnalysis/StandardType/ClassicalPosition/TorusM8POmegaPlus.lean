module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private def torM8P_idx {n : ℕ} (p : Fin n) (T : Bool) : Fin n ⊕ Fin n :=
  if T then Sum.inr p else Sum.inl p

private theorem torM8P_idx_surjective {n : ℕ} (i : Fin n ⊕ Fin n) :
    ∃ p T, i = torM8P_idx p T := by
  rcases i with k | k
  · exact ⟨k, false, rfl⟩
  · exact ⟨k, true, rfl⟩

private theorem torM8P_polar_frame (n : ℕ) (F : Type) [Field F] (hn : 3 ≤ n)
    (v : Fin n ⊕ Fin n → F) (p : Fin n) (T : Bool) :
    QuadraticMap.polar (⇑(Spin.quadPlus n F)) v ((Spin.plusFrame n F hn).vec p T) =
      v (torM8P_idx p T) := by
  cases T <;>
    simp [torM8P_idx, Spin.plusFrame_vec, Spin.plusVec_true, Spin.plusVec_false,
      Spin.polar_quadPlus_single_inl, Spin.polar_quadPlus_single_inr]

private theorem torM8P_single_idx (n : ℕ) (F : Type) [Field F] (hn : 3 ≤ n)
    (p : Fin n) (T : Bool) :
    Pi.single (torM8P_idx p T) (1 : F) = (Spin.plusFrame n F hn).vec p (!T) := by
  cases T <;>
    simp [torM8P_idx, Spin.plusFrame_vec, Spin.plusVec_true, Spin.plusVec_false]

private theorem torM8P_single_inj {n : ℕ} {F : Type} [Field F] {i j : Fin n ⊕ Fin n}
    (h : (Pi.single i (1 : F) : Fin n ⊕ Fin n → F) = Pi.single j 1) : i = j := by
  have h1 := congrFun h i
  rw [Pi.single_eq_same] at h1
  by_contra hne
  have h2 : (Pi.single j (1 : F) : Fin n ⊕ Fin n → F) i = 0 :=
    Pi.single_eq_of_ne hne 1
  rw [h2] at h1
  exact one_ne_zero h1

theorem ggTorus_apply_eq_zero_POmegaPlus (n : ℕ) (F : Type) [Field F]
    (hn : 3 ≤ n)
    {h : ↥(spinGroup (Spin.quadPlus n F))} (hh : h ∈ ggTorus (Spin.plusDatum n F hn))
    {i j : Fin n ⊕ Fin n} (hij : i ≠ j) :
    (((Spin.spinMatrix (Spin.quadPlus n F)) h : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) F) i j = 0 := by
  let Q := Spin.quadPlus n F
  let Frm := Spin.plusFrame n F hn
  rw [Spin.coe_spinMatrix, LinearMap.toMatrix'_apply]
  obtain ⟨p, T, hi⟩ : ∃ p T, i = torM8P_idx p T := torM8P_idx_surjective i
  obtain ⟨q, S, hj⟩ : ∃ q S, Pi.single j 1 = Frm.vec q S := by
    rcases j with k | k
    · exact ⟨k, true, by simp [Frm, Spin.plusFrame_vec, Spin.plusVec_true]⟩
    · exact ⟨k, false, by simp [Frm, Spin.plusFrame_vec, Spin.plusVec_false]⟩
  rw [hj, hi]
  change (⇑(Spin.spinAction Q h) (Frm.vec q S)) (torM8P_idx p T) = 0
  rw [← torM8P_polar_frame n F hn (⇑(Spin.spinAction Q h) (Frm.vec q S)) p T]
  obtain ⟨I, hIp, hIq⟩ := Spin.exists_ne_and_ne hn p q
  obtain ⟨γ, hγ, hγeq⟩ := Spin.exists_mem_rootsD_toStdD_eq n hIp
    (Spin.boolSign_eq_one_or_eq_neg_one S) (Spin.boolSign_eq_one_or_eq_neg_one T)
  have hmem : h ∈ Subgroup.normalizer ((Frm.longRoot hIp S T).range) := by
    have h1 : h ∈ Subgroup.normalizer ((Spin.plusDatum n F hn).rootGroup γ) :=
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ)) hγ
    rwa [show (Spin.plusDatum n F hn).rootGroup γ = Spin.plusRootGroup n F hn γ from rfl,
      Spin.plusRootGroup_eq hn hIp S T hγeq] at h1
  set l := Frm.longRoot hIp S T (Multiplicative.ofAdd (1 : F)) with hl
  have hl_mem : l ∈ (Frm.longRoot hIp S T).range := ⟨Multiplicative.ofAdd 1, rfl⟩
  obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.mp hmem l).mp hl_mem
  obtain ⟨c', hc'eq⟩ : ∃ c' : F, y = Multiplicative.ofAdd c' :=
    ⟨Multiplicative.toAdd y, by simp⟩
  rw [hc'eq] at hy
  have hc' : c' ≠ 0 := by
    intro hc0
    have hlong0 : Frm.longRoot hIp S T (Multiplicative.ofAdd c') = 1 := by
      rw [hc0]
      exact map_one _
    have hl1 : l = 1 := by
      have h1 : h * l * h⁻¹ = 1 := by rw [← hy, hlong0]
      calc l = h⁻¹ * (h * l * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hof : Multiplicative.ofAdd (1 : F) = Multiplicative.ofAdd (0 : F) := by
      apply Frm.longRoot_injective hIp S T
      rw [hl] at hl1
      rw [hl1]
      simpa [hc0] using hlong0
    have : (1 : F) = 0 := by simpa using congrArg Multiplicative.toAdd hof
    exact one_ne_zero this
  have hu : Q (Frm.vec p T) = 0 := Frm.map_vec p T
  have hw : Q (Frm.vec I S) = 0 := Frm.map_vec I S
  have huw : QuadraticMap.polar (⇑Q) (Frm.vec p T) (Frm.vec I S) = 0 := by
    rw [Frm.polar_vec_vec]
    simp [Ne.symm hIp]
  have hconj : Spin.spinAction Q h *
        CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (Frm.vec I S) *
          (Spin.spinAction Q h)⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (c' • Frm.vec I S) := by
    have h1 : Spin.spinAction Q (h * l * h⁻¹) =
        Spin.spinAction Q (Frm.longRoot hIp S T (Multiplicative.ofAdd c')) := by
      rw [hy.symm]
    simp only [map_mul, map_inv, hl, Spin.HypFrame.spinAction_longRoot_eq_eichler,
      one_smul] at h1
    exact h1
  have hb_u : QuadraticMap.polar (⇑Q) (Frm.vec q S) (Frm.vec p T) = 0 := by
    rw [Frm.polar_vec_vec]
    by_cases hcond : q = p ∧ S = !T
    · exfalso
      apply hij
      have hsingle : (Pi.single i (1 : F) : Fin n ⊕ Fin n → F) = Pi.single j 1 := by
        rw [hi, torM8P_single_idx n F hn p T, ← hcond.1, ← hcond.2, ← hj]
      exact torM8P_single_inj hsingle
    · simp [hcond]
  have hb_w : QuadraticMap.polar (⇑Q) (Frm.vec q S) (Frm.vec I S) = 0 := by
    rw [Frm.polar_vec_vec]
    cases S <;> simp [Ne.symm hIq]
  have heich_b : CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (Frm.vec I S)
      (Frm.vec q S) = Frm.vec q S := by
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu huw (Frm.vec q S)]
    rw [hb_u, hb_w, hw]
    module
  have happ : Spin.spinAction Q h
        (CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (Frm.vec I S) (Frm.vec q S)) =
      CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (c' • Frm.vec I S)
        (Spin.spinAction Q h (Frm.vec q S)) := by
    have h := congrArg (fun e : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) =>
      e (Spin.spinAction Q h (Frm.vec q S))) hconj
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
    exact h
  have hAb : Spin.spinAction Q h (Frm.vec q S) =
      CFSG.ClassicalGroups.Orthogonal.eichler Q (Frm.vec p T) (c' • Frm.vec I S)
        (Spin.spinAction Q h (Frm.vec q S)) := by
    rw [← happ, heich_b]
  have hQcw : Q (c' • Frm.vec I S) = 0 := by
    simp [QuadraticMap.map_smul, hw]
  have hucw : QuadraticMap.polar (⇑Q) (Frm.vec p T) (c' • Frm.vec I S) = 0 := by
    rw [QuadraticMap.polar_smul_right, huw, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu hucw
    (Spin.spinAction Q h (Frm.vec q S))] at hAb
  rw [hQcw, zero_mul, add_zero] at hAb
  have heq : QuadraticMap.polar (⇑Q) (Spin.spinAction Q h (Frm.vec q S)) (Frm.vec p T) •
        (c' • Frm.vec I S) =
      QuadraticMap.polar (⇑Q) (Spin.spinAction Q h (Frm.vec q S)) (c' • Frm.vec I S) •
        Frm.vec p T := by
    have h1 : Spin.spinAction Q h (Frm.vec q S) +
          (QuadraticMap.polar (⇑Q) (Spin.spinAction Q h (Frm.vec q S)) (Frm.vec p T) •
            (c' • Frm.vec I S) -
            QuadraticMap.polar (⇑Q) (Spin.spinAction Q h (Frm.vec q S)) (c' • Frm.vec I S) •
              Frm.vec p T) = Spin.spinAction Q h (Frm.vec q S) + 0 := by
      rw [add_zero, ← add_sub_assoc]
      exact hAb.symm
    exact sub_eq_zero.mp (add_left_cancel h1)
  have huw' : QuadraticMap.polar (⇑Q) (Frm.vec p T) (Frm.vec I (!S)) = 0 :=
    Frm.polar_vec_of_ne (Ne.symm hIp) T (!S)
  have hfinal : QuadraticMap.polar (⇑Q) (Spin.spinAction Q h (Frm.vec q S)) (Frm.vec p T) * c' =
      0 := by
    have h := congrArg (fun z => QuadraticMap.polar (⇑Q) z (Frm.vec I (!S))) heq
    simp only [QuadraticMap.polar_smul_left, Frm.polar_vec_not, huw', smul_eq_mul,
      mul_one, smul_zero] at h
    simpa using h
  exact (mul_eq_zero.mp hfinal).resolve_right hc'

end CFSG.StandardType.ClassicalPosition
