module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

section Operators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V}

theorem Wt49.cube_A1_A2sq (hW : Wt49 A0 A1 A2 X Xi S Si) : (A1 * A2 ^ 2) ^ 3 = 1 := by
  have hc : Commute A1 (A2 ^ 2) :=
    Commute.pow_right (show Commute A1 A2 from hW.comm12) 2
  rw [hc.mul_pow 3, hW.cube1, one_mul, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul,
    hW.cube2, one_pow]

theorem Wt49.A1_eq_A2_on_inf (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      A1 v = A2 v := by
  intro v hv
  have hb : (A1 * A2 ^ 2) v = v :=
    (mem_range_e2_iff (A1 * A2 ^ 2) (Wt49.cube_A1_A2sq hW) v).mp hv.2
  have hpow : A2 * A2 ^ 2 = A2 ^ 3 := by
    conv_rhs => rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ']
  have hmul : A2 * (A1 * A2 ^ 2) = A1 := by
    calc A2 * (A1 * A2 ^ 2) = A2 * A1 * A2 ^ 2 := (mul_assoc A2 A1 (A2 ^ 2)).symm
      _ = A1 * A2 * A2 ^ 2 := by rw [hW.comm12.symm]
      _ = A1 * (A2 * A2 ^ 2) := mul_assoc A1 A2 (A2 ^ 2)
      _ = A1 * A2 ^ 3 := by rw [hpow]
      _ = A1 := by rw [hW.cube2, mul_one]
  have h := congrArg (fun u => A2 u) hb
  rw [← Module.End.mul_apply, hmul] at h
  exact h

theorem Wt49.A2_mem_inf_of_mem (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      A2 v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)) := by
  intro v hv
  have hv0 : A0 v = v := (mem_range_e2_iff A0 hW.cube0 v).mp hv.1
  have hA1A2 := Wt49.A1_eq_A2_on_inf hW v hv
  have h3 : A2 (A2 (A2 v)) = v := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hW.cube2
    simpa [pow_succ, mul_assoc, Module.End.mul_apply] using h
  refine ⟨?_, ?_⟩
  · exact (mem_range_e2_iff A0 hW.cube0 (A2 v)).mpr (by
      calc A0 (A2 v) = (A0 * A2) v := rfl
        _ = (A2 * A0) v := by rw [hW.comm02]
        _ = A2 (A0 v) := rfl
        _ = A2 v := by rw [hv0])
  · exact (mem_range_e2_iff (A1 * A2 ^ 2) (Wt49.cube_A1_A2sq hW) (A2 v)).mpr (by
      calc (A1 * A2 ^ 2) (A2 v) = A1 (A2 (A2 (A2 v))) := by
            simp only [pow_two, Module.End.mul_apply]
        _ = A1 v := by rw [h3]
        _ = A2 v := hA1A2)

theorem Wt49.fpf_A2_on_inf (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    ∀ v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      A2 v = v → v = 0 := by
  intro v hv hv2
  have hb : (A1 * A2 ^ 2) v = v :=
    (mem_range_e2_iff (A1 * A2 ^ 2) (Wt49.cube_A1_A2sq hW) v).mp hv.2
  have hv2sq : A2 (A2 v) = v := by rw [hv2, hv2]
  have hv1 : A1 v = v := by
    calc A1 v = A1 (A2 (A2 v)) := by rw [hv2sq]
      _ = (A1 * A2 ^ 2) v := by simp only [pow_two, Module.End.mul_apply]
      _ = v := hb
  have hmem : v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
    ⟨hv.1, (mem_range_e2_iff A1 hW.cube1 v).mpr hv1⟩
  rw [hD.1] at hmem
  simpa using hmem

theorem Wt49.z_apply_eq_A2_sq_of_mem (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      (A0 * A1 * A2) v = A2 (A2 v) := by
  intro v hv
  have hv0 : A0 v = v := (mem_range_e2_iff A0 hW.cube0 v).mp hv.1
  have hA1A2 := Wt49.A1_eq_A2_on_inf hW
  have hA2mem := Wt49.A2_mem_inf_of_mem hW v hv
  calc (A0 * A1 * A2) v = (A1 * A2 * A0) v := by rw [← hW.prod_rotate]
    _ = A1 (A2 (A0 v)) := rfl
    _ = A1 (A2 v) := by rw [hv0]
    _ = A2 (A2 v) := hA1A2 (A2 v) hA2mem

theorem Wt49.fpf_z_on_inf (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    ∀ v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      (A0 * A1 * A2) v = v → v = 0 := by
  intro v hv hvZ
  have hZeq := Wt49.z_apply_eq_A2_sq_of_mem hW v hv
  have hA2sq : A2 (A2 v) = v := hZeq.symm.trans hvZ
  have h3 : A2 (A2 (A2 v)) = v := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hW.cube2
    simpa [pow_succ, mul_assoc, Module.End.mul_apply] using h
  have hA2v : A2 v = v := by
    have h := congrArg (fun u => A2 u) hA2sq
    rw [h3] at h
    exact h.symm
  exact Wt49.fpf_A2_on_inf hW hD v hv hA2v

theorem Wt49.inf_range_e2_le_Wbz2 (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)) ≤ Wbz2 A0 A1 A2 := by
  intro v hv
  unfold Wbz2 Uz
  refine ⟨?_, ?_⟩
  · rw [hW.rels.2.2.2.2]
    exact hv.2
  · refine (le_ker_e2_of_fpf (Z := A0 * A1 * A2)
        (D := LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)))
        hW.rels.2.1 ?_ ?_) hv
    · intro w hw
      rw [show (A0 * A1 * A2) w = A2 (A2 w) from Wt49.z_apply_eq_A2_sq_of_mem hW w hw]
      exact Wt49.A2_mem_inf_of_mem hW (A2 w) (Wt49.A2_mem_inf_of_mem hW w hw)
    · intro w hw hwZ
      exact Wt49.fpf_z_on_inf hW hD w hw hwZ

theorem Wt49.comm_A0_products (hW : Wt49 A0 A1 A2 X Xi S Si) :
    A0 * (A1 * A2) = (A1 * A2) * A0 ∧
      A0 * (A1 * A2 ^ 2) = (A1 * A2 ^ 2) * A0 := by
  have h02 : A0 * A2 ^ 2 = A2 ^ 2 * A0 := by
    rw [pow_two]
    calc A0 * (A2 * A2) = A0 * A2 * A2 := (mul_assoc A0 A2 A2).symm
      _ = A2 * A0 * A2 := by rw [hW.comm02]
      _ = A2 * (A0 * A2) := mul_assoc A2 A0 A2
      _ = A2 * (A2 * A0) := by rw [hW.comm02]
      _ = A2 * A2 * A0 := (mul_assoc A2 A2 A0).symm
  refine ⟨?_, ?_⟩
  · calc A0 * (A1 * A2) = A0 * A1 * A2 := (mul_assoc A0 A1 A2).symm
      _ = A1 * A0 * A2 := by rw [hW.comm01]
      _ = A1 * (A0 * A2) := mul_assoc A1 A0 A2
      _ = A1 * (A2 * A0) := by rw [hW.comm02]
      _ = A1 * A2 * A0 := (mul_assoc A1 A2 A0).symm
  · calc A0 * (A1 * A2 ^ 2) = A0 * A1 * A2 ^ 2 := (mul_assoc A0 A1 (A2 ^ 2)).symm
      _ = A1 * A0 * A2 ^ 2 := by rw [hW.comm01]
      _ = A1 * (A0 * A2 ^ 2) := mul_assoc A1 A0 (A2 ^ 2)
      _ = A1 * (A2 ^ 2 * A0) := by rw [h02]
      _ = A1 * A2 ^ 2 * A0 := (mul_assoc A1 (A2 ^ 2) A0).symm

theorem Wt49.range_e2_A0_le_sup_range_e2 (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hD : Disj49 A0 A1 A2) :
    LinearMap.range (e2 A0) ≤
      (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) ⊔
        (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) := by
  intro v hv
  have hdec := e2_decomp_vec (P := A1) (Q := A2) hW.cube1 hW.cube2 hW.comm12 v
  obtain ⟨h12, h12sq⟩ := hW.comm_A0_products
  have hC1 : e2 A1 v ∈ LinearMap.range (e2 A0) :=
    range_e2_invariant_of_comm (e2 A1) A0 (mul_e2_comm_of_comm A0 A1 hW.comm01).symm v hv
  have hC2 : e2 A2 v ∈ LinearMap.range (e2 A0) :=
    range_e2_invariant_of_comm (e2 A2) A0 (mul_e2_comm_of_comm A0 A2 hW.comm02).symm v hv
  have hC12 : e2 (A1 * A2) v ∈ LinearMap.range (e2 A0) :=
    range_e2_invariant_of_comm (e2 (A1 * A2)) A0
      (mul_e2_comm_of_comm A0 (A1 * A2) h12).symm v hv
  have hC12sq : e2 (A1 * A2 ^ 2) v ∈ LinearMap.range (e2 A0) :=
    range_e2_invariant_of_comm (e2 (A1 * A2 ^ 2)) A0
      (mul_e2_comm_of_comm A0 (A1 * A2 ^ 2) h12sq).symm v hv
  have hC12' : e2 A1 (e2 A2 v) ∈ LinearMap.range (e2 A0) :=
    range_e2_invariant_of_comm (e2 A1) A0 (mul_e2_comm_of_comm A0 A1 hW.comm01).symm
      (e2 A2 v) hC2
  have h1 : e2 A1 v = 0 := by
    have hmem : e2 A1 v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
      ⟨hC1, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
    rw [hD.1] at hmem
    simpa using hmem
  have h2 : e2 A2 v = 0 := by
    have hmem : e2 A2 v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A2) :=
      ⟨hC2, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
    rw [hD.2.1] at hmem
    simpa using hmem
  have h3 : e2 A1 (e2 A2 v) = 0 := by
    have hmem : e2 A1 (e2 A2 v) ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
      ⟨hC12', LinearMap.mem_range.mpr ⟨e2 A2 v, rfl⟩⟩
    rw [hD.1] at hmem
    simpa using hmem
  have hdecomp : v = e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v := by
    rw [h3, h2, h1] at hdec
    simpa using hdec
  refine Submodule.mem_sup.mpr
    ⟨e2 (A1 * A2 ^ 2) v, ⟨hC12sq, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩,
      e2 (A1 * A2) v, ⟨hC12, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩, ?_⟩
  exact (add_comm _ _).trans hdecomp.symm

theorem Wt49.finrank_inf_range_e2_A0_conj (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Module.finrank (ZMod 2)
        ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) =
      Module.finrank (ZMod 2)
        ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) := by
  have hrot := hW.rotate
  have hS1 : (Xi * S * X) * A0 = A0 * (Xi * S * X) := by
    have h := congrArg (fun T => (Xi * S * X) * T) hrot.fix2
    have h' : (Xi * S * X) * ((Xi * Si * X) * A0 * (Xi * S * X)) = A0 * (Xi * S * X) := by
      calc (Xi * S * X) * ((Xi * Si * X) * A0 * (Xi * S * X))
          = (Xi * S * X * (Xi * Si * X * A0)) * (Xi * S * X) :=
            (mul_assoc (Xi * S * X) ((Xi * Si * X) * A0) (Xi * S * X)).symm
        _ = ((Xi * S * X * (Xi * Si * X)) * A0) * (Xi * S * X) := by
              rw [(mul_assoc (Xi * S * X) (Xi * Si * X) A0).symm]
        _ = (1 * A0) * (Xi * S * X) := by rw [hrot.SSi]
        _ = A0 * (Xi * S * X) := by rw [one_mul]
    rw [h'] at h
    exact h.symm
  have hSi1 : (Xi * Si * X) * A0 = A0 * (Xi * Si * X) := by
    have h := congrArg (fun T => T * (Xi * Si * X)) hrot.fix2
    have h'' : ((Xi * Si * X) * A0 * (Xi * S * X)) * (Xi * Si * X)
        = (Xi * Si * X) * A0 := by
      calc ((Xi * Si * X) * A0 * (Xi * S * X)) * (Xi * Si * X)
          = ((Xi * Si * X) * A0) * ((Xi * S * X) * (Xi * Si * X)) :=
            (mul_assoc ((Xi * Si * X) * A0) (Xi * S * X) (Xi * Si * X)).symm
        _ = ((Xi * Si * X) * A0) * 1 := by rw [hrot.SSi]
        _ = (Xi * Si * X) * A0 := mul_one _
    rw [h''] at h
    exact h
  refine finrank_inf_conj_eq (A := A1) (B := A2) (S := Xi * S * X) (Si := Xi * Si * X)
    (P := LinearMap.range (e2 A0)) hW.cube1 hW.cube2 hW.comm12 hrot.SiS hrot.SSi hrot.inv0
    hrot.fix1
    (fun v hv => range_e2_invariant_of_comm (Xi * S * X) A0 hS1 v hv)
    (fun v hv => range_e2_invariant_of_comm (Xi * Si * X) A0 hSi1 v hv)

theorem Wt49.finrank_fixed_le_four (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (e2 A0)) ≤ 4 := by
  haveI : Module.Finite (ZMod 2) V :=
    Module.Finite.of_fg_top
      (Submodule.fg_def.mpr ⟨Set.univ, Set.finite_univ, Submodule.span_univ⟩)
  have hWbz2fin : Module.finrank (ZMod 2) ↥(Wbz2 A0 A1 A2) ≤ 2 := by
    have h2 : 2 ^ Module.finrank (ZMod 2) ↥(Wbz2 A0 A1 A2) = 4 := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(Wbz2 A0 A1 A2))
      rw [Nat.card_zmod, hW.pieces.2.2.2] at h
      exact h.symm
    by_contra hlt
    push Not at hlt
    have h3 : 3 ≤ Module.finrank (ZMod 2) ↥(Wbz2 A0 A1 A2) := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h3
    rw [h2] at hpow
    norm_num at hpow
  have hDfin : Module.finrank (ZMod 2)
      ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) ≤ 2 :=
    (Submodule.finrank_mono (Wt49.inf_range_e2_le_Wbz2 hW hD)).trans hWbz2fin
  have heq : Module.finrank (ZMod 2)
      ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) =
      Module.finrank (ZMod 2)
      ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) :=
    Wt49.finrank_inf_range_e2_A0_conj hW
  calc Module.finrank (ZMod 2) ↥(LinearMap.range (e2 A0))
      ≤ Module.finrank (ZMod 2)
          ↥((LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) ⊔
            (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)))) :=
        Submodule.finrank_mono (Wt49.range_e2_A0_le_sup_range_e2 hW hD)
    _ ≤ Module.finrank (ZMod 2)
            ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) +
          Module.finrank (ZMod 2)
            ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ 4 := by omega

end Operators

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
