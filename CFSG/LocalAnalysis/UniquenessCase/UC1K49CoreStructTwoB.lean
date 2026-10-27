module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

section Operators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V}

theorem finrank_le_two_of_natCard_eq_four {W : Submodule (ZMod 2) V}
    (hcard : Nat.card ↥W = 4) : Module.finrank (ZMod 2) ↥W ≤ 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥W)
  rw [Nat.card_zmod, hcard] at h
  by_contra hle
  push Not at hle
  have h3 : 3 ≤ Module.finrank (ZMod 2) ↥W := by omega
  have h8 : 8 ≤ 2 ^ Module.finrank (ZMod 2) ↥W := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) ↥W := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem Wt49.X_mul_A0_mul_Xi (hW : Wt49 A0 A1 A2 X Xi S Si) : X * A0 * Xi = A2 := by
  calc X * A0 * Xi = X * (Xi * A2 * X) * Xi := by rw [← hW.rot2]
    _ = (X * Xi) * A2 * (X * Xi) := by noncomm_ring
    _ = A2 := by rw [hW.XXi]; simp

theorem Wt49.X_mul_A0 (hW : Wt49 A0 A1 A2 X Xi S Si) : X * A0 = A2 * X := by
  calc X * A0 = X * A0 * (Xi * X) := by rw [hW.XiX, mul_one]
    _ = (X * A0 * Xi) * X := by noncomm_ring
    _ = A2 * X := by rw [hW.X_mul_A0_mul_Xi]

theorem Wt49.Xi_mul_A2 (hW : Wt49 A0 A1 A2 X Xi S Si) : Xi * A2 = A0 * Xi := by
  calc Xi * A2 = Xi * A2 * (X * Xi) := by rw [hW.XXi, mul_one]
    _ = (Xi * A2 * X) * Xi := by noncomm_ring
    _ = A0 * Xi := by rw [hW.rot2]

theorem Wt49.S_mul_A2 (hW : Wt49 A0 A1 A2 X Xi S Si) : S * A2 = A2 * S := by
  have h : S * A2 * Si = A2 := by
    calc S * A2 * Si = S * (Si * A2 * S) * Si := by rw [hW.fix2]
      _ = (S * Si) * A2 * (S * Si) := by noncomm_ring
      _ = A2 := by rw [hW.SSi]; simp
  calc S * A2 = S * A2 * (Si * S) := by rw [hW.SiS, mul_one]
    _ = (S * A2 * Si) * S := by noncomm_ring
    _ = A2 * S := by rw [h]

theorem Wt49.Si_mul_A2 (hW : Wt49 A0 A1 A2 X Xi S Si) : Si * A2 = A2 * Si := by
  calc Si * A2 = Si * A2 * (S * Si) := by rw [hW.SSi, mul_one]
    _ = (Si * A2 * S) * Si := by noncomm_ring
    _ = A2 * Si := by rw [hW.fix2]

theorem Wt49.Si_mul_A1 (hW : Wt49 A0 A1 A2 X Xi S Si) : Si * A1 = A1 * Si := by
  calc Si * A1 = Si * A1 * (S * Si) := by rw [hW.SSi, mul_one]
    _ = (Si * A1 * S) * Si := by noncomm_ring
    _ = A1 * Si := by rw [hW.fix1]

theorem Wt49.Si_mul_A0 (hW : Wt49 A0 A1 A2 X Xi S Si) : Si * A0 = A0 ^ 2 * Si := by
  calc Si * A0 = Si * A0 * (S * Si) := by rw [hW.SSi, mul_one]
    _ = (Si * A0 * S) * Si := by noncomm_ring
    _ = A0 ^ 2 * Si := by rw [hW.inv0]

theorem Wt49.S1_mul_A0 (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (Xi * S * X) * A0 = A0 * (Xi * S * X) := by
  calc (Xi * S * X) * A0 = Xi * S * (X * A0) := by noncomm_ring
    _ = Xi * S * (A2 * X) := by rw [hW.X_mul_A0]
    _ = Xi * (S * A2) * X := by noncomm_ring
    _ = Xi * (A2 * S) * X := by rw [hW.S_mul_A2]
    _ = (Xi * A2) * S * X := by noncomm_ring
    _ = (A0 * Xi) * S * X := by rw [hW.Xi_mul_A2]
    _ = A0 * (Xi * S * X) := by noncomm_ring

theorem Wt49.Si1_mul_A0 (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (Xi * Si * X) * A0 = A0 * (Xi * Si * X) := by
  calc (Xi * Si * X) * A0 = Xi * Si * (X * A0) := by noncomm_ring
    _ = Xi * Si * (A2 * X) := by rw [hW.X_mul_A0]
    _ = Xi * (Si * A2) * X := by noncomm_ring
    _ = Xi * (A2 * Si) * X := by rw [hW.Si_mul_A2]
    _ = (Xi * A2) * Si * X := by noncomm_ring
    _ = (A0 * Xi) * Si * X := by rw [hW.Xi_mul_A2]
    _ = A0 * (Xi * Si * X) := by noncomm_ring

theorem Wt49.cube_mul_A1_A2sq (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (A1 * A2 ^ 2) ^ 3 = 1 := by
  rw [Commute.mul_pow (Commute.pow_right (show Commute A1 A2 from hW.comm12) 2) 3,
    hW.cube1]
  have hA2sq3 : (A2 ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hW.cube2, one_pow]
  rw [hA2sq3, one_mul]

theorem Wt49.cube_mul_A0_A2sq (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (A0 * A2 ^ 2) ^ 3 = 1 := by
  rw [Commute.mul_pow (Commute.pow_right (show Commute A0 A2 from hW.comm02) 2) 3,
    hW.cube0]
  have hA2sq3 : (A2 ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hW.cube2, one_pow]
  rw [hA2sq3, one_mul]

theorem Wt49.cube_A0A1 (hW : Wt49 A0 A1 A2 X Xi S Si) : (A0 * A1) ^ 3 = 1 := by
  rw [Commute.mul_pow (show Commute A0 A1 from hW.comm01) 3, hW.cube0, hW.cube1, mul_one]

theorem Wt49.cube_A0A2 (hW : Wt49 A0 A1 A2 X Xi S Si) : (A0 * A2) ^ 3 = 1 := by
  rw [Commute.mul_pow (show Commute A0 A2 from hW.comm02) 3, hW.cube0, hW.cube2, mul_one]

theorem Wt49.A0_eq_A1_of_fixed_b (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (hv : (A0 * A1 ^ 2) v = v) : A0 v = A1 v := by
  have hv' : A0 (A1 (A1 v)) = v := by
    simpa [Module.End.mul_apply, pow_two] using hv
  have hcube : A1 (A1 (A1 v)) = v := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hW.cube1
    simpa [pow_succ, pow_two, Module.End.mul_apply] using h
  have hcomm : A1 (A0 (A1 (A1 v))) = A0 (A1 (A1 (A1 v))) := by
    rw [← Module.End.mul_apply A1 A0, ← hW.comm01, Module.End.mul_apply A0 A1]
  have h := congrArg A1 hv'
  rw [hcomm, hcube] at h
  exact h

theorem Wt49.z_eq_A0_of_fixed (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (hb : (A0 * A1 ^ 2) v = v) (h02 : (A0 * A2) v = v) :
    (A0 * A1 * A2) v = A0 v := by
  have hA01 : A0 v = A1 v := hW.A0_eq_A1_of_fixed_b hb
  have hA0A2v : A0 (A2 v) = v := by simpa [Module.End.mul_apply] using h02
  have hA0A1A2 : A0 * A1 * A2 = A1 * (A0 * A2) := by rw [hW.comm01, mul_assoc]
  calc (A0 * A1 * A2) v = (A1 * (A0 * A2)) v := by rw [hA0A1A2]
    _ = A1 ((A0 * A2) v) := by rw [Module.End.mul_apply]
    _ = A1 v := by rw [Module.End.mul_apply, hA0A2v]
    _ = A0 v := hA01.symm

theorem Wt49.range_e2_A0_le_join (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    LinearMap.range (e2 A0) ≤
      (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) ⊔
      (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) := by
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have hA0_A1A2 : A0 * (A1 * A2) = (A1 * A2) * A0 := (Commute.mul_right c01 c02).eq
  have hA0_A1A2sq : A0 * (A1 * A2 ^ 2) = (A1 * A2 ^ 2) * A0 :=
    (Commute.mul_right c01 (c02.pow_right 2)).eq
  intro v hv
  have hv0 : A0 v = v := (mem_range_e2_iff A0 hW.cube0 v).mp hv
  have hmem0 : ∀ (T : Module.End (ZMod 2) V), A0 * T = T * A0 → ∀ x : V,
      A0 x = x → A0 (e2 T x) = e2 T x := by
    intro T hT x hx
    calc A0 (e2 T x) = (A0 * e2 T) x := by rw [Module.End.mul_apply]
      _ = (e2 T * A0) x := by rw [mul_e2_comm_of_comm A0 T hT]
      _ = e2 T (A0 x) := by rw [Module.End.mul_apply]
      _ = e2 T x := by rw [hx]
  have h1 : e2 A1 v = 0 := by
    have hmem : e2 A1 v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
      ⟨(mem_range_e2_iff A0 hW.cube0 _).mpr (hmem0 A1 hW.comm01 v hv0), ⟨v, rfl⟩⟩
    rw [hD.1] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have h4 : e2 A2 v = 0 := by
    have hmem : e2 A2 v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A2) :=
      ⟨(mem_range_e2_iff A0 hW.cube0 _).mpr (hmem0 A2 hW.comm02 v hv0), ⟨v, rfl⟩⟩
    rw [hD.2.1] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hA0e2A2v : A0 (e2 A2 v) = e2 A2 v := hmem0 A2 hW.comm02 v hv0
  have h5 : e2 A1 (e2 A2 v) = 0 := by
    have hmem : e2 A1 (e2 A2 v) ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
      ⟨(mem_range_e2_iff A0 hW.cube0 _).mpr (hmem0 A1 hW.comm01 _ hA0e2A2v),
        ⟨e2 A2 v, rfl⟩⟩
    rw [hD.1] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hdec := e2_decomp_vec (P := A1) (Q := A2) hW.cube1 hW.cube2 hW.comm12 v
  have hz : v = e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v := by
    calc v = e2 A1 v + e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v + e2 A2 v +
          e2 A1 (e2 A2 v) := hdec
      _ = e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v := by rw [h5, h4, h1]; abel
  have ht2 : e2 (A1 * A2) v ∈
      LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)) :=
    ⟨(mem_range_e2_iff A0 hW.cube0 _).mpr (hmem0 (A1 * A2) hA0_A1A2 v hv0), ⟨v, rfl⟩⟩
  have ht3 : e2 (A1 * A2 ^ 2) v ∈
      LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)) :=
    ⟨(mem_range_e2_iff A0 hW.cube0 _).mpr (hmem0 (A1 * A2 ^ 2) hA0_A1A2sq v hv0),
      ⟨v, rfl⟩⟩
  rw [hz]
  exact Submodule.add_mem_sup ht2 ht3

theorem Wt49.invariance_A0_A1A2sq (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ v ∈ (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))),
      (A0 * A1 * A2) v ∈
        (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) := by
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have c12 : Commute A1 A2 := hW.comm12
  have hz_A0 : (A0 * A1 * A2) * A0 = A0 * (A0 * A1 * A2) :=
    (Commute.mul_left (Commute.mul_left (Commute.refl A0) c01.symm) c02.symm).eq
  have hz_A1A2sq : (A0 * A1 * A2) * (A1 * A2 ^ 2) = (A1 * A2 ^ 2) * (A0 * A1 * A2) := by
    have h1 : Commute (A0 * A1) (A1 * A2 ^ 2) :=
      (Commute.mul_left c01 (Commute.refl A1)).mul_right
        ((Commute.mul_left c02 c12).pow_right 2)
    have h2 : Commute A2 (A1 * A2 ^ 2) := c12.symm.mul_right ((Commute.refl A2).pow_right 2)
    exact (Commute.mul_left h1 h2).eq
  intro v hv
  exact ⟨range_e2_invariant_of_comm (A0 * A1 * A2) A0 hz_A0 v hv.1,
    range_e2_invariant_of_comm (A0 * A1 * A2) (A1 * A2 ^ 2) hz_A1A2sq v hv.2⟩

theorem Wt49.fpf_A0_A1A2sq (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    ∀ v ∈ (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))),
      (A0 * A1 * A2) v = v → v = 0 := by
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have hA0_A1A2 : A0 * (A1 * A2) = (A1 * A2) * A0 := (Commute.mul_right c01 c02).eq
  have hA1c : A1 ^ 2 * A1 = 1 := by rw [← pow_succ]; exact hW.cube1
  have hA2c : A2 ^ 2 * A2 = 1 := by rw [← pow_succ]; exact hW.cube2
  intro v hv hzv
  have hA0v : A0 v = v := (mem_range_e2_iff A0 hW.cube0 v).mp hv.1
  have hA1A2sq : (A1 * A2 ^ 2) v = v :=
    (mem_range_e2_iff (A1 * A2 ^ 2) hW.cube_mul_A1_A2sq v).mp hv.2
  have hz_eq : (A0 * A1 * A2) v = A1 (A2 v) := by
    calc (A0 * A1 * A2) v = (A0 * (A1 * A2)) v := by rw [mul_assoc]
      _ = A0 ((A1 * A2) v) := by rw [Module.End.mul_apply]
      _ = ((A1 * A2) * A0) v := by rw [← Module.End.mul_apply, hA0_A1A2]
      _ = (A1 * A2) (A0 v) := by rw [Module.End.mul_apply]
      _ = (A1 * A2) v := by rw [hA0v]
      _ = A1 (A2 v) := by rw [Module.End.mul_apply]
  have h1 : A1 (A2 v) = v := by rw [hz_eq] at hzv; exact hzv
  have h2 : A1 (A2 (A2 v)) = v := by
    have h := hA1A2sq
    rw [Module.End.mul_apply, pow_two, Module.End.mul_apply] at h
    exact h
  have hA2eq : A2 v = A2 (A2 v) := by
    have h : (A1 ^ 2) (A1 (A2 v)) = (A1 ^ 2) (A1 (A2 (A2 v))) := by rw [h1, h2]
    calc A2 v = (A1 ^ 2) (A1 (A2 v)) := by
          rw [← Module.End.mul_apply, hA1c, Module.End.one_apply]
      _ = (A1 ^ 2) (A1 (A2 (A2 v))) := h
      _ = A2 (A2 v) := by rw [← Module.End.mul_apply, hA1c, Module.End.one_apply]
  have hA2sq2 : (A2 ^ 2) v = v := by
    have h : A2 (A2 v) = A2 (A2 (A2 v)) := congrArg A2 hA2eq
    calc (A2 ^ 2) v = A2 (A2 v) := by rw [pow_two, Module.End.mul_apply]
      _ = A2 (A2 (A2 v)) := h
      _ = ((A2 * A2) * A2) v := by rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      _ = (1 : Module.End (ZMod 2) V) v := by rw [← pow_two A2, hA2c]
      _ = v := Module.End.one_apply v
  have hA2v : A2 v = v := by rw [hA2eq]; exact hA2sq2
  have hA1v : A1 v = v := by
    calc A1 v = A1 ((A2 ^ 2) v) := by rw [hA2sq2]
      _ = (A1 * A2 ^ 2) v := by rw [Module.End.mul_apply]
      _ = v := hA1A2sq
  have hmem : v ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
    ⟨(mem_range_e2_iff A0 hW.cube0 v).mpr hA0v,
      (mem_range_e2_iff A1 hW.cube1 v).mpr hA1v⟩
  rw [hD.1] at hmem
  exact (Submodule.mem_bot _).mp hmem

theorem Wt49.fixed_A0_le_Wbz2 (hW : Wt49 A0 A1 A2 X Xi S Si) (hD : Disj49 A0 A1 A2) :
    (LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))) ≤ Wbz2 A0 A1 A2 := by
  have hker := le_ker_e2_of_fpf hW.rels.2.1 hW.invariance_A0_A1A2sq (hW.fpf_A0_A1A2sq hD)
  intro v hv
  show v ∈ (LinearMap.range (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2)) :
    Submodule (ZMod 2) V) ⊓ Uz A0 A1 A2
  rw [Submodule.mem_inf, hW.rels.2.2.2.2]
  exact ⟨hv.2, hker hv⟩

theorem Wt49.fixed_eq_bot (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) : LinearMap.range (e2 A0) = ⊥ := by
  let D : Submodule (ZMod 2) V :=
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2))
  let D' : Submodule (ZMod 2) V :=
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))
  have hC_le : LinearMap.range (e2 A0) ≤ D' ⊔ D := hW.range_e2_A0_le_join hD
  have hD_le : D ≤ Wbz2 A0 A1 A2 := hW.fixed_A0_le_Wbz2 hD
  have hfin : Module.finrank (ZMod 2) ↥D' = Module.finrank (ZMod 2) ↥D := by
    change Module.finrank (ZMod 2)
        ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) =
      Module.finrank (ZMod 2)
        ↥(LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)))
    exact finrank_inf_conj_eq hW.cube1 hW.cube2 hW.comm12 hW.rotate.SiS hW.rotate.SSi
      hW.rotate.inv0 hW.rotate.fix1
      (range_e2_invariant_of_comm (Xi * S * X) A0 hW.S1_mul_A0)
      (range_e2_invariant_of_comm (Xi * Si * X) A0 hW.Si1_mul_A0)
  have hDbot : D = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : v ∈ Wbz2 A0 A1 A2 := hD_le hv
    have hA0v : A0 v = v := (mem_range_e2_iff A0 hW.cube0 v).mp hv.1
    exact hP.2.2.1 v hmem hA0v
  have hD'bot : D' = ⊥ := by
    have hzero : Module.finrank (ZMod 2) ↥D' = 0 := by rw [hfin, hDbot, finrank_bot]
    exact (Submodule.finrank_eq_zero).mp hzero
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : v ∈ D' ⊔ D := hC_le hv
  rw [hD'bot, hDbot, bot_sup_eq] at hv'
  exact (Submodule.mem_bot _).mp hv'

theorem Wt49.finrank_V_le_two_mul (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    Module.finrank (ZMod 2) V ≤
      2 * Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) := by
  have h0 : LinearMap.range (e2 A0) = ⊥ := hW.fixed_eq_bot hP hD
  have h1 : LinearMap.range (e2 A1) = ⊥ :=
    hW.rotate.fixed_eq_bot (hW.patIIb_rotate hP) hD.rotate
  have hze0 : e2 A0 = 0 := LinearMap.range_eq_bot.mp h0
  have hze1 : e2 A1 = 0 := LinearMap.range_eq_bot.mp h1
  have hsum := e2_end_sum A0 A1 hW.cube0 hW.cube1 hW.comm01
  rw [hze0, hze1] at hsum
  simp only [zero_add, add_zero, mul_zero] at hsum
  have htop : (⊤ : Submodule (ZMod 2) V) ≤
      LinearMap.range (e2 (A0 * A1)) ⊔ LinearMap.range (e2 (A0 * A1 ^ 2)) := by
    intro v _
    have hv := congrArg (fun f : Module.End (ZMod 2) V => f v) hsum
    simp only [LinearMap.add_apply, Module.End.one_apply] at hv
    rw [← hv]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have hle : Module.finrank (ZMod 2) V ≤
      Module.finrank (ZMod 2)
        ↥(LinearMap.range (e2 (A0 * A1)) ⊔ LinearMap.range (e2 (A0 * A1 ^ 2))) := by
    have h := Submodule.finrank_mono htop
    rwa [finrank_top] at h
  have hfin : Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1))) =
      Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) := by
    have hPtop : ∀ v ∈ (⊤ : Submodule (ZMod 2) V), S v ∈ (⊤ : Submodule (ZMod 2) V) :=
      fun _ _ => Submodule.mem_top
    have hPtop' : ∀ v ∈ (⊤ : Submodule (ZMod 2) V), Si v ∈ (⊤ : Submodule (ZMod 2) V) :=
      fun _ _ => Submodule.mem_top
    have h := finrank_inf_conj_eq hW.cube0 hW.cube1 hW.comm01 hW.SiS hW.SSi hW.inv0 hW.fix1
      hPtop hPtop'
    rw [top_inf_eq, top_inf_eq] at h
    exact h
  calc Module.finrank (ZMod 2) V
      ≤ Module.finrank (ZMod 2)
          ↥(LinearMap.range (e2 (A0 * A1)) ⊔ LinearMap.range (e2 (A0 * A1 ^ 2))) := hle
    _ ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1))) +
          Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = 2 * Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) := by
        rw [hfin]; ring

theorem Wt49.range_e2_b_le_E1_join_E2 (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    LinearMap.range (e2 (A0 * A1 ^ 2)) ≤
      (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))) ⊔
      (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2 ^ 2))) := by
  have h0 : LinearMap.range (e2 A0) = ⊥ := hW.fixed_eq_bot hP hD
  have h2 : LinearMap.range (e2 A2) = ⊥ :=
    hW.rotate.rotate.fixed_eq_bot (hW.rotate.patIIb_rotate (hW.patIIb_rotate hP))
      hD.rotate.rotate
  have hze0 : e2 A0 = 0 := LinearMap.range_eq_bot.mp h0
  have hze2 : e2 A2 = 0 := LinearMap.range_eq_bot.mp h2
  have hsum2 := e2_end_sum A0 A2 hW.cube0 hW.cube2 hW.comm02
  rw [hze0, hze2] at hsum2
  simp only [zero_add, add_zero, mul_zero] at hsum2
  have hbase : ∀ v : V, v = e2 (A0 * A2) v + e2 (A0 * A2 ^ 2) v := by
    intro v
    have hv := congrArg (fun f : Module.End (ZMod 2) V => f v) hsum2
    simp only [LinearMap.add_apply, Module.End.one_apply] at hv
    exact hv.symm
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have c12 : Commute A1 A2 := hW.comm12
  have hcomm1 : (A0 * A1 ^ 2) * (A0 * A2) = (A0 * A2) * (A0 * A1 ^ 2) :=
    ((Commute.mul_left (Commute.refl A0) (c01.symm.pow_left 2)).mul_right
      (Commute.mul_left c02 (c12.pow_left 2))).eq
  have hcomm2 : (A0 * A1 ^ 2) * (A0 * A2 ^ 2) = (A0 * A2 ^ 2) * (A0 * A1 ^ 2) :=
    ((Commute.mul_left (Commute.refl A0) (c01.symm.pow_left 2)).mul_right
      ((Commute.mul_left c02 (c12.pow_left 2)).pow_right 2)).eq
  intro v hv
  have hbv : (A0 * A1 ^ 2) v = v := (mem_range_e2_iff (A0 * A1 ^ 2) hW.rels.1 v).mp hv
  have ht1 : e2 (A0 * A2) v ∈
      LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2)) := by
    refine ⟨?_, ⟨v, rfl⟩⟩
    refine (mem_range_e2_iff (A0 * A1 ^ 2) hW.rels.1 _).mpr ?_
    calc (A0 * A1 ^ 2) (e2 (A0 * A2) v)
        = ((A0 * A1 ^ 2) * e2 (A0 * A2)) v := rfl
      _ = (e2 (A0 * A2) * (A0 * A1 ^ 2)) v := by rw [mul_e2_comm_of_comm _ _ hcomm1]
      _ = e2 (A0 * A2) ((A0 * A1 ^ 2) v) := by rw [Module.End.mul_apply]
      _ = e2 (A0 * A2) v := by rw [hbv]
  have ht2 : e2 (A0 * A2 ^ 2) v ∈
      LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2 ^ 2)) := by
    refine ⟨?_, ⟨v, rfl⟩⟩
    refine (mem_range_e2_iff (A0 * A1 ^ 2) hW.rels.1 _).mpr ?_
    calc (A0 * A1 ^ 2) (e2 (A0 * A2 ^ 2) v)
        = ((A0 * A1 ^ 2) * e2 (A0 * A2 ^ 2)) v := rfl
      _ = (e2 (A0 * A2 ^ 2) * (A0 * A1 ^ 2)) v := by rw [mul_e2_comm_of_comm _ _ hcomm2]
      _ = e2 (A0 * A2 ^ 2) ((A0 * A1 ^ 2) v) := by rw [Module.End.mul_apply]
      _ = e2 (A0 * A2 ^ 2) v := by rw [hbv]
  rw [hbase v]
  exact Submodule.add_mem_sup ht1 ht2

theorem Wt49.E1_invariant (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ v ∈ (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))),
      (A0 * A1 * A2) v ∈
        (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))) := by
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have c12 : Commute A1 A2 := hW.comm12
  have hz_A0b : (A0 * A1 * A2) * (A0 * A1 ^ 2) = (A0 * A1 ^ 2) * (A0 * A1 * A2) := by
    have h1 : Commute (A0 * A1) (A0 * A1 ^ 2) :=
      (Commute.mul_left (Commute.refl A0) c01.symm).mul_right
        ((Commute.mul_left c01 (Commute.refl A1)).pow_right 2)
    have h2 : Commute A2 (A0 * A1 ^ 2) := c02.symm.mul_right (c12.symm.pow_right 2)
    exact (Commute.mul_left h1 h2).eq
  have hz_A0A2 : (A0 * A1 * A2) * (A0 * A2) = (A0 * A2) * (A0 * A1 * A2) := by
    have h1 : Commute (A0 * A1) (A0 * A2) :=
      (Commute.mul_left (Commute.refl A0) c01.symm).mul_right (Commute.mul_left c02 c12)
    have h2 : Commute A2 (A0 * A2) := c02.symm.mul_right (Commute.refl A2)
    exact (Commute.mul_left h1 h2).eq
  intro v hv
  exact ⟨range_e2_invariant_of_comm (A0 * A1 * A2) (A0 * A1 ^ 2) hz_A0b v hv.1,
    range_e2_invariant_of_comm (A0 * A1 * A2) (A0 * A2) hz_A0A2 v hv.2⟩

theorem Wt49.E1_fpf (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    ∀ v ∈ (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))),
      (A0 * A1 * A2) v = v → v = 0 := by
  have h0 : LinearMap.range (e2 A0) = ⊥ := hW.fixed_eq_bot hP hD
  intro v hv hzv
  have hbv : (A0 * A1 ^ 2) v = v :=
    (mem_range_e2_iff (A0 * A1 ^ 2) hW.rels.1 v).mp hv.1
  have h02 : (A0 * A2) v = v := (mem_range_e2_iff (A0 * A2) hW.cube_A0A2 v).mp hv.2
  have hzA0 : (A0 * A1 * A2) v = A0 v := hW.z_eq_A0_of_fixed hbv h02
  have hA0v : A0 v = v := by rw [← hzA0]; exact hzv
  have hmem : v ∈ LinearMap.range (e2 A0) := (mem_range_e2_iff A0 hW.cube0 v).mpr hA0v
  rw [h0] at hmem
  exact (Submodule.mem_bot _).mp hmem

theorem Wt49.E1_le_Wb (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))) ≤ Wb A0 A1 A2 := by
  have hker := le_ker_e2_of_fpf hW.rels.2.1 hW.E1_invariant (hW.E1_fpf hP hD)
  intro v hv
  exact ⟨hv.1, hker hv⟩

theorem Wt49.Si_mul_b (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Si * (A0 * A1 ^ 2) = (A0 * A1) ^ 2 * Si := by
  calc Si * (A0 * A1 ^ 2) = (Si * A0) * A1 ^ 2 := by rw [mul_assoc]
    _ = (A0 ^ 2 * Si) * A1 ^ 2 := by rw [hW.Si_mul_A0]
    _ = A0 ^ 2 * (Si * A1 ^ 2) := by rw [mul_assoc]
    _ = A0 ^ 2 * (A1 ^ 2 * Si) := by
        rw [((show Commute Si A1 from hW.Si_mul_A1).pow_right 2).eq]
    _ = (A0 ^ 2 * A1 ^ 2) * Si := by rw [mul_assoc]
    _ = (A0 * A1) ^ 2 * Si := by
        rw [← Commute.mul_pow (show Commute A0 A1 from hW.comm01) 2]

theorem Wt49.Si_mul_b2 (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Si * (A0 * A2 ^ 2) = (A0 * A2) ^ 2 * Si := by
  calc Si * (A0 * A2 ^ 2) = (Si * A0) * A2 ^ 2 := by rw [mul_assoc]
    _ = (A0 ^ 2 * Si) * A2 ^ 2 := by rw [hW.Si_mul_A0]
    _ = A0 ^ 2 * (Si * A2 ^ 2) := by rw [mul_assoc]
    _ = A0 ^ 2 * (A2 ^ 2 * Si) := by
        rw [((show Commute Si A2 from hW.Si_mul_A2).pow_right 2).eq]
    _ = (A0 ^ 2 * A2 ^ 2) * Si := by rw [mul_assoc]
    _ = (A0 * A2) ^ 2 * Si := by
        rw [← Commute.mul_pow (show Commute A0 A2 from hW.comm02) 2]

theorem Wt49.Si_fixed_b (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (hbv : (A0 * A1 ^ 2) v = v) (hb2v : (A0 * A2 ^ 2) v = v) :
    (A0 * A1) (Si v) = Si v ∧ (A0 * A2) (Si v) = Si v := by
  have hg2 : ((A0 * A1) ^ 2) (Si v) = Si v := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hW.Si_mul_b
    rw [Module.End.mul_apply] at h
    rw [hbv] at h
    exact h.symm
  have hg : (A0 * A1) (Si v) = Si v := by
    have h : (A0 * A1) (((A0 * A1) ^ 2) (Si v)) = (A0 * A1) (Si v) := congrArg (A0 * A1) hg2
    rw [← Module.End.mul_apply, show (A0 * A1) * (A0 * A1) ^ 2 = (A0 * A1) ^ 3 by
          rw [← pow_succ'], hW.cube_A0A1, Module.End.one_apply] at h
    exact h.symm
  have hg2' : ((A0 * A2) ^ 2) (Si v) = Si v := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hW.Si_mul_b2
    rw [Module.End.mul_apply] at h
    rw [hb2v] at h
    exact h.symm
  have hg' : (A0 * A2) (Si v) = Si v := by
    have h : (A0 * A2) (((A0 * A2) ^ 2) (Si v)) = (A0 * A2) (Si v) := congrArg (A0 * A2) hg2'
    rw [← Module.End.mul_apply, show (A0 * A2) * (A0 * A2) ^ 2 = (A0 * A2) ^ 3 by
          rw [← pow_succ'], hW.cube_A0A2, Module.End.one_apply] at h
    exact h.symm
  exact ⟨hg, hg'⟩

theorem Wt49.Si_A1_A2_eq_A0sq (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (h1 : (A0 * A1) (Si v) = Si v) (h2 : (A0 * A2) (Si v) = Si v) :
    A1 (Si v) = (A0 ^ 2) (Si v) ∧ A2 (Si v) = (A0 ^ 2) (Si v) := by
  have hA0c3 : A0 * A0 ^ 2 = 1 := by rw [← pow_succ']; exact hW.cube0
  have key : ∀ T : Module.End (ZMod 2) V, (A0 * T) (Si v) = Si v →
      T (Si v) = (A0 ^ 2) (Si v) := by
    intro T hT
    rw [Module.End.mul_apply] at hT
    have h := congrArg (fun x => (A0 ^ 2) x) hT
    rw [show (A0 ^ 2) (A0 (T (Si v))) = T (Si v) by
          rw [← Module.End.mul_apply, show A0 ^ 2 * A0 = A0 ^ 3 by rw [← pow_succ],
            hW.cube0, Module.End.one_apply]] at h
    exact h
  exact ⟨key A1 h1, key A2 h2⟩

theorem Wt49.Si_z_eq_A0 (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (hA1w : A1 (Si v) = (A0 ^ 2) (Si v)) (hA2w : A2 (Si v) = (A0 ^ 2) (Si v)) :
    e2 (A0 * A1 * A2) (Si v) = e2 A0 (Si v) := by
  have c01 : Commute A0 A1 := hW.comm01
  have c02 : Commute A0 A2 := hW.comm02
  have hA0sqsq : A0 ^ 2 * A0 ^ 2 = A0 := by
    rw [← pow_add]
    rw [show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add, hW.cube0, one_mul, pow_one]
  have hconjA1A0 : A1 * A0 ^ 2 = A0 ^ 2 * A1 := (c01.symm.pow_right 2).eq
  have hA1A2w : (A1 * A2) (Si v) = A0 (Si v) := by
    have hconj : A1 ((A0 ^ 2) (Si v)) = (A0 ^ 2) (A1 (Si v)) := by
      calc A1 ((A0 ^ 2) (Si v)) = (A1 * A0 ^ 2) (Si v) := by rw [Module.End.mul_apply]
        _ = (A0 ^ 2 * A1) (Si v) := by rw [hconjA1A0]
        _ = (A0 ^ 2) (A1 (Si v)) := by rw [Module.End.mul_apply]
    rw [Module.End.mul_apply, hA2w, hconj, hA1w, ← Module.End.mul_apply, hA0sqsq]
  have hzw : (A0 * A1 * A2) (Si v) = (A0 ^ 2) (Si v) := by
    rw [mul_assoc, Module.End.mul_apply, hA1A2w, ← Module.End.mul_apply, ← pow_two]
  have hzA0 : Commute (A0 * A1 * A2) A0 :=
    Commute.mul_left (Commute.mul_left (Commute.refl A0) c01.symm) c02.symm
  have hz2w : ((A0 * A1 * A2) ^ 2) (Si v) = A0 (Si v) := by
    rw [pow_two, Module.End.mul_apply, hzw]
    have hconj : (A0 * A1 * A2) ((A0 ^ 2) (Si v)) = (A0 ^ 2) ((A0 * A1 * A2) (Si v)) := by
      calc (A0 * A1 * A2) ((A0 ^ 2) (Si v)) = ((A0 * A1 * A2) * A0 ^ 2) (Si v) := rfl
        _ = (A0 ^ 2 * (A0 * A1 * A2)) (Si v) := by rw [(hzA0.pow_right 2).eq]
        _ = (A0 ^ 2) ((A0 * A1 * A2) (Si v)) := by rw [Module.End.mul_apply]
    rw [hconj, hzw, ← Module.End.mul_apply, hA0sqsq]
  rw [e2_eq (A0 * A1 * A2) hW.rels.2.1, e2_eq A0 hW.cube0]
  simp only [LinearMap.add_apply, Module.End.one_apply]
  rw [hzw, hz2w]
  abel

theorem Wt49.Si_bz2_fixed (hW : Wt49 A0 A1 A2 X Xi S Si) {v : V}
    (hA1w : A1 (Si v) = (A0 ^ 2) (Si v)) (hA2w : A2 (Si v) = (A0 ^ 2) (Si v)) :
    (A1 * A2 ^ 2) (Si v) = Si v := by
  have c02 : Commute A0 A2 := hW.comm02
  have hA0sqsq : A0 ^ 2 * A0 ^ 2 = A0 := by
    rw [← pow_add]
    rw [show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add, hW.cube0, one_mul, pow_one]
  have hA0c3 : A0 * A0 ^ 2 = 1 := by rw [← pow_succ']; exact hW.cube0
  have h2w : A2 (A2 (Si v)) = A0 (Si v) := by
    rw [hA2w]
    have hconj : A2 ((A0 ^ 2) (Si v)) = (A0 ^ 2) (A2 (Si v)) := by
      calc A2 ((A0 ^ 2) (Si v)) = (A2 * A0 ^ 2) (Si v) := by rw [Module.End.mul_apply]
        _ = (A0 ^ 2 * A2) (Si v) := by rw [(c02.symm.pow_right 2).eq]
        _ = (A0 ^ 2) (A2 (Si v)) := by rw [Module.End.mul_apply]
    rw [hconj, hA2w, ← Module.End.mul_apply, hA0sqsq]
  rw [Module.End.mul_apply, pow_two, Module.End.mul_apply, h2w]
  have hconj : A1 (A0 (Si v)) = A0 (A1 (Si v)) := by
    calc A1 (A0 (Si v)) = (A1 * A0) (Si v) := by rw [Module.End.mul_apply]
      _ = (A0 * A1) (Si v) := by rw [hW.comm01]
      _ = A0 (A1 (Si v)) := by rw [Module.End.mul_apply]
  rw [hconj, hA1w, ← Module.End.mul_apply, hA0c3, Module.End.one_apply]

theorem Wt49.map_Si_E2_le_Wbz2 (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    Submodule.map Si
        (LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2 ^ 2))) ≤
      Wbz2 A0 A1 A2 := by
  rintro w ⟨v, hv, rfl⟩
  have hbv : (A0 * A1 ^ 2) v = v :=
    (mem_range_e2_iff (A0 * A1 ^ 2) hW.rels.1 v).mp hv.1
  have hb2v : (A0 * A2 ^ 2) v = v :=
    (mem_range_e2_iff (A0 * A2 ^ 2) hW.cube_mul_A0_A2sq v).mp hv.2
  obtain ⟨h1, h2⟩ := hW.Si_fixed_b hbv hb2v
  obtain ⟨hA1w, hA2w⟩ := hW.Si_A1_A2_eq_A0sq h1 h2
  have hze0 : e2 A0 = 0 := LinearMap.range_eq_bot.mp (hW.fixed_eq_bot hP hD)
  have hker : e2 (A0 * A1 * A2) (Si v) = 0 := by
    rw [hW.Si_z_eq_A0 hA1w hA2w, hze0, LinearMap.zero_apply]
  have hb2w : (A1 * A2 ^ 2) (Si v) = Si v := hW.Si_bz2_fixed hA1w hA2w
  have hmem_range : Si v ∈ LinearMap.range (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2)) := by
    rw [hW.rels.2.2.2.2]
    exact (mem_range_e2_iff (A1 * A2 ^ 2) hW.cube_mul_A1_A2sq (Si v)).mpr hb2w
  show Si v ∈ (LinearMap.range (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2)) :
    Submodule (ZMod 2) V) ⊓ Uz A0 A1 A2
  exact ⟨hmem_range, hker⟩

theorem Wt49.finrank_Cb_le_four (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) ≤ 4 := by
  let E1 : Submodule (ZMod 2) V :=
    LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2))
  let E2 : Submodule (ZMod 2) V :=
    LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ LinearMap.range (e2 (A0 * A2 ^ 2))
  have hCb_le : LinearMap.range (e2 (A0 * A1 ^ 2)) ≤ E1 ⊔ E2 :=
    hW.range_e2_b_le_E1_join_E2 hP hD
  have hE1_le : E1 ≤ Wb A0 A1 A2 := hW.E1_le_Wb hP hD
  have hE2_le : Submodule.map Si E2 ≤ Wbz2 A0 A1 A2 := hW.map_Si_E2_le_Wbz2 hP hD
  have hE2fin : Module.finrank (ZMod 2) ↥(Submodule.map Si E2) =
      Module.finrank (ZMod 2) ↥E2 := by
    refine finrank_eq_of_mutual hW.SiS hW.SSi (P := Submodule.map Si E2) (Q := E2) ?_ ?_
    · rintro v ⟨u, hu, rfl⟩
      rw [← Module.End.mul_apply, hW.SSi, Module.End.one_apply]
      exact hu
    · intro v hv
      exact ⟨v, hv, rfl⟩
  have hE2le : Module.finrank (ZMod 2) ↥E2 ≤ 2 := by
    have hle := Submodule.finrank_mono hE2_le
    rw [hE2fin] at hle
    exact hle.trans (finrank_le_two_of_natCard_eq_four hW.pieces.2.2.2)
  have hE1le : Module.finrank (ZMod 2) ↥E1 ≤ 2 := by
    have hle := Submodule.finrank_mono hE1_le
    exact hle.trans (finrank_le_two_of_natCard_eq_four hW.pieces.2.1)
  calc Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2)))
      ≤ Module.finrank (ZMod 2) ↥(E1 ⊔ E2) := Submodule.finrank_mono hCb_le
    _ ≤ Module.finrank (ZMod 2) ↥E1 + Module.finrank (ZMod 2) ↥E2 :=
        Submodule.finrank_add_le_finrank_add_finrank E1 E2
    _ ≤ 2 + 2 := add_le_add hE1le hE2le
    _ = 4 := by norm_num

theorem Wt49.finrank_le_eight (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatIIb A0 A1 A2)
    (hD : Disj49 A0 A1 A2) : Module.finrank (ZMod 2) V ≤ 8 := by
  have hV := hW.finrank_V_le_two_mul hP hD
  have hCb := hW.finrank_Cb_le_four hP hD
  calc Module.finrank (ZMod 2) V
      ≤ 2 * Module.finrank (ZMod 2) ↥(LinearMap.range (e2 (A0 * A1 ^ 2))) := hV
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 hCb
    _ = 8 := by norm_num

end Operators

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
