module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

section Operators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V}

theorem caseI_pair0_apply_cube (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1) (u : V) :
    T (T (T u)) = u := by
  have h := congrArg (fun f : Module.End (ZMod 2) V => f u) hT
  rw [Module.End.one_apply] at h
  rwa [show T ^ 3 = T * (T * T) by rw [pow_succ, pow_two, mul_assoc],
    Module.End.mul_apply, Module.End.mul_apply] at h

theorem caseI_pair0_e2_sq {T : Module.End (ZMod 2) V} (hT : T ^ 3 = 1) :
    e2 (T ^ 2) = e2 T := by
  have hT2 : (T ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hT, one_pow]
  rw [e2_eq (T ^ 2) hT2, e2_eq T hT]
  have h4 : (T ^ 2) ^ 2 = T := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hT, one_mul, pow_one]
  rw [h4]
  abel

theorem caseI_pair0_preserves_ker (T U : Module.End (ZMod 2) V) (hT : T * U = U * T) :
    ∀ v ∈ LinearMap.ker (e2 U), T v ∈ LinearMap.ker (e2 U) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, ← mul_e2_comm_of_comm T U hT, Module.End.mul_apply, hv,
    map_zero]

theorem caseI_pair0_preserves_ker_of_e2 (T U : Module.End (ZMod 2) V)
    (hT : T * e2 U = e2 U * T) :
    ∀ v ∈ LinearMap.ker (e2 U), T v ∈ LinearMap.ker (e2 U) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, ← hT, Module.End.mul_apply, hv, map_zero]

theorem caseI_pair0_e2_preserves_ker (T U : Module.End (ZMod 2) V) (hT : T * U = U * T) :
    ∀ v ∈ LinearMap.ker (e2 U), e2 T v ∈ LinearMap.ker (e2 U) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, ← e2_end_comm hT, Module.End.mul_apply, hv, map_zero]

theorem caseI_pair0_e2_preserves_range (T U : Module.End (ZMod 2) V) (hT : T * U = U * T) :
    ∀ w ∈ LinearMap.range (e2 U), e2 T w ∈ LinearMap.range (e2 U) := by
  rintro w ⟨w', rfl⟩
  exact ⟨e2 T w', by rw [← Module.End.mul_apply, ← e2_end_comm hT, Module.End.mul_apply]⟩

theorem caseI_pair0_fpf_ker (h0 : A0 ^ 3 = 1) :
    ∀ v ∈ LinearMap.ker (e2 A0), A0 v = v → v = 0 := by
  intro v hv hfix
  rw [LinearMap.mem_ker] at hv
  have h : e2 A0 v = v := (e2_eq_self_iff A0 h0 v).mpr hfix
  rw [h] at hv
  exact hv

theorem caseI_pair0_conj_e2_comm (C Ci : Module.End (ZMod 2) V) (hCiC : Ci * C = 1)
    (hCCi : C * Ci = 1) (h : Ci * A0 * C = A0 ^ 2) (h0 : A0 ^ 3 = 1) :
    C * e2 A0 = e2 A0 * C ∧ Ci * e2 A0 = e2 A0 * Ci := by
  have h1 : Ci * e2 A0 * C = e2 A0 := by
    rw [mul_e2_mul Ci C A0 hCCi hCiC, h, caseI_pair0_e2_sq h0]
  constructor
  · have h2 := congrArg (fun f => C * f) h1
    have h3 : C * (Ci * e2 A0 * C) = e2 A0 * C := by
      rw [← mul_assoc, ← mul_assoc, hCCi, one_mul]
    rw [h3] at h2
    exact h2.symm
  · calc Ci * e2 A0 = Ci * e2 A0 * (C * Ci) := by rw [hCCi, mul_one]
      _ = (Ci * e2 A0 * C) * Ci := by noncomm_ring
      _ = e2 A0 * Ci := by rw [h1]

theorem caseI_pair0_comm_A0_A0C2 (C : Module.End (ZMod 2) V) (hA0C : A0 * C = C * A0) :
    A0 * (A0 * C ^ 2) = (A0 * C ^ 2) * A0 := by
  rw [mul_assoc, (Commute.pow_right hA0C 2).eq.symm]

theorem caseI_pair0_comm_B_A0C2 (B C : Module.End (ZMod 2) V)
    (hA0B : A0 * B = B * A0) (hBC : B * C = C * B) :
    B * (A0 * C ^ 2) = (A0 * C ^ 2) * B := by
  rw [← mul_assoc, hA0B.symm, mul_assoc, (Commute.pow_right hBC 2).eq, ← mul_assoc]

theorem caseI_pair0_comm_C_A0C2 (C : Module.End (ZMod 2) V) (hA0C : A0 * C = C * A0)
    (hC : C ^ 3 = 1) : C * (A0 * C ^ 2) = (A0 * C ^ 2) * C := by
  calc C * (A0 * C ^ 2) = (C * A0) * C ^ 2 := by rw [mul_assoc]
    _ = (A0 * C) * C ^ 2 := by rw [hA0C.symm]
    _ = A0 * (C * C ^ 2) := by rw [mul_assoc]
    _ = A0 * C ^ 3 := by rw [← pow_succ']
    _ = A0 := by rw [hC, mul_one]
    _ = (A0 * C ^ 2) * C := by rw [mul_assoc, ← pow_succ, hC, mul_one]

theorem caseI_pair0_cube_prod (B C : Module.End (ZMod 2) V) (hA0 : A0 ^ 3 = 1)
    (hB : B ^ 3 = 1) (hC : C ^ 3 = 1) (hA0B : A0 * B = B * A0)
    (hA0C : A0 * C = C * A0) (hBC : B * C = C * B) : (A0 * B * C) ^ 3 = 1 := by
  have hABC : Commute (A0 * B) C := Commute.mul_left hA0C hBC
  rw [Commute.mul_pow hABC 3, Commute.mul_pow hA0B 3, hA0, hB, hC, one_mul, one_mul]

theorem caseI_pair0_preserves_Y (B C T : Module.End (ZMod 2) V)
    (hT0 : T * A0 = A0 * T) (hTB : T * B = B * T) (hTC : T * C = C * T) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      T v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) := by
  intro v hv
  obtain ⟨⟨hv0, hvB⟩, hvC⟩ := hv
  exact ⟨⟨caseI_pair0_preserves_ker T A0 hT0 v hv0,
    range_e2_invariant_of_comm T B hTB v hvB⟩,
    caseI_pair0_preserves_ker T C hTC v hvC⟩

theorem caseI_pair0_preserves_Y_of_e2 (B C T : Module.End (ZMod 2) V)
    (hT0 : T * e2 A0 = e2 A0 * T) (hTB : T * B = B * T) (hTC : T * C = C * T) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      T v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) := by
  intro v hv
  obtain ⟨⟨hv0, hvB⟩, hvC⟩ := hv
  exact ⟨⟨caseI_pair0_preserves_ker_of_e2 T A0 hT0 v hv0,
    range_e2_invariant_of_comm T B hTB v hvB⟩,
    caseI_pair0_preserves_ker T C hTC v hvC⟩

theorem caseI_pair0_e2_preserves_Y (B C T : Module.End (ZMod 2) V)
    (hT0 : T * A0 = A0 * T) (hTB : T * B = B * T) (hTC : T * C = C * T) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      e2 T v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) := by
  intro v hv
  obtain ⟨⟨hv0, hvB⟩, hvC⟩ := hv
  exact ⟨⟨caseI_pair0_e2_preserves_ker T A0 hT0 v hv0,
    caseI_pair0_e2_preserves_range T B hTB v hvB⟩,
    caseI_pair0_e2_preserves_ker T C hTC v hvC⟩


private theorem caseI_pair0_second_piece_fpf (B C : Module.End (ZMod 2) V)
    (hA0 : A0 ^ 3 = 1) (hB3 : B ^ 3 = 1) (hC : C ^ 3 = 1)
    (hA0B : A0 * B = B * A0) (hA0C : A0 * C = C * A0)
    {u : V} (huK : u ∈ LinearMap.ker (e2 A0)) (huB : u ∈ LinearMap.range (e2 B))
    (huW : u ∈ LinearMap.range (e2 (A0 * C ^ 2))) (hzu : (A0 * B * C) u = u) : u = 0 := by
  have hAC23 : (A0 * C ^ 2) ^ 3 = 1 := by
    rw [Commute.mul_pow (Commute.pow_right hA0C 2) 3, hA0, ← pow_mul,
      show 2 * 3 = 3 * 2 by norm_num, pow_mul, hC, one_pow, one_mul]
  have hBu : B u = u := (mem_range_e2_iff B hB3 u).mp huB
  have hAC2 : (A0 * C ^ 2) u = u := (mem_range_e2_iff (A0 * C ^ 2) hAC23 u).mp huW
  have hCAC2 : C * (A0 * C ^ 2) = A0 := by
    rw [← mul_assoc, hA0C.symm, mul_assoc, ← pow_succ', hC, mul_one]
  have hCu : C u = A0 u := by
    have h1 : C ((A0 * C ^ 2) u) = C u := congrArg C hAC2
    rw [← Module.End.mul_apply, hCAC2] at h1
    exact h1.symm
  have hBfix : B (A0 u) = A0 u := by
    rw [← Module.End.mul_apply, hA0B.symm, Module.End.mul_apply, hBu]
  have hzA : (A0 * B * C) u = A0 (A0 u) := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hCu, hBfix]
  have hA0sq : A0 (A0 u) = u := hzA ▸ hzu
  have hA0u : A0 u = u := by
    have h3 := congrArg A0 hA0sq
    have h3' : A0 (A0 (A0 u)) = u := caseI_pair0_apply_cube A0 hA0 u
    rw [h3'] at h3
    exact h3.symm
  exact caseI_pair0_fpf_ker hA0 u huK hA0u

private theorem caseI_pair0_second_piece_D_invariant (B C : Module.End (ZMod 2) V)
    (hA0B : A0 * B = B * A0) (hA0C : A0 * C = C * A0) (hBC : B * C = C * B)
    (hC : C ^ 3 = 1) :
    ∀ u ∈ (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
        LinearMap.range (e2 (A0 * C ^ 2)),
      (A0 * B * C) u ∈
        (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
          LinearMap.range (e2 (A0 * C ^ 2)) := by
  have hcommA : A0 * (A0 * C ^ 2) = (A0 * C ^ 2) * A0 := caseI_pair0_comm_A0_A0C2 C hA0C
  have hcommB : B * (A0 * C ^ 2) = (A0 * C ^ 2) * B := caseI_pair0_comm_B_A0C2 B C hA0B hBC
  have hcommC : C * (A0 * C ^ 2) = (A0 * C ^ 2) * C := caseI_pair0_comm_C_A0C2 C hA0C hC
  have hA0Y : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      A0 v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    caseI_pair0_preserves_Y B C A0 rfl hA0B hA0C
  have hBY : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      B v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    caseI_pair0_preserves_Y B C B hA0B.symm rfl hBC
  have hCY : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      C v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    caseI_pair0_preserves_Y B C C hA0C.symm hBC.symm rfl
  have hA0W : ∀ v ∈ LinearMap.range (e2 (A0 * C ^ 2)),
      A0 v ∈ LinearMap.range (e2 (A0 * C ^ 2)) :=
    range_e2_invariant_of_comm A0 (A0 * C ^ 2) hcommA
  have hBW : ∀ v ∈ LinearMap.range (e2 (A0 * C ^ 2)),
      B v ∈ LinearMap.range (e2 (A0 * C ^ 2)) :=
    range_e2_invariant_of_comm B (A0 * C ^ 2) hcommB
  have hCW : ∀ v ∈ LinearMap.range (e2 (A0 * C ^ 2)),
      C v ∈ LinearMap.range (e2 (A0 * C ^ 2)) :=
    range_e2_invariant_of_comm C (A0 * C ^ 2) hcommC
  intro u hu
  obtain ⟨huY, huW⟩ := hu
  have h1Y : C u ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    hCY u huY
  have h2Y : B (C u) ∈
      LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) := hBY (C u) h1Y
  have h3Y : A0 (B (C u)) ∈
      LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    hA0Y (B (C u)) h2Y
  have h1W : C u ∈ LinearMap.range (e2 (A0 * C ^ 2)) := hCW u huW
  have h2W : B (C u) ∈ LinearMap.range (e2 (A0 * C ^ 2)) := hBW (C u) h1W
  have h3W : A0 (B (C u)) ∈ LinearMap.range (e2 (A0 * C ^ 2)) := hA0W (B (C u)) h2W
  rw [Module.End.mul_apply, Module.End.mul_apply]
  exact ⟨h3Y, h3W⟩

theorem caseI_pair0_second_piece_eq_bot (B C : Module.End (ZMod 2) V)
    (hA0 : A0 ^ 3 = 1) (hB : B ^ 3 = 1) (hC : C ^ 3 = 1)
    (hA0B : A0 * B = B * A0) (hA0C : A0 * C = C * A0) (hBC : B * C = C * B)
    (hSiS : Si * S = 1) (hSSi : S * Si = 1) (hSiA0 : Si * A0 * S = A0 ^ 2)
    (hSiB : Si * B * S = B) (hSiC : Si * C * S = C)
    (htriv : ∀ u, u ∈ LinearMap.range (e2 (A0 * C ^ 2)) →
      u ∈ LinearMap.ker (e2 (A0 * B * C)) → A0 u = u) :
    (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
      LinearMap.range (e2 (A0 * C ^ 2)) = ⊥ := by
  let Y : Submodule (ZMod 2) V :=
    LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)
  let W : Submodule (ZMod 2) V := LinearMap.range (e2 (A0 * C ^ 2))
  let D : Submodule (ZMod 2) V := Y ⊓ W
  change D = ⊥
  have hZ3 : (A0 * B * C) ^ 3 = 1 := caseI_pair0_cube_prod B C hA0 hB hC hA0B hA0C hBC
  have hDinv : ∀ u ∈ D, (A0 * B * C) u ∈ D :=
    caseI_pair0_second_piece_D_invariant B C hA0B hA0C hBC hC
  have hDfpf : ∀ u ∈ D, (A0 * B * C) u = u → u = 0 := by
    intro u hu hzu
    obtain ⟨huY, huW⟩ := hu
    obtain ⟨⟨huK, huB⟩, _⟩ := huY
    exact caseI_pair0_second_piece_fpf B C hA0 hB hC hA0B hA0C huK huB huW hzu
  have hDker : D ≤ LinearMap.ker (e2 (A0 * B * C)) := le_ker_e2_of_fpf hZ3 hDinv hDfpf
  rw [Submodule.eq_bot_iff]
  intro u hu
  obtain ⟨huY, huW⟩ := hu
  have huK : u ∈ LinearMap.ker (e2 A0) := huY.1.1
  exact caseI_pair0_fpf_ker hA0 u huK (htriv u huW (hDker ⟨huY, huW⟩))


private theorem caseI_pair0_mul_eq_of_conj_mul (M N : Module.End (ZMod 2) V)
    (hSSi : S * Si = 1) (h : Si * M * S = N) : Si * M = N * Si := by
  calc Si * M = Si * M * (S * Si) := by rw [hSSi, mul_one]
    _ = (Si * M * S) * Si := by noncomm_ring
    _ = N * Si := by rw [h]

private theorem caseI_pair0_conj_e2_AC (C : Module.End (ZMod 2) V) (h0 : A0 ^ 3 = 1)
    (hC : C ^ 3 = 1)
    (hA0C : A0 * C = C * A0) (hSiS : Si * S = 1) (hSSi : S * Si = 1)
    (hSiA0 : Si * A0 * S = A0 ^ 2) (hSiC : Si * C * S = C) :
    Si * e2 (A0 * C) * S = e2 (A0 * C ^ 2) := by
  have hconj : Si * (A0 * C) * S = A0 ^ 2 * C := by
    calc Si * (A0 * C) * S = (Si * A0 * S) * (Si * C * S) := by
          rw [show Si * (A0 * C) * S = Si * A0 * (S * Si) * C * S by
            rw [hSSi]; noncomm_ring]
          noncomm_ring
      _ = A0 ^ 2 * C := by rw [hSiA0, hSiC]
  rw [mul_e2_mul Si S (A0 * C) hSSi hSiS, hconj]
  have hA06 : (A0 ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, h0, one_pow]
  have h3 : (A0 ^ 2 * C) ^ 3 = 1 := by
    rw [Commute.mul_pow (Commute.pow_left hA0C 2) 3, hA06, hC, one_mul]
  rw [← caseI_pair0_e2_sq h3]
  congr 1
  rw [Commute.mul_pow (Commute.pow_left hA0C 2) 2, ← pow_mul,
    show 2 * 2 = 3 + 1 by norm_num, pow_add, h0, one_mul, pow_one]

private theorem caseI_pair0_Y_e2_AC2_eq_zero (B C : Module.End (ZMod 2) V)
    (h2 : (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
      LinearMap.range (e2 (A0 * C ^ 2)) = ⊥)
    (hY2 : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      e2 (A0 * C ^ 2) v ∈
        LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C))
    {v : V} (hv : v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓
      LinearMap.ker (e2 C)) :
    e2 (A0 * C ^ 2) v = 0 := by
  have hmem : e2 (A0 * C ^ 2) v ∈
      (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
        LinearMap.range (e2 (A0 * C ^ 2)) :=
    ⟨hY2 v hv, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  rw [h2] at hmem
  exact hmem

private theorem caseI_pair0_Y_e2_AC_eq_zero (B C : Module.End (ZMod 2) V)
    (h2 : (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
      LinearMap.range (e2 (A0 * C ^ 2)) = ⊥)
    (hY2 : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      e2 (A0 * C ^ 2) v ∈
        LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C))
    (hSiY : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      Si v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C))
    (hSiAC' : Si * e2 (A0 * C) = e2 (A0 * C ^ 2) * Si) (hSSi : S * Si = 1)
    {v : V} (hv : v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓
      LinearMap.ker (e2 C)) :
    e2 (A0 * C) v = 0 := by
  have hSi1 : Si (e2 (A0 * C) v) = e2 (A0 * C ^ 2) (Si v) := by
    rw [← Module.End.mul_apply, hSiAC', Module.End.mul_apply]
  have hmem : Si (e2 (A0 * C) v) ∈
      (LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C)) ⊓
        LinearMap.range (e2 (A0 * C ^ 2)) := by
    rw [hSi1]
    exact ⟨hY2 (Si v) (hSiY v hv), LinearMap.mem_range.mpr ⟨Si v, rfl⟩⟩
  have hSi0 : Si (e2 (A0 * C) v) = 0 := by rw [h2] at hmem; exact hmem
  calc e2 (A0 * C) v = S (Si (e2 (A0 * C) v)) := by
        rw [← Module.End.mul_apply, hSSi, Module.End.one_apply]
    _ = 0 := by rw [hSi0, map_zero]

theorem caseI_pair0_Y_eq_bot (B C : Module.End (ZMod 2) V)
    (hA0 : A0 ^ 3 = 1) (hB : B ^ 3 = 1) (hC : C ^ 3 = 1)
    (hA0B : A0 * B = B * A0) (hA0C : A0 * C = C * A0) (hBC : B * C = C * B)
    (hSiS : Si * S = 1) (hSSi : S * Si = 1) (hSiA0 : Si * A0 * S = A0 ^ 2)
    (hSiB : Si * B * S = B) (hSiC : Si * C * S = C)
    (htriv : ∀ u, u ∈ LinearMap.range (e2 (A0 * C ^ 2)) →
      u ∈ LinearMap.ker (e2 (A0 * B * C)) → A0 u = u) :
    LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) = ⊥ := by
  have h2 := caseI_pair0_second_piece_eq_bot B C hA0 hB hC hA0B hA0C hBC hSiS hSSi
    hSiA0 hSiB hSiC htriv
  have hSiB' : Si * B = B * Si := caseI_pair0_mul_eq_of_conj_mul B B hSSi hSiB
  have hSiC' : Si * C = C * Si := caseI_pair0_mul_eq_of_conj_mul C C hSSi hSiC
  have hSiE2 : Si * e2 A0 = e2 A0 * Si :=
    (caseI_pair0_conj_e2_comm S Si hSiS hSSi hSiA0 hA0).2
  have hSiAC : Si * e2 (A0 * C) * S = e2 (A0 * C ^ 2) :=
    caseI_pair0_conj_e2_AC C hA0 hC hA0C hSiS hSSi hSiA0 hSiC
  have hSiAC' : Si * e2 (A0 * C) = e2 (A0 * C ^ 2) * Si :=
    caseI_pair0_mul_eq_of_conj_mul (e2 (A0 * C)) (e2 (A0 * C ^ 2)) hSSi hSiAC
  have hY2 : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      e2 (A0 * C ^ 2) v ∈
        LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    caseI_pair0_e2_preserves_Y B C (A0 * C ^ 2)
      (caseI_pair0_comm_A0_A0C2 C hA0C).symm (caseI_pair0_comm_B_A0C2 B C hA0B hBC).symm
      (caseI_pair0_comm_C_A0C2 C hA0C hC).symm
  have hSiY : ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C),
      Si v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 C) :=
    caseI_pair0_preserves_Y_of_e2 B C Si hSiE2 hSiB' hSiC'
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨⟨hvK, hvB⟩, hvC⟩ := hv
  have h0v : e2 A0 v = 0 := hvK
  have hCv : e2 C v = 0 := hvC
  have hdec := e2_decomp_vec hA0 hC hA0C v
  have hvsum : v = e2 (A0 * C) v + e2 (A0 * C ^ 2) v := by
    calc v = e2 A0 v + e2 (A0 * C) v + e2 (A0 * C ^ 2) v + e2 C v +
          e2 A0 (e2 C v) := hdec
      _ = e2 (A0 * C) v + e2 (A0 * C ^ 2) v := by
          rw [h0v, hCv, map_zero]; abel
  have ht2 : e2 (A0 * C ^ 2) v = 0 :=
    caseI_pair0_Y_e2_AC2_eq_zero B C h2 hY2 ⟨⟨hvK, hvB⟩, hvC⟩
  have ht1 : e2 (A0 * C) v = 0 :=
    caseI_pair0_Y_e2_AC_eq_zero B C h2 hY2 hSiY hSiAC' hSSi ⟨⟨hvK, hvB⟩, hvC⟩
  rw [hvsum, ht1, ht2, add_zero]


private def caseI_endSubring (D : Submodule (ZMod 2) V) : Subring (Module.End (ZMod 2) V) where
  carrier := {T | ∀ v ∈ D, T v ∈ D}
  mul_mem' := by
    intro a b ha hb v hv
    rw [Module.End.mul_apply]
    exact ha _ (hb v hv)
  one_mem' := by intro v hv; rwa [Module.End.one_apply]
  add_mem' := by
    intro a b ha hb v hv
    rw [LinearMap.add_apply]
    exact D.add_mem (ha v hv) (hb v hv)
  zero_mem' := by
    intro v hv
    rw [LinearMap.zero_apply]
    exact D.zero_mem
  neg_mem' := by
    intro a ha v hv
    rw [LinearMap.neg_apply]
    exact D.neg_mem (ha v hv)

theorem caseI_pair0_preserves_D (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ T ∈ Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)),
      ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)),
        T v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)) := by
  have hA0AB : A0 * (A1 * A2) = (A1 * A2) * A0 := by
    calc A0 * (A1 * A2) = (A0 * A1) * A2 := (mul_assoc A0 A1 A2).symm
      _ = (A1 * A0) * A2 := by rw [hW.comm01]
      _ = A1 * (A0 * A2) := mul_assoc A1 A0 A2
      _ = A1 * (A2 * A0) := by rw [hW.comm02]
      _ = A1 * A2 * A0 := (mul_assoc A1 A2 A0).symm
  have hA1AB : A1 * (A1 * A2) = (A1 * A2) * A1 := by rw [mul_assoc, hW.comm12.symm]
  have hA2AB : A2 * (A1 * A2) = (A1 * A2) * A2 := by rw [← mul_assoc, hW.comm12.symm]
  let D : Submodule (ZMod 2) V := LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))
  have hA0D : A0 ∈ caseI_endSubring D := by
    intro v hv
    exact ⟨caseI_pair0_preserves_ker A0 A0 rfl v hv.1,
      range_e2_invariant_of_comm A0 (A1 * A2) hA0AB v hv.2⟩
  have hA1D : A1 ∈ caseI_endSubring D := by
    intro v hv
    exact ⟨caseI_pair0_preserves_ker A1 A0 hW.comm01.symm v hv.1,
      range_e2_invariant_of_comm A1 (A1 * A2) hA1AB v hv.2⟩
  have hA2D : A2 ∈ caseI_endSubring D := by
    intro v hv
    exact ⟨caseI_pair0_preserves_ker A2 A0 hW.comm02.symm v hv.1,
      range_e2_invariant_of_comm A2 (A1 * A2) hA2AB v hv.2⟩
  have hle : Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) ≤
      caseI_endSubring D := by
    rw [Subring.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hA0D, hA1D, hA2D]
  intro T hT
  change ∀ v ∈ D, T v ∈ D
  exact hle hT


private theorem caseI_pair0_D_e2_mem (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)),
      e2 (A0 * A1 ^ 2) v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) ∧
    (∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)),
      e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v ∈
        LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) := by
  obtain ⟨hB3, hZ3, hBZ, _⟩ := hW.rels
  have hpres := caseI_pair0_preserves_D hW
  have hbmem : A0 * A1 ^ 2 ∈ Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ (Subring.subset_closure (by simp))
      (Subring.pow_mem _ (Subring.subset_closure (by simp)) 2)
  have hzmem : A0 * A1 * A2 ∈ Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.subset_closure (by simp))
      (Subring.subset_closure (by simp))) (Subring.subset_closure (by simp))
  have hbzmem : (A0 * A1 ^ 2) * (A0 * A1 * A2) ∈
      Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hbmem hzmem
  have he2bmem : e2 (A0 * A1 ^ 2) ∈
      Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) := by
    rw [e2_eq (A0 * A1 ^ 2) hB3]
    exact Subring.add_mem _ (Subring.add_mem _ (Subring.one_mem _) hbmem)
      (Subring.pow_mem _ hbmem 2)
  have hbz3 : ((A0 * A1 ^ 2) * (A0 * A1 * A2)) ^ 3 = 1 := by
    rw [Commute.mul_pow hBZ 3, hB3, hZ3, one_mul]
  have he2bzmem : e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) ∈
      Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) := by
    rw [e2_eq _ hbz3]
    exact Subring.add_mem _ (Subring.add_mem _ (Subring.one_mem _) hbzmem)
      (Subring.pow_mem _ hbzmem 2)
  exact ⟨hpres _ he2bmem, hpres _ he2bzmem⟩

private theorem caseI_pair0_D_fpf (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∀ w ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)),
      (A0 * A1 * A2) w = w → w = 0 := by
  have hAB3 : (A1 * A2) ^ 3 = 1 := by
    rw [Commute.mul_pow hW.comm12 3, hW.cube1, hW.cube2, one_mul]
  intro w hw hzw
  have hwAB' : (A1 * A2) w = w := (mem_range_e2_iff (A1 * A2) hAB3 w).mp hw.2
  have hA1A2w : A1 (A2 w) = w := by rw [← Module.End.mul_apply, hwAB']
  have hzwA : (A0 * A1 * A2) w = A0 w := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hA1A2w]
  exact caseI_pair0_fpf_ker hW.cube0 w hw.1 (hzwA ▸ hzw)

private theorem caseI_pair0_D_le_Uz (hW : Wt49 A0 A1 A2 X Xi S Si) :
    LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)) ≤
      LinearMap.ker (e2 (A0 * A1 * A2)) := by
  have hzmem : A0 * A1 * A2 ∈ Subring.closure ({A0, A1, A2} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.subset_closure (by simp))
      (Subring.subset_closure (by simp))) (Subring.subset_closure (by simp))
  have hZ3 : (A0 * A1 * A2) ^ 3 = 1 :=
    caseI_pair0_cube_prod A1 A2 hW.cube0 hW.cube1 hW.cube2 hW.comm01 hW.comm02 hW.comm12
  exact le_ker_e2_of_fpf hZ3 (caseI_pair0_preserves_D hW _ hzmem) (caseI_pair0_D_fpf hW)

private theorem caseI_pair0_D_e2_b_zero (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2)
    {v : V} (hv : v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) :
    e2 (A0 * A1 ^ 2) v = 0 := by
  obtain ⟨⟨_, h01, h02⟩, _, _⟩ := hP
  have hAB3 : (A1 * A2) ^ 3 = 1 := by
    rw [Commute.mul_pow hW.comm12 3, hW.cube1, hW.cube2, one_mul]
  have hDleU := caseI_pair0_D_le_Uz hW
  obtain ⟨hbD, _⟩ := caseI_pair0_D_e2_mem hW
  have hbWb : e2 (A0 * A1 ^ 2) v ∈ Wb A0 A1 A2 :=
    ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, hDleU (hbD v hv)⟩
  have hfix : (A1 * A2) (e2 (A0 * A1 ^ 2) v) = e2 (A0 * A1 ^ 2) v :=
    (mem_range_e2_iff (A1 * A2) hAB3 _).mp (hbD v hv).2
  have hA1fix : A1 (e2 (A0 * A1 ^ 2) v) = e2 (A0 * A1 ^ 2) v := h01 _ hbWb
  have hA2fix : A2 (e2 (A0 * A1 ^ 2) v) = e2 (A0 * A1 ^ 2) v := by
    have h1 : A1 (A2 (e2 (A0 * A1 ^ 2) v)) = e2 (A0 * A1 ^ 2) v := by
      rw [← Module.End.mul_apply, hfix]
    have h2 : A1 (A1 (A1 (A2 (e2 (A0 * A1 ^ 2) v)))) =
        A1 (A1 (e2 (A0 * A1 ^ 2) v)) := by rw [h1]
    have h3 : A1 (A1 (e2 (A0 * A1 ^ 2) v)) = e2 (A0 * A1 ^ 2) v := by
      rw [hA1fix, hA1fix]
    calc A2 (e2 (A0 * A1 ^ 2) v) =
          A1 (A1 (A1 (A2 (e2 (A0 * A1 ^ 2) v)))) :=
          (caseI_pair0_apply_cube A1 hW.cube1 (A2 (e2 (A0 * A1 ^ 2) v))).symm
      _ = A1 (A1 (e2 (A0 * A1 ^ 2) v)) := h2
      _ = e2 (A0 * A1 ^ 2) v := h3
  exact h02 _ hbWb hA2fix

private theorem caseI_pair0_D_e2_bz_zero (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2)
    {v : V} (hv : v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2))) :
    e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v = 0 := by
  obtain ⟨_, ⟨_, h11, h12⟩, _⟩ := hP
  have hAB3 : (A1 * A2) ^ 3 = 1 := by
    rw [Commute.mul_pow hW.comm12 3, hW.cube1, hW.cube2, one_mul]
  have hDleU := caseI_pair0_D_le_Uz hW
  obtain ⟨_, hbzD⟩ := caseI_pair0_D_e2_mem hW
  have hbzWbz : e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v ∈ Wbz A0 A1 A2 :=
    ⟨LinearMap.mem_range.mpr ⟨v, rfl⟩, hDleU (hbzD v hv)⟩
  have hfix : (A1 * A2) (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v) =
      e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v :=
    (mem_range_e2_iff (A1 * A2) hAB3 _).mp (hbzD v hv).2
  have hA2fix : A2 (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v) =
      e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v := h12 _ hbzWbz
  have hA1fix : A1 (e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v) =
      e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v := by
    calc A1 _ = A1 (A2 _) := by rw [hA2fix]
      _ = (A1 * A2) _ := (Module.End.mul_apply A1 A2 _).symm
      _ = _ := hfix
  exact h11 _ hbzWbz hA1fix

theorem caseI_pair0_triv_on_D (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2)),
      A1 v = v ∧ A2 v = v := by
  have h21 : TrivOn (Wbz2 A0 A1 A2) A1 := hP.2.2.2.1
  have h22 : TrivOn (Wbz2 A0 A1 A2) A2 := hP.2.2.2.2
  obtain ⟨hB3, hZ3, hBZ, _, _⟩ := hW.rels
  have hDleU := caseI_pair0_D_le_Uz hW
  intro v hv
  have hb0 := caseI_pair0_D_e2_b_zero hW hP hv
  have hbz0 := caseI_pair0_D_e2_bz_zero hW hP hv
  have hzv : e2 (A0 * A1 * A2) v = 0 := LinearMap.mem_ker.mp (hDleU hv)
  have hdec := e2_decomp_vec hB3 hZ3 hBZ v
  have hv_eq : v = e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2) v := by
    calc v = e2 (A0 * A1 ^ 2) v + e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2)) v +
          e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2) v + e2 (A0 * A1 * A2) v +
          e2 (A0 * A1 ^ 2) (e2 (A0 * A1 * A2) v) := hdec
      _ = e2 ((A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2) v := by
          rw [hb0, hbz0, hzv, map_zero]; abel
  have hv2 : v ∈ Wbz2 A0 A1 A2 :=
    ⟨LinearMap.mem_range.mpr ⟨v, hv_eq.symm⟩, hDleU hv⟩
  exact ⟨h21 v hv2, h22 v hv2⟩

theorem caseI_pair0_triv_A2_on_K_range_A1 (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hP : PatI A0 A1 A2) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A1), A2 v = v := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := hP
  have hA2sq : e2 (A0 * A2 ^ 2) = e2 (A0 * A1 ^ 2 * (A0 * A1 * A2)) := by
    rw [hW.rels.2.2.2.1]
    have hA06 : (A0 ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hW.cube0, one_pow]
    have h3 : (A0 ^ 2 * A2) ^ 3 = 1 := by
      rw [Commute.mul_pow (Commute.pow_left hW.comm02 2) 3, hA06, hW.cube2, one_mul]
    rw [← caseI_pair0_e2_sq h3]
    congr 1
    rw [Commute.mul_pow (Commute.pow_left hW.comm02 2) 2, ← pow_mul,
      show 2 * 2 = 3 + 1 by norm_num, pow_add, hW.cube0, one_mul, pow_one]
  have htriv : ∀ u, u ∈ LinearMap.range (e2 (A0 * A2 ^ 2)) →
      u ∈ LinearMap.ker (e2 (A0 * A1 * A2)) → A0 u = u := by
    intro u hu huU
    rw [hA2sq] at hu
    exact h10 u ⟨hu, huU⟩
  have hY1 : LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.ker (e2 A2) = ⊥ :=
    caseI_pair0_Y_eq_bot A1 A2 hW.cube0 hW.cube1 hW.cube2 hW.comm01 hW.comm02 hW.comm12
      hW.SiS hW.SSi hW.inv0 hW.fix1 hW.fix2 htriv
  intro v hv
  obtain ⟨hvK, hvA1⟩ := hv
  have hwK : e2 A2 v ∈ LinearMap.ker (e2 A0) :=
    caseI_pair0_e2_preserves_ker A2 A0 hW.comm02.symm v hvK
  have hwA1 : e2 A2 v ∈ LinearMap.range (e2 A1) :=
    caseI_pair0_e2_preserves_range A2 A1 hW.comm12.symm v hvA1
  have hsub : v - e2 A2 v ∈
      LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.ker (e2 A2) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _ hvK hwK
    · exact Submodule.sub_mem _ hvA1 hwA1
    · change e2 A2 (v - e2 A2 v) = 0
      rw [map_sub, ← Module.End.mul_apply, e2_end_mul_self A2 hW.cube2, sub_self]
  have hzero : v - e2 A2 v = 0 := by rw [hY1] at hsub; exact hsub
  have hv_eq : v = e2 A2 v := sub_eq_zero.mp hzero
  calc A2 v = A2 (e2 A2 v) := congrArg A2 hv_eq
    _ = e2 A2 v := g_apply_e2 A2 hW.cube2 v
    _ = v := hv_eq.symm

theorem caseI_pair0_triv_A1_on_K_range_A2 (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hP : PatI A0 A1 A2) :
    ∀ v ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A2), A1 v = v := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := hP
  have htriv : ∀ u, u ∈ LinearMap.range (e2 (A0 * A1 ^ 2)) →
      u ∈ LinearMap.ker (e2 (A0 * A2 * A1)) → A0 u = u := by
    intro u hu huU
    have huU' : u ∈ LinearMap.ker (e2 (A0 * A1 * A2)) := by
      rwa [show A0 * A2 * A1 = A0 * A1 * A2 by
        rw [mul_assoc, hW.comm12.symm, mul_assoc]] at huU
    exact h00 u ⟨hu, huU'⟩
  have hY2 : LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A2) ⊓ LinearMap.ker (e2 A1) = ⊥ :=
    caseI_pair0_Y_eq_bot A2 A1 hW.cube0 hW.cube2 hW.cube1 hW.comm02 hW.comm01
      hW.comm12.symm hW.SiS hW.SSi hW.inv0 hW.fix2 hW.fix1 htriv
  intro v hv
  obtain ⟨hvK, hvA2⟩ := hv
  have hwK : e2 A1 v ∈ LinearMap.ker (e2 A0) :=
    caseI_pair0_e2_preserves_ker A1 A0 hW.comm01.symm v hvK
  have hwA2 : e2 A1 v ∈ LinearMap.range (e2 A2) :=
    caseI_pair0_e2_preserves_range A1 A2 hW.comm12 v hvA2
  have hsub : v - e2 A1 v ∈
      LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 A2) ⊓ LinearMap.ker (e2 A1) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _ hvK hwK
    · exact Submodule.sub_mem _ hvA2 hwA2
    · change e2 A1 (v - e2 A1 v) = 0
      rw [map_sub, ← Module.End.mul_apply, e2_end_mul_self A1 hW.cube1, sub_self]
  have hzero : v - e2 A1 v = 0 := by rw [hY2] at hsub; exact hsub
  have hv_eq : v = e2 A1 v := sub_eq_zero.mp hzero
  calc A1 v = A1 (e2 A1 v) := congrArg A1 hv_eq
    _ = e2 A1 v := g_apply_e2 A1 hW.cube1 v
    _ = v := hv_eq.symm


private theorem caseI_pair0_rotate_S1_comm (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (Xi * Si * X) * A0 = A0 * (Xi * Si * X) ∧
      A1 * (Xi * S * X) = (Xi * S * X) * A1 ^ 2 ∧
      A2 * (Xi * S * X) = (Xi * S * X) * A2 := by
  have h3 : Wt49 A1 A2 A0 X Xi (Xi * S * X) (Xi * Si * X) := hW.rotate
  have hSi1A0 : (Xi * Si * X) * A0 = A0 * (Xi * Si * X) := by
    calc (Xi * Si * X) * A0 =
          (Xi * Si * X) * A0 * ((Xi * S * X) * (Xi * Si * X)) := by rw [h3.SSi, mul_one]
      _ = ((Xi * Si * X) * A0 * (Xi * S * X)) * (Xi * Si * X) := by noncomm_ring
      _ = A0 * (Xi * Si * X) := by rw [h3.fix2]
  have hA1S1 : A1 * (Xi * S * X) = (Xi * S * X) * A1 ^ 2 := by
    calc A1 * (Xi * S * X) =
          ((Xi * S * X) * (Xi * Si * X)) * (A1 * (Xi * S * X)) := by
          rw [h3.SSi, one_mul]
      _ = (Xi * S * X) * ((Xi * Si * X) * A1 * (Xi * S * X)) := by noncomm_ring
      _ = (Xi * S * X) * A1 ^ 2 := by rw [h3.inv0]
  have hA2S1 : A2 * (Xi * S * X) = (Xi * S * X) * A2 := by
    calc A2 * (Xi * S * X) =
          ((Xi * S * X) * (Xi * Si * X)) * (A2 * (Xi * S * X)) := by
          rw [h3.SSi, one_mul]
      _ = (Xi * S * X) * ((Xi * Si * X) * A2 * (Xi * S * X)) := by noncomm_ring
      _ = (Xi * S * X) * A2 := by rw [h3.fix1]
  exact ⟨hSi1A0, hA1S1, hA2S1⟩

private theorem caseI_pair0_rotate_e2_comm (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (Xi * Si * X) * e2 (A1 * A2 ^ 2) = e2 (A1 * A2) * (Xi * Si * X) := by
  have h3 : Wt49 A1 A2 A0 X Xi (Xi * S * X) (Xi * Si * X) := hW.rotate
  have hAB3 : (A1 * A2) ^ 3 = 1 := by
    rw [Commute.mul_pow hW.comm12 3, hW.cube1, hW.cube2, one_mul]
  have hconj : (Xi * Si * X) * (A1 * A2 ^ 2) * (Xi * S * X) = (A1 * A2) ^ 2 := by
    calc (Xi * Si * X) * (A1 * A2 ^ 2) * (Xi * S * X)
        = (Xi * Si * X) * A1 * ((Xi * S * X) * (Xi * Si * X)) * A2 *
            ((Xi * S * X) * (Xi * Si * X)) * A2 * (Xi * S * X) := by
          rw [h3.SSi]; noncomm_ring
      _ = ((Xi * Si * X) * A1 * (Xi * S * X)) * ((Xi * Si * X) * A2 * (Xi * S * X)) *
            ((Xi * Si * X) * A2 * (Xi * S * X)) := by noncomm_ring
      _ = A1 ^ 2 * A2 ^ 2 := by rw [h3.inv0, h3.fix1, mul_assoc, ← pow_two]
      _ = (A1 * A2) ^ 2 := (Commute.mul_pow hW.comm12 2).symm
  have hSi1AB : (Xi * Si * X) * e2 (A1 * A2 ^ 2) * (Xi * S * X) = e2 (A1 * A2) := by
    rw [mul_e2_mul (Xi * Si * X) (Xi * S * X) (A1 * A2 ^ 2) h3.SSi h3.SiS, hconj]
    exact caseI_pair0_e2_sq hAB3
  calc (Xi * Si * X) * e2 (A1 * A2 ^ 2)
      = (Xi * Si * X) * e2 (A1 * A2 ^ 2) * ((Xi * S * X) * (Xi * Si * X)) := by
        rw [h3.SSi, mul_one]
    _ = ((Xi * Si * X) * e2 (A1 * A2 ^ 2) * (Xi * S * X)) * (Xi * Si * X) := by
        noncomm_ring
    _ = e2 (A1 * A2) * (Xi * Si * X) := by rw [hSi1AB]

theorem caseI_pair0_triv_on_D' (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2) :
    ∀ w ∈ LinearMap.ker (e2 A0) ⊓ LinearMap.range (e2 (A1 * A2 ^ 2)),
      A1 w = w ∧ A2 w = w := by
  have hT3 := caseI_pair0_triv_on_D hW hP
  have h3 : Wt49 A1 A2 A0 X Xi (Xi * S * X) (Xi * Si * X) := hW.rotate
  obtain ⟨hSi1A0, hA1S1, hA2S1⟩ := caseI_pair0_rotate_S1_comm hW
  have hSi1AB' := caseI_pair0_rotate_e2_comm hW
  intro w hw
  obtain ⟨hwK, hwAB2⟩ := hw
  have hSi1K : (Xi * Si * X) w ∈ LinearMap.ker (e2 A0) :=
    caseI_pair0_preserves_ker (Xi * Si * X) A0 hSi1A0 w hwK
  have hSi1R : (Xi * Si * X) w ∈ LinearMap.range (e2 (A1 * A2)) := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hwAB2
    have h : (Xi * Si * X) w = e2 (A1 * A2) ((Xi * Si * X) u) := by
      rw [← hu, ← Module.End.mul_apply, hSi1AB', Module.End.mul_apply]
    exact LinearMap.mem_range.mpr ⟨(Xi * Si * X) u, h.symm⟩
  have hD := hT3 ((Xi * Si * X) w) ⟨hSi1K, hSi1R⟩
  have hSw : (Xi * S * X) ((Xi * Si * X) w) = w := by
    rw [← Module.End.mul_apply, h3.SSi, Module.End.one_apply]
  have hA1sq : (A1 ^ 2) ((Xi * Si * X) w) = (Xi * Si * X) w := by
    rw [pow_two, Module.End.mul_apply, hD.1, hD.1]
  constructor
  · calc A1 w = A1 ((Xi * S * X) ((Xi * Si * X) w)) := congrArg A1 hSw.symm
      _ = (A1 * (Xi * S * X)) ((Xi * Si * X) w) := (Module.End.mul_apply A1 _ _).symm
      _ = ((Xi * S * X) * A1 ^ 2) ((Xi * Si * X) w) := by rw [hA1S1]
      _ = (Xi * S * X) ((A1 ^ 2) ((Xi * Si * X) w)) := Module.End.mul_apply _ (A1 ^ 2) _
      _ = (Xi * S * X) ((Xi * Si * X) w) := congrArg (Xi * S * X) hA1sq
      _ = w := hSw
  · calc A2 w = A2 ((Xi * S * X) ((Xi * Si * X) w)) := congrArg A2 hSw.symm
      _ = (A2 * (Xi * S * X)) ((Xi * Si * X) w) := (Module.End.mul_apply A2 _ _).symm
      _ = ((Xi * S * X) * A2) ((Xi * Si * X) w) := by rw [hA2S1]
      _ = (Xi * S * X) (A2 ((Xi * Si * X) w)) := Module.End.mul_apply _ A2 _
      _ = (Xi * S * X) ((Xi * Si * X) w) := by rw [hD.2]
      _ = w := hSw


private theorem caseI_pair0_comm_A0_prods (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (A1 * A2) * A0 = A0 * (A1 * A2) ∧ (A1 * A2 ^ 2) * A0 = A0 * (A1 * A2 ^ 2) := by
  constructor
  · calc (A1 * A2) * A0 = A1 * (A2 * A0) := mul_assoc A1 A2 A0
      _ = A1 * (A0 * A2) := by rw [hW.comm02]
      _ = (A1 * A0) * A2 := (mul_assoc A1 A0 A2).symm
      _ = (A0 * A1) * A2 := by rw [hW.comm01]
      _ = A0 * (A1 * A2) := mul_assoc A0 A1 A2
  · calc (A1 * A2 ^ 2) * A0 = A1 * (A2 ^ 2 * A0) := mul_assoc A1 (A2 ^ 2) A0
      _ = A1 * (A0 * A2 ^ 2) := by rw [(Commute.pow_right hW.comm02 2).eq.symm]
      _ = (A1 * A0) * A2 ^ 2 := (mul_assoc A1 A0 (A2 ^ 2)).symm
      _ = (A0 * A1) * A2 ^ 2 := by rw [hW.comm01]
      _ = A0 * (A1 * A2 ^ 2) := mul_assoc A0 A1 (A2 ^ 2)

private theorem caseI_pair0_triv_A1_on_ker (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hP : PatI A0 A1 A2) : TrivOn (LinearMap.ker (e2 A0)) A1 := by
  have hT3 := caseI_pair0_triv_on_D hW hP
  have hT4 := caseI_pair0_triv_on_D' hW hP
  have htrivA1 := caseI_pair0_triv_A1_on_K_range_A2 hW hP
  obtain ⟨hAB, hAB2⟩ := caseI_pair0_comm_A0_prods hW
  intro v hv
  have hdec := e2_decomp_vec hW.cube1 hW.cube2 hW.comm12 v
  have h1 : A1 (e2 A1 v) = e2 A1 v := g_apply_e2 A1 hW.cube1 v
  have h2 : A1 (e2 (A1 * A2) v) = e2 (A1 * A2) v :=
    (hT3 _ ⟨caseI_pair0_e2_preserves_ker (A1 * A2) A0 hAB v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩).1
  have h3 : A1 (e2 (A1 * A2 ^ 2) v) = e2 (A1 * A2 ^ 2) v :=
    (hT4 _ ⟨caseI_pair0_e2_preserves_ker (A1 * A2 ^ 2) A0 hAB2 v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩).1
  have h4 : A1 (e2 A2 v) = e2 A2 v :=
    htrivA1 _ ⟨caseI_pair0_e2_preserves_ker A2 A0 hW.comm02.symm v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  have h5 : A1 (e2 A1 (e2 A2 v)) = e2 A1 (e2 A2 v) := g_apply_e2 A1 hW.cube1 _
  calc A1 v = A1 (e2 A1 v + e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v + e2 A2 v +
        e2 A1 (e2 A2 v)) := congrArg A1 hdec
    _ = e2 A1 v + e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v + e2 A2 v +
        e2 A1 (e2 A2 v) := by simp only [map_add, h1, h2, h3, h4, h5]
    _ = v := hdec.symm

private theorem caseI_pair0_triv_A2_on_ker (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hP : PatI A0 A1 A2) : TrivOn (LinearMap.ker (e2 A0)) A2 := by
  have hT3 := caseI_pair0_triv_on_D hW hP
  have hT4 := caseI_pair0_triv_on_D' hW hP
  have htrivA2 := caseI_pair0_triv_A2_on_K_range_A1 hW hP
  obtain ⟨hAB, hAB2⟩ := caseI_pair0_comm_A0_prods hW
  intro v hv
  have hdec := e2_decomp_vec hW.cube1 hW.cube2 hW.comm12 v
  have h1 : A2 (e2 A1 v) = e2 A1 v :=
    htrivA2 _ ⟨caseI_pair0_e2_preserves_ker A1 A0 hW.comm01.symm v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  have h2 : A2 (e2 (A1 * A2) v) = e2 (A1 * A2) v :=
    (hT3 _ ⟨caseI_pair0_e2_preserves_ker (A1 * A2) A0 hAB v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩).2
  have h3 : A2 (e2 (A1 * A2 ^ 2) v) = e2 (A1 * A2 ^ 2) v :=
    (hT4 _ ⟨caseI_pair0_e2_preserves_ker (A1 * A2 ^ 2) A0 hAB2 v hv,
      LinearMap.mem_range.mpr ⟨v, rfl⟩⟩).2
  have h4 : A2 (e2 A2 v) = e2 A2 v := g_apply_e2 A2 hW.cube2 v
  have h5 : A2 (e2 A1 (e2 A2 v)) = e2 A1 (e2 A2 v) :=
    htrivA2 _ ⟨caseI_pair0_e2_preserves_ker A1 A0 hW.comm01.symm _
      (caseI_pair0_e2_preserves_ker A2 A0 hW.comm02.symm v hv),
      LinearMap.mem_range.mpr ⟨e2 A2 v, rfl⟩⟩
  calc A2 v = A2 (e2 A1 v + e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v + e2 A2 v +
        e2 A1 (e2 A2 v)) := congrArg A2 hdec
    _ = e2 A1 v + e2 (A1 * A2) v + e2 (A1 * A2 ^ 2) v + e2 A2 v +
        e2 A1 (e2 A2 v) := by simp only [map_add, h1, h2, h3, h4, h5]
    _ = v := hdec.symm

theorem Wt49.caseI_pair0 (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2) :
    TrivOn (LinearMap.ker (e2 A0)) A1 ∧ TrivOn (LinearMap.ker (e2 A0)) A2 := by
  exact ⟨caseI_pair0_triv_A1_on_ker hW hP, caseI_pair0_triv_A2_on_ker hW hP⟩

theorem Wt49.caseI_pairs (hW : Wt49 A0 A1 A2 X Xi S Si) (hP : PatI A0 A1 A2) :
    (TrivOn (LinearMap.ker (e2 A0)) A1 ∧ TrivOn (LinearMap.ker (e2 A0)) A2) ∧
    (TrivOn (LinearMap.ker (e2 A1)) A0 ∧ TrivOn (LinearMap.ker (e2 A1)) A2) ∧
    (TrivOn (LinearMap.ker (e2 A2)) A0 ∧ TrivOn (LinearMap.ker (e2 A2)) A1) := by
  have hP1 := hW.patI_rotate hP
  have h1 := hW.rotate.caseI_pair0 hP1
  have h2 := hW.rotate.rotate.caseI_pair0 (hW.rotate.patI_rotate hP1)
  exact ⟨hW.caseI_pair0 hP, ⟨h1.2, h1.1⟩, h2⟩

end Operators

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}

namespace Ctx49

variable (c : Ctx49 H X L Q I x A a n N M)
variable [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]

include c in
theorem caseI_trivial_on_ker (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) {i j : ℕ} (hi : i < 3)
    (hj : j < 3) (hij : i ≠ j) :
    ∀ g : ↥H, (g : G) ∈ Lc L x j → ∀ v ∈ LinearMap.ker (e2 (c.opA i)), op49 c.chief g v = v := by
  have hW := c.wt
  have hfix : ∀ w ∈ LinearMap.ker (e2 (c.opA i)), c.opA j w = w := by
    obtain ⟨⟨h01, h02⟩, ⟨h10, h12⟩, ⟨h20, h21⟩⟩ := hW.caseI_pairs hP
    interval_cases i <;> interval_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h02
    · exact h10
    · exact absurd rfl hij
    · exact h12
    · exact h20
    · exact h21
    · exact absurd rfl hij
  refine c.Lc_trivial_of_invariant j (LinearMap.ker (e2 (c.opA i))) ?_ hfix
  intro g hg w hw
  have hcomm : op49 c.chief g * c.opA i = c.opA i * op49 c.chief g :=
    c.op_comm hj hi hij.symm hg (c.ai_mem i)
  have hec := mul_e2_comm_of_comm _ _ hcomm
  rw [LinearMap.mem_ker] at hw ⊢
  rw [← Module.End.mul_apply, ← hec, Module.End.mul_apply, hw, map_zero]

@[expose] noncomputable def caseI_L_trivial_W' (i : ℕ) :
    Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  Submodule.span (ZMod 2)
    {v | ∃ g : ↥H, (g : G) ∈ Lc L x i ∧ ∃ w ∈ LinearMap.ker (e2 (c.opA i)),
      op49 c.chief g w = v}

theorem caseI_L_trivial_op_mul (g g' : ↥H) :
    op49 c.chief (g * g') = op49 c.chief g * op49 c.chief g' := by
  simp [op49]

theorem caseI_L_trivial_op_one : op49 c.chief (1 : ↥H) = 1 := by
  simp [op49]

theorem caseI_L_trivial_cube {i : ℕ} (hi : i < 3) : (c.opA i) ^ 3 = 1 := by
  have hW := c.wt
  interval_cases i
  · exact hW.cube0
  · exact hW.cube1
  · exact hW.cube2

theorem caseI_L_trivial_ker_le_W' (i : ℕ) :
    LinearMap.ker (e2 (c.opA i)) ≤ caseI_L_trivial_W' c i := by
  intro w hw
  exact Submodule.subset_span ⟨(1 : ↥H), (Lc L x i).one_mem, w, hw, by simp [op49]⟩

theorem caseI_L_trivial_W'_inv (i : ℕ) {g : ↥H} (hg : (g : G) ∈ Lc L x i)
    {w : Additive (N ⧸ M.subgroupOf N)} (hw : w ∈ caseI_L_trivial_W' c i) :
    op49 c.chief g w ∈ caseI_L_trivial_W' c i := by
  have hle : caseI_L_trivial_W' c i ≤
      Submodule.comap (op49 c.chief g) (caseI_L_trivial_W' c i) := by
    rw [caseI_L_trivial_W', Submodule.span_le]
    rintro v ⟨g', hg', u, hu, rfl⟩
    exact Submodule.subset_span ⟨g * g', (Lc L x i).mul_mem hg hg', u, hu, by
      rw [caseI_L_trivial_op_mul c, Module.End.mul_apply]⟩
  exact hle hw

theorem caseI_L_trivial_W'_fixed (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) {i j : ℕ}
    (hi : i < 3) (hj : j < 3) (hij : i ≠ j) {h : ↥H} (hh : (h : G) ∈ Lc L x j) :
    ∀ w ∈ caseI_L_trivial_W' c i, op49 c.chief h w = w := by
  have hle : caseI_L_trivial_W' c i ≤ LinearMap.eqLocus (op49 c.chief h) 1 := by
    rw [caseI_L_trivial_W', Submodule.span_le]
    rintro v ⟨g, hg, u, hu, rfl⟩
    change op49 c.chief h (op49 c.chief g u) = op49 c.chief g u
    rw [← Module.End.mul_apply, c.op_comm (i := j) (j := i) hj hi hij.symm hh hg,
      Module.End.mul_apply, c.caseI_trivial_on_ker hP hi hj hij h hh u hu]
  intro w hw
  have hfix := hle hw
  change op49 c.chief h w = w at hfix
  exact hfix

@[expose] def caseI_L_trivial_T (i : ℕ) : Subgroup ↥(Lc L x i) where
  carrier := {g | ∀ v : Additive (N ⧸ M.subgroupOf N),
    (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) - 1) v ∈ caseI_L_trivial_W' c i}
  one_mem' := by
    intro v
    have h1 : op49 c.chief (Subgroup.inclusion (c.Lc_H i) (1 : ↥(Lc L x i))) = 1 := by
      rw [map_one]
      exact caseI_L_trivial_op_one c
    rw [h1]
    simp
  mul_mem' := by
    intro g g' hg hg' v
    have h1 : (op49 c.chief (Subgroup.inclusion (c.Lc_H i) (g * g')) - 1) v =
        (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) - 1)
            (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g') v) +
          (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g') - 1) v := by
      rw [map_mul, caseI_L_trivial_op_mul c]
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
      abel
    rw [h1]
    exact Submodule.add_mem _ (hg _) (hg' v)
  inv_mem' := by
    intro g hg v
    have hgg : op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) *
        op49 c.chief (Subgroup.inclusion (c.Lc_H i) g⁻¹) = 1 := by
      rw [← caseI_L_trivial_op_mul c, ← map_mul, mul_inv_cancel, map_one,
        caseI_L_trivial_op_one c]
    have hval : op49 c.chief (Subgroup.inclusion (c.Lc_H i) g)
        (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g⁻¹) v) = v := by
      rw [← Module.End.mul_apply, hgg, Module.End.one_apply]
    have hmem : (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) - 1)
        (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g⁻¹) v) ∈
          caseI_L_trivial_W' c i := hg _
    rw [LinearMap.sub_apply, hval, Module.End.one_apply] at hmem
    have hneg : op49 c.chief (Subgroup.inclusion (c.Lc_H i) g⁻¹) v - v ∈
        caseI_L_trivial_W' c i := by
      simpa only [neg_sub] using Submodule.neg_mem _ hmem
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using hneg

theorem caseI_L_trivial_T_normal (i : ℕ) : (caseI_L_trivial_T c i).Normal := by
  refine ⟨fun g hg h => ?_⟩
  intro v
  have hgg : op49 c.chief (Subgroup.inclusion (c.Lc_H i) h) *
      op49 c.chief (Subgroup.inclusion (c.Lc_H i) h⁻¹) = 1 := by
    rw [← caseI_L_trivial_op_mul c, ← map_mul, mul_inv_cancel, map_one,
      caseI_L_trivial_op_one c]
  have hval : op49 c.chief (Subgroup.inclusion (c.Lc_H i) h)
      (op49 c.chief (Subgroup.inclusion (c.Lc_H i) h⁻¹) v) = v := by
    rw [← Module.End.mul_apply, hgg, Module.End.one_apply]
  have hw : (op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) - 1)
      (op49 c.chief (Subgroup.inclusion (c.Lc_H i) h⁻¹) v) ∈
        caseI_L_trivial_W' c i := hg _
  have hfix : op49 c.chief (Subgroup.inclusion (c.Lc_H i) h)
      ((op49 c.chief (Subgroup.inclusion (c.Lc_H i) g) - 1)
        (op49 c.chief (Subgroup.inclusion (c.Lc_H i) h⁻¹) v)) ∈
        caseI_L_trivial_W' c i :=
    caseI_L_trivial_W'_inv c i h.2 hw
  rw [map_mul, map_mul, caseI_L_trivial_op_mul c, caseI_L_trivial_op_mul c]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
  simpa only [LinearMap.sub_apply, map_sub, Module.End.one_apply, hval] using hfix

theorem caseI_L_trivial_T_eq_top (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) {i : ℕ}
    (hi : i < 3) : caseI_L_trivial_T c i = ⊤ := by
  let K : Subgroup G := (caseI_L_trivial_T c i).map (Lc L x i).subtype
  have hKL : K ≤ Lc L x i := Subgroup.map_subtype_le _
  have hKs : K.subgroupOf (Lc L x i) = caseI_L_trivial_T c i := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      exact (Subtype.ext hyx) ▸ hy
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hKnorm : Lc L x i ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mp
      (hKs.symm ▸ caseI_L_trivial_T_normal c i)
  have hOK : Lc L x i ⊓ Q ≤ K := by
    intro q hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hq.1⟩, ?_, rfl⟩
    intro v
    have hqt : op49 c.chief (Subgroup.inclusion (c.Lc_H i) (⟨q, hq.1⟩ : ↥(Lc L x i))) = 1 := by
      have h1 : (chiefRep (p := 2) c.chief.2.1 c.chief.2.2.1
          (Subgroup.inclusion (c.Lc_H i) (⟨q, hq.1⟩ : ↥(Lc L x i)))) = 1 := by
        apply (chiefRep_eq_one_iff (p := 2) c.chief.2.1 c.chief.2.2.1 _).mpr
        intro w hw
        exact (Subgroup.commutator_le.mp (chief_q_trivial49 c.setup c.chief c.NQ)) w hw q hq.2
      simpa [op49] using congrArg Units.val h1
    rw [hqt]
    simp
  have hai : (c.ai i : G) ∈ K := by
    refine Subgroup.mem_map.mpr ⟨⟨c.ai i, c.ai_mem i⟩, ?_, rfl⟩
    intro v
    have he : Subgroup.inclusion (c.Lc_H i) (⟨c.ai i, c.ai_mem i⟩ : ↥(Lc L x i)) =
        c.ai i := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    rw [he]
    refine caseI_L_trivial_ker_le_W' c i ?_
    rw [ker_e2_eq_range_one_sub (c.opA i) (caseI_L_trivial_cube c (i := i) hi)]
    exact ⟨-v, by simp only [LinearMap.sub_apply, Module.End.one_apply, map_neg]; abel⟩
  have htop : K = Lc L x i :=
    eq_top_of_isAlt_five_quotient (K := K) (O := Lc L x i ⊓ Q) (L := Lc L x i)
      hKL hKnorm hOK (c.Lc_pCore i) (c.Lc_alt i)
      ⟨(c.ai i : G), hai, fun hh => c.ai_not_mem_Q i hh.2⟩
  rw [← hKs, htop, Subgroup.subgroupOf_self]

theorem caseI_L_trivial_diff_mem (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) {i : ℕ}
    (hi : i < 3) {g : ↥H} (hg : (g : G) ∈ Lc L x i)
    (v : Additive (N ⧸ M.subgroupOf N)) :
    (op49 c.chief g - 1) v ∈ caseI_L_trivial_W' c i := by
  have htop := caseI_L_trivial_T_eq_top c hP (i := i) hi
  have hmem : (⟨(g : G), hg⟩ : ↥(Lc L x i)) ∈ caseI_L_trivial_T c i := by
    rw [htop]
    exact Subgroup.mem_top _
  have he : Subgroup.inclusion (c.Lc_H i) (⟨(g : G), hg⟩ : ↥(Lc L x i)) = g := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
  simpa only [he] using hmem v

theorem caseI_L_trivial_fix_iff (h : ↥H) (y : ↥N) :
    op49 c.chief h (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk y) ↔ ⁅(y : G), (h : G)⁆ ∈ M := by
  have h1 : op49 c.chief h (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk (chiefConj c.chief.2.1 h y)) :=
    chiefRep_apply_mk (p := 2) c.chief.2.1 c.chief.2.2.1 h y
  rw [h1, Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hc : ⁅(y : G), (h : G)⁆ =
        (y : G) * (((chiefConj c.chief.2.1 h y)⁻¹ * y : ↥N) : G) * (y : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe, commutatorElement_def]
      group
    rw [hc]
    exact c.chief.2.2.2.1 (y : G) y.2 _ (Subgroup.mem_subgroupOf.mp hq)
  · intro hq
    have hc : ⁅(y : G), (h : G)⁆ =
        (y : G) * (((chiefConj c.chief.2.1 h y)⁻¹ * y : ↥N) : G) * (y : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe, commutatorElement_def]
      group
    have hmem : (y : G)⁻¹ * ⁅(y : G), (h : G)⁆ * (y : G) ∈ M := by
      simpa only [inv_inv] using
        c.chief.2.2.2.1 (y : G)⁻¹ (N.inv_mem y.2) _ hq
    rw [hc] at hmem
    convert hmem using 1
    group

@[expose] def caseI_L_trivial_F (j : ℕ) : Subgroup ↥N where
  carrier := {y | ∀ h : ↥H, (h : G) ∈ Lc L x j →
    op49 c.chief h (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk y)}
  one_mem' := by
    intro h hh
    rw [QuotientGroup.mk_one, ofMul_one, map_zero]
  mul_mem' := by
    intro y y' hy hy' h hh
    rw [QuotientGroup.mk_mul, ofMul_mul, map_add, hy h hh, hy' h hh]
  inv_mem' := by
    intro y hy h hh
    rw [QuotientGroup.mk_inv, ofMul_inv, map_neg, hy h hh]

theorem caseI_L_trivial_commutator_le_F (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) {i j : ℕ}
    (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    ⁅N, Lc L x i⁆ ≤ (caseI_L_trivial_F c j).map N.subtype := by
  rw [Subgroup.commutator_le]
  intro n hn g hg
  have hgN : g * n * g⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (c.chief.2.1 (c.Lc_H i hg)) n).mp hn
  have huN : g * n * g⁻¹ * n⁻¹ ∈ N := N.mul_mem hgN (N.inv_mem hn)
  let n' : ↥N := ⟨n, hn⟩
  let u : ↥N := ⟨g * n * g⁻¹ * n⁻¹, huN⟩
  let g' : ↥H := ⟨g, c.Lc_H i hg⟩
  have huF : u ∈ caseI_L_trivial_F c j := by
    intro h hh
    have hdiff : (op49 c.chief g' - 1) (Additive.ofMul (QuotientGroup.mk n')) =
        Additive.ofMul (QuotientGroup.mk u) := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
      rw [show op49 c.chief g' (Additive.ofMul (QuotientGroup.mk n')) =
          Additive.ofMul (QuotientGroup.mk (chiefConj c.chief.2.1 g' n')) from
        chiefRep_apply_mk (p := 2) c.chief.2.1 c.chief.2.2.1 g' n']
      have hu : u = chiefConj c.chief.2.1 g' n' * n'⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe]
      rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv]
      abel
    rw [← hdiff]
    exact caseI_L_trivial_W'_fixed c hP hi hj hij hh _
      (caseI_L_trivial_diff_mem c hP hi (g := g') hg (QuotientGroup.mk n'))
  refine Subgroup.mem_map.mpr ⟨u⁻¹, (caseI_L_trivial_F c j).inv_mem huF, ?_⟩
  show ((u⁻¹ : ↥N) : G) = ⁅n, g⁆
  rw [Subgroup.coe_inv, commutatorElement_def]
  show ((g * n * g⁻¹ * n⁻¹ : G))⁻¹ = n * g * n⁻¹ * g⁻¹
  group

theorem caseI_L_trivial_M_le_F (j : ℕ) : M ≤ (caseI_L_trivial_F c j).map N.subtype := by
  intro m hm
  refine Subgroup.mem_map.mpr ⟨⟨m, le_of_lt c.chief.1 hm⟩, ?_, rfl⟩
  intro h hh
  have hm0 : ((⟨m, le_of_lt c.chief.1 hm⟩ : ↥N) : N ⧸ M.subgroupOf N) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hm
  rw [hm0, ofMul_one, map_zero]

theorem caseI_L_trivial (hP : PatI (c.opA 0) (c.opA 1) (c.opA 2)) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) →
      ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M := by
  intro V hV i j hi hj hij
  have hFV : V i ≤ (caseI_L_trivial_F c j).map N.subtype := by
    rw [hV i]
    exact sup_le (caseI_L_trivial_commutator_le_F c hP hi hj hij)
      (caseI_L_trivial_M_le_F c j)
  rw [Subgroup.commutator_le]
  intro y hy h hh
  obtain ⟨y', hy'F, rfl⟩ := Subgroup.mem_map.mp (hFV hy)
  exact (caseI_L_trivial_fix_iff c ⟨h, c.Lc_H j hh⟩ y').mp
    (hy'F ⟨h, c.Lc_H j hh⟩ hh)

end Ctx49

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
