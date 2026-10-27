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

theorem pat_transport {P Q : Submodule (ZMod 2) V} {S Si T T' : Module.End (ZMod 2) V}
    (hSiS : Si * S = 1) (hSSi : S * Si = 1) (hQ : ∀ v ∈ Q, Si v ∈ P)
    (hST : S * T = T' * S) :
    (TrivOn P T → TrivOn Q T') ∧ (FpfOn P T → FpfOn Q T') := by
  have hSiS' : ∀ z : V, Si (S z) = z := fun z => by
    rw [← Module.End.mul_apply, hSiS, Module.End.one_apply]
  have hSSi' : ∀ z : V, S (Si z) = z := fun z => by
    rw [← Module.End.mul_apply, hSSi, Module.End.one_apply]
  constructor
  · intro hT y hy
    have hyP : Si y ∈ P := hQ y hy
    calc T' y = T' (S (Si y)) := by rw [hSSi' y]
      _ = (T' * S) (Si y) := (Module.End.mul_apply T' S (Si y)).symm
      _ = (S * T) (Si y) := by rw [hST]
      _ = S (T (Si y)) := Module.End.mul_apply S T (Si y)
      _ = S (Si y) := by rw [hT (Si y) hyP]
      _ = y := hSSi' y
  · intro hfpf y hy hyfix
    have hyP : Si y ∈ P := hQ y hy
    have hS : S (T (Si y)) = S (Si y) := by
      rw [← Module.End.mul_apply, hST, Module.End.mul_apply, hSSi' y, hyfix]
    have hfix : T (Si y) = Si y := by
      calc T (Si y) = Si (S (T (Si y))) := (hSiS' (T (Si y))).symm
        _ = Si (S (Si y)) := by rw [hS]
        _ = Si y := hSiS' (Si y)
    have hzero : Si y = 0 := hfpf (Si y) hyP hfix
    calc y = S (Si y) := (hSSi' y).symm
      _ = S 0 := by rw [hzero]
      _ = 0 := map_zero S

theorem pat_mem_inf_of_mul {T B B' Z : Module.End (ZMod 2) V} (hmul : T * e2 B = e2 B' * T)
    (hker : T * e2 Z = e2 Z * T) :
    ∀ v ∈ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z),
      T v ∈ LinearMap.range (e2 B') ⊓ LinearMap.ker (e2 Z) := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv1
    refine LinearMap.mem_range.mpr ⟨T u, ?_⟩
    calc e2 B' (T u) = (e2 B' * T) u := (Module.End.mul_apply (e2 B') T u).symm
      _ = (T * e2 B) u := by rw [← hmul]
      _ = T (e2 B u) := Module.End.mul_apply T (e2 B) u
  · apply (LinearMap.mem_ker (f := e2 Z)).mpr
    have hv2' : e2 Z v = 0 := (LinearMap.mem_ker (f := e2 Z)).mp hv2
    rw [← Module.End.mul_apply, ← hker, Module.End.mul_apply, hv2', map_zero]

theorem pat_Xi_mul_A (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Xi * A0 = A1 * Xi ∧ Xi * A1 = A2 * Xi ∧ Xi * A2 = A0 * Xi := by
  have h0 : Xi * A0 * X * Xi = A1 * Xi := by rw [hW.rot0]
  have h1 : Xi * A1 * X * Xi = A2 * Xi := by rw [hW.rot1]
  have h2 : Xi * A2 * X * Xi = A0 * Xi := by rw [hW.rot2]
  rw [show Xi * A0 * X * Xi = Xi * A0 by rw [mul_assoc, hW.XXi, mul_one]] at h0
  rw [show Xi * A1 * X * Xi = Xi * A1 by rw [mul_assoc, hW.XXi, mul_one]] at h1
  rw [show Xi * A2 * X * Xi = Xi * A2 by rw [mul_assoc, hW.XXi, mul_one]] at h2
  exact ⟨h0, h1, h2⟩

theorem pat_X_mem (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (∀ v ∈ Wbz2 A0 A1 A2, X v ∈ Wb A0 A1 A2) ∧
      (∀ v ∈ Wbz A0 A1 A2, X v ∈ Wbz2 A0 A1 A2) := by
  obtain ⟨hB, hZ, hBZ, -, -⟩ := hW.rels
  obtain ⟨-, -, -, hcZ, -, hBZ2e2, hBe2⟩ :=
    e2_conj_relations (A0 * A1 ^ 2) (A0 * A1 * A2) X Xi hW.XiX hW.XXi hB hZ hBZ
      hW.X_comm_z hW.Xi_b_X
  exact ⟨pat_mem_inf_of_mul hBe2.symm hcZ, pat_mem_inf_of_mul hBZ2e2.symm hcZ⟩

theorem pat_invariant_Wb {T : Module.End (ZMod 2) V}
    (hTB : Commute T (A0 * A1 ^ 2)) (hTZ : Commute T (A0 * A1 * A2)) :
    ∀ v ∈ Wb A0 A1 A2, T v ∈ Wb A0 A1 A2 := by
  intro v hv
  refine ⟨range_e2_invariant_of_comm T (A0 * A1 ^ 2) hTB.eq v hv.1, ?_⟩
  change e2 (A0 * A1 * A2) (T v) = 0
  have hcomm : T * e2 (A0 * A1 * A2) = e2 (A0 * A1 * A2) * T :=
    mul_e2_comm_of_comm T (A0 * A1 * A2) hTZ.eq
  have hv2 : e2 (A0 * A1 * A2) v = 0 :=
    (LinearMap.mem_ker (f := e2 (A0 * A1 * A2))).mp hv.2
  rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply, hv2, map_zero]

theorem pat_case_dichotomy_W (W : Submodule (ZMod 2) V) (A0 A1 A2 Z : Module.End (ZMod 2) V)
    (hWcard : Nat.card ↥W = 4) (hA03 : A0 ^ 3 = 1) (hA23 : A2 ^ 3 = 1)
    (hW0 : ∀ x : V, x ∈ W → A0 x ∈ W) (hW1 : ∀ x : V, x ∈ W → A1 x ∈ W)
    (hW2 : ∀ x : V, x ∈ W → A2 x ∈ W)
    (hZfpf : ∀ x : V, x ∈ W → Z x = x → x = 0)
    (hAeq : ∀ x : V, x ∈ W → A0 x = A1 x) (hprod : A0 * A1 * A2 = Z) :
    (TrivOn W A0 ∧ TrivOn W A1 ∧ FpfOn W A2) ∨
      (FpfOn W A0 ∧ FpfOn W A1 ∧ TrivOn W A2) ∨
      (FpfOn W A0 ∧ FpfOn W A1 ∧ FpfOn W A2) := by
  have hA1fpf_of : (∀ x : V, x ∈ W → A0 x = x → x = 0) →
      (∀ x : V, x ∈ W → A1 x = x → x = 0) := by
    intro h x hx hx1
    exact h x hx (by rw [hAeq x hx]; exact hx1)
  rcases eq_one_or_fpf_on_of_card_four W A0 hWcard hW0 hA03 with hA0one | hA0fpf
  · refine Or.inl ⟨hA0one, fun x hx => (hAeq x hx).symm.trans (hA0one x hx), ?_⟩
    intro x hx hA2x
    apply hZfpf x hx
    have hZx : Z x = A0 (A1 (A2 x)) := by
      have h := congrArg (fun f : Module.End (ZMod 2) V => f x) hprod
      simpa [Module.End.mul_apply] using h.symm
    rw [hZx, hA2x, hA0one (A1 x) (hW1 x hx), ← hAeq x hx, hA0one x hx]
  · rcases eq_one_or_fpf_on_of_card_four W A2 hWcard hW2 hA23 with hA2one | hA2fpf
    · exact Or.inr (Or.inl ⟨hA0fpf, hA1fpf_of hA0fpf, hA2one⟩)
    · exact Or.inr (Or.inr ⟨hA0fpf, hA1fpf_of hA0fpf, hA2fpf⟩)

theorem pat_from_Wb (hW : Wt49 A0 A1 A2 X Xi S Si)
    (hW0 : ∀ v ∈ Wb A0 A1 A2, A0 v ∈ Wb A0 A1 A2)
    (hW1 : ∀ v ∈ Wb A0 A1 A2, A1 v ∈ Wb A0 A1 A2)
    (hW2 : ∀ v ∈ Wb A0 A1 A2, A2 v ∈ Wb A0 A1 A2)
    (hZfpf : ∀ v ∈ Wb A0 A1 A2, (A0 * A1 * A2) v = v → v = 0)
    (hAeq : ∀ v ∈ Wb A0 A1 A2, A0 v = A1 v) :
    PatI A0 A1 A2 ∨ PatIIa A0 A1 A2 ∨ PatIIb A0 A1 A2 := by
  obtain ⟨hXb2, hXb⟩ := pat_X_mem hW
  obtain ⟨hXiA0, hXiA1, hXiA2⟩ := pat_Xi_mul_A hW
  have t0 := pat_transport hW.XXi hW.XiX hXb2 hXiA0
  have t1 := pat_transport hW.XXi hW.XiX hXb2 hXiA1
  have t2 := pat_transport hW.XXi hW.XiX hXb2 hXiA2
  have s0 := pat_transport hW.XXi hW.XiX hXb hXiA0
  have s1 := pat_transport hW.XXi hW.XiX hXb hXiA1
  have s2 := pat_transport hW.XXi hW.XiX hXb hXiA2
  rcases pat_case_dichotomy_W (Wb A0 A1 A2) A0 A1 A2 (A0 * A1 * A2) hW.pieces.2.1
      hW.cube0 hW.cube2 hW0 hW1 hW2 hZfpf hAeq rfl with hI | hIIa | hIIb
  · obtain ⟨h0, h1, h2⟩ := hI
    exact Or.inl ⟨⟨h0, h1, h2⟩, ⟨s2.1 (t1.1 h1), s0.2 (t2.2 h2), s1.1 (t0.1 h0)⟩,
      ⟨t2.2 h2, t0.1 h0, t1.1 h1⟩⟩
  · obtain ⟨h0, h1, h2⟩ := hIIa
    exact Or.inr (Or.inl ⟨⟨h0, h1, h2⟩, ⟨s2.2 (t1.2 h1), s0.1 (t2.1 h2), s1.2 (t0.2 h0)⟩,
      ⟨t2.1 h2, t0.2 h0, t1.2 h1⟩⟩)
  · obtain ⟨h0, h1, h2⟩ := hIIb
    exact Or.inr (Or.inr ⟨⟨h0, h1, h2⟩, ⟨s2.2 (t1.2 h1), s0.2 (t2.2 h2), s1.2 (t0.2 h0)⟩,
      ⟨t2.2 h2, t0.2 h0, t1.2 h1⟩⟩)

theorem Wt49.pat (hW : Wt49 A0 A1 A2 X Xi S Si) :
    PatI A0 A1 A2 ∨ PatIIa A0 A1 A2 ∨ PatIIb A0 A1 A2 := by
  obtain ⟨hB, hZ, hBZ, -, -⟩ := hW.rels
  have hc01 : Commute A0 A1 := hW.comm01
  have hc02 : Commute A0 A2 := hW.comm02
  have hc12 : Commute A1 A2 := hW.comm12
  have hW0 : ∀ v ∈ Wb A0 A1 A2, A0 v ∈ Wb A0 A1 A2 :=
    pat_invariant_Wb ((Commute.refl A0).mul_right (hc01.pow_right 2))
      (((Commute.refl A0).mul_right hc01).mul_right hc02)
  have hW1 : ∀ v ∈ Wb A0 A1 A2, A1 v ∈ Wb A0 A1 A2 :=
    pat_invariant_Wb (hc01.symm.mul_right ((Commute.refl A1).pow_right 2))
      (((hc01.symm).mul_right (Commute.refl A1)).mul_right hc12)
  have hW2 : ∀ v ∈ Wb A0 A1 A2, A2 v ∈ Wb A0 A1 A2 :=
    pat_invariant_Wb ((hc02.symm).mul_right ((hc12.symm).pow_right 2))
      (((hc02.symm).mul_right hc12.symm).mul_right (Commute.refl A2))
  have hZfpf : ∀ v ∈ Wb A0 A1 A2, (A0 * A1 * A2) v = v → v = 0 := by
    intro v hv hvfix
    have hv2 : e2 (A0 * A1 * A2) v = 0 :=
      (LinearMap.mem_ker (f := e2 (A0 * A1 * A2))).mp hv.2
    have hve : e2 (A0 * A1 * A2) v = v := (e2_eq_self_iff (A0 * A1 * A2) hZ v).mpr hvfix
    rw [hve] at hv2
    exact hv2
  have hAeq : ∀ v ∈ Wb A0 A1 A2, A0 v = A1 v := by
    intro v hv
    have hA1B : A1 * (A0 * A1 ^ 2) = A0 := by
      calc A1 * (A0 * A1 ^ 2) = (A1 * A0) * A1 ^ 2 := by rw [mul_assoc]
        _ = (A0 * A1) * A1 ^ 2 := by rw [← hW.comm01]
        _ = A0 * (A1 * A1 ^ 2) := by rw [mul_assoc]
        _ = A0 * A1 ^ 3 := by rw [← pow_succ']
        _ = A0 := by rw [hW.cube1, mul_one]
    have hBv : (A0 * A1 ^ 2) v = v := (mem_range_e2_iff (A0 * A1 ^ 2) hB v).mp hv.1
    have h : A1 ((A0 * A1 ^ 2) v) = A1 v := by rw [hBv]
    simpa only [← Module.End.mul_apply, hA1B] using h
  exact pat_from_Wb hW hW0 hW1 hW2 hZfpf hAeq

theorem Wt49.pair_eq (hW : Wt49 A0 A1 A2 X Xi S Si) (h : FpfOn (Wb A0 A1 A2) A0) :
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) =
      LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) := by
  obtain ⟨hB, hZ, -, -, -⟩ := hW.rels
  have hA2Z : A2 * (A0 * A1 * A2) = (A0 * A1 * A2) * A2 :=
    (Commute.mul_right ((Commute.mul_left (hW.comm02 : Commute A0 A2)
      (hW.comm12 : Commute A1 A2)).symm) (Commute.refl A2)).eq
  have hBA1 : A0 * A1 ^ 2 * A1 = A0 := by
    rw [mul_assoc, ← pow_succ, hW.cube1, mul_one]
  have hY := Y_eq_bot_of_fpf A0 A1 A2 (A0 * A1 ^ 2) (A0 * A1 * A2) hW.cube0 hW.cube1 hW.cube2
    hB hZ hW.comm02 hW.comm12 hA2Z rfl hBA1 (fun x hx => h x hx)
  exact pair_eq_of_Y_eq_bot A0 A1 A2 hW.comm02 hW.comm12 hW.cube2 hY

theorem Wt49.pairs_eq (hW : Wt49 A0 A1 A2 X Xi S Si) (h0 : FpfOn (Wb A0 A1 A2) A0)
    (h1 : FpfOn (Wbz2 A0 A1 A2) A1) (h2 : FpfOn (Wbz A0 A1 A2) A2) :
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) =
        LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) ∧
      LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A2) =
        LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) ∧
      LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) =
        LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) := by
  have e01 := hW.pair_eq h0
  have e12 := hW.rotate.pair_eq (by rwa [hW.Wb_rotate])
  have e20 := hW.rotate.rotate.pair_eq (by rwa [hW.rotate.Wb_rotate, hW.Wbz2_rotate])
  refine ⟨e01, ?_, ?_⟩
  · rw [inf_comm (LinearMap.range (e2 A0)) (LinearMap.range (e2 A2)), e20]
    ac_rfl
  · rw [e12]
    ac_rfl

end Operators

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}

namespace Ctx49

variable (c : Ctx49 H X L Q I x A a n N M)
variable [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]

theorem disj_Lc_fixes (D : Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))
    (k i j : ℕ) (hk : k < 3) (hi : i < 3) (hj : j < 3) (hik : i ≠ k) (hjk : j ≠ k)
    (hDk : D = LinearMap.range (e2 (c.opA i)) ⊓ LinearMap.range (e2 (c.opA j)))
    (hfix : ∀ w ∈ D, op49 c.chief (c.ai k) w = w) :
    ∀ g : ↥H, (g : G) ∈ Lc L x k → ∀ w ∈ D, op49 c.chief g w = w := by
  have hinv : ∀ g : ↥H, (g : G) ∈ Lc L x k → ∀ w ∈ D, op49 c.chief g w ∈ D := by
    intro g hg w hw
    rw [hDk] at hw ⊢
    exact ⟨range_e2_invariant_of_comm (op49 c.chief g) (c.opA i)
        (c.op_comm (i := k) (j := i) hk hi hik.symm hg (c.ai_mem i)) w hw.1,
      range_e2_invariant_of_comm (op49 c.chief g) (c.opA j)
        (c.op_comm (i := k) (j := j) hk hj hjk.symm hg (c.ai_mem j)) w hw.2⟩
  exact c.Lc_trivial_of_invariant k D hinv hfix

theorem disj
    (hII : PatIIa (c.opA 0) (c.opA 1) (c.opA 2) ∨ PatIIb (c.opA 0) (c.opA 1) (c.opA 2)) :
    Disj49 (c.opA 0) (c.opA 1) (c.opA 2) := by
  have hW := c.wt
  have h0 : FpfOn (Wb (c.opA 0) (c.opA 1) (c.opA 2)) (c.opA 0) :=
    hII.elim (fun h => h.1.1) (fun h => h.1.1)
  have h1 : FpfOn (Wbz2 (c.opA 0) (c.opA 1) (c.opA 2)) (c.opA 1) :=
    hII.elim (fun h => h.2.2.2.1) (fun h => h.2.2.2.1)
  have h2 : FpfOn (Wbz (c.opA 0) (c.opA 1) (c.opA 2)) (c.opA 2) :=
    hII.elim (fun h => h.2.1.2.2) (fun h => h.2.1.2.2)
  obtain ⟨e01, e02, e12⟩ := hW.pairs_eq h0 h1 h2
  have hfix0 : ∀ w ∈ LinearMap.range (e2 (c.opA 0)) ⊓ LinearMap.range (e2 (c.opA 1)) ⊓
      LinearMap.range (e2 (c.opA 2)), op49 c.chief (c.ai 0) w = w := by
    intro w hw
    exact (mem_range_e2_iff (c.opA 0) hW.cube0 w).mp hw.1.1
  have hfix1 : ∀ w ∈ LinearMap.range (e2 (c.opA 0)) ⊓ LinearMap.range (e2 (c.opA 1)) ⊓
      LinearMap.range (e2 (c.opA 2)), op49 c.chief (c.ai 1) w = w := by
    intro w hw
    exact (mem_range_e2_iff (c.opA 1) hW.cube1 w).mp hw.1.2
  have hfix2 : ∀ w ∈ LinearMap.range (e2 (c.opA 0)) ⊓ LinearMap.range (e2 (c.opA 1)) ⊓
      LinearMap.range (e2 (c.opA 2)), op49 c.chief (c.ai 2) w = w := by
    intro w hw
    exact (mem_range_e2_iff (c.opA 2) hW.cube2 w).mp hw.2
  have hL0 := disj_Lc_fixes c _ 0 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e12.symm hfix0
  have hL1 := disj_Lc_fixes c _ 1 0 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e02.symm hfix1
  have hL2 := disj_Lc_fixes c _ 2 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) e01.symm hfix2
  have hD : LinearMap.range (e2 (c.opA 0)) ⊓ LinearMap.range (e2 (c.opA 1)) ⊓
      LinearMap.range (e2 (c.opA 2)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    exact c.eq_zero_of_fixed (fun g hg => hL0 g hg v hv) (fun g hg => hL1 g hg v hv)
      (fun g hg => hL2 g hg v hv)
  exact ⟨e01.trans hD, e02.trans hD, e12.trans hD⟩

end Ctx49

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
