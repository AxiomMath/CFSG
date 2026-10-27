module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Fixed

variable {n : ℕ} {K : Type*} [Field K] [CharP K 2]

theorem compl_fixes_pair {c : MulAut (projectiveSL n K)} (hc : c ∈ compl) {a b : Fin n}
    (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) :
    c (proj n K (SpecialLinearGroup.transvection hba 1 * SpecialLinearGroup.transvection hrab 1)) =
      proj n K (SpecialLinearGroup.transvection hba 1 *
        SpecialLinearGroup.transvection hrab 1) := by
  have hcomm : SpecialLinearGroup.transvection hba (1 : K) *
      SpecialLinearGroup.transvection hrab 1 =
      SpecialLinearGroup.transvection hrab 1 * SpecialLinearGroup.transvection hba 1 :=
    transvection_comm hba hrab ha hb.symm 1 1
  have hγ : graphAut (proj n K (SpecialLinearGroup.transvection hba (1 : K) *
      SpecialLinearGroup.transvection hrab 1)) =
      proj n K (SpecialLinearGroup.transvection hba 1 *
        SpecialLinearGroup.transvection hrab 1) := by
    rw [map_mul, map_mul, graphAut_proj_transvection, graphAut_proj_transvection,
      transvection_congr _ hba (Fin.rev_rev b) (Fin.rev_rev a), ← map_mul, ← map_mul, hcomm]
  have hf : ∀ σ : K ≃+* K, fieldAut n K σ (proj n K (SpecialLinearGroup.transvection hba (1 : K) *
      SpecialLinearGroup.transvection hrab 1)) =
      proj n K (SpecialLinearGroup.transvection hba 1 *
        SpecialLinearGroup.transvection hrab 1) := by
    intro σ
    rw [map_mul, map_mul, fieldAut_proj_transvection, fieldAut_proj_transvection, map_one,
      ← map_mul]
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact hf σ
  · rw [MulAut.mul_apply, hγ, hf]

omit [CharP K 2] in
theorem fieldAut_fixes (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) :
    fieldAut n K σ (proj n K (SpecialLinearGroup.transvection hij 1)) =
      proj n K (SpecialLinearGroup.transvection hij 1) := by
  rw [fieldAut_proj_transvection, map_one]

end Fixed

section Spread

variable {n : ℕ} {K : Type*} [Field K]

theorem eq_bot_of_transvections [Finite K] [CharP K 2] (hn : 2 ≤ n)
    {S : Subgroup (SpecialLinearGroup (Fin n) K)} (hS2 : IsPGroup 2 S)
    (hT : ∀ (i j : Fin n) (hij : i ≠ j), ∀ w ∈ fixVec S,
      ((SpecialLinearGroup.transvection hij (1 : K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w ∈ fixVec S) : S = ⊥ := by
  have h0 : (Pi.single (⟨0, by omega⟩ : Fin n) (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  obtain ⟨w, -, hw0, hwW⟩ := exists_ne_zero_mem_fixVec hS2 ⊤ (fun _ _ _ _ => Submodule.mem_top)
    Submodule.mem_top h0
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw0
  have hall : ∀ i, i ≠ k → Pi.single i (1 : K) ∈ fixVec S := fun i hik =>
    single_mem_of_transvection hik (hT i k hik) hwW hk
  apply eq_bot_of_forall_single_mem
  intro i
  by_cases hik : i = k
  · subst hik
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
    exact single_mem_of_transvection (Ne.symm hj) (hT i j (Ne.symm hj)) (hall j hj) (by simp)
  · exact hall i hik

theorem single_mem_of_rev {W : Submodule K (Fin n → K)}
    (hF1 : ∀ (a : Fin n) (ha : a ≠ Fin.rev a), ∀ w ∈ W,
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hF2 : ∀ (a b : Fin n) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b), a ≠ Fin.rev a →
      b ≠ Fin.rev b → ∀ w ∈ W, ((SpecialLinearGroup.transvection hba (1 : K) *
        SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {w : Fin n → K} (hw : w ∈ W) {k : Fin n} (hk : k ≠ Fin.rev k) (hwk : w k ≠ 0) :
    ∀ b, b ≠ Fin.rev b → Pi.single b (1 : K) ∈ W := by
  set a₀ := Fin.rev k with ha₀def
  have hra₀ : Fin.rev a₀ = k := Fin.rev_rev k
  have ha₀ : a₀ ≠ Fin.rev a₀ := by
    rw [hra₀]
    exact Ne.symm hk
  have ha₀k : a₀ ≠ k := by
    intro h
    exact ha₀ (h.trans hra₀.symm)
  have he₀ : Pi.single a₀ (1 : K) ∈ W := by
    refine single_mem_of_transvection ha₀k (fun v hv => ?_) hw hwk
    rw [← transvection_congr ha₀ ha₀k rfl hra₀]
    exact hF1 a₀ ha₀ v hv
  intro b hb
  by_cases hb₁ : b = a₀
  · rw [hb₁]
    exact he₀
  by_cases hb₂ : b = k
  · subst hb₂
    have hk' : b ≠ a₀ := hb₁
    refine single_mem_of_transvection hk' (fun v hv => ?_) he₀ (by simp)
    rw [← transvection_congr hk hk' rfl ha₀def.symm]
    exact hF1 b hk v hv
  · have hrab : Fin.rev a₀ ≠ Fin.rev b := fun h => hb₁ (Fin.rev_injective h).symm
    have hda : Fin.rev b ≠ a₀ := by
      intro h
      apply hb₂
      rw [← Fin.rev_rev b, h, hra₀]
    exact single_mem_of_pair hb₁ hrab hda (hF2 a₀ b hb₁ hrab ha₀ hb) he₀

end Spread

section Index

variable {m : ℕ}

theorem ne_rev_of_odd (hm : Odd m) (b : Fin (m + 1)) : b ≠ Fin.rev b := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_rev] at this
  obtain ⟨k, hk⟩ := hm
  omega

@[expose] def midIdx (m : ℕ) : Fin (m + 1) :=
  ⟨m / 2, by omega⟩

theorem rev_midIdx (hm : Even m) : Fin.rev (midIdx m) = midIdx m := by
  obtain ⟨k, hk⟩ := hm
  apply Fin.ext
  rw [Fin.val_rev]
  simp only [midIdx]
  omega

theorem ne_rev_of_ne_mid (hm : Even m) {b : Fin (m + 1)} (hb : b ≠ midIdx m) :
    b ≠ Fin.rev b := by
  intro h
  apply hb
  obtain ⟨k, hk⟩ := hm
  have := congrArg Fin.val h
  rw [Fin.val_rev] at this
  apply Fin.ext
  simp only [midIdx]
  omega

theorem zero_ne_midIdx (hm : 2 ≤ m) : (0 : Fin (m + 1)) ≠ midIdx m := by
  simp only [midIdx, ne_eq, Fin.ext_iff, Fin.val_zero]
  omega

theorem last_ne_midIdx (hm : 1 ≤ m) : Fin.last m ≠ midIdx m := by
  simp only [midIdx, ne_eq, Fin.ext_iff, Fin.val_last]
  omega

end Index

section Cases

variable {m : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem single_zero_ne_zero : (Pi.single (0 : Fin (m + 1)) (1 : K) : Fin (m + 1) → K) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem eq_bot_of_odd (hm : Odd m) {S : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)}
    (hS2 : IsPGroup 2 S)
    (hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S,
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b), a ≠ Fin.rev a →
      b ≠ Fin.rev b → ∀ w ∈ fixVec S, ((SpecialLinearGroup.transvection hba (1 : K) *
        SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S) : S = ⊥ := by
  obtain ⟨w, -, hw0, hwW⟩ := exists_ne_zero_mem_fixVec hS2 ⊤ (fun _ _ _ _ => Submodule.mem_top)
    Submodule.mem_top single_zero_ne_zero
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw0
  have hall := single_mem_of_rev hF1 hF2 hwW (ne_rev_of_odd hm k) hk
  exact eq_bot_of_forall_single_mem fun b => hall b (ne_rev_of_odd hm b)

end Cases

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem transvection_swap {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (β : K) :
    SpecialLinearGroup.transvection hjk (1 : K) * SpecialLinearGroup.transvection hij 1 *
      SpecialLinearGroup.transvection hik (β + 1) =
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hjk 1 *
      SpecialLinearGroup.transvection hik β := by
  refine Subtype.ext ?_
  change ((SpecialLinearGroup.transvection hjk (1 : K) : SpecialLinearGroup ι K) : Matrix ι ι K) *
      (SpecialLinearGroup.transvection hij (1 : K) : SpecialLinearGroup ι K) *
      (SpecialLinearGroup.transvection hik (β + 1) : SpecialLinearGroup ι K) =
    ((SpecialLinearGroup.transvection hij (1 : K) : SpecialLinearGroup ι K) : Matrix ι ι K) *
      (SpecialLinearGroup.transvection hjk (1 : K) : SpecialLinearGroup ι K) *
      (SpecialLinearGroup.transvection hik β : SpecialLinearGroup ι K)
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, transvection_mulVec, transvection_mulVec, transvection_mulVec,
    transvection_mulVec, transvection_mulVec, transvection_mulVec]
  funext l
  by_cases hli : l = i
  · subst hli
    simp [hij, hik]
    ring
  · by_cases hlj : l = j
    · subst hlj
      simp [hli, hik]
    · simp [Pi.single_apply, hli, hlj]

variable {m : ℕ}

noncomputable abbrev unitaryElt (hm : 2 ≤ m) (β : K) : SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection (zero_ne_midIdx hm) (1 : K) *
    SpecialLinearGroup.transvection (last_ne_midIdx (by omega)).symm 1 *
    SpecialLinearGroup.transvection (last_ne_zero (m := m) (by omega)).symm β

omit [CharP K 2] in
theorem unitaryElt_mulVec (hm : 2 ≤ m) (β : K) (v : Fin (m + 1) → K) :
    ((unitaryElt hm β : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      *ᵥ v = v + Pi.single 0 (β * v (Fin.last m)) + Pi.single (midIdx m) (v (Fin.last m)) +
        Pi.single 0 (v (midIdx m) + v (Fin.last m)) := by
  change (((SpecialLinearGroup.transvection (zero_ne_midIdx hm) (1 : K) :
      SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((SpecialLinearGroup.transvection (last_ne_midIdx (by omega)).symm (1 : K) :
        SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      ((SpecialLinearGroup.transvection (last_ne_zero (m := m) (by omega)).symm β :
        SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, transvection_mulVec, transvection_mulVec,
    transvection_mulVec]
  have h0m := zero_ne_midIdx hm
  have hml := (last_ne_midIdx (m := m) (by omega)).symm
  have h0l := (last_ne_zero (m := m) (by omega)).symm
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h0l.symm,
    Pi.single_eq_of_ne h0m.symm, one_mul, add_zero]

end Unitary

section Odd

variable {m : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem eq_bot_of_even_unitary (hm : Even m) (hm2 : 2 ≤ m)
    {S : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)} (hS2 : IsPGroup 2 S)
    (hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S,
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b), a ≠ Fin.rev a →
      b ≠ Fin.rev b → ∀ w ∈ fixVec S, ((SpecialLinearGroup.transvection hba (1 : K) *
        SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    {β : K} (hy : ∀ w ∈ fixVec S, ((unitaryElt hm2 β : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S) : S = ⊥ := by
  have hlast : Fin.last m ≠ midIdx m := last_ne_midIdx (by omega)
  have h0 : (0 : Fin (m + 1)) ≠ midIdx m := zero_ne_midIdx hm2
  have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := (last_ne_zero (by omega)).symm
  have hspread : ∀ w ∈ fixVec S, ∀ k, k ≠ midIdx m → w k ≠ 0 → ∀ b, b ≠ midIdx m →
      Pi.single b (1 : K) ∈ fixVec S := fun w hw k hk hwk b hb =>
    single_mem_of_rev hF1 hF2 hw (ne_rev_of_ne_mid hm hk) hwk b (ne_rev_of_ne_mid hm hb)
  have hmid_mem : (∀ b, b ≠ midIdx m → Pi.single b (1 : K) ∈ fixVec S) →
      Pi.single (midIdx m) (1 : K) ∈ fixVec S := by
    intro h
    have he0 := h 0 h0
    have h1 := hy _ (h (Fin.last m) hlast)
    rw [unitaryElt_mulVec] at h1
    have h2 := sub_mem (sub_mem h1 (h (Fin.last m) hlast)) (Submodule.smul_mem _ (β + 1) he0)
    convert h2 using 1
    funext l
    by_cases hl0 : l = 0
    · subst hl0
      simp [h0, h0l, hlast.symm]
    · by_cases hlm : l = midIdx m
      · subst hlm
        simp [hlast.symm, h0.symm]
      · simp [Pi.single_apply, hl0, hlm]
  have hfinish : (∀ b, b ≠ midIdx m → Pi.single b (1 : K) ∈ fixVec S) → S = ⊥ := fun h =>
    eq_bot_of_forall_single_mem fun b => by
      by_cases hb : b = midIdx m
      · rw [hb]
        exact hmid_mem h
      · exact h b hb
  obtain ⟨w, -, hw0, hwW⟩ := exists_ne_zero_mem_fixVec hS2 ⊤ (fun _ _ _ _ => Submodule.mem_top)
    Submodule.mem_top single_zero_ne_zero
  by_cases hk : ∃ k, k ≠ midIdx m ∧ w k ≠ 0
  · obtain ⟨k, hk, hwk⟩ := hk
    exact hfinish (hspread w hwW k hk hwk)
  · push Not at hk
    have hwm : w (midIdx m) ≠ 0 := by
      intro h
      apply hw0
      funext l
      by_cases hl : l = midIdx m
      · rw [hl, h]
        rfl
      · exact hk l hl
    have h1 := sub_mem (hy w hwW) hwW
    rw [unitaryElt_mulVec, hk (Fin.last m) hlast] at h1
    have he0 : Pi.single 0 (1 : K) ∈ fixVec S := by
      have h2 := Submodule.smul_mem _ (w (midIdx m))⁻¹ h1
      convert h2 using 1
      funext l
      by_cases hl0 : l = 0
      · subst hl0
        simp [inv_mul_cancel₀ hwm]
      · simp [hl0]
    exact hfinish (hspread _ he0 0 h0 (by simp))

omit [Finite K] [CharP K 2] in
theorem col_eq_of_mulVec_single {n : ℕ} {s : SpecialLinearGroup (Fin n) K} {b : Fin n}
    (h : ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single b 1 =
      Pi.single b 1) (i : Fin n) :
    ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i b =
      if i = b then 1 else 0 := by
  have := congrFun h i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, Pi.single_apply]

omit [Finite K] in
theorem eigen_eq_one {n : ℕ} {s : SpecialLinearGroup (Fin n) K} {a : ℕ} (hs : s ^ 2 ^ a = 1)
    {v : Fin n → K} (hv : v ≠ 0) {c : K}
    (h : ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) : c = 1 := by
  have hpow : ∀ N : ℕ, ((s ^ N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      c ^ N • v := by
    intro N
    induction N with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact Matrix.one_mulVec v
    | succ N ih =>
      change (((s ^ N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (s : Matrix (Fin n) (Fin n) K)) *ᵥ v = _
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 := hpow (2 ^ a)
  rw [hs] at h1
  change (1 : Matrix (Fin n) (Fin n) K) *ᵥ v = _ at h1
  rw [Matrix.one_mulVec] at h1
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have h2 : c ^ 2 ^ a = 1 := by
    have := congrFun h1 k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h3 : (c ^ 2 ^ a - 1) * v k = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (c + 1) ^ 2 ^ a = 0 := by
    rw [add_pow_char_pow, h2, one_pow, CharTwo.add_self_eq_zero]
  have h5 : c + 1 = 0 := pow_eq_zero_iff (pow_ne_zero a two_ne_zero) |>.mp h4
  calc c = c + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h5, zero_add]

theorem eq_bot_of_even_graph (hm : Even m) (hm2 : 2 ≤ m)
    {S : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)} (hS2 : IsPGroup 2 S)
    (hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S,
      ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b), a ≠ Fin.rev a →
      b ≠ Fin.rev b → ∀ w ∈ fixVec S, ((SpecialLinearGroup.transvection hba (1 : K) *
        SpecialLinearGroup.transvection hrab (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S)
    (hγ : ∀ s ∈ S, gammaSL s = s) : S = ⊥ := by
  have hrevmid : Fin.rev (midIdx m) = midIdx m := rev_midIdx hm
  have hrev_ne : ∀ i : Fin (m + 1), i ≠ midIdx m → Fin.rev i ≠ midIdx m := fun i hi h =>
    hi (by rw [← Fin.rev_rev i, h, hrevmid])
  have hent : ∀ s ∈ S, ∀ i j, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j =
      ((s⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (Fin.rev j) (Fin.rev i) := by
    intro s hs i j
    have h := congrArg (fun g : SpecialLinearGroup (Fin (m + 1)) K =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j) (hγ s hs)
    simp only [coe_gammaSL, Matrix.submatrix_apply, Matrix.transpose_apply, Fin.revPerm_apply] at h
    exact h.symm
  obtain ⟨w, -, hw0, hwW⟩ := exists_ne_zero_mem_fixVec hS2 ⊤ (fun _ _ _ _ => Submodule.mem_top)
    Submodule.mem_top single_zero_ne_zero
  by_cases h : ∃ w' ∈ fixVec S, ∃ k, k ≠ midIdx m ∧ w' k ≠ 0
  · obtain ⟨w', hw', k, hk, hwk⟩ := h
    have hall : ∀ b, b ≠ midIdx m → Pi.single b (1 : K) ∈ fixVec S := fun b hb =>
      single_mem_of_rev hF1 hF2 hw' (ne_rev_of_ne_mid hm hk) hwk b (ne_rev_of_ne_mid hm hb)
    apply eq_bot_of_forall_single_mem
    intro b
    by_cases hb : b = midIdx m
    · subst hb
      intro s hs
      have hoff : ∀ i, i ≠ midIdx m → ((s : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) i (midIdx m) = 0 := by
        intro i hi
        rw [hent s hs i (midIdx m), hrevmid,
          col_eq_of_mulVec_single (hall (Fin.rev i) (hrev_ne i hi) _ (S.inv_mem hs)) (midIdx m)]
        simp [Ne.symm (hrev_ne i hi)]
      have hsv : ((s : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
          *ᵥ Pi.single (midIdx m) 1 = ((s : SpecialLinearGroup (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) (midIdx m) (midIdx m) •
              Pi.single (midIdx m) 1 := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
        by_cases hi : i = midIdx m
        · subst hi
          simp
        · simp [hoff i hi, hi]
      obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
      have ha' : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
      have hne : (Pi.single (midIdx m) (1 : K) : Fin (m + 1) → K) ≠ 0 := by
        intro h0
        have := congrFun h0 (midIdx m)
        simp at this
      rw [hsv, eigen_eq_one ha' hne hsv, one_smul]
    · exact hall b hb
  · push Not at h
    exfalso
    have hwm : w (midIdx m) ≠ 0 := by
      intro h0
      apply hw0
      funext l
      by_cases hl : l = midIdx m
      · rw [hl, h0]
        rfl
      · exact h w hwW l hl
    have hemid : Pi.single (midIdx m) (1 : K) ∈ fixVec S := by
      have e : Pi.single (midIdx m) (1 : K) = (w (midIdx m))⁻¹ • w := by
        funext l
        by_cases hl : l = midIdx m
        · subst hl
          simp [inv_mul_cancel₀ hwm]
        · simp [hl, h w hwW l hl]
      rw [e]
      exact Submodule.smul_mem _ _ hwW
    have hrow : ∀ s ∈ S, ∀ j, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (midIdx m) j = if j = midIdx m then 1 else 0 := by
      intro s hs j
      rw [hent s hs (midIdx m) j, hrevmid, col_eq_of_mulVec_single (hemid _ (S.inv_mem hs))]
      by_cases hj : j = midIdx m
      · simp [hj, hrevmid]
      · simp [hrev_ne j hj, hj]
    set U : Submodule K (Fin (m + 1) → K) := LinearMap.ker (LinearMap.proj (midIdx m))
    have hU : ∀ s ∈ S, ∀ u ∈ U, ((s : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ u ∈ U := by
      intro s hs u hu
      simp only [U, LinearMap.mem_ker, LinearMap.proj_apply] at hu ⊢
      rw [Matrix.mulVec, dotProduct]
      simp [hrow s hs, hu]
    have he0U : Pi.single 0 (1 : K) ∈ U := by
      simp only [U, LinearMap.mem_ker, LinearMap.proj_apply]
      exact Pi.single_eq_of_ne (zero_ne_midIdx hm2).symm 1
    obtain ⟨u, huU, hu0, huW⟩ := exists_ne_zero_mem_fixVec hS2 U hU he0U single_zero_ne_zero
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hu0
    have hkm : k ≠ midIdx m := by
      intro hkm
      subst hkm
      apply hk
      simpa [U] using huU
    exact hk (h u huW k hkm)

end Odd

section Input

variable {m : ℕ} {K : Type*} [Field K] [CharP K 2]

theorem exists_trace_one {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ β : K, σ β = β + 1 := by
  obtain ⟨z, hz⟩ : ∃ z, σ z ≠ z := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  have hσz : σ (σ z) = z := by
    have := congrArg (fun τ : K ≃+* K => τ z) hσσ
    exact this
  set d := z + σ z with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hz
    have : σ z = -z := eq_neg_of_add_eq_zero_right h0
    rw [this, CharTwo.neg_eq]
  have hσd : σ d = d := by
    rw [hd, map_add, hσz, add_comm]
  refine ⟨z * d⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hσd]
  field_simp
  rw [hd]
  linear_combination (CharTwo.add_self_eq_zero z).symm

theorem compl_fixes_unitary (hm : Even m) (hm2 : 2 ≤ m) {σ : K ≃+* K} {β : K}
    (hβ : σ β = β + 1) :
    (fieldAut (m + 1) K σ * graphAut : MulAut (projectiveSL (m + 1) K))
      (proj (m + 1) K (unitaryElt hm2 β)) = proj (m + 1) K (unitaryElt hm2 β) := by
  have hrevmid := rev_midIdx hm
  have hg : graphAut (proj (m + 1) K (unitaryElt hm2 β)) =
      proj (m + 1) K (SpecialLinearGroup.transvection (last_ne_midIdx (m := m) (by omega)).symm
        (1 : K) * SpecialLinearGroup.transvection (zero_ne_midIdx hm2) 1 *
        SpecialLinearGroup.transvection (last_ne_zero (m := m) (by omega)).symm β) := by
    simp only [unitaryElt, map_mul, graphAut_proj_transvection]
    rw [transvection_congr _ (last_ne_midIdx (m := m) (by omega)).symm hrevmid (Fin.rev_zero m),
      transvection_congr _ (zero_ne_midIdx hm2) (Fin.rev_last m) hrevmid,
      transvection_congr _ (last_ne_zero (m := m) (by omega)).symm (Fin.rev_last m)
        (Fin.rev_zero m)]
  rw [MulAut.mul_apply, hg]
  simp only [map_mul, fieldAut_proj_transvection, map_one, hβ]
  rw [← map_mul, ← map_mul, transvection_swap (zero_ne_midIdx hm2)
    (last_ne_midIdx (m := m) (by omega)).symm (last_ne_zero (m := m) (by omega)).symm β,
    map_mul, map_mul]

theorem pslCoreInput_holds : PSLCoreInput := by
  intro m K _ _ _ hm c hc hc2 _ Q hfix hQ2 hnorm
  obtain ⟨S, hS2, hSQ, hSZ, hS⟩ := exists_lift Q hQ2
  have hinv : ∀ h : SpecialLinearGroup (Fin (m + 1)) K,
      c (proj (m + 1) K h) = proj (m + 1) K h → ∀ w ∈ fixVec S,
        ((h : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈
          fixVec S := by
    intro h hh w hw
    refine mulVec_mem_fixVec (fun s hs => ?_) hw
    have hh' : c (proj (m + 1) K h⁻¹) = proj (m + 1) K h⁻¹ := by rw [map_inv, map_inv, hh]
    have := conj_mem_lift hS2 hSQ hS (y := h⁻¹) (fun q hq => hnorm _ hh' q hq) hs
    rwa [inv_inv] at this
  suffices hSbot : S = ⊥ by rw [← hSQ, hSbot, Subgroup.map_bot]
  obtain ⟨σ, hσσ, hcσ⟩ := involution_compl (by omega) hc hc2
  rcases hcσ with rfl | rfl
  · exact eq_bot_of_transvections (by omega) hS2 fun i j hij => hinv _ (fieldAut_fixes σ hij)
  · have hF1 : ∀ (a : Fin (m + 1)) (ha : a ≠ Fin.rev a), ∀ w ∈ fixVec S,
        ((SpecialLinearGroup.transvection ha (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S := fun a ha =>
      hinv _ (compl_fixes hc ha (Fin.rev_rev a) rfl)
    have hF2 : ∀ (a b : Fin (m + 1)) (hba : b ≠ a) (hrab : Fin.rev a ≠ Fin.rev b),
        a ≠ Fin.rev a → b ≠ Fin.rev b → ∀ w ∈ fixVec S,
          ((SpecialLinearGroup.transvection hba (1 : K) * SpecialLinearGroup.transvection hrab
            (1 : K) : SpecialLinearGroup (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ w ∈ fixVec S :=
      fun a b hba hrab ha hb => hinv _ (compl_fixes_pair hc hba hrab ha hb)
    rcases Nat.even_or_odd m with hme | hmo
    · by_cases hσ1 : σ = 1
      · subst hσ1
        refine eq_bot_of_even_graph hme (by omega) hS2 hF1 hF2 fun s hs => ?_
        have hsQ : proj (m + 1) K s ∈ Q := hSQ ▸ ⟨s, hs, rfl⟩
        have h1 : proj (m + 1) K (gammaSL s) = proj (m + 1) K s := by
          have := hfix _ hsQ
          rwa [map_one, one_mul, graphAut_proj] at this
        obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
        have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have h2 : gammaSL s ∈ S := hS _ (by rw [h1]; exact hsQ) ⟨k, by rw [← map_pow, hk', map_one]⟩
        have h3 : (gammaSL s)⁻¹ * s ∈ S ⊓ scalars (m + 1) K :=
          ⟨S.mul_mem (S.inv_mem h2) hs, proj_eq_proj_iff.mp h1⟩
        rw [hSZ, Subgroup.mem_bot] at h3
        exact inv_mul_eq_one.mp h3
      · obtain ⟨β, hβ⟩ := exists_trace_one hσσ hσ1
        exact eq_bot_of_even_unitary hme (by omega) hS2 hF1 hF2
          (hinv _ (compl_fixes_unitary hme (by omega) hβ))
    · exact eq_bot_of_odd hmo hS2 hF1 hF2

end Input

end AutPSL

end CFSG.StandardType
