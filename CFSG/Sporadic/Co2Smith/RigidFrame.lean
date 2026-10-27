module

public import CFSG.Sporadic.Co2Smith.RigidBasis

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native

universe u

@[expose] def vcode (e0 e1 e2 : Bool) : Fin 8 :=
  ⟨(if e0 then 1 else 0) + 2 * (if e1 then 1 else 0) + 4 * (if e2 then 1 else 0), by
    split_ifs <;> omega⟩

theorem vcode_bits (a : Fin 8) :
    vcode (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2) = a := by
  revert a
  decide

@[expose] def stdMat (k : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) := rowsMatrix 8 Native.stdRows[k]!

abbrev sv (a : Fin 8) : Fin 8 → ZMod 2 := Pi.single a 1

theorem std_y1 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 0 b (vcode e0 e1 e2) =
    (if e0 then sv (vcode false e1 e2) + sv (vcode true e1 e2) else sv (vcode true e1 e2)) b := by
  decide

theorem std_s1 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 1 b (vcode e0 e1 e2) =
    (if e0 then sv (vcode false e1 e2) + sv (vcode true e1 e2) else sv (vcode false e1 e2)) b := by
  decide

theorem std_y2 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 2 b (vcode e0 e1 e2) =
    (if e1 then sv (vcode e0 false e2) + sv (vcode e0 true e2) else sv (vcode e0 true e2)) b := by
  decide

theorem std_s2 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 3 b (vcode e0 e1 e2) =
    (if e1 then sv (vcode e0 false e2) + sv (vcode e0 true e2) else sv (vcode e0 false e2)) b := by
  decide

theorem std_y3 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 4 b (vcode e0 e1 e2) =
    (if e2 then sv (vcode e0 e1 false) + sv (vcode e0 e1 true) else sv (vcode e0 e1 true)) b := by
  decide

theorem std_s3 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat 5 b (vcode e0 e1 e2) =
    (if e2 then sv (vcode e0 e1 false) + sv (vcode e0 e1 true) else sv (vcode e0 e1 false)) b := by
  decide

theorem std_p12 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8,
    stdMat 6 b (vcode e0 e1 e2) = sv (vcode e1 e0 e2) b := by
  decide

theorem std_p23 : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8,
    stdMat 7 b (vcode e0 e1 e2) = sv (vcode e0 e2 e1) b := by
  decide

theorem p12_rel
    (k : ℕ) (hk : k < 6) : frS 6 * frS k = frS (sw12 k) * frS 6 := frS_p12 hk

theorem p23_rel
    (k : ℕ) (hk : k < 6) : frS 7 * frS k = frS (sw23 k) * frS 7 := frS_p23 hk

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem v_vcode
    (e0 e1 e2 : Bool) : c.v (vcode e0 e1 e2) = c.vv e0 e1 e2 := by
  cases e0 <;> cases e1 <;> cases e2 <;> rfl

theorem β_sv
    (a : Fin 8) : c.β (sv a) = c.v a := c.β_single a

theorem β_sv_add
    (a b : Fin 8) : c.β (sv a + sv b) = c.v a * c.v b := by
  rw [c.β_add, c.β_sv, c.β_sv]

theorem yb_conj
    {p k k' : ℕ} (hp : frS p * frS k = frS k' * frS p) (e : Bool) (m : c.M) :
    c.mA (frS p) (c.yb k e m) = c.yb k' e (c.mA (frS p) m) := by
  cases e
  · rfl
  · exact c.mA_conj_of hp m

theorem s_y
    (i : ℕ) (hi : i < 3) (m : c.M) :
    c.mA (frS (2 * i + 1)) (c.mA (frS (2 * i)) m) =
      c.mA (frS (2 * i)) (c.mA (frS (2 * i)) (c.mA (frS (2 * i + 1)) m)) := by
  have h := c.mA_sy i hi (c.mA (frS (2 * i + 1)) m)
  rwa [c.mA_s2 i hi] at h

theorem comm_frS
    {k l : ℕ} (hk : k < 6) (hl : l < 6) (hkl : k / 2 ≠ l / 2) :
    frS k * frS l = frS l * frS k := frS_comm' hk hl hkl

theorem yy0
    (m : c.M) : c.mA (frS 0) (c.mA (frS 0) m) = m * c.mA (frS 0) m :=
  c.yy_eq (Or.inl rfl) c.y1_fpf m

theorem yy2
    (m : c.M) : c.mA (frS 2) (c.mA (frS 2) m) = m * c.mA (frS 2) m :=
  c.yy_eq (Or.inr (Or.inl rfl)) c.y2_fpf m

theorem yy4
    (m : c.M) : c.mA (frS 4) (c.mA (frS 4) m) = m * c.mA (frS 4) m :=
  c.yy_eq (Or.inr (Or.inr rfl)) c.y3_fpf m

theorem y1_vv
    (e0 e1 e2 : Bool) : c.mA (frS 0) (c.vv e0 e1 e2) =
    if e0 then c.vv false e1 e2 * c.vv true e1 e2 else c.vv true e1 e2 := by
  cases e0
  · rfl
  · exact c.yy0 _

theorem y2_vv
    (e0 e1 e2 : Bool) : c.mA (frS 2) (c.vv e0 e1 e2) =
    if e1 then c.vv e0 false e2 * c.vv e0 true e2 else c.vv e0 true e2 := by
  rw [vv, c.yb_conj (comm_frS (k := 2) (l := 0) (by norm_num) (by norm_num) (by norm_num))]
  cases e1
  · rfl
  · simp only [↓reduceIte]
    rw [yb_true, c.yy2, yb_mul]
    rfl

theorem y3_vv
    (e0 e1 e2 : Bool) : c.mA (frS 4) (c.vv e0 e1 e2) =
    if e2 then c.vv e0 e1 false * c.vv e0 e1 true else c.vv e0 e1 true := by
  rw [vv, c.yb_conj (comm_frS (k := 4) (l := 0) (by norm_num) (by norm_num) (by norm_num)),
    c.yb_conj (comm_frS (k := 4) (l := 2) (by norm_num) (by norm_num) (by norm_num))]
  cases e2
  · rfl
  · simp only [↓reduceIte]
    rw [yb_true, c.yy4, yb_mul, yb_mul]
    rfl

theorem s1_vv
    (e0 e1 e2 : Bool) : c.mA (frS 1) (c.vv e0 e1 e2) =
    if e0 then c.vv false e1 e2 * c.vv true e1 e2 else c.vv false e1 e2 := by
  have hfix : c.mA (frS 1) (c.yb 2 e1 (c.yb 4 e2 c.w)) = c.yb 2 e1 (c.yb 4 e2 c.w) := by
    rw [c.yb_conj (comm_frS (k := 1) (l := 2) (by norm_num) (by norm_num) (by norm_num)),
      c.yb_conj (comm_frS (k := 1) (l := 4) (by norm_num) (by norm_num) (by norm_num)), c.s1_w]
  cases e0
  · exact hfix
  · show c.mA (frS 1) (c.mA (frS 0) _) = _
    simp only [↓reduceIte]
    have h := c.s_y 0 (by norm_num) (c.yb 2 e1 (c.yb 4 e2 c.w))
    simp only [mul_zero, zero_add] at h
    rw [h, hfix, c.yy0]
    rfl

theorem s2_vv
    (e0 e1 e2 : Bool) : c.mA (frS 3) (c.vv e0 e1 e2) =
    if e1 then c.vv e0 false e2 * c.vv e0 true e2 else c.vv e0 false e2 := by
  have hfix : c.mA (frS 3) (c.yb 4 e2 c.w) = c.yb 4 e2 c.w := by
    rw [c.yb_conj (comm_frS (k := 3) (l := 4) (by norm_num) (by norm_num) (by norm_num)),
      c.s2_w]
  rw [vv, c.yb_conj (comm_frS (k := 3) (l := 0) (by norm_num) (by norm_num) (by norm_num))]
  cases e1
  · rw [yb_false, hfix]
    rfl
  · simp only [↓reduceIte]
    rw [yb_true]
    have h := c.s_y 1 (by norm_num) (c.yb 4 e2 c.w)
    simp only [mul_one, show 2 + 1 = 3 from rfl] at h
    rw [h, hfix, c.yy2, yb_mul]
    rfl

theorem s3_vv
    (e0 e1 e2 : Bool) : c.mA (frS 5) (c.vv e0 e1 e2) =
    if e2 then c.vv e0 e1 false * c.vv e0 e1 true else c.vv e0 e1 false := by
  rw [vv, c.yb_conj (comm_frS (k := 5) (l := 0) (by norm_num) (by norm_num) (by norm_num)),
    c.yb_conj (comm_frS (k := 5) (l := 2) (by norm_num) (by norm_num) (by norm_num))]
  cases e2
  · rw [yb_false, c.s3_w]
    rfl
  · simp only [↓reduceIte]
    rw [yb_true]
    have h := c.s_y 2 (by norm_num) c.w
    simp only [show 2 * 2 = 4 from rfl, show 4 + 1 = 5 from rfl] at h
    rw [h, c.s3_w, c.yy4, yb_mul, yb_mul]
    rfl

theorem p_w
    {p : ℕ} (σ : ℕ → ℕ)
    (hrel : ∀ k ∈ [1, 3, 5], frS p * frS k = frS (σ k) * frS p)
    (hsurj : ∀ k ∈ [1, 3, 5], ∃ j ∈ [1, 3, 5], σ j = k) : c.mA (frS p) c.w = c.w := by
  have hfix : ∀ k ∈ [1, 3, 5], c.mA (frS k) c.w = c.w := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact c.s1_w
    · exact c.s2_w
    · exact c.s3_w
  have hmem : c.mA (frS p) c.w ∈ c.C123 := by
    have key : ∀ k ∈ [1, 3, 5], c.mA (frS k) (c.mA (frS p) c.w) = c.mA (frS p) c.w := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := hsurj k hk
      rw [← c.mA_conj_of (hrel j hj), hfix j hj]
    exact ⟨⟨⟨Subgroup.mem_top _, key 1 (by simp)⟩, key 3 (by simp)⟩, key 5 (by simp)⟩
  rcases c.eq_w_of_mem hmem with h | h
  · exact absurd (c.mA_injective _ (h.trans (map_one _).symm)) c.w_ne_one
  · exact h

theorem p12_w :
    c.mA (frS 6) c.w = c.w :=
  c.p_w sw12 (fun k hk => p12_rel k (by simp at hk; omega)) (by decide)

theorem p23_w :
    c.mA (frS 7) c.w = c.w :=
  c.p_w sw23 (fun k hk => p23_rel k (by simp at hk; omega)) (by decide)

theorem p12_vv
    (e0 e1 e2 : Bool) : c.mA (frS 6) (c.vv e0 e1 e2) = c.vv e1 e0 e2 := by
  rw [vv, c.yb_conj (p12_rel 0 (by norm_num)), c.yb_conj (p12_rel 2 (by norm_num)),
    c.yb_conj (p12_rel 4 (by norm_num)), c.p12_w]
  exact c.yb_comm 2 0 (by norm_num) (by norm_num) (by norm_num) e0 e1 _

theorem p23_vv
    (e0 e1 e2 : Bool) : c.mA (frS 7) (c.vv e0 e1 e2) = c.vv e0 e2 e1 := by
  rw [vv, c.yb_conj (p23_rel 0 (by norm_num)), c.yb_conj (p23_rel 2 (by norm_num)),
    c.yb_conj (p23_rel 4 (by norm_num)), c.p23_w]
  exact congrArg (c.yb 0 e0) (c.yb_comm 4 2 (by norm_num) (by norm_num) (by norm_num) e1 e2 _)

theorem rep_of_vv
    (k : ℕ) (f : Bool → Bool → Bool → Fin 8 → ZMod 2)
    (hf : ∀ e0 e1 e2, c.mA (frS k) (c.vv e0 e1 e2) = c.β (f e0 e1 e2))
    (hstd : ∀ e0 e1 e2 : Bool, ∀ b : Fin 8, stdMat k b (vcode e0 e1 e2) = f e0 e1 e2 b) :
    c.Rep (c.mA (frS k)) (stdMat k) := by
  refine c.rep_of_cols _ _ fun a => ?_
  rw [← vcode_bits a, c.v_vcode, hf]
  congr 1
  funext b
  rw [hstd]

theorem β_ite
    (p : Prop) [Decidable p] (u u' : Fin 8 → ZMod 2) :
    c.β (if p then u else u') = if p then c.β u else c.β u' := by
  split_ifs <;> rfl

theorem rep_std
    (k : ℕ) (hk : k < 8) : c.Rep (c.mA (frS k)) (stdMat k) := by
  interval_cases k
  · refine c.rep_of_vv 0 _ (fun e0 e1 e2 => ?_) std_y1
    rw [c.y1_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 1 _ (fun e0 e1 e2 => ?_) std_s1
    rw [c.s1_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 2 _ (fun e0 e1 e2 => ?_) std_y2
    rw [c.y2_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 3 _ (fun e0 e1 e2 => ?_) std_s2
    rw [c.s2_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 4 _ (fun e0 e1 e2 => ?_) std_y3
    rw [c.y3_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 5 _ (fun e0 e1 e2 => ?_) std_s3
    rw [c.s3_vv, c.β_ite, c.β_sv_add, c.β_sv, c.v_vcode, c.v_vcode]
  · refine c.rep_of_vv 6 _ (fun e0 e1 e2 => ?_) std_p12
    rw [c.p12_vv, c.β_sv, c.v_vcode]
  · refine c.rep_of_vv 7 _ (fun e0 e1 e2 => ?_) std_p23
    rw [c.p23_vv, c.β_sv, c.v_vcode]

end LocalConfig

end CFSG.Sporadic.Co2Smith
