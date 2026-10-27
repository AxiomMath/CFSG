module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoACore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev ggQ2_DW_LEc (n : ℕ) : Type :=
  @LinearEquiv (ZMod 3) (ZMod 3) _ _ (RingHom.id _) (RingHom.id _) _ _ (GGBCV n) (GGBCV n)
    (AddCommGroup.toAddCommMonoid) (AddCommGroup.toAddCommMonoid)
    (ggBCModule n) (ggBCModule n)

abbrev ggQ2_DW_Dualc (n : ℕ) : Type :=
  @Module.Dual (ZMod 3) (GGBCV n) _ _ (ggBCModule n)

lemma ggQ2_DW_sq (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 := by
  have h : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
  exact h a ha

lemma ggQ2_DW_two_div (a : ZMod 3) (ha : a ≠ 0) : 2 / a = -a := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (ggQ2_DW_sq a ha), h2]
  exact neg_one_mul a

lemma ggQ2_DW_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  have h : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = -1 := by decide
  exact h a ha

lemma ggQ2_DW_dot_apply {n : ℕ} (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp [ggBCDot, dotProduct, LinearMap.sum_apply]

lemma ggQ2_DW_dot_apply_c {n : ℕ} (c v : GGBCV n) :
    (ggBCDot c : ggQ2_DW_Dualc n) v = c ⬝ᵥ v := by
  change ggBCDot c v = c ⬝ᵥ v
  exact ggQ2_DW_dot_apply c v

@[expose] noncomputable def ggQ2_DW_reflc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) : ggQ2_DW_LEc n :=
  let f : ggQ2_DW_Dualc n :=
    (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2_DW_Dualc n)
  @Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup (ggBCModule n)
    c f (by
      change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) c) = 2
      rw [ggQ2_DW_dot_apply_c]
      field_simp)

lemma ggQ2_DW_reflc_eq {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    (ggBCRefl c hc).toFun = (ggQ2_DW_reflc c hc).toFun := rfl

lemma ggQ2_DW_reflection_apply {n : ℕ} (c : GGBCV n) (f : ggQ2_DW_Dualc n) (hf : f c = 2)
    (v : GGBCV n) :
    (@Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
      (ggBCModule n) c f hf).toFun v = v - f v • c :=
  @Module.reflection_apply (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
    (ggBCModule n) (x := c) (f := f) v hf

lemma ggQ2_DW_reflc_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    (ggQ2_DW_reflc c hc).toFun v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  let f : ggQ2_DW_Dualc n := (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2_DW_Dualc n)
  have hf : f c = 2 := by
    change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) c) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  change (@Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
    (ggBCModule n) c f hf).toFun v = _
  rw [ggQ2_DW_reflection_apply]
  change v - ((2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) v)) • c = _
  rw [ggQ2_DW_dot_apply_c]
  rw [ggQ2_DW_two_div (c ⬝ᵥ c) hc]
  rw [show (-(c ⬝ᵥ c) * (c ⬝ᵥ v)) = -((c ⬝ᵥ v) * (c ⬝ᵥ c)) by
    rw [mul_comm (c ⬝ᵥ v) (c ⬝ᵥ c)]
    exact neg_mul (c ⬝ᵥ c) (c ⬝ᵥ v)]
  rw [sub_eq_add_neg]
  congr 1
  exact (congrArg Neg.neg (neg_smul (c ⬝ᵥ v * c ⬝ᵥ c) c)).trans
    (neg_neg ((c ⬝ᵥ v * c ⬝ᵥ c) • c))

lemma ggQ2_DW_bc_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    (ggBCRefl c hc).toFun v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  rw [ggQ2_DW_reflc_eq]
  exact ggQ2_DW_reflc_apply c hc v

lemma ggQ2_DW_bc_apply' {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  change (ggBCRefl c hc).toFun v = _
  exact ggQ2_DW_bc_apply c hc v

lemma ggQ2_DW_A_dot_self_eq_wt {n : ℕ} (v : GGBCV n) :
    v ⬝ᵥ v = (ggBCWt v : ZMod 3) := by
  have h : ∀ i, v i * v i = if v i ≠ 0 then (1 : ZMod 3) else 0 := by
    intro i
    by_cases hi : v i = 0
    · simp [hi]
    · simp [hi, ggQ2_DW_sq (v i) hi]
  rw [dotProduct, ggBCWt]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [← Finset.sum_filter]
  simp

lemma ggQ2_DW_sum_nat_indicator (p m : ℕ) (k : ℕ) (hk : k < m)
    (c : ZMod p) (g : Fin m → ZMod p) :
    ∑ l : Fin m, (if (l:ℕ) = k then c else 0) * g l = c * g ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    have hb' : (b:ℕ) ≠ k := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ggQ2_DW_sum_ggDSimple (p m : ℕ) (i : Fin m) (hi : (i:ℕ)+1 < m)
    (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l = g i - g ⟨(i:ℕ)+1, hi⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) +
      (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_pos hi]
    by_cases h1 : (l:ℕ) = (i:ℕ)
    · have h2 : ¬ (l:ℕ) = (i:ℕ)+1 := by omega
      simp [h1, h2]
    · by_cases h2 : (l:ℕ) = (i:ℕ)+1
      · simp [h1, h2]
      · simp [h1, h2]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) * g l +
              (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl; intro l _; rw [hpoint l]; ring
    _ = (∑ l : Fin m, (if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g i + (-1) * g ⟨(i:ℕ)+1, hi⟩ := by
          rw [ggQ2_DW_sum_nat_indicator (k := (i:ℕ)) (hk := i.isLt),
            ggQ2_DW_sum_nat_indicator (k := (i:ℕ)+1) (hk := hi)]
    _ = g i - g ⟨(i:ℕ)+1, hi⟩ := by ring

lemma ggQ2_DW_sum_ggDSimple_fork (p m : ℕ) (hm : 2 ≤ m) (i : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l = g ⟨m-2, by omega⟩ + g ⟨m-1, by omega⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l:ℕ) = m-2 then (1:ZMod p) else 0) +
      (if (l:ℕ) = m-1 then (1:ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_neg hi]
    by_cases h2 : (l:ℕ)+2 = m
    · have h : (l:ℕ) = m - 2 := by omega
      rw [if_pos (Or.inl h2), h]
      have hlt : ¬ (m - 2 : ℕ) = m - 1 := by omega
      simp [hlt]
    · by_cases h1 : (l:ℕ)+1 = m
      · have h : (l:ℕ) = m - 1 := by omega
        rw [if_pos (Or.inr h1), h]
        have hlt : ¬ (m - 1 : ℕ) = m - 2 := by omega
        simp [hlt]
      · have hc : ¬ ((l:ℕ)+2 = m ∨ (l:ℕ)+1 = m) := by omega
        rw [if_neg hc]
        have hlt2 : ¬ (l:ℕ) = m - 2 := by omega
        have hlt1 : ¬ (l:ℕ) = m - 1 := by omega
        simp [hlt2, hlt1]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l:ℕ) = m-2 then (1:ZMod p) else 0) * g l +
              (if (l:ℕ) = m-1 then (1:ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl; intro l _; rw [hpoint l]; ring
    _ = (∑ l : Fin m, (if (l:ℕ) = m-2 then (1:ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l:ℕ) = m-1 then (1:ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g ⟨m-2, by omega⟩ + 1 * g ⟨m-1, by omega⟩ := by
          rw [ggQ2_DW_sum_nat_indicator (k := m-2) (hk := by omega),
            ggQ2_DW_sum_nat_indicator (k := m-1) (hk := by omega)]
    _ = g ⟨m-2, by omega⟩ + g ⟨m-1, by omega⟩ := by ring

lemma ggQ2_DW_eval_chain (p m : ℕ) (j : Fin m) (hj : (j:ℕ)+1 < m) (l : Fin m) :
    ggDSimple p m j l =
      (if (l:ℕ) = (j:ℕ) then (1:ZMod p) else 0) +
      (if (l:ℕ) = (j:ℕ)+1 then (-1:ZMod p) else 0) := by
  rw [ggDSimple, if_pos hj]
  by_cases h1 : (l:ℕ) = (j:ℕ)
  · have h2 : ¬ (l:ℕ) = (j:ℕ)+1 := by omega
    simp [h1, h2]
  · by_cases h2 : (l:ℕ) = (j:ℕ)+1
    · simp [h1, h2]
    · simp [h1, h2]

lemma ggQ2_DW_eval_fork (p m : ℕ) (j : Fin m) (hj : ¬ (j:ℕ)+1 < m) (l : Fin m) :
    ggDSimple p m j l =
      (if (l:ℕ)+2 = m ∨ (l:ℕ)+1 = m then (1:ZMod p) else 0) := by
  rw [ggDSimple, if_neg hj]

private lemma ggQ2xDWR_D_cc (m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : (j:ℕ)+1 < m) :
    CartanMatrix.D m i j =
      (if (i:ℕ) = (j:ℕ) then 2 else if (j:ℕ) = (i:ℕ)+1 then -1
       else if (i:ℕ) = (j:ℕ)+1 then -1 else 0) := by
  rw [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xDWR_D_cf (m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    CartanMatrix.D m i j =
      (if (i:ℕ) = m-2 then 0 else if (i:ℕ)+3 = m then -1 else 0) := by
  rw [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xDWR_D_ff (m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    CartanMatrix.D m i j = 2 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2xDWR_D_comm (m : ℕ) (i j : Fin m) :
    CartanMatrix.D m i j = CartanMatrix.D m j i :=
  congrFun (congrFun (CartanMatrix.D_transpose m).symm i) j

lemma ggQ2_DW_dot_cc (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  rw [ggQ2_DW_sum_ggDSimple p m i hi]
  rw [ggQ2_DW_eval_chain p m j hj i, ggQ2_DW_eval_chain p m j hj ⟨(i:ℕ)+1, hi⟩]
  rw [ggQ2xDWR_D_cc m hm i j hi hj]
  simp only [Fin.val_mk]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

lemma ggQ2_DW_dot_cf (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  rw [ggQ2_DW_sum_ggDSimple p m i hi]
  rw [ggQ2_DW_eval_fork p m j hj i, ggQ2_DW_eval_fork p m j hj ⟨(i:ℕ)+1, hi⟩]
  rw [ggQ2xDWR_D_cf m hm i j hi hj]
  simp only [Fin.val_mk]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

lemma ggQ2_DW_dot_fc (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (hj : (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  have hsum : (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (∑ l : Fin m, ggDSimple p m j l * ggDSimple p m i l) :=
    Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  rw [hsum, ggQ2_DW_dot_cf p m hm j i hj hi]
  rw [ggQ2xDWR_D_comm m i j]

lemma ggQ2_DW_dot_ff (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  rw [ggQ2_DW_sum_ggDSimple_fork p m (by omega) i hi]
  rw [ggQ2_DW_eval_fork p m j hj ⟨m-2, by omega⟩, ggQ2_DW_eval_fork p m j hj ⟨m-1, by omega⟩]
  rw [ggQ2xDWR_D_ff m hm i j hi hj]
  simp only [Fin.val_mk]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

lemma ggQ2_DW_simple_dot (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    ∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l =
      (CartanMatrix.D m i j : ZMod p) := by
  by_cases hi : (i:ℕ)+1 < m
  · by_cases hj : (j:ℕ)+1 < m
    · exact ggQ2_DW_dot_cc p m hm i j hi hj
    · exact ggQ2_DW_dot_cf p m hm i j hi hj
  · by_cases hj : (j:ℕ)+1 < m
    · exact ggQ2_DW_dot_fc p m hm i j hi hj
    · exact ggQ2_DW_dot_ff p m hm i j hi hj

@[expose] noncomputable def ggQ2_DW_fvec (p m : ℕ) (k : Fin m) : Fin m → ZMod p :=
  Pi.single k 1

@[expose] noncomputable def ggQ2_DW_dotLin (p m : ℕ) (u : Fin m → ZMod p) :
    (Fin m → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun v := ∑ j, u j * v j
  map_add' a b := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by simp only [RingHom.id_apply]; ring)

lemma ggQ2_DW_dotLin_apply (p m : ℕ) (u v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m u v = ∑ j, u j * v j := rfl

lemma ggQ2_DW_u_self (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    ggQ2_DW_dotLin p m (ggDSimple p m i) (ggDSimple p m i) = 2 := by
  rw [ggQ2_DW_dotLin_apply, ggQ2_DW_simple_dot p m hm i i]
  simp

@[expose] noncomputable def ggQ2_DW_r (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) :=
  Module.reflection (x := ggDSimple p m i) (ggQ2_DW_u_self p m hm i)

lemma ggQ2_DW_r_apply (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) (v : Fin m → ZMod p) :
    ggQ2_DW_r p m hm i v = v - (ggQ2_DW_dotLin p m (ggDSimple p m i) v) • ggDSimple p m i :=
  Module.reflection_apply v (ggQ2_DW_u_self p m hm i)

@[expose] noncomputable def ggQ2_DW_Q (p m : ℕ) :
    Equiv.Perm (Fin m) →* ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) where
  toFun σ := LinearEquiv.funCongrLeft (ZMod p) (ZMod p) σ.symm
  map_one' := by ext v j; rfl
  map_mul' σ τ := by ext v j; rfl

lemma ggQ2_DW_Q_apply (p m : ℕ) (σ : Equiv.Perm (Fin m)) (v : Fin m → ZMod p)
    (j : Fin m) : ggQ2_DW_Q p m σ v j = v (σ.symm j) := rfl

lemma ggQ2_DW_r_eq_swap (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) (hi : (i:ℕ)+1 < m) :
    ggQ2_DW_r p m hm i = ggQ2_DW_Q p m (Equiv.swap i ⟨(i:ℕ)+1, hi⟩) := by
  ext v j
  rw [ggQ2_DW_r_apply, ggQ2_DW_Q_apply, ggQ2_DW_dotLin_apply,
    ggQ2_DW_sum_ggDSimple p m i hi]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ggQ2_DW_eval_chain p m i hi]
  by_cases h1 : (j:ℕ) = (i:ℕ)
  · have hj : j = i := Fin.ext h1
    subst j
    have hne : ¬ (i:ℕ) = (i:ℕ)+1 := by omega
    rw [if_pos rfl, if_neg hne]
    rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm i = ⟨(i:ℕ)+1, hi⟩ from by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]]
    simp
  · by_cases h2 : (j:ℕ) = (i:ℕ)+1
    · have hj : j = ⟨(i:ℕ)+1, hi⟩ := Fin.ext h2
      subst j
      have hne : ¬ (i:ℕ)+1 = (i:ℕ) := by omega
      have hne2 : ¬ (i:ℕ)+1 = (i:ℕ)+1+1 := by omega
      rw [if_neg (by omega : ¬ ((⟨(i:ℕ)+1, hi⟩ : Fin m).val = (i:ℕ))),
        if_pos rfl]
      rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm ⟨(i:ℕ)+1, hi⟩ = i from by
        rw [Equiv.symm_swap, Equiv.swap_apply_right]]
      simp
    · rw [if_neg (by exact fun h => h1 h), if_neg (by exact fun h => h2 h)]
      rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm j = j from by
        rw [Equiv.symm_swap]
        exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
      simp

@[expose] noncomputable def ggQ2_DW_Wc (p m : ℕ) (hm : 4 ≤ m) :
    Subgroup ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) :=
  Subgroup.closure (Set.range (ggQ2_DW_r p m hm))

lemma ggQ2_DW_Q_mem_Wc (p m : ℕ) (hm : 4 ≤ m) (σ : Equiv.Perm (Fin m)) :
    ggQ2_DW_Q p m σ ∈ ggQ2_DW_Wc p m hm := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hle : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤
      (ggQ2_DW_Wc p (n+1) hm).comap (ggQ2_DW_Q p (n+1)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hi : (i.castSucc : Fin (n+1)).val + 1 < n + 1 := by
      simp only [Fin.val_castSucc]; omega
    change ggQ2_DW_Q p (n+1) (Equiv.swap i.castSucc i.succ) ∈ ggQ2_DW_Wc p (n+1) hm
    have hidx : i.succ = (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (n+1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc]
    rw [hidx, ← ggQ2_DW_r_eq_swap p (n+1) hm i.castSucc hi]
    exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
  have htop : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  have hσ : σ ∈ Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
    rw [htop]; exact Subgroup.mem_top σ
  exact hle hσ

lemma ggQ2_DW_dotLin_fvec_left (p m : ℕ) (a : Fin m) (v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a) v = v a := by
  rw [ggQ2_DW_dotLin_apply, Finset.sum_eq_single a]
  · simp [ggQ2_DW_fvec]
  · intro b _ hb; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ a) h

lemma ggQ2_DW_dotLin_sub_left (p m : ℕ) (u w v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (u - w) v = ggQ2_DW_dotLin p m u v - ggQ2_DW_dotLin p m w v := by
  simp only [ggQ2_DW_dotLin_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun l _ => by simp only [Pi.sub_apply]; ring)

lemma ggQ2_DW_dotLin_fvec_sub (p m : ℕ) (a b : Fin m) (v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a - ggQ2_DW_fvec p m b) v = v a - v b := by
  rw [ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

lemma ggQ2_DW_Q_fvec (p m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ggQ2_DW_Q p m σ (ggQ2_DW_fvec p m k) = ggQ2_DW_fvec p m (σ k) := by
  funext j
  rw [ggQ2_DW_Q_apply, ggQ2_DW_fvec, ggQ2_DW_fvec]
  by_cases h : j = σ k
  · subst h; simp
  · have h' : σ.symm j ≠ k := by
      intro hh; apply h; rw [← hh]; simp
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

lemma ggQ2_DW_Q_isom (p m : ℕ) (σ : Equiv.Perm (Fin m)) (u v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (ggQ2_DW_Q p m σ u) (ggQ2_DW_Q p m σ v) = ggQ2_DW_dotLin p m u v := by
  simp only [ggQ2_DW_dotLin_apply, ggQ2_DW_Q_apply]
  exact Equiv.sum_comp σ.symm (fun j => u j * v j)

lemma ggQ2_DW_Wt_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ggBCWt ((Pi.single a (1 : ZMod 3) : GGBCV n) - Pi.single b 1) = 2 := by
  unfold ggBCWt
  rw [Finset.card_eq_two]
  refine ⟨a, b, hab, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hja : j = a
  · subst hja
    simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), hab] <;>
      decide +kernel
  · by_cases hjb : j = b
    · subst hjb
      simp [Pi.sub_apply, Pi.single_eq_of_ne hab, Pi.single_eq_same, hab] <;>
        decide +kernel
    · simp [Pi.sub_apply, Pi.single_eq_of_ne hja, Pi.single_eq_of_ne hjb, hja, hjb]

lemma ggQ2_DW_Wt_add_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ggBCWt ((Pi.single a (1 : ZMod 3) : GGBCV n) + Pi.single b 1) = 2 := by
  unfold ggBCWt
  rw [Finset.card_eq_two]
  refine ⟨a, b, hab, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hja : j = a
  · subst hja
    simp [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), hab] <;>
      decide +kernel
  · by_cases hjb : j = b
    · subst hjb
      simp [Pi.add_apply, Pi.single_eq_of_ne hab, Pi.single_eq_same, hab] <;>
        decide +kernel
    · simp [Pi.add_apply, Pi.single_eq_of_ne hja, Pi.single_eq_of_ne hjb, hja, hjb]

lemma ggQ2_DW_sub_norm {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) = 2 := by
  rw [ggQ2_DW_A_dot_self_eq_wt, ggQ2_DW_Wt_sub_single i j hij]
  norm_num

lemma ggQ2_DW_add_norm {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) = 2 := by
  rw [ggQ2_DW_A_dot_self_eq_wt, ggQ2_DW_Wt_add_single i j hij]
  norm_num

lemma ggQ2_DW_refl_congr {n : ℕ} {c1 c2 : GGBCV n} (hv : c1 = c2)
    (h1 : c1 ⬝ᵥ c1 ≠ 0) (h2 : c2 ⬝ᵥ c2 ≠ 0) :
    ggBCRefl c1 h1 = ggBCRefl c2 h2 := by
  subst hv
  exact congrArg (ggBCRefl c1) (Subsingleton.elim h1 h2)

lemma ggQ2_DW_neg_mul_neg (x : ZMod 3) : -x * -x = x * x := by
  revert x; decide +kernel

lemma ggQ2_DW_scalar_a : ∀ x : ZMod 3, x * -1 = -x := by decide

lemma ggQ2_DW_scalar_c : ∀ a b x : ZMod 3, -a * b * -x = a * b * x := by decide

lemma ggQ2_DW_scalar_d : ∀ x y : ZMod 3, x + (x - y) * -1 * (1 - 0) = y := by decide

lemma ggQ2_DW_scalar_e : ∀ x y : ZMod 3, y + (x - y) * -1 * (0 - 1) = x := by decide

lemma ggQ2_DW_scalar_f : ∀ x y : ZMod 3, x + -1 * y = x - y := by decide

lemma ggQ2_DW_scalar_g : ∀ x y : ZMod 3, -1 * x + y = -(x - y) := by decide

lemma ggQ2_DW_scalar_h : ∀ x y : ZMod 3, -1 * x + -1 * y = -(x + y) := by decide

lemma ggQ2_DW_neg_dot_self {n : ℕ} (c : GGBCV n) : (-c) ⬝ᵥ (-c) = c ⬝ᵥ c := by
  simp only [dotProduct, Pi.neg_apply]
  exact Finset.sum_congr rfl (fun i _ => ggQ2_DW_neg_mul_neg (c i))

lemma ggQ2_DW_neg_dot {n : ℕ} (c v : GGBCV n) : (-c) ⬝ᵥ v = -(c ⬝ᵥ v) := by
  simp only [dotProduct, Pi.neg_apply]
  rw [Finset.sum_congr rfl
    (fun i _ => (by decide +kernel : ∀ a b : ZMod 3, -a * b = -(a * b)) (c i) (v i))]
  exact Finset.sum_neg_distrib (s := Finset.univ) (f := fun i : Fin n => c i * v i)

lemma ggQ2_DW_refl_neg {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (hc' : (-c) ⬝ᵥ (-c) ≠ 0) :
    ggBCRefl (-c) hc' = ggBCRefl c hc := by
  ext v k
  rw [ggQ2_DW_bc_apply', ggQ2_DW_bc_apply', ggQ2_DW_neg_dot_self, ggQ2_DW_neg_dot]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  congr 1
  exact ggQ2_DW_scalar_c (c ⬝ᵥ v) (c ⬝ᵥ c) (c k)

lemma ggQ2_DW_bc_conj {m : ℕ} (P : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (hP : ∀ u v, P u ⬝ᵥ P v = u ⬝ᵥ v) (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) :
    P * ggBCRefl c hc * P.symm =
      ggBCRefl (P c) (by rw [hP c c]; exact hc) := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2_DW_bc_apply', map_add, map_smul,
    LinearEquiv.apply_symm_apply, ggQ2_DW_bc_apply']
  have hcv : c ⬝ᵥ P.symm v = (P c) ⬝ᵥ v := by
    have := hP c (P.symm v)
    simpa using this.symm
  have hcc : (P c) ⬝ᵥ (P c) = c ⬝ᵥ c := hP c c
  rw [hcv, hcc]

lemma ggQ2_DW_simple_norm {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    ggDSimple 3 m i ⬝ᵥ ggDSimple 3 m i = 2 := by
  rw [show ggDSimple 3 m i ⬝ᵥ ggDSimple 3 m i =
    ∑ l, ggDSimple 3 m i l * ggDSimple 3 m i l from rfl,
    ggQ2_DW_simple_dot 3 m hm i i]
  simp

lemma ggQ2_DW_r_eq_bc {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    ggQ2_DW_r 3 m hm i =
      ggBCRefl (ggDSimple 3 m i) (by rw [ggQ2_DW_simple_norm hm i]; decide) := by
  apply LinearEquiv.ext
  intro v
  rw [ggQ2_DW_r_apply, ggQ2_DW_bc_apply', ggQ2_DW_simple_norm hm i]
  have hcoef : ((ggDSimple 3 m i) ⬝ᵥ v) * (2 : ZMod 3) = -(ggDSimple 3 m i ⬝ᵥ v) := by
    rw [show (2 : ZMod 3) = -1 by decide]; exact ggQ2_DW_scalar_a _
  rw [hcoef, sub_eq_add_neg]
  congr 1
  change -((ggDSimple 3 m i ⬝ᵥ v) • ggDSimple 3 m i) =
    (-(ggDSimple 3 m i ⬝ᵥ v)) • ggDSimple 3 m i
  exact (neg_smul _ _).symm

lemma ggQ2_DW_sub_refl_eq_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (hc : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0) :
    ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) hc =
      ggQ2_DW_Q 3 m (Equiv.swap i j) := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [ggQ2_DW_Q_apply, ggQ2_DW_bc_apply']
  have hcc : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) = 2 :=
    ggQ2_DW_sub_norm i j hij
  have hdot : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ v = v i - v j := by
    change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j) v = v i - v j
    exact ggQ2_DW_dotLin_fvec_sub 3 m i j v
  rw [hcc, hdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.single_apply, Pi.single_apply, Equiv.symm_swap]
  by_cases hki : k = i
  · rw [if_pos hki, if_neg (by rw [hki]; exact hij), hki, Equiv.swap_apply_left]
    rw [show (2 : ZMod 3) = -1 by decide]
    exact ggQ2_DW_scalar_d (v i) (v j)
  · by_cases hkj : k = j
    · rw [if_neg hki, if_pos hkj, hkj, Equiv.swap_apply_right]
      rw [show (2 : ZMod 3) = -1 by decide]
      exact ggQ2_DW_scalar_e (v i) (v j)
    · rw [if_neg hki, if_neg hkj, sub_self, Equiv.swap_apply_def, if_neg hki, if_neg hkj]
      rw [show (2 : ZMod 3) = -1 by decide, mul_zero, add_zero]

lemma ggQ2_DW_Q_add_fvec {p m : ℕ} (σ : Equiv.Perm (Fin m)) (a b : Fin m) :
    ggQ2_DW_Q p m σ (ggQ2_DW_fvec p m a + ggQ2_DW_fvec p m b) =
      ggQ2_DW_fvec p m (σ a) + ggQ2_DW_fvec p m (σ b) := by
  rw [map_add, ggQ2_DW_Q_fvec, ggQ2_DW_Q_fvec]

lemma ggQ2_DW_exists_perm_pair {m : ℕ} (hm : 4 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin m),
      ggQ2_DW_Q 3 m τ
        ((Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
          Pi.single ⟨m - 1, by omega⟩ 1) =
        (Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1 := by
  have hab : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  by_cases hja : j = ⟨m - 2, by omega⟩
  · refine ⟨Equiv.swap ⟨m - 1, by omega⟩ i, ?_⟩
    have hia : i ≠ ⟨m - 2, by omega⟩ := by
      intro h; exact hij (h.trans hja.symm)
    have hτa : Equiv.swap ⟨m - 1, by omega⟩ i (⟨m - 2, by omega⟩ : Fin m) =
        ⟨m - 2, by omega⟩ := by
      rw [Equiv.swap_apply_def, if_neg hab, if_neg (fun h => hia h.symm)]
    have hτb : Equiv.swap ⟨m - 1, by omega⟩ i (⟨m - 1, by omega⟩ : Fin m) = i :=
      Equiv.swap_apply_left _ _
    change ggQ2_DW_Q 3 m (Equiv.swap ⟨m - 1, by omega⟩ i)
      (ggQ2_DW_fvec 3 m ⟨m - 2, by omega⟩ + ggQ2_DW_fvec 3 m ⟨m - 1, by omega⟩) = _
    rw [ggQ2_DW_Q_add_fvec, hτa, hτb, hja]
    exact add_comm _ _
  · refine ⟨Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j, ?_⟩
    have hτa : (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
        (⟨m - 2, by omega⟩ : Fin m) = i := by
      rw [Equiv.Perm.mul_apply]
      have h1 : (Equiv.swap ⟨m - 1, by omega⟩ j) (⟨m - 2, by omega⟩ : Fin m) =
          ⟨m - 2, by omega⟩ := by
        rw [Equiv.swap_apply_def, if_neg hab, if_neg (fun h => hja h.symm)]
      rw [h1, Equiv.swap_apply_left]
    have hτb : (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
        (⟨m - 1, by omega⟩ : Fin m) = j := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_def,
        if_neg hja, if_neg (fun h => hij h.symm)]
    change ggQ2_DW_Q 3 m (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
      (ggQ2_DW_fvec 3 m ⟨m - 2, by omega⟩ + ggQ2_DW_fvec 3 m ⟨m - 1, by omega⟩) = _
    rw [ggQ2_DW_Q_add_fvec, hτa, hτb]
    rfl

lemma ggQ2_DW_weight_two {m : ℕ} {v : GGBCV m} (hv : ggBCWt v = 2) :
    ∃ (i j : Fin m) (a b : ZMod 3), i ≠ j ∧ a ≠ 0 ∧ b ≠ 0 ∧
      v = a • (Pi.single i 1 : GGBCV m) + b • (Pi.single j 1 : GGBCV m) := by
  unfold ggBCWt at hv
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hv
  have hvi : v i ≠ 0 := by
    have hmem : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  have hvj : v j ≠ 0 := by
    have hmem : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  refine ⟨i, j, v i, v j, hij, hvi, hvj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, smul_eq_mul, mul_one, mul_zero, add_zero]
  · by_cases hkj : k = j
    · subst hkj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), smul_eq_mul, mul_one,
        mul_zero, zero_add]
    · have hvk : v k = 0 := by
        by_contra hne
        have hmem : k ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hne]
        rw [hS] at hmem
        simp [hki, hkj] at hmem
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, smul_zero, smul_zero, add_zero]
      exact hvk

lemma ggQ2_DW_add_refl_mem_Wc (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) (hij : i ≠ j)
    (hc : ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ≠ 0) :
    ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hc ∈
      ggQ2_DW_Wc 3 m hm := by
  obtain ⟨τ, hτ⟩ := ggQ2_DW_exists_perm_pair hm i j hij
  let a : Fin m := ⟨m - 2, by omega⟩
  let b : Fin m := ⟨m - 1, by omega⟩
  have hab : a ≠ b := by
    intro h; have := congrArg Fin.val h; simp only [a, b, Fin.val_mk] at this; omega
  have hcA : ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ≠ 0 := by
    rw [ggQ2_DW_add_norm a b hab]; decide
  have hrb : ggQ2_DW_r 3 m hm b =
      ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hcA := by
    rw [ggQ2_DW_r_eq_bc hm b]
    refine ggQ2_DW_refl_congr ?_ _ _
    funext k
    have hb : ¬ ((b : ℕ) + 1 < m) := by simp only [b, Fin.val_mk]; omega
    simp only [ggDSimple, hb, if_false, Pi.add_apply, Pi.single_apply]
    by_cases hka : k = a
    · subst hka
      rw [if_pos (Or.inl (by simp only [a, Fin.val_mk]; omega)), if_pos rfl,
        if_neg (fun h => hab h), add_zero]
    · by_cases hkb : k = b
      · subst hkb
        rw [if_pos (Or.inr (by simp only [b, Fin.val_mk]; omega)),
          if_neg (fun h => hab h.symm), if_pos rfl, zero_add]
      · have h1 : ¬ (k : ℕ) + 2 = m := by
          intro h; exact hka (Fin.ext (by simp only [a, Fin.val_mk]; omega))
        have h2 : ¬ (k : ℕ) + 1 = m := by
          intro h; exact hkb (Fin.ext (by simp only [b, Fin.val_mk]; omega))
        rw [if_neg (by rintro (h | h); exact h1 h; exact h2 h), if_neg hka, if_neg hkb,
          add_zero]
  have hQ : ggQ2_DW_Q 3 m τ ∈ ggQ2_DW_Wc 3 m hm := ggQ2_DW_Q_mem_Wc 3 m hm τ
  have hmem : ggQ2_DW_Q 3 m τ * ggQ2_DW_r 3 m hm b * (ggQ2_DW_Q 3 m τ).symm ∈
      ggQ2_DW_Wc 3 m hm :=
    (ggQ2_DW_Wc 3 m hm).mul_mem
      ((ggQ2_DW_Wc 3 m hm).mul_mem hQ (Subgroup.subset_closure ⟨b, rfl⟩))
      ((ggQ2_DW_Wc 3 m hm).inv_mem hQ)
  have hconj := ggQ2_DW_bc_conj (ggQ2_DW_Q 3 m τ) (ggQ2_DW_Q_isom 3 m τ)
    ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hcA
  have heq : ggBCRefl (ggQ2_DW_Q 3 m τ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1))
        (by
          change ggQ2_DW_dotLin 3 m
            (ggQ2_DW_Q 3 m τ ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1))
            (ggQ2_DW_Q 3 m τ ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)) ≠ 0
          rw [ggQ2_DW_Q_isom 3 m τ
            ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)
            ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)]
          exact hcA) =
      ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hc :=
    ggQ2_DW_refl_congr hτ _ hc
  rw [← heq, ← hconj, ← hrb]
  exact hmem

lemma ggQ2_DW_Droot_refl_mem_Wc (m : ℕ) (hm : 4 ≤ m) {z : GGBCV m}
    (hz : z ∈ ggDRoots m) (hz0 : z ⬝ᵥ z ≠ 0) :
    ggBCRefl z hz0 ∈ ggQ2_DW_Wc 3 m hm := by
  obtain ⟨i, j, l, k, hij, hl, hk, hz_eq⟩ :=
    ggQ2_DW_weight_two (m := m) (by simpa [ggDRoots] using hz)
  have hli : l = 1 ∨ l = -1 := ggQ2_DW_eq_one_or_neg_one l hl
  have hki : k = 1 ∨ k = -1 := ggQ2_DW_eq_one_or_neg_one k hk
  rcases hli with rfl | rfl <;> rcases hki with rfl | rfl
  · have hz' : z = (Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1 := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [ggQ2_DW_refl_congr hz' hz0 (by rw [ggQ2_DW_add_norm i j hij]; decide)]
    exact ggQ2_DW_add_refl_mem_Wc m hm i j hij (by rw [ggQ2_DW_add_norm i j hij]; decide)
  · have hz' : z = (Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1 := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact ggQ2_DW_scalar_f _ _
    rw [ggQ2_DW_refl_congr hz' hz0 (by rw [ggQ2_DW_sub_norm i j hij]; decide),
      ggQ2_DW_sub_refl_eq_swap i j hij (by rw [ggQ2_DW_sub_norm i j hij]; decide)]
    exact ggQ2_DW_Q_mem_Wc 3 m hm (Equiv.swap i j)
  · have hz' : z = -((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        one_mul]
      exact ggQ2_DW_scalar_g _ _
    have hcsub : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
        ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0 := by
      rw [ggQ2_DW_sub_norm i j hij]; decide
    have hcneg : (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self, ggQ2_DW_sub_norm i j hij]; decide
    rw [ggQ2_DW_refl_congr hz' hz0 hcneg]
    rw [show ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) hcneg =
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) hcsub from
      ggQ2_DW_refl_neg ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) hcsub hcneg]
    rw [ggQ2_DW_sub_refl_eq_swap i j hij hcsub]
    exact ggQ2_DW_Q_mem_Wc 3 m hm (Equiv.swap i j)
  · have hz' : z = -((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact ggQ2_DW_scalar_h _ _
    have hcadd : ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ
        ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ≠ 0 := by
      rw [ggQ2_DW_add_norm i j hij]; decide
    have hcneg : (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self, ggQ2_DW_add_norm i j hij]; decide
    rw [ggQ2_DW_refl_congr hz' hz0 hcneg]
    rw [show ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) hcneg =
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hcadd from
      ggQ2_DW_refl_neg ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hcadd hcneg]
    exact ggQ2_DW_add_refl_mem_Wc m hm i j hij hcadd

theorem ggQ2_DW_cartan_D {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (e : Fin m ≃ D.ι) (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) (i j : Fin m) :
    D.cartan (e i) (e j) = CartanMatrix.D m i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1 (e i)]; simp
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = ggCoxeterMatrixD m i j := by
      rw [he, CoxeterMatrix.reindex_apply]; simp
    have hlabel : ggCoxeterMatrixD m i j = 2 ∨ ggCoxeterMatrixD m i j = 3 := by
      by_cases h : CartanMatrix.D m i j = 0
      · exact Or.inl (by rw [ggCoxeterMatrixD_apply]; simp [hij, h])
      · exact Or.inr (by rw [ggCoxeterMatrixD_apply]; simp [hij, h])
    rcases hlabel with h2 | h3
    · have hD0 : CartanMatrix.D m i j = 0 := by
        by_contra h0
        rw [ggCoxeterMatrixD_apply, if_neg hij] at h2
        simp [h0] at h2
      rw [hD0]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · have hDne : CartanMatrix.D m i j ≠ 0 := by
        intro h0; rw [ggCoxeterMatrixD_apply, if_neg hij, h0] at h3; simp at h3
      have hDneg : CartanMatrix.D m i j = -1 := by
        rcases (CartanMatrix.isSimplyLaced_D m) hij with h | h
        · exact absurd h hDne
        · exact h
      rw [hDneg]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

@[expose] noncomputable def ggQ2_DW_dotBilin (m : ℕ) : LinearMap.BilinForm (ZMod 3) (GGBCV m) :=
  Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) (ZMod 3))

lemma ggQ2_DW_dotBilin_apply {m : ℕ} (x y : GGBCV m) :
    ggQ2_DW_dotBilin m x y = x ⬝ᵥ y := by
  rw [ggQ2_DW_dotBilin, Matrix.toBilin'_apply]
  simp [Matrix.one_apply, dotProduct]

lemma ggQ2_DW_linConj_simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j)
    (i : Fin m) :
    ggLinConj τ (D.simpleRefl (e i)) = ggQ2_DW_r p m hm i := by
  apply LinearEquiv.ext
  intro y
  rw [ggLinConj_apply]
  change τ (D.simpleRefl (e i) (τ.symm y)) = ggQ2_DW_r p m hm i y
  rw [ggQ2_DW_r_apply, ggQ2_DW_dotLin_apply]
  have hsr : D.simpleRefl (e i) (τ.symm y) =
      τ.symm y - (D.root (e i) (τ.symm y)) • D.coroot (e i) := by
    rw [show D.simpleRefl (e i) = Module.reflection (D.root_coroot_self (e i)) from rfl,
      Module.reflection_apply]
  rw [hsr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hτ i, hroot i (τ.symm y),
    LinearEquiv.apply_symm_apply]

lemma ggQ2_DW_linWeylMap {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j) :
    (D.weyl).map (ggLinConj τ).toMonoidHom = ggQ2_DW_Wc p m hm := by
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, -, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    exact ⟨i, (ggQ2_DW_linConj_simpleRefl D hm e τ hτ hroot i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D.simpleRefl (e i), ⟨e i, Set.mem_univ _, rfl⟩,
      ggQ2_DW_linConj_simpleRefl D hm e τ hτ hroot i⟩

lemma ggQ2_DW_hB' (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 4 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i) :
    ∀ i j, ggQ2_DW_dotBilin m (τ (D.coroot i)) (τ (D.coroot j)) = (D.cartan i j : ZMod 3) := by
  intro i j
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  rw [hτ i', hτ j', ggQ2_DW_dotBilin_apply,
    show ggDSimple 3 m i' ⬝ᵥ ggDSimple 3 m j' =
      ∑ l, ggDSimple 3 m i' l * ggDSimple 3 m j' l from rfl,
    ggQ2_DW_simple_dot 3 m hm i' j', ggQ2_DW_cartan_D D e hD i' j']

lemma ggQ2_DW_Droots_le_map (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) :
    ggBCReflGp (ggDRoots m) ≤ A.map (ggLinConj τ).toMonoidHom := by
  have hm4 : 4 ≤ m := by omega
  show Subgroup.closure (ggBCReflSet (ggDRoots m)) ≤ A.map (ggLinConj τ).toMonoidHom
  rw [Subgroup.closure_le]
  rintro t ⟨c, hc, hcc, rfl⟩
  have hWc : ggBCRefl c hcc ∈ ggQ2_DW_Wc 3 m hm4 := ggQ2_DW_Droot_refl_mem_Wc m hm4 hc hcc
  rw [← ggQ2_DW_linWeylMap D hm4 e τ hτ hroot] at hWc
  exact Subgroup.map_mono hW hWc

end CFSG.StandardType

end
