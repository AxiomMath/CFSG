module

public import CFSG.RankThree.GF2n.Smith81.S81TP2
public import CFSG.RankThree.GF2n.Smith81.S81BNCore
public import CFSG.RankThree.GF2n.Smith81.S81E7Form

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section Quad

variable {K : Type} [Field K]

@[expose] def qf (v : V K) : K :=
  ∑ a : Fin e7Data.d, if a < opp a then v a * v (opp a) else 0

theorem qf_smul (c : K) (v : V K) : qf (c • v) = c ^ 2 * qf v := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a < opp a
  · simp only [if_pos ha, Finsupp.smul_apply, smul_eq_mul]
    ring
  · simp only [if_neg ha, mul_zero]

theorem beta_eq_sum (u v : V K) :
    beta u v = ∑ a : Fin e7Data.d, if a < opp a then u a * v (opp a) + u (opp a) * v a else 0 := by
  have split : ∑ a : Fin e7Data.d, u a * v (opp a) =
      ∑ a : Fin e7Data.d, (if a < opp a then u a * v (opp a) else 0) +
        ∑ a : Fin e7Data.d, (if a < opp a then (0 : K) else u a * v (opp a)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  have second : ∑ a : Fin e7Data.d, (if a < opp a then (0 : K) else u a * v (opp a)) =
      ∑ a : Fin e7Data.d, (if a < opp a then u (opp a) * v a else 0) := by
    refine Fintype.sum_equiv (Function.Involutive.toPerm opp opp_opp) _ _ fun a => ?_
    show (if a < opp a then (0 : K) else u a * v (opp a)) =
      (if opp a < opp (opp a) then u (opp (opp a)) * v (opp a) else 0)
    rw [opp_opp]
    by_cases h : a < opp a
    · rw [if_pos h, if_neg (lt_asymm h)]
    · rw [if_neg h, if_pos (lt_of_le_of_ne (not_lt.mp h) (opp_ne_self a))]
  unfold beta
  rw [split, second, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

theorem qf_add (u v : V K) : qf (u + v) = qf u + qf v + beta u v := by
  unfold qf
  rw [beta_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finsupp.add_apply]
  split_ifs <;> ring

theorem qf_eq_zero_of_support {v : V K} (h : ∀ a, v a = 0 ∨ v (opp a) = 0) : qf v = 0 := by
  unfold qf
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < opp a
  · rw [if_pos ha]
    rcases h a with h1 | h1
    · rw [h1, zero_mul]
    · rw [h1, mul_zero]
  · rw [if_neg ha]

theorem beta_single_left (a : Fin e7Data.d) (y : V K) :
    beta (Finsupp.single a 1) y = y (opp a) := by
  unfold beta
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [Finsupp.single_apply, hc, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem qf_single (a : Fin e7Data.d) : qf (Finsupp.single a (1 : K)) = 0 := by
  refine qf_eq_zero_of_support fun b => ?_
  by_cases hb : b = a
  · right
    have hob : opp b ≠ a := by
      intro h
      apply opp_ne_self a
      calc opp a = opp b := by rw [hb]
        _ = a := h
    simp [Finsupp.single_apply, hob, Ne.symm hob]
  · left
    simp [Finsupp.single_apply, hb, Ne.symm hb]

theorem opp_wt_eq {b₁ b₂ : Fin e7Data.d} (h : opp b₁ = b₂) :
    e7Data.wt b₁ + e7Data.wt b₂ = 0 := by
  have := wt_opp b₁
  rw [h] at this
  rw [this]
  abel

variable [CharP K 2]

theorem opp_shift_ne_self {δ : Rt} (hδ : IsRoot .E7 δ) {a : Fin e7Data.d} (h : pr a δ = -1) :
    opp (shift δ a) ≠ a := by
  have key : ∀ γ : Rt, IsRoot .E7 γ → ∀ b : Fin e7Data.d,
      e7Data.wt b + e7Data.wt b + MinData.toWeight γ ≠ 0 :=
    (forall_isRoot_iff fun γ => ∀ b : Fin e7Data.d,
      e7Data.wt b + e7Data.wt b + MinData.toWeight γ ≠ 0).2 (by decide +kernel)
  intro heq
  have h1 := wt_opp (shift δ a)
  rw [heq, wt_shift hδ h] at h1
  exact key δ hδ a (by rw [add_assoc]; exact eq_neg_iff_add_eq_zero.mp h1)

theorem qf_rootOp {δ : Rt} (hδ : IsRoot .E7 δ) (v : V K) : qf (e7Data.rootOp K δ v) = 0 := by
  refine qf_eq_zero_of_support fun a => ?_
  by_cases ha : pr a δ = 1
  · right
    have hA : ¬ pr (opp a) δ = 1 := by
      rw [pr_opp, ha] <;> norm_num
    rw [rootOp_apply hδ v (opp a), if_neg hA]
  · left
    rw [rootOp_apply hδ v a, if_neg ha]

theorem beta_rootOp_self {δ : Rt} (hδ : IsRoot .E7 δ) (v : V K) :
    beta v (e7Data.rootOp K δ v) = 0 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  unfold beta
  simp only [rootOp_apply hδ v]
  refine Finset.sum_involution (fun a _ => if pr a δ = -1 then opp (shift δ a) else a) ?_ ?_ ?_ ?_
  · intro a _
    by_cases h : pr a δ = -1
    · have hA : pr (opp a) δ = 1 := by rw [pr_opp, h] <;> norm_num
      have hB : shift (-δ) (opp a) = opp (shift δ a) := (opp_shift hδ h).symm
      have hC : pr (opp (opp (shift δ a))) δ = 1 := by rw [opp_opp, pr_shift_self hδ h]
      have hD : shift (-δ) (opp (opp (shift δ a))) = a := by rw [opp_opp, shift_neg_shift hδ h]
      rw [if_pos h, if_pos hA, if_pos hC, hB, hD]
      linear_combination (v a * v (opp (shift δ a))) * h2
    · have hA : ¬ pr (opp a) δ = 1 := by
        rw [pr_opp]
        intro hc
        apply h
        omega
      rw [if_neg h, if_neg hA]
      ring
  · intro a _ hfa
    by_cases h : pr a δ = -1
    · rw [if_pos h]
      exact opp_shift_ne_self hδ h
    · exfalso
      have hA : ¬ pr (opp a) δ = 1 := by
        rw [pr_opp]
        intro hc
        apply h
        omega
      apply hfa
      rw [if_neg hA, mul_zero]
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    by_cases h : pr a δ = -1
    · have ha' : pr (opp (shift δ a)) δ = -1 := by rw [pr_opp, pr_shift_self hδ h]
      rw [if_pos h, if_pos ha', opp_shift hδ ha', opp_opp, shift_neg_shift hδ h]
    · rw [if_neg h, if_neg h]

theorem qf_xu {δ : Rt} (hδ : IsRoot .E7 δ) (c : K) (v : V K) :
    qf ((e7Data_valid.xu K δ c : Module.End K (V K)) v) = qf v := by
  rw [e7Data_valid.xu_apply, qf_add, qf_smul, qf_rootOp hδ, beta_smul_right, beta_rootOp_self hδ]
  ring

end Quad

section AlgA

variable {K : Type} [Field K] [CharP K 2]

@[expose] def Hop (K : Type) [Field K] (ε : Rt) : Module.End K (V K) :=
  diagOp (fun b => ((pr b ε : ℤ) : K))

theorem Hop_single (ε : Rt) (a : Fin e7Data.d) :
    Hop K ε (Finsupp.single a 1) = ((pr a ε : ℤ) : K) • Finsupp.single a 1 :=
  diagOp_single _ a

theorem Hop_apply (ε : Rt) (v : V K) (b : Fin e7Data.d) :
    Hop K ε v b = ((pr b ε : ℤ) : K) * v b := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | single a c =>
    have e : (Finsupp.single a c : V K) = c • Finsupp.single a 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, map_smul, Hop_single]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases hab : a = b
    · rw [if_pos hab, ← hab]
      ring
    · simp [hab]

@[expose] def algA (K : Type) [Field K] (P : Set Rt) : Submodule K (Module.End K (V K)) :=
  Submodule.span K ({Y | ∃ γ ∈ P, Y = e7Data.rootOp K γ} ∪ {Y | ∃ γ ∈ P, Y = Hop K γ})

theorem rootOp_mem_algA {P : Set Rt} {γ : Rt} (hγ : γ ∈ P) : e7Data.rootOp K γ ∈ algA K P :=
  Submodule.subset_span (Or.inl ⟨γ, hγ, rfl⟩)

theorem Hop_mem_algA {P : Set Rt} {γ : Rt} (hγ : γ ∈ P) : Hop K γ ∈ algA K P :=
  Submodule.subset_span (Or.inr ⟨γ, hγ, rfl⟩)

theorem rootOp_neg_add_apply {δ : Rt} (hδ : IsRoot .E7 δ) (v : V K) :
    e7Data.rootOp K δ (e7Data.rootOp K (-δ) v) + e7Data.rootOp K (-δ) (e7Data.rootOp K δ v) =
      Hop K δ v := by
  have hδ' : IsRoot .E7 (-δ) := isRoot_neg hδ
  refine Finsupp.ext fun b => ?_
  rw [Finsupp.add_apply, Hop_apply, rootOp_apply hδ (e7Data.rootOp K (-δ) v) b,
    rootOp_apply hδ' (e7Data.rootOp K δ v) b]
  rcases pr_mem hδ b with h1 | h1 | h1
  ·
    have h2 : pr b (-δ) = 1 := by simp [pr_neg, h1]
    have h3 : ¬ pr b δ = 1 := by rw [h1]; norm_num
    rw [if_neg h3, zero_add, if_pos h2, neg_neg, rootOp_apply hδ v (shift δ b),
      if_pos (pr_shift_self hδ h1), shift_neg_shift hδ h1, h1]
    simp [CharTwo.neg_eq]
  ·
    have h2 : ¬ pr b (-δ) = 1 := by simp [pr_neg, h1]
    have h3 : ¬ pr b δ = 1 := by rw [h1]; norm_num
    rw [if_neg h3, zero_add, if_neg h2, h1]
    simp
  ·
    have h2 : ¬ pr b (-δ) = 1 := by simp [pr_neg, h1]
    have h4 : pr (shift (-δ) b) (-δ) = 1 := by simp [pr_neg, pr_shift_neg hδ h1]
    rw [if_pos h1, rootOp_apply hδ' v (shift (-δ) b), if_pos h4, neg_neg,
      shift_shift_neg hδ h1, if_neg h2, add_zero, h1]
    simp

theorem rootOp_Hop_add_apply {δ : Rt} (hδ : IsRoot .E7 δ) (ε : Rt) (v : V K) :
    e7Data.rootOp K δ (Hop K ε v) + Hop K ε (e7Data.rootOp K δ v) =
      ((ipR δ ε : ℤ) : K) • e7Data.rootOp K δ v := by
  refine Finsupp.ext fun b => ?_
  rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, rootOp_apply hδ (Hop K ε v) b,
    Hop_apply ε v (shift (-δ) b), Hop_apply ε (e7Data.rootOp K δ v) b, rootOp_apply hδ v b]
  by_cases h1 : pr b δ = 1
  · have h2 : pr b (-δ) = -1 := by simp [pr_neg, h1]
    have h3 := pr_shift (isRoot_neg hδ) h2 ε
    rw [MinData.toWeight_neg, neg_dotProduct] at h3
    have hc : pr (shift (-δ) b) ε = pr b ε - ipR δ ε := by
      rw [h3]
      unfold ipR
      ring
    simp only [if_pos h1]
    rw [hc, Int.cast_sub]
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (((pr b ε : ℤ) : K) * v (shift (-δ) b) -
      ((ipR δ ε : ℤ) : K) * v (shift (-δ) b)) * h2'
  · simp [h1]

theorem rootOp_Hop_rootOp_apply {δ : Rt} (hδ : IsRoot .E7 δ) (ε : Rt) (v : V K) :
    e7Data.rootOp K δ (Hop K ε (e7Data.rootOp K δ v)) = 0 := by
  have h := rootOp_Hop_add_apply hδ ε (e7Data.rootOp K δ v)
  have hEE : e7Data.rootOp K δ (e7Data.rootOp K δ v) = 0 := by
    have h0 := LinearMap.congr_fun (e7Data_valid.rootOp_mul_self (R := K) δ) v
    rwa [Module.End.mul_apply, LinearMap.zero_apply] at h0
  rw [hEE, map_zero, smul_zero, add_zero] at h
  exact h

set_option maxRecDepth 20000 in
theorem rootOp_comm_add {γ δ : Rt} (hγ : IsRoot .E7 γ) (hδ : IsRoot .E7 δ)
    (hr : IsRoot .E7 (γ + δ)) :
    e7Data.rootOp K γ * e7Data.rootOp K δ + e7Data.rootOp K δ * e7Data.rootOp K γ =
      e7Data.rootOp K (γ + δ) ∧
    e7Data.rootOp K δ * e7Data.rootOp K γ * e7Data.rootOp K δ = 0 := by
  have hne : γ + δ ≠ 0 := root_ne_zero hr
  obtain ⟨⟨σ, hσ, hcomm⟩, hxyx, hyxy⟩ := (e7Data_valid.pairRel (R := K) hγ hδ hne).1 hr
  refine ⟨?_, hyxy⟩
  have e1 : e7Data.rootOp K γ * e7Data.rootOp K δ + e7Data.rootOp K δ * e7Data.rootOp K γ =
      e7Data.rootOp K γ * e7Data.rootOp K δ - e7Data.rootOp K δ * e7Data.rootOp K γ := by
    have h2 := add_self_eq_zero_of_charTwo (K := K) (e7Data.rootOp K δ * e7Data.rootOp K γ)
    have h3 : -(e7Data.rootOp K δ * e7Data.rootOp K γ) = e7Data.rootOp K δ * e7Data.rootOp K γ :=
      neg_eq_of_add_eq_zero_right h2
    rw [sub_eq_add_neg, h3]
  rw [e1, hcomm]
  rcases hσ with rfl | rfl
  · rw [one_smul]
  · rw [neg_smul, one_smul]
    exact neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo (K := K) _)

theorem conj_expand (c : K) (E Y : Module.End K (V K)) :
    ((1 : Module.End K (V K)) + c • E) * Y * ((1 : Module.End K (V K)) + c • E) =
      Y + c • (E * Y + Y * E) + c ^ 2 • (E * Y * E) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, sq]
  abel

set_option maxRecDepth 20000 in
theorem conj_rootOp_mem_algA {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    (hPadd : ∀ β ∈ P, ∀ γ ∈ P, IsRoot .E7 (β + γ) → β + γ ∈ P)
    {δ γ : Rt} (hδ : δ ∈ P) (hγ : γ ∈ P) (c : K) :
    ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) * e7Data.rootOp K γ *
      ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) ∈ algA K P := by
  rw [conj_expand]
  have hδ' : IsRoot .E7 δ := hP δ hδ
  by_cases h0 : γ + δ = 0
  ·
    have hγδ : γ = -δ := eq_neg_of_add_eq_zero_left h0
    subst hγδ
    have hsum : e7Data.rootOp K δ * e7Data.rootOp K (-δ) +
        e7Data.rootOp K (-δ) * e7Data.rootOp K δ = Hop K δ := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.add_apply, Module.End.mul_apply]
      exact rootOp_neg_add_apply hδ' v
    rw [hsum, rootOp_xyx hδ']
    exact add_mem (add_mem (rootOp_mem_algA hγ) (Submodule.smul_mem _ _ (Hop_mem_algA hδ)))
      (Submodule.smul_mem _ _ (rootOp_mem_algA hδ))
  · by_cases hr : IsRoot .E7 (γ + δ)
    ·
      obtain ⟨h1, h2⟩ := rootOp_comm_add (K := K) (hP γ hγ) hδ' hr
      have hc : e7Data.rootOp K δ * e7Data.rootOp K γ +
          e7Data.rootOp K γ * e7Data.rootOp K δ = e7Data.rootOp K (γ + δ) :=
        (add_comm _ _).trans h1
      rw [hc, h2]
      simp only [smul_zero, add_zero]
      exact add_mem (rootOp_mem_algA hγ)
        (Submodule.smul_mem _ _ (rootOp_mem_algA (hPadd γ hγ δ hδ hr)))
    ·
      have hcomm : e7Data.rootOp K γ * e7Data.rootOp K δ =
          e7Data.rootOp K δ * e7Data.rootOp K γ :=
        (e7Data_valid.pairRel (R := K) (hP γ hγ) hδ' h0).2 hr
      have hs : e7Data.rootOp K δ * e7Data.rootOp K γ +
          e7Data.rootOp K γ * e7Data.rootOp K δ = 0 := by
        rw [← hcomm]
        exact add_self_eq_zero_of_charTwo (K := K) _
      have hz : e7Data.rootOp K δ * e7Data.rootOp K γ * e7Data.rootOp K δ = 0 := by
        rw [← hcomm, mul_assoc, e7Data_valid.rootOp_mul_self (R := K) δ, mul_zero]
      rw [hs, hz]
      simp only [smul_zero, add_zero]
      exact rootOp_mem_algA hγ

set_option maxRecDepth 20000 in
theorem conj_Hop_mem_algA {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    {δ ε : Rt} (hδ : δ ∈ P) (hε : ε ∈ P) (c : K) :
    ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) * Hop K ε *
      ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) ∈ algA K P := by
  rw [conj_expand]
  have hδ' : IsRoot .E7 δ := hP δ hδ
  have hA : e7Data.rootOp K δ * Hop K ε + Hop K ε * e7Data.rootOp K δ =
      ((ipR δ ε : ℤ) : K) • e7Data.rootOp K δ := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]
    exact rootOp_Hop_add_apply hδ' ε v
  have hB : e7Data.rootOp K δ * Hop K ε * e7Data.rootOp K δ = 0 := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, LinearMap.zero_apply]
    exact rootOp_Hop_rootOp_apply hδ' ε v
  rw [hA, hB]
  simp only [smul_zero, add_zero, smul_smul]
  exact add_mem (Hop_mem_algA hε) (Submodule.smul_mem _ _ (rootOp_mem_algA hδ))

set_option maxRecDepth 20000 in
theorem conj_xu_mem_algA {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    (hPadd : ∀ β ∈ P, ∀ γ ∈ P, IsRoot .E7 (β + γ) → β + γ ∈ P)
    {δ : Rt} (hδ : δ ∈ P) (c : K) {Y : Module.End K (V K)} (hY : Y ∈ algA K P) :
    ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) * Y *
      ((1 : Module.End K (V K)) + c • e7Data.rootOp K δ) ∈ algA K P := by
  unfold algA at hY
  induction hY using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨γ, hγ, rfl⟩ | ⟨ε, hε, rfl⟩
    · exact conj_rootOp_mem_algA hP hPadd hδ hγ c
    · exact conj_Hop_mem_algA hP hδ hε c
  | zero =>
    rw [mul_zero, zero_mul]
    exact zero_mem _
  | add x y hx hy ihx ihy =>
    rw [mul_add (_ : Module.End K (V K)) x y, add_mul]
    exact add_mem ihx ihy
  | smul a x hx ih =>
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ _ ih

@[expose] def GrpP (K : Type) [Field K] (P : Set Rt) : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ β ∈ P, ∃ c : K, g = e7Data_valid.xu K β c}

set_option maxRecDepth 20000 in
theorem conj_grpP_mem_algA {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    (hPadd : ∀ β ∈ P, ∀ γ ∈ P, IsRoot .E7 (β + γ) → β + γ ∈ P)
    {l : (Module.End K (V K))ˣ} (hl : l ∈ GrpP K P) {Y : Module.End K (V K)} (hY : Y ∈ algA K P) :
    (l : Module.End K (V K)) * Y * ((l⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ∈ algA K P ∧
    ((l⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) * Y * (l : Module.End K (V K)) ∈
      algA K P := by
  unfold GrpP at hl
  revert hY
  revert Y
  induction hl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨β, hβ, c, rfl⟩ := hg
    intro Y hY
    rw [xu_inv_self β c, e7Data_valid.xu_val]
    exact ⟨conj_xu_mem_algA hP hPadd hβ c hY, conj_xu_mem_algA hP hPadd hβ c hY⟩
  | one =>
    intro Y hY
    simp only [Units.val_one, inv_one, one_mul, mul_one]
    exact ⟨hY, hY⟩
  | mul l₁ l₂ hl₁ hl₂ ih₁ ih₂ =>
    intro Y hY
    have h1 := (ih₁ (ih₂ hY).1).1
    have h2 := (ih₂ (ih₁ hY).2).2
    simp only [Units.val_mul, mul_inv_rev, mul_assoc] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | inv g hg ih =>
    intro Y hY
    rw [inv_inv]
    exact ⟨(ih hY).2, (ih hY).1⟩

set_option maxRecDepth 20000 in
theorem qf_grpP {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β) {l : (Module.End K (V K))ˣ}
    (hl : l ∈ GrpP K P) (v : V K) : qf ((l : Module.End K (V K)) v) = qf v := by
  unfold GrpP at hl
  revert v
  induction hl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨β, hβ, c, rfl⟩ := hg
    intro v
    exact qf_xu (hP β hβ) c v
  | one =>
    intro v
    simp only [Units.val_one, Module.End.one_apply]
  | mul g h hg hh ihg ihh =>
    intro v
    rw [Units.val_mul, Module.End.mul_apply, ihg, ihh]
  | inv g hg ih =>
    intro v
    have hinv : (g : Module.End K (V K)) (((g⁻¹ : (Module.End K (V K))ˣ) :
        Module.End K (V K)) v) = v := by
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have h1 := ih (((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v)
    rw [hinv] at h1
    exact h1.symm

end AlgA

section Line

variable {K : Type} [Field K] [CharP K 2]

@[expose] def NearP (P : Set Rt) (a b : Fin e7Data.d) : Prop :=
  b = a ∨ ∃ γ ∈ P, pr a γ = -1 ∧ b = shift γ a

set_option maxRecDepth 20000 in
theorem algA_apply_single_zero {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β) {a : Fin e7Data.d}
    {Y : Module.End K (V K)} (hY : Y ∈ algA K P) {b : Fin e7Data.d} (hb : ¬ NearP P a b) :
    Y (Finsupp.single a 1) b = 0 := by
  unfold algA at hY
  induction hY using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩
    · rw [rootOp_single (K := K) (hP γ hγ) a]
      split_ifs with hpr
      · have hne : shift γ a ≠ b := fun e => hb (Or.inr ⟨γ, hγ, hpr, e.symm⟩)
        rw [Finsupp.single_apply, if_neg hne]
      · simp
    · have hab : a ≠ b := fun e => hb (Or.inl e.symm)
      simp [Hop_single, Finsupp.single_apply, hab]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ihx => simp [ihx]

theorem qf_algA_single {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β) {a : Fin e7Data.d}
    (hT : ∀ b₁ b₂, NearP P a b₁ → NearP P a b₂ → opp b₁ ≠ b₂)
    {Y : Module.End K (V K)} (hY : Y ∈ algA K P) : qf (Y (Finsupp.single a 1)) = 0 := by
  apply qf_eq_zero_of_support
  intro b
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hb1 : NearP P a b := by
    by_contra hb
    exact h1 (algA_apply_single_zero hP hY hb)
  have hb2 : NearP P a (opp b) := by
    by_contra hb
    exact h2 (algA_apply_single_zero hP hY hb)
  exact hT b (opp b) hb1 hb2 rfl

theorem qf_algA_orbit {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    (hPadd : ∀ β ∈ P, ∀ γ ∈ P, IsRoot .E7 (β + γ) → β + γ ∈ P) {a : Fin e7Data.d}
    (hT : ∀ b₁ b₂, NearP P a b₁ → NearP P a b₂ → opp b₁ ≠ b₂)
    {l : (Module.End K (V K))ˣ} (hl : l ∈ GrpP K P) {Y : Module.End K (V K)} (hY : Y ∈ algA K P) :
    qf (Y ((l : Module.End K (V K)) (Finsupp.single a 1))) = 0 := by
  have hinv : ∀ z : V K,
      (l : Module.End K (V K)) (((l⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) z) = z := by
    intro z
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have hY' := (conj_grpP_mem_algA hP hPadd hl hY).2
  have hkey : Y ((l : Module.End K (V K)) (Finsupp.single a 1)) =
      (l : Module.End K (V K))
        ((((l⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) * Y *
          (l : Module.End K (V K))) (Finsupp.single a 1)) := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hinv]
  rw [hkey, qf_grpP hP hl]
  exact qf_algA_single hP hT hY'

theorem line_coord_vanish {P : Set Rt} (hP : ∀ β ∈ P, IsRoot .E7 β)
    (hPadd : ∀ β ∈ P, ∀ γ ∈ P, IsRoot .E7 (β + γ) → β + γ ∈ P) {a : Fin e7Data.d}
    (hT : ∀ b₁ b₂, NearP P a b₁ → NearP P a b₂ → opp b₁ ≠ b₂)
    {l l' : (Module.End K (V K))ˣ} (hl : l ∈ GrpP K P) (hl' : l' ∈ GrpP K P) {α β γ : K}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : α • (Finsupp.single a 1 : V K) + β • (l : Module.End K (V K)) (Finsupp.single a 1) =
      γ • (l' : Module.End K (V K)) (Finsupp.single a 1)) :
    ((l : Module.End K (V K)) (Finsupp.single a 1)) (opp a) = 0 ∧
    ∀ g ∈ P, pr a g = -1 → ∀ d ∈ P, pr a d = 0 → pr (opp (shift g a)) d ≠ 0 →
      ((l : Module.End K (V K)) (Finsupp.single a 1)) (opp (shift g a)) = 0 := by
  have hqw : qf (Finsupp.single a (1 : K)) = 0 := qf_single a
  have hqv : qf ((l : Module.End K (V K)) (Finsupp.single a 1)) = 0 := by
    rw [qf_grpP hP hl, qf_single]
  have hqv' : qf ((l' : Module.End K (V K)) (Finsupp.single a 1)) = 0 := by
    rw [qf_grpP hP hl', qf_single]
  have hαβ : α * β ≠ 0 := mul_ne_zero hα hβ
  constructor
  ·
    have h1 : α * β * ((l : Module.End K (V K)) (Finsupp.single a 1)) (opp a) = 0 := by
      have hF := congrArg qf h
      simp only [qf_add, qf_smul, beta_smul_left, beta_smul_right, beta_single_left, hqw, hqv,
        hqv'] at hF
      linear_combination hF
    exact (mul_eq_zero.1 h1).resolve_left hαβ
  · intro g hg hag d hd had hd0
    obtain ⟨Y, hYdef⟩ : ∃ Y : Module.End K (V K), Y = e7Data.rootOp K g + Hop K d := ⟨_, rfl⟩
    have hYmem : Y ∈ algA K P := by
      rw [hYdef]
      exact add_mem (rootOp_mem_algA hg) (Hop_mem_algA hd)
    have hYw : Y (Finsupp.single a 1) = Finsupp.single (shift g a) 1 := by
      rw [hYdef, LinearMap.add_apply, rootOp_single (K := K) (hP g hg) a,
        Hop_single (K := K) d a, if_pos hag, had, Int.cast_zero, zero_smul, add_zero]
    have hne : ¬ pr (opp (shift g a)) g = 1 := by
      rw [pr_opp, pr_shift_self (hP g hg) hag]
      norm_num
    have hcoord : ∀ z : V K, Y z (opp (shift g a)) =
        ((pr (opp (shift g a)) d : ℤ) : K) * z (opp (shift g a)) := by
      intro z
      rw [hYdef, LinearMap.add_apply, Finsupp.add_apply, rootOp_apply (hP g hg) z,
        if_neg hne, zero_add, Hop_apply]
    have hc : ((pr (opp (shift g a)) d : ℤ) : K) ≠ 0 := by
      rcases pr_mem (hP d hd) (opp (shift g a)) with h' | h' | h'
      · rw [h']
        simp
      · exact absurd h' hd0
      · rw [h']
        simp
    have hβ0 : beta (Y (Finsupp.single a 1))
        (Y ((l : Module.End K (V K)) (Finsupp.single a 1))) = 0 := by
      have h2 := congrArg (⇑Y) h
      rw [map_add, map_smul, map_smul, map_smul] at h2
      have h3 := congrArg qf h2
      have hYw0 : qf (Y (Finsupp.single a 1)) = 0 := qf_algA_single hP hT hYmem
      have hYv0 : qf (Y ((l : Module.End K (V K)) (Finsupp.single a 1))) = 0 :=
        qf_algA_orbit hP hPadd hT hl hYmem
      have hYv'0 : qf (Y ((l' : Module.End K (V K)) (Finsupp.single a 1))) = 0 :=
        qf_algA_orbit hP hPadd hT hl' hYmem
      simp only [qf_add, qf_smul, beta_smul_left, beta_smul_right, hYw0, hYv0, hYv'0] at h3
      have h4 : α * β * beta (Y (Finsupp.single a 1))
          (Y ((l : Module.End K (V K)) (Finsupp.single a 1))) = 0 := by
        linear_combination h3
      exact (mul_eq_zero.1 h4).resolve_left hαβ
    rw [hYw, beta_single_left] at hβ0
    have hz := hcoord ((l : Module.End K (V K)) (Finsupp.single a 1))
    rw [hβ0] at hz
    exact (mul_eq_zero.1 hz.symm).resolve_left hc

end Line

section Glue

open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem minuscLine_of_core {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
    (core : ∀ g ∈ Γ, ∀ g' ∈ Γ, ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      a • p₀ + b • g p₀ = c • g' p₀ → g p₀ ∈ Wsp (Submodule.span K {p₀}) U₀) :
    MinuscLine Γ p₀ U₀ where
  line_iff g₁ hg₁ g₂ hg₂ g₃ hg₃ a b c ha hb hc h := by
    have hinv : g₁⁻¹ ∈ Γ := inv_mem hg₁
    have h' : a • p₀ + b • (g₁⁻¹ * g₂) p₀ = c • (g₁⁻¹ * g₃) p₀ := by
      have h1 := congrArg (fun v => g₁⁻¹ v) h
      simpa [map_add, map_smul] using h1
    have hcore := core _ (mul_mem hinv hg₂) _ (mul_mem hinv hg₃) a b c ha hb hc h'
    have hspan : Submodule.span K {g₁ p₀} = (Submodule.span K {p₀}).map (g₁ : V →ₗ[K] V) := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    rw [hspan, Wsp_map]
    exact ⟨(g₁⁻¹ * g₂) p₀, hcore, by simp⟩

end Glue

end CFSG.RankThree.GF2n.Smith81.MinuscT
