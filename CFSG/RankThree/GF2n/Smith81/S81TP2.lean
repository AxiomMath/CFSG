module

public import CFSG.RankThree.GF2n.Smith81.S81TUni
public import CFSG.RankThree.GF2n.Smith81.S81TAlg
public import CFSG.RankThree.GF2n.Smith81.S81THeight
public import CFSG.RankThree.GF2n.Smith81.S81TClique

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section Torus

variable {K : Type} [Field K] [CharP K 2]

theorem root_ne_zero {α : Rt} (hα : IsRoot .E7 α) : α ≠ 0 := by
  intro h0
  have := ipR_self hα
  rw [h0] at this
  simp [ipR] at this

theorem xu_inv_self (γ : Rt) (c : K) :
    (e7Data_valid.xu K γ c)⁻¹ = e7Data_valid.xu K γ c := by
  have h : e7Data_valid.xu K γ c * e7Data_valid.xu K γ c = 1 := by
    rw [← e7Data_valid.xu_add, CharTwo.add_self_eq_zero, e7Data_valid.xu_zero]
  exact inv_eq_of_mul_eq_one_right h

theorem rootOp_neg_Pσ_one {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    e7Data.rootOp K (-β) (Pσ K β 1 v) = e7Data.rootOp K (-β) v := by
  ext b
  rw [rootOp_apply (isRoot_neg hβ), rootOp_apply (isRoot_neg hβ)]
  by_cases h1 : pr b (-β) = 1
  · rw [if_pos h1, if_pos h1, neg_neg, Pσ_apply]
    have h2 : pr b β = -1 := by rw [pr_neg] at h1; omega
    rw [if_pos (pr_shift_self hβ h2)]
  · rw [if_neg h1, if_neg h1]

set_option maxRecDepth 20000 in
theorem rootOp_xyx {α : Rt} (hα : IsRoot .E7 α) :
    e7Data.rootOp K α * e7Data.rootOp K (-α) * e7Data.rootOp K α = e7Data.rootOp K α := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, rootOp_neg_rootOp hα, rootOp_Pσ_neg_one hα]

set_option maxRecDepth 20000 in
theorem rootOp_yxy {α : Rt} (hα : IsRoot .E7 α) :
    e7Data.rootOp K (-α) * e7Data.rootOp K α * e7Data.rootOp K (-α) = e7Data.rootOp K (-α) := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, rootOp_rootOp_neg hα, rootOp_neg_Pσ_one hα]

@[expose] def hTor (K : Type) [Field K] (α : Rt) (c : K) : (Module.End K (V K))ˣ :=
  e7Data_valid.xu K α c * e7Data_valid.xu K (-α) c⁻¹ * e7Data_valid.xu K α c *
    (e7Data_valid.xu K α 1 * e7Data_valid.xu K (-α) (1 : K)⁻¹ * e7Data_valid.xu K α 1)

set_option maxRecDepth 20000 in
theorem hTor_conj {α : Rt} (hα : IsRoot .E7 α) {c : K} (hc : c ≠ 0) (s : K) :
    hTor K α c * e7Data_valid.xu K α s = e7Data_valid.xu K α (c ^ 2 * s) * hTor K α c := by
  apply Units.ext
  have h := sl2_torus_conj (K := K) (A := Module.End K (V K)) (X := e7Data.rootOp K α)
    (Y := e7Data.rootOp K (-α)) (e7Data_valid.rootOp_mul_self (R := K) α)
    (e7Data_valid.rootOp_mul_self (R := K) (-α)) (rootOp_xyx hα) (rootOp_yxy hα) hc s
  simp only [hTor, Units.val_mul, e7Data_valid.xu_val]
  exact h

set_option maxRecDepth 20000 in
theorem xu_commutator_of_add {γ δ α : Rt} (hγ : IsRoot .E7 γ) (hδ : IsRoot .E7 δ)
    (hα : IsRoot .E7 α) (h : γ + δ = α) :
    e7Data_valid.xu K γ 1 * e7Data_valid.xu K δ 1 * e7Data_valid.xu K γ 1 * e7Data_valid.xu K δ 1 =
      e7Data_valid.xu K α 1 := by
  have hne : γ + δ ≠ 0 := by rw [h]; exact root_ne_zero hα
  have hr : IsRoot .E7 (γ + δ) := by rw [h]; exact hα
  obtain ⟨⟨σ, hσ, hcomm⟩, hxyx, hyxy⟩ := (e7Data_valid.pairRel (R := K) hγ hδ hne).1 hr
  have hyy := e7Data_valid.rootOp_mul_self (R := K) δ
  have hxx := e7Data_valid.rootOp_mul_self (R := K) γ
  have hc : e7Data.rootOp K γ * e7Data.rootOp K δ + e7Data.rootOp K δ * e7Data.rootOp K γ =
      e7Data.rootOp K α := by
    have e1 : e7Data.rootOp K γ * e7Data.rootOp K δ + e7Data.rootOp K δ * e7Data.rootOp K γ =
        e7Data.rootOp K γ * e7Data.rootOp K δ - e7Data.rootOp K δ * e7Data.rootOp K γ := by
      have h2 := add_self_eq_zero_of_charTwo (K := K) (e7Data.rootOp K δ * e7Data.rootOp K γ)
      have h3 : -(e7Data.rootOp K δ * e7Data.rootOp K γ) = e7Data.rootOp K δ * e7Data.rootOp K γ :=
        neg_eq_of_add_eq_zero_right h2
      rw [sub_eq_add_neg, h3]
    rw [e1, hcomm, h]
    rcases hσ with rfl | rfl
    · rw [one_smul]
    · rw [neg_smul, one_smul]
      exact neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo (K := K) _)
  apply Units.ext
  simp only [Units.val_mul, e7Data_valid.xu_val, one_smul]
  have h2 : ∀ x : Module.End K (V K), x + x = 0 := fun x => add_self_eq_zero_of_charTwo (K := K) x
  exact commutator_alg h2 hxx hyy hxyx hyxy hc

theorem xu_commute_tOp {γ : Rt} (hγ : IsRoot .E7 γ) {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β)
    (h : ∀ β ∈ S, 0 ≤ ipR γ β) (c : K) :
    Commute (e7Data_valid.xu K γ c : Module.End K (V K)) (tOp K S) := by
  show (e7Data_valid.xu K γ c : Module.End K (V K)) * tOp K S =
    tOp K S * (e7Data_valid.xu K γ c : Module.End K (V K))
  rw [e7Data_valid.xu_val, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    rootOp_comm_tOp hγ hS h]

theorem lem24 {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} [DecidablePred okD]
    (hneg : ∀ γ, okD γ → okD (-γ)) [Finite K] (hK4 : 4 ≤ Nat.card K) {α : Rt}
    (hα : α ∈ A2list okD S) :
    ∃ a b : (Module.End K (V K))ˣ, a ∈ GrpR K okD ∧ b ∈ GrpR K okD ∧
      Commute (a : Module.End K (V K)) (tOp K S) ∧ Commute (b : Module.End K (V K)) (tOp K S) ∧
      a * b * a⁻¹ * b⁻¹ = e7Data_valid.xu K α 1 := by
  obtain ⟨k, hk, hokα, hpos, hAS, hcov⟩ := mem_A2list.1 hα
  have hαr : IsRoot .E7 α := hk ▸ isRoot_rt k
  rcases hcov with ⟨k₁, k₂, hsum, hok1, hok2, hAS1, hAS2⟩ | hperp
  · have hr1 := isRoot_rt k₁
    have hr2 := isRoot_rt k₂
    refine ⟨e7Data_valid.xu K (rt k₁) 1, e7Data_valid.xu K (rt k₂) 1, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨rt k₁, hr1, hok1, 1, rfl⟩
    · exact Subgroup.subset_closure ⟨rt k₂, hr2, hok2, 1, rfl⟩
    · exact xu_commute_tOp hr1 hS.1 hAS1 1
    · exact xu_commute_tOp hr2 hS.1 hAS2 1
    · rw [xu_inv_self, xu_inv_self]
      exact xu_commutator_of_add hr1 hr2 hαr hsum
  · obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one (K := K) hK4
    have hc2 : c ^ 2 + 1 ≠ 0 := sq_add_one_ne_zero hc1
    obtain ⟨s, hs⟩ : ∃ s : K, s = (c ^ 2 + 1)⁻¹ := ⟨_, rfl⟩
    have hnegr : IsRoot .E7 (-α) := isRoot_neg hαr
    have hmem1 : ∀ d : K, e7Data_valid.xu K α d ∈ GrpR K okD := fun d =>
      Subgroup.subset_closure ⟨α, hαr, hokα, d, rfl⟩
    have hmem2 : ∀ d : K, e7Data_valid.xu K (-α) d ∈ GrpR K okD := fun d =>
      Subgroup.subset_closure ⟨-α, hnegr, hneg α hokα, d, rfl⟩
    have hnn : ∀ β ∈ S, 0 ≤ ipR α β := fun β hβ => by rw [hperp β hβ]
    have hnn' : ∀ β ∈ S, 0 ≤ ipR (-α) β := fun β hβ => by rw [ipR_neg_left, hperp β hβ]; norm_num
    have hc1' := xu_commute_tOp (K := K) hαr hS.1 hnn
    have hc2' := xu_commute_tOp (K := K) hnegr hS.1 hnn'
    refine ⟨hTor K α c, e7Data_valid.xu K α s, ?_, hmem1 s, ?_, hc1' s, ?_⟩
    · unfold hTor
      exact mul_mem (mul_mem (mul_mem (hmem1 c) (hmem2 c⁻¹)) (hmem1 c))
        (mul_mem (mul_mem (hmem1 1) (hmem2 _)) (hmem1 1))
    · unfold hTor
      simp only [Units.val_mul]
      have h12 := (hc1' c).mul_left (hc2' c⁻¹)
      have h123 := h12.mul_left (hc1' c)
      have h45 := (hc1' 1).mul_left (hc2' (1 : K)⁻¹)
      have h456 := h45.mul_left (hc1' 1)
      exact h123.mul_left h456
    · have hconj := hTor_conj hαr hc0 s
      have e1 : hTor K α c * e7Data_valid.xu K α s * (hTor K α c)⁻¹ =
          e7Data_valid.xu K α (c ^ 2 * s) := by
        rw [hconj, mul_inv_cancel_right]
      rw [e1, xu_inv_self, ← e7Data_valid.xu_add]
      congr 1
      rw [hs]
      field_simp

end Torus

section Support

variable {K : Type} [Field K] [CharP K 2]

theorem pr_ne_neg_one_of_support {α : Rt} (hα : IsRoot .E7 α) {s : V K}
    (hker : e7Data.rootOp K α s = 0) {μ : Fin e7Data.d} (hμ : s μ ≠ 0) : pr μ α ≠ -1 := by
  intro h
  have hν1 : pr (shift α μ) α = 1 := pr_shift_self hα h
  have h1 := congrArg (fun x : V K => x (shift α μ)) hker
  simp only [Finsupp.zero_apply] at h1
  rw [rootOp_apply hα, if_pos hν1, shift_neg_shift hα h] at h1
  exact hμ h1

theorem support_inMtop {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} {inL : Fin e7Data.d → Prop}
    (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL) {A2 : List Rt}
    (hA2 : ∀ α ∈ A2, IsRoot .E7 α) {s v : V K} (hsv : NOp K S v = s)
    (hs : s ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a})
    (hker : ∀ α ∈ A2, e7Data.rootOp K α s = 0) (hTwo : Two inL S) (hNM : NoMixed inL A2 S) :
    ∀ a, s a ≠ 0 → inMtop inL A2 S a := by
  intro μ hμ
  have hμL : inL μ := by
    by_contra hn
    exact hμ ((Finsupp.mem_supported' K s).1 hs μ hn)
  have hA : ∀ ν, s ν ≠ 0 → ∀ α ∈ A2, pr ν α ≠ -1 := fun ν hν α hα =>
    pr_ne_neg_one_of_support (hA2 α hα) (hker α hα) hν
  have hsμ : ∀ ν, s ν = (tOp K S v) ν - v ν := fun ν => by
    rw [← hsv, NOp_eq, LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply]
  have hμtop : ∃ β ∈ S, pr μ β = 1 := by
    by_contra hn
    simp only [not_exists, not_and] at hn
    apply hμ
    rw [hsμ, tOp_apply_of_no_top hS.1 v μ hn, sub_self]
  obtain ⟨i, hi, h1⟩ := hμtop
  have hμM : inM inL A2 S μ := ⟨hμL, ⟨i, hi, by rw [h1]; norm_num⟩, hA μ hμ⟩
  refine ⟨hμM, fun j hj hjneg => ?_⟩
  have hij : i ≠ j := fun e => by rw [e] at h1; omega
  have hri : IsRoot .E7 i := hS.1 i hi
  have hrj : IsRoot .E7 j := hS.1 j hj
  have hort : ipR i j = 0 := hS.2.2 i hi j hj hij
  have hort' : ipR j i = 0 := (ipR_comm j i).trans hort
  have hzero : ∀ β ∈ S, β ≠ i → β ≠ j → pr μ β = 0 := by
    intro β hβ hβi hβj
    by_contra hne
    have := three_distinct_of_filter_length hS.2.1 (fun β => decide (pr μ β ≠ 0)) (hTwo μ hμL)
      hi hj hβ (by simp [h1]) (by simp [hjneg]) (by simpa using hne)
    rcases this with e | e | e
    · exact hij e
    · exact hβi e.symm
    · exact hβj e.symm
  have htop : ∀ β ∈ S, β ≠ i → pr μ β ≠ 1 := by
    intro β hβ hβi
    by_cases hβj : β = j
    · rw [hβj, hjneg]; norm_num
    · rw [hzero β hβ hβi hβj]; norm_num
  have hC1 := tOp_apply_of_one_top hS v μ hi h1 htop
  have hμ₁i : pr (shift (-i) μ) i = -1 := pr_shift_neg hri h1
  have hμ₁j : pr (shift (-i) μ) j = -1 := by
    rw [pr_shift_neg_orth hri hort h1, hjneg]
  have hμ'j : pr (shift j (shift (-i) μ)) j = 1 := pr_shift_self hrj hμ₁j
  have hμ'sh : ∀ β : Rt, pr (shift j (shift (-i) μ)) β = pr (shift (-i) μ) β + ipR j β := fun β => by
    rw [pr_shift hrj hμ₁j β]
  have hμ'i : pr (shift j (shift (-i) μ)) i = -1 := by
    rw [hμ'sh, hort', add_zero, hμ₁i]
  have htop' : ∀ β ∈ S, β ≠ j → pr (shift j (shift (-i) μ)) β ≠ 1 := by
    intro β hβ hβj
    by_cases hβi : β = i
    · rw [hβi, hμ'i]; norm_num
    · have hort2 : ipR j β = 0 := (ipR_comm j β).trans (hS.2.2 β hβ j hj hβj)
      have hort3 : ipR i β = 0 := hS.2.2 i hi β hβ (fun e => hβi e.symm)
      rw [hμ'sh, hort2, add_zero, pr_shift_neg_orth hri hort3 h1, hzero β hβ hβi hβj]
      norm_num
  have hC1' := tOp_apply_of_one_top hS v (shift j (shift (-i) μ)) hj hμ'j htop'
  rw [shift_neg_shift hrj hμ₁j] at hC1'
  have hsμ' : s (shift j (shift (-i) μ)) = s μ := by
    rw [hsμ, hsμ, hC1, hC1']
    abel
  have hμ'ne : s (shift j (shift (-i) μ)) ≠ 0 := by rw [hsμ']; exact hμ
  have hμ'L : inL (shift j (shift (-i) μ)) := by
    have e1 := hcl i hri (hSok i hi) μ h1
    have e2 := hcl j hrj (hSok j hj) (shift j (shift (-i) μ)) hμ'j
    rw [shift_neg_shift hrj hμ₁j] at e2
    exact e2.1 (e1.2 hμL)
  have hμ'M : inM inL A2 S (shift j (shift (-i) μ)) :=
    ⟨hμ'L, ⟨j, hj, by rw [hμ'j]; norm_num⟩, hA _ hμ'ne⟩
  refine hNM μ _ hμM hμ'M i hi j hj h1 hjneg ?_
  have w1 := wt_shift hrj hμ₁j
  have w2 := wt_shift (isRoot_neg hri) (show pr μ (-i) = -1 by rw [pr_neg, h1])
  rw [w1, w2, MinData.toWeight_neg]
  abel

theorem P2_of_clique {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} [DecidablePred okD]
    {inL : Fin e7Data.d → Prop} (hSok : ∀ β ∈ S, okD β) (hneg : ∀ γ, okD γ → okD (-γ))
    (hcl : ClosedL okD inL) (hTwo : Two inL S) (hNM : NoMixed inL (A2list okD S) S)
    (hCl : CliqueOK inL (A2list okD S) S) [Finite K] (hK4 : 4 ≤ Nat.card K)
    {S' : AddSubgroup (V K)} (hne : S' ≠ ⊥)
    (hsupp : ∀ s ∈ S', s ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a})
    (hR : ∀ s ∈ S', s ∈ LinearMap.range (NOp K S))
    (hstab : ∀ a b : (Module.End K (V K))ˣ, a ∈ GrpR K okD → b ∈ GrpR K okD →
      Commute (a : Module.End K (V K)) (tOp K S) → Commute (b : Module.End K (V K)) (tOp K S) →
      ∀ s ∈ S', ((a * b * a⁻¹ * b⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) s ∈ S') :
    ∃ p ∈ S', p ≠ 0 ∧ IsHWLine K (Submodule.span K {p}) := by
  have hA2r : ∀ α ∈ A2list okD S, IsRoot .E7 α := fun α hα => by
    obtain ⟨k, hk, -⟩ := mem_A2list.1 hα
    exact hk ▸ isRoot_rt k
  have hA2pos : ∀ α ∈ A2list okD S, 0 < MinData.toWeight α ⬝ᵥ rho2 := fun α hα => by
    obtain ⟨k, hk, -, hpos, -⟩ := mem_A2list.1 hα
    subst hk
    exact hgt_pos k hpos
  have hstabE : ∀ α ∈ A2list okD S, ∀ s ∈ S', e7Data.rootOp K α s ∈ S' := by
    intro α hα s hs
    obtain ⟨a, b, ha, hb, hac, hbc, hab⟩ := lem24 hS hneg hK4 hα
    have h1 := hstab a b ha hb hac hbc s hs
    rw [hab, e7Data_valid.xu_apply, one_smul] at h1
    have h2 := S'.sub_mem h1 hs
    simpa using h2
  obtain ⟨s, hsS, hs0, hker⟩ := exists_mem_ker_rootOps S' hne (A2list okD S) hA2r hA2pos hstabE
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (hR s hsS)
  have hMtop := support_inMtop hS hSok hcl hA2r hv (hsupp s hsS) hker hTwo hNM
  exact ⟨s, hsS, hs0, isHWLine_of_clique hCl s hs0 hMtop⟩

end Support

theorem sOrth_of_cond {S : List Rt} (h : (∀ β ∈ S, ∃ k : Fin 126, rt k = β) ∧ S.Nodup ∧
    ∀ β ∈ S, ∀ γ ∈ S, β ≠ γ → ipR β γ = 0) : SOrth S :=
  ⟨fun β hβ => by
    obtain ⟨k, hk⟩ := h.1 β hβ
    exact hk ▸ isRoot_rt k, h.2.1, h.2.2⟩

theorem sOrth_of_K12 {okD : Rt → Prop} [DecidablePred okD] {inL : Fin e7Data.d → Prop} {S : List Rt}
    (h : K12Cond okD inL S) : SOrth S := sOrth_of_cond ⟨h.1, h.2.1, h.2.2.1⟩

theorem sOrth_of_K3 {okD : Rt → Prop} {inL : Fin e7Data.d → Prop} {S : List Rt}
    (h : K3Cond okD inL S) : SOrth S := sOrth_of_cond ⟨h.1, h.2.1, h.2.2.1⟩

end CFSG.RankThree.GF2n.Smith81.MinuscT
