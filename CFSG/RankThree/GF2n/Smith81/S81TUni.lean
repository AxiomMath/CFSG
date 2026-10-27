module

public import CFSG.RankThree.GF2n.Smith81.S81TKer
public import CFSG.RankThree.GF2n.Smith81.S81TFin

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

theorem isRoot_rt (k : Fin 126) : IsRoot .E7 (rt k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

section Uni

variable {K : Type} [Field K] [CharP K 2]

@[expose] def RangeL (K : Type) [Field K] (S : List Rt) (inL : Fin e7Data.d → Prop) : Submodule K (V K) :=
  Submodule.map (NOp K S) (Finsupp.supported K K {a : Fin e7Data.d | inL a})

theorem rootOp_mem_supported {okD : Rt → Prop} {inL : Fin e7Data.d → Prop} (hcl : ClosedL okD inL)
    {α : Rt} (hα : IsRoot .E7 α) (hok : okD α) {w : V K}
    (hw : w ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}) :
    e7Data.rootOp K α w ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a} := by
  rw [Finsupp.mem_supported'] at hw ⊢
  intro b hb
  rw [rootOp_apply hα]
  by_cases h1 : pr b α = 1
  · rw [if_pos h1]
    apply hw
    intro hin
    exact hb ((hcl α hα hok b h1).1 hin)
  · rw [if_neg h1]

theorem single_mem_RangeL {S : List Rt} (hS : SOrth S) {okD : Rt → Prop}
    {inL : Fin e7Data.d → Prop} (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL)
    {ν : Fin e7Data.d} (hν : inL ν) (h : ∀ β ∈ S, pr ν β = 0 ∨ pr ν β = 1)
    (hne : ∃ β ∈ S, pr ν β = 1) : (Finsupp.single ν (1 : K) : V K) ∈ RangeL K S inL := by
  obtain ⟨i, hi, h1⟩ := hne
  refine ⟨Finsupp.single (shift (-i) ν) 1, ?_, ?_⟩
  · exact Finsupp.single_mem_supported K 1 ((hcl i (hS.1 i hi) (hSok i hi) ν h1).2 hν)
  · rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply, tOp_single_bottom hS hi ν h1 h,
      add_sub_cancel_left]

theorem heis_sub_mem {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} {inL : Fin e7Data.d → Prop}
    [DecidablePred inL] (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL) {α : Rt}
    (hα : IsRoot .E7 α) (hok : okD α) (hA : inAplus S α) {c : V K}
    (hc : c ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}) (hC : NOp K S c = 0) :
    e7Data.rootOp K α c ∈ RangeL K S inL := by
  obtain ⟨w, hw, u, hu, rfl⟩ := ker_NOp_le_L hS hSok hcl hc hC
  have hnn : ∀ β ∈ S, 0 ≤ ipR α β := fun β hβ => by
    rcases hA.1 β hβ with h | h <;> omega
  rw [map_add]
  refine add_mem ?_ ?_
  · rw [rootOp_NOp_apply hα hS.1 hnn w]
    exact ⟨_, rootOp_mem_supported hcl hα hok hw, rfl⟩
  · rw [Finsupp.supported_eq_span_single] at hu
    refine Submodule.span_induction (p := fun x _ => e7Data.rootOp K α x ∈ RangeL K S inL) ?_ ?_ ?_ ?_
      hu
    · rintro x ⟨μ, hμ, rfl⟩
      obtain ⟨hμL, hμperp⟩ := hμ
      rw [rootOp_single hα]
      by_cases hpr : pr μ α = -1
      · rw [if_pos hpr]
        have hν1 : pr (shift α μ) α = 1 := pr_shift_self hα hpr
        have hνL : inL (shift α μ) :=
          (hcl α hα hok (shift α μ) hν1).1 (by rw [shift_neg_shift hα hpr]; exact hμL)
        have hpν : ∀ β ∈ S, pr (shift α μ) β = ipR α β := fun β hβ => by
          rw [pr_shift hα hpr, hμperp β hβ, zero_add]
        refine single_mem_RangeL hS hSok hcl hνL (fun β hβ => ?_) ?_
        · rw [hpν β hβ]; exact hA.1 β hβ
        · obtain ⟨β, hβ, h1⟩ := hA.2
          exact ⟨β, hβ, by rw [hpν β hβ]; exact h1⟩
      · rw [if_neg hpr]
        exact zero_mem _
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]; exact add_mem hx hy
    · intro a x _ hx
      rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem fix_heis_le {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} {inL : Fin e7Data.d → Prop}
    [DecidablePred inL] (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL)
    (hStar : StarProp okD inL S) {c : V K}
    (hc : c ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}) (hC : NOp K S c = 0)
    (hfix : ∀ α : Rt, IsRoot .E7 α → okD α → inAplus S α → e7Data.rootOp K α c = 0) :
    c ∈ RangeL K S inL := by
  obtain ⟨w, hw, u, hu, hc₀⟩ := ker_NOp_le_L hS hSok hcl hc hC
  have hu0 : u = 0 := by
    ext μ
    rw [Finsupp.zero_apply]
    by_contra hμ
    have hμmem : μ ∈ {a : Fin e7Data.d | inL a ∧ perpWt S a} := by
      by_contra hn
      exact hμ ((Finsupp.mem_supported' K u).1 hu μ hn)
    obtain ⟨hμL, hμperp⟩ := hμmem
    obtain ⟨k, hkok, hkA, hkpr⟩ := hStar μ hμL hμperp
    have hrk : IsRoot .E7 (rt k) := isRoot_rt k
    have h0 := hfix (rt k) hrk hkok hkA
    have hν1 : pr (shift (rt k) μ) (rt k) = 1 := pr_shift_self hrk hkpr
    have h1 := congrArg (fun x : V K => x (shift (rt k) μ)) h0
    simp only [Finsupp.zero_apply] at h1
    rw [rootOp_apply hrk, if_pos hν1, shift_neg_shift hrk hkpr] at h1
    have hNw : (NOp K S w) μ = 0 := by
      rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
        tOp_apply_of_no_top hS.1 w μ (fun β hβ => by rw [hμperp β hβ]; norm_num), sub_self]
    have hcμ : c μ = u μ := by
      rw [hc₀, Finsupp.add_apply, hNw, zero_add]
    exact hμ (hcμ ▸ h1)
  rw [hu0, add_zero] at hc₀
  exact ⟨w, hw, hc₀.symm⟩

theorem tOp_single_perp {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) {a : Fin e7Data.d}
    (h : ∀ β ∈ S, pr a β = 0) (t : K) :
    tOp K S (Finsupp.single a t) = Finsupp.single a t := by
  induction S with
  | nil => rw [tOp_nil, Module.End.one_apply]
  | cons β S ih =>
    have hβ : IsRoot .E7 β := hS β (List.mem_cons_self ..)
    have hE : e7Data.rootOp K β (Finsupp.single a t) = 0 := by
      have e : (Finsupp.single a t : V K) = t • Finsupp.single a 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [e, map_smul, rootOp_single hβ, if_neg (by rw [h β (List.mem_cons_self ..)]; norm_num),
        smul_zero]
    rw [tOp_cons, Module.End.mul_apply, ih (fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ))
      (fun γ hγ => h γ (List.mem_cons_of_mem _ hγ)), LinearMap.add_apply, Module.End.one_apply, hE,
      add_zero]

theorem cov_of_star2 {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} {inL : Fin e7Data.d → Prop}
    [DecidablePred inL] (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL)
    (hStar2 : Star2Prop okD inL S) {c : V K}
    (hc : c ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}) (hC : NOp K S c = 0) :
    ∃ r ∈ RangeL K S inL, c - r ∈ AddSubgroup.closure
      {v : V K | ∃ α : Rt, IsRoot .E7 α ∧ okD α ∧ inPerpS S α ∧
        ∃ c' ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}, NOp K S c' = 0 ∧
          v = e7Data.rootOp K α c'} := by
  obtain ⟨w, hw, u, hu, hc₀⟩ := ker_NOp_le_L hS hSok hcl hc hC
  refine ⟨NOp K S w, ⟨w, hw, rfl⟩, ?_⟩
  have hcu : c - NOp K S w = u := by rw [hc₀]; abel
  rw [hcu]
  have hgen : ∀ μ : Fin e7Data.d, inL μ → perpWt S μ → ∀ t : K,
      (Finsupp.single μ t : V K) ∈ AddSubgroup.closure
        {v : V K | ∃ α : Rt, IsRoot .E7 α ∧ okD α ∧ inPerpS S α ∧
          ∃ c' ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}, NOp K S c' = 0 ∧
            v = e7Data.rootOp K α c'} := by
    intro μ hμL hμperp t
    obtain ⟨k, hkok, hkperp, hkpr⟩ := hStar2 μ hμL hμperp
    have hrk : IsRoot .E7 (rt k) := isRoot_rt k
    have hμ1 : pr μ (rt k) = 1 := hkpr
    have hμ'pr : pr (shift (-(rt k)) μ) (rt k) = -1 := pr_shift_neg hrk hμ1
    apply AddSubgroup.subset_closure
    refine ⟨rt k, hrk, hkok, hkperp, Finsupp.single (shift (-(rt k)) μ) t, ?_, ?_, ?_⟩
    · exact Finsupp.single_mem_supported K t ((hcl (rt k) hrk hkok μ hμ1).2 hμL)
    · have hperp' : ∀ β ∈ S, pr (shift (-(rt k)) μ) β = 0 := fun β hβ => by
        rw [pr_shift_neg_orth hrk (hkperp β hβ) hμ1, hμperp β hβ]
      rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply, tOp_single_perp hS.1 hperp' t,
        sub_self]
    · have e : (Finsupp.single (shift (-(rt k)) μ) t : V K) =
          t • Finsupp.single (shift (-(rt k)) μ) 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have e2 : (Finsupp.single μ t : V K) = t • Finsupp.single μ 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [e, map_smul, rootOp_single hrk, if_pos hμ'pr, shift_shift_neg hrk hμ1, e2]
  have hu' := (Finsupp.mem_supported' K u).1 hu
  have hsum : u = ∑ μ ∈ u.support, Finsupp.single μ (u μ) := by
    conv_lhs => rw [← Finsupp.sum_single u]
    rfl
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun μ hμ => ?_
  have hμmem : μ ∈ {a : Fin e7Data.d | inL a ∧ perpWt S a} := by
    by_contra hn
    exact (Finsupp.mem_support_iff.1 hμ) (hu' μ hn)
  exact hgen μ hμmem.1 hμmem.2 (u μ)

end Uni

end CFSG.RankThree.GF2n.Smith81.MinuscT
