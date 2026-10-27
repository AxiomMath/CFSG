module

public import CFSG.RankThree.GF2n.Smith81.S81TDefs

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section SigmaBeta

variable {K : Type} [Field K] [CharP K 2]

@[expose] def Pσ (K : Type) [Field K] (β : Rt) (ε : ℤ) : Module.End K (V K) :=
  projP K (fun b => pr b β = ε)

theorem Pσ_apply (β : Rt) (ε : ℤ) (v : V K) (b : Fin e7Data.d) :
    Pσ K β ε v b = if pr b β = ε then v b else 0 := projP_apply _ v b

theorem Pσ_idem (β : Rt) (ε : ℤ) (v : V K) : Pσ K β ε (Pσ K β ε v) = Pσ K β ε v := by
  ext b
  simp only [Pσ_apply]
  split_ifs <;> rfl

theorem Pσ_sum {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    Pσ K β (-1) v + Pσ K β 0 v + Pσ K β 1 v = v := by
  ext b
  simp only [Finsupp.add_apply, Pσ_apply]
  rcases pr_mem hβ b with h | h | h <;> simp [h]

theorem Pσ_rootOp_of_ne {β : Rt} (hβ : IsRoot .E7 β) {ε : ℤ} (hε : ε ≠ 1) (v : V K) :
    Pσ K β ε (e7Data.rootOp K β v) = 0 := by
  ext b
  rw [Pσ_apply, rootOp_apply hβ]
  by_cases h1 : pr b β = ε
  · rw [if_pos h1, if_neg (fun h2 => hε (h1.symm.trans h2))]
    try rfl
  · rw [if_neg h1]
    try rfl

theorem Pσ_one_rootOp {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    Pσ K β 1 (e7Data.rootOp K β v) = e7Data.rootOp K β v := by
  ext b
  rw [Pσ_apply]
  by_cases h1 : pr b β = 1
  · rw [if_pos h1]
  · rw [if_neg h1, rootOp_apply hβ, if_neg h1]
    try rfl

theorem rootOp_Pσ_of_ne {β : Rt} (hβ : IsRoot .E7 β) {ε : ℤ} (hε : ε ≠ -1) (v : V K) :
    e7Data.rootOp K β (Pσ K β ε v) = 0 := by
  ext b
  rw [rootOp_apply hβ]
  by_cases h1 : pr b β = 1
  · rw [if_pos h1, Pσ_apply]
    have h2 : pr (shift (-β) b) β = -1 := pr_shift_neg hβ h1
    rw [if_neg (fun h3 => hε (h3.symm.trans h2))]
    try rfl
  · rw [if_neg h1]
    try rfl

theorem rootOp_Pσ_neg_one {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    e7Data.rootOp K β (Pσ K β (-1) v) = e7Data.rootOp K β v := by
  ext b
  rw [rootOp_apply hβ, rootOp_apply hβ]
  by_cases h1 : pr b β = 1
  · rw [if_pos h1, if_pos h1, Pσ_apply]
    have h2 : pr (shift (-β) b) β = -1 := pr_shift_neg hβ h1
    rw [if_pos h2]
  · rw [if_neg h1, if_neg h1]

theorem rootOp_neg_rootOp {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    e7Data.rootOp K (-β) (e7Data.rootOp K β v) = Pσ K β (-1) v := by
  ext b
  rw [rootOp_apply (isRoot_neg hβ), Pσ_apply]
  by_cases h1 : pr b β = -1
  · have h2 : pr b (-β) = 1 := by rw [pr_neg, h1]; norm_num
    rw [if_pos h2, if_pos h1, rootOp_apply hβ, neg_neg]
    have h3 : pr (shift β b) β = 1 := pr_shift_self hβ h1
    rw [if_pos h3, shift_neg_shift hβ h1]
  · have h2 : ¬ pr b (-β) = 1 := by rw [pr_neg]; omega
    rw [if_neg h2, if_neg h1]

theorem rootOp_rootOp_neg {β : Rt} (hβ : IsRoot .E7 β) (v : V K) :
    e7Data.rootOp K β (e7Data.rootOp K (-β) v) = Pσ K β 1 v := by
  ext b
  rw [rootOp_apply hβ, Pσ_apply]
  by_cases h1 : pr b β = 1
  · have h2 : pr (shift (-β) b) β = -1 := pr_shift_neg hβ h1
    have h3 : pr (shift (-β) b) (-β) = 1 := by rw [pr_neg, h2]; norm_num
    rw [if_pos h1, if_pos h1, rootOp_apply (isRoot_neg hβ), if_pos h3, neg_neg, shift_shift_neg hβ h1]
  · rw [if_neg h1, if_neg h1]

end SigmaBeta

section KerInduction

variable {K : Type} [Field K] [CharP K 2]

theorem ipR_neg_left (α β : Rt) : ipR (-α) β = - ipR α β := by
  rw [ipR, MinData.toWeight_neg, neg_dotProduct]

theorem NOp_cons_apply (β : Rt) (S : List Rt) (v : V K) :
    NOp K (β :: S) v = NOp K S v + e7Data.rootOp K β (tOp K S v) := by
  rw [NOp_eq, NOp_eq, tOp_cons, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, Module.End.one_apply, Module.End.one_apply]
  abel

theorem pr_shift_neg_orth {γ β : Rt} (hγ : IsRoot .E7 γ) (hortho : ipR γ β = 0)
    {b : Fin e7Data.d} (h : pr b γ = 1) : pr (shift (-γ) b) β = pr b β := by
  have h1 : pr b (-γ) = -1 := by rw [pr_neg, h]
  have h0 : MinData.toWeight γ ⬝ᵥ β = 0 := hortho
  rw [pr_shift (isRoot_neg hγ) h1 β, MinData.toWeight_neg, neg_dotProduct, h0, neg_zero, add_zero]

theorem neg_eq_self_V (x : V K) : -x = x :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo (K := K) x)

set_option maxRecDepth 20000 in
theorem ker_NOp_le_aux : ∀ (S : List Rt), SOrth S → ∀ c : V K, NOp K S c = 0 →
    ∃ w : V K, ∃ u ∈ Finsupp.supported K K {a : Fin e7Data.d | perpWt S a},
      c = NOp K S w + u := by
  intro S
  induction S with
  | nil =>
    intro _ c _
    refine ⟨0, c, ?_, by rw [NOp_eq, tOp_nil, sub_self, LinearMap.zero_apply, zero_add]⟩
    rw [Finsupp.mem_supported']
    intro x hx
    exact absurd (fun β hb => absurd hb (by simp)) hx
  | cons β S ih =>
    intro hS c hc
    have hS' : SOrth S := hS.cons
    have hβ : IsRoot .E7 β := hS.head_root
    have hSr : ∀ γ ∈ S, IsRoot .E7 γ := hS'.1
    have hortho : ∀ γ ∈ S, ipR γ β = 0 := fun γ hγ => (ipR_comm γ β).trans (hS.head_orth hγ)
    have hEc : ∀ v : V K, e7Data.rootOp K β (tOp K S v) = tOp K S (e7Data.rootOp K β v) :=
      rootOp_tOp_apply (K := K) hβ hSr (fun γ hγ => (hS.head_orth hγ).ge)
    have hLc : ∀ v : V K, e7Data.rootOp K (-β) (tOp K S v) = tOp K S (e7Data.rootOp K (-β) v) :=
      rootOp_tOp_apply (K := K) (isRoot_neg hβ) hSr
        (fun γ hγ => by rw [ipR_neg_left, hS.head_orth hγ]; norm_num)
    have hPc : ∀ (ε : ℤ) (v : V K), Pσ K β ε (tOp K S v) = tOp K S (Pσ K β ε v) := fun ε v =>
      projP_tOp_apply (K := K) hSr (fun b => pr b β = ε)
        (fun γ hγ b hb => by
          show pr (shift (-γ) b) β = ε ↔ pr b β = ε
          rw [pr_shift_neg_orth (hSr γ hγ) (hortho γ hγ) hb]) v
    have hPN : ∀ (ε : ℤ) (v : V K), Pσ K β ε (NOp K S v) = NOp K S (Pσ K β ε v) := fun ε v =>
      projP_NOp_apply (K := K) hSr (fun b => pr b β = ε)
        (fun γ hγ b hb => by
          show pr (shift (-γ) b) β = ε ↔ pr b β = ε
          rw [pr_shift_neg_orth (hSr γ hγ) (hortho γ hγ) hb]) v
    have hT2 : ∀ v : V K, tOp K S (tOp K S v) = v := tOp_tOp_apply (K := K) hS'
    have hcl : tOp K S c + e7Data.rootOp K β (tOp K S c) = c := by
      have h := hc
      rw [NOp_cons_apply, NOp_eq, LinearMap.sub_apply, Module.End.one_apply] at h
      have h' : tOp K S c + e7Data.rootOp K β (tOp K S c) - c = 0 := by
        rw [← h]; abel
      exact sub_eq_zero.1 h'
    have h1 : tOp K S (Pσ K β (-1) c) = Pσ K β (-1) c := by
      have := congrArg (Pσ K β (-1)) hcl
      rw [map_add, Pσ_rootOp_of_ne hβ (by norm_num), add_zero, hPc] at this
      exact this
    have h0 : tOp K S (Pσ K β 0 c) = Pσ K β 0 c := by
      have := congrArg (Pσ K β 0) hcl
      rw [map_add, Pσ_rootOp_of_ne hβ (by norm_num), add_zero, hPc] at this
      exact this
    have h2 : tOp K S (Pσ K β 1 c) + e7Data.rootOp K β (Pσ K β (-1) c) = Pσ K β 1 c := by
      have := congrArg (Pσ K β 1) hcl
      rw [map_add, hPc, Pσ_one_rootOp hβ] at this
      have e : e7Data.rootOp K β (tOp K S c) = e7Data.rootOp K β (Pσ K β (-1) c) := by
        rw [← rootOp_Pσ_neg_one hβ (tOp K S c), hPc, h1]
      rw [e] at this
      exact this
    set w₁ : V K := e7Data.rootOp K (-β) (tOp K S (Pσ K β 1 c)) with hw₁
    have hT1 : tOp K S w₁ = e7Data.rootOp K (-β) (Pσ K β 1 c) := by
      rw [hw₁, ← hLc, hT2]
    have hT2' : e7Data.rootOp K β (tOp K S w₁) = Pσ K β 1 c := by
      rw [hT1, rootOp_rootOp_neg hβ, Pσ_idem]
    have hw₁' : w₁ = e7Data.rootOp K (-β) (Pσ K β 1 c) + Pσ K β (-1) c := by
      have e : tOp K S (Pσ K β 1 c) = Pσ K β 1 c + e7Data.rootOp K β (Pσ K β (-1) c) := by
        have h3 : tOp K S (Pσ K β 1 c) = Pσ K β 1 c - e7Data.rootOp K β (Pσ K β (-1) c) :=
          eq_sub_of_add_eq h2
        rw [h3, sub_eq_add_neg, neg_eq_self_V]
      rw [hw₁, e, map_add, rootOp_neg_rootOp hβ, Pσ_idem]
    have hN1 : NOp K (β :: S) w₁ = Pσ K β 1 c + Pσ K β (-1) c := by
      rw [NOp_cons_apply, NOp_eq, LinearMap.sub_apply, Module.End.one_apply, hT2', hT1, hw₁']
      have e : e7Data.rootOp K (-β) (Pσ K β 1 c) -
          (e7Data.rootOp K (-β) (Pσ K β 1 c) + Pσ K β (-1) c) + Pσ K β 1 c =
          Pσ K β 1 c + (-Pσ K β (-1) c) := by abel
      rw [e, neg_eq_self_V]
    have hN0 : NOp K S (Pσ K β 0 c) = 0 := by
      rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply, h0, sub_self]
    obtain ⟨w₂, u', hu', hc0⟩ := ih hS' (Pσ K β 0 c) hN0
    have hc0' : Pσ K β 0 c = NOp K S (Pσ K β 0 w₂) + Pσ K β 0 u' := by
      have := congrArg (Pσ K β 0) hc0
      rwa [Pσ_idem, map_add, hPN] at this
    have hNP0 : NOp K (β :: S) (Pσ K β 0 w₂) = NOp K S (Pσ K β 0 w₂) := by
      rw [NOp_cons_apply, hEc, rootOp_Pσ_of_ne hβ (by norm_num), map_zero, add_zero]
    refine ⟨w₁ + Pσ K β 0 w₂, Pσ K β 0 u', ?_, ?_⟩
    · rw [Finsupp.mem_supported'] at hu' ⊢
      intro a ha
      rw [Pσ_apply]
      by_cases hp : pr a β = 0
      · rw [if_pos hp]
        apply hu'
        intro hperp
        apply ha
        intro γ hγ
        rcases List.mem_cons.1 hγ with rfl | hγS
        · exact hp
        · exact hperp γ hγS
      · rw [if_neg hp]
    · calc c = Pσ K β (-1) c + Pσ K β 0 c + Pσ K β 1 c := (Pσ_sum hβ c).symm
        _ = (Pσ K β 1 c + Pσ K β (-1) c) + (NOp K S (Pσ K β 0 w₂) + Pσ K β 0 u') := by
          rw [← hc0']; abel
        _ = NOp K (β :: S) (w₁ + Pσ K β 0 w₂) + Pσ K β 0 u' := by
          rw [map_add, hN1, hNP0]; abel

end KerInduction

section Coord

variable {K : Type} [Field K] [CharP K 2]

theorem tOp_apply_of_no_top {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (v : V K)
    (ν : Fin e7Data.d) (h : ∀ β ∈ S, pr ν β ≠ 1) : (tOp K S v) ν = v ν := by
  induction S with
  | nil => rw [tOp_nil, Module.End.one_apply]
  | cons β S ih =>
    have hβ : IsRoot .E7 β := hS β (List.mem_cons_self ..)
    have hS' : ∀ γ ∈ S, IsRoot .E7 γ := fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ)
    have hνβ : pr ν β ≠ 1 := h β (List.mem_cons_self ..)
    have h' : ∀ γ ∈ S, pr ν γ ≠ 1 := fun γ hγ => h γ (List.mem_cons_of_mem _ hγ)
    rw [tOp_cons, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Finsupp.add_apply,
      rootOp_apply hβ, if_neg hνβ, add_zero]
    exact ih hS' h'

theorem tOp_apply_of_one_top {S : List Rt} (hS : SOrth S) (v : V K) (ν : Fin e7Data.d) {i : Rt}
    (hi : i ∈ S) (h1 : pr ν i = 1) (h : ∀ β ∈ S, β ≠ i → pr ν β ≠ 1) :
    (tOp K S v) ν = v ν + v (shift (-i) ν) := by
  induction S with
  | nil => exact absurd hi (by simp)
  | cons β S ih =>
    have hβ : IsRoot .E7 β := hS.head_root
    have hS' : SOrth S := hS.cons
    have hβS : β ∉ S := by
      obtain ⟨-, hnd, -⟩ := hS
      exact (List.nodup_cons.1 hnd).1
    rw [tOp_cons, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Finsupp.add_apply,
      rootOp_apply hβ]
    rcases List.mem_cons.1 hi with hiβ | hiS
    · rw [hiβ] at h1 ⊢
      rw [if_pos h1]
      have hne : ∀ γ ∈ S, γ ≠ β := fun γ hγ e => hβS (by rw [← e]; exact hγ)
      have hS'r : ∀ γ ∈ S, IsRoot .E7 γ := fun γ hγ => hS'.root hγ
      have hνS : ∀ γ ∈ S, pr ν γ ≠ 1 := fun γ hγ =>
        h γ (List.mem_cons_of_mem _ hγ) (by rw [hiβ]; exact hne γ hγ)
      have hneg : pr ν (-β) = -1 := by rw [pr_neg, h1]
      have hpsh : ∀ γ ∈ S, pr (shift (-β) ν) γ ≠ 1 := by
        intro γ hγ
        have hor : MinData.toWeight β ⬝ᵥ γ = 0 := hS.head_orth hγ
        have hsh := pr_shift (isRoot_neg hβ) hneg γ
        rw [MinData.toWeight_neg, neg_dotProduct, hor, neg_zero, add_zero] at hsh
        rw [hsh]
        exact hνS γ hγ
      rw [tOp_apply_of_no_top (S := S) hS'r v ν hνS,
        tOp_apply_of_no_top (S := S) hS'r v (shift (-β) ν) hpsh]
    · have hβi : β ≠ i := fun e => hβS (by rw [e]; exact hiS)
      rw [if_neg (h β (List.mem_cons_self ..) hβi), add_zero]
      exact ih hS' hiS (fun γ hγ hγi => h γ (List.mem_cons_of_mem _ hγ) hγi)

end Coord

section Range

variable {K : Type} [Field K] [CharP K 2]

private theorem aux_range_pr_shift_orth {i β : Rt} {ν : Fin e7Data.d} (hi : IsRoot .E7 i)
    (h1 : pr ν i = 1) (hiβ : ipR i β = 0) : pr (shift (-i) ν) β = pr ν β := by
  have h1' : pr ν (-i) = -1 := by rw [pr_neg, h1]
  have h0 : MinData.toWeight i ⬝ᵥ β = 0 := hiβ
  rw [pr_shift (isRoot_neg hi) h1' β, MinData.toWeight_neg, neg_dotProduct, h0, neg_zero, add_zero]

private theorem aux_range_rootOp_kill {i β : Rt} {ν : Fin e7Data.d} (hi : IsRoot .E7 i)
    (h1 : pr ν i = 1) (hβ : IsRoot .E7 β) (hiβ : ipR i β = 0) (hν : pr ν β ≠ -1) :
    e7Data.rootOp K β (Finsupp.single (shift (-i) ν) 1) = 0 := by
  have h2 : ¬ (pr (shift (-i) ν) β = -1) := by
    rw [aux_range_pr_shift_orth hi h1 hiβ]
    exact hν
  rw [rootOp_single hβ, if_neg h2]

private theorem aux_range_rootOp_nu {β : Rt} {ν : Fin e7Data.d} (hβ : IsRoot .E7 β)
    (hν : pr ν β ≠ -1) : e7Data.rootOp K β (Finsupp.single ν 1) = 0 := by
  rw [rootOp_single hβ, if_neg hν]

private theorem aux_range_rootOp_top {i : Rt} {ν : Fin e7Data.d} (hi : IsRoot .E7 i)
    (h1 : pr ν i = 1) :
    e7Data.rootOp K i (Finsupp.single (shift (-i) ν) 1) = Finsupp.single ν 1 := by
  rw [rootOp_single hi, if_pos (pr_shift_neg hi h1), shift_shift_neg hi h1]

private theorem aux_range_tOp {i : Rt} {ν : Fin e7Data.d} (hi : IsRoot .E7 i) (h1 : pr ν i = 1)
    (S : List Rt) :
    S.Nodup → (∀ β ∈ S, IsRoot .E7 β) → (∀ β ∈ S, β ≠ i → ipR i β = 0) →
    (∀ β ∈ S, pr ν β ≠ -1) →
    (i ∈ S → tOp K S (Finsupp.single (shift (-i) ν) 1) =
        Finsupp.single (shift (-i) ν) 1 + Finsupp.single ν 1) ∧
    (i ∉ S → tOp K S (Finsupp.single (shift (-i) ν) 1) = Finsupp.single (shift (-i) ν) 1) := by
  induction S with
  | nil =>
    intro _ _ _ _
    refine ⟨fun h => by simp at h, fun _ => ?_⟩
    rw [tOp_nil, Module.End.one_apply]
  | cons β S ih =>
    intro hnd hroot horth hpr
    have hβ : IsRoot .E7 β := hroot β (List.mem_cons_self ..)
    have hβS : β ∉ S := (List.nodup_cons.1 hnd).1
    obtain ⟨ih1, ih2⟩ := ih (List.nodup_cons.1 hnd).2
      (fun γ hγ => hroot γ (List.mem_cons_of_mem _ hγ))
      (fun γ hγ hne => horth γ (List.mem_cons_of_mem _ hγ) hne)
      (fun γ hγ => hpr γ (List.mem_cons_of_mem _ hγ))
    have hν : pr ν β ≠ -1 := hpr β (List.mem_cons_self ..)
    by_cases hβi : β = i
    · have hSi : i ∉ S := fun h => hβS (by rw [hβi]; exact h)
      refine ⟨fun _ => ?_, fun h => absurd (List.mem_cons.2 (Or.inl hβi.symm)) h⟩
      rw [tOp_cons, Module.End.mul_apply, ih2 hSi, hβi, LinearMap.add_apply, Module.End.one_apply,
        aux_range_rootOp_top (K := K) hi h1]
    · have hiβ : ipR i β = 0 := horth β (List.mem_cons_self ..) hβi
      have hE1 := aux_range_rootOp_kill (K := K) hi h1 hβ hiβ hν
      have hE2 := aux_range_rootOp_nu (K := K) hβ hν
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hiS : i ∈ S := (List.mem_cons.1 h).resolve_left (fun e => hβi e.symm)
        rw [tOp_cons, Module.End.mul_apply, ih1 hiS, LinearMap.add_apply, Module.End.one_apply,
          map_add, hE1, hE2]
        simp only [add_zero]
      · have hiS : i ∉ S := fun hS' => h (List.mem_cons_of_mem _ hS')
        rw [tOp_cons, Module.End.mul_apply, ih2 hiS, LinearMap.add_apply, Module.End.one_apply, hE1]
        simp only [add_zero]

theorem tOp_single_bottom {S : List Rt} (hS : SOrth S) {i : Rt} (hi : i ∈ S) (ν : Fin e7Data.d)
    (h1 : pr ν i = 1) (h : ∀ β ∈ S, pr ν β = 0 ∨ pr ν β = 1) :
    tOp K S (Finsupp.single (shift (-i) ν) 1) =
      Finsupp.single (shift (-i) ν) 1 + Finsupp.single ν 1 := by
  have hri : IsRoot .E7 i := hS.root hi
  have hpr : ∀ β ∈ S, pr ν β ≠ -1 := by
    intro β hβ e
    rcases h β hβ with h0 | h0 <;> omega
  have horth : ∀ β ∈ S, β ≠ i → ipR i β = 0 := fun β hβ hne =>
    (ipR_comm i β).trans (hS.2.2 β hβ i hi hne)
  exact (aux_range_tOp (K := K) hri h1 S hS.2.1 hS.1 horth hpr).1 hi

end Range

section Derived

variable {K : Type} [Field K] [CharP K 2]

theorem ker_NOp_le {S : List Rt} (hS : SOrth S) :
    LinearMap.ker (NOp K S) ≤
      LinearMap.range (NOp K S) ⊔ Finsupp.supported K K {a : Fin e7Data.d | perpWt S a} := by
  intro c hc
  obtain ⟨w, u, hu, rfl⟩ := ker_NOp_le_aux S hS c (LinearMap.mem_ker.1 hc)
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ w) hu

theorem ker_NOp_le_L {S : List Rt} (hS : SOrth S) {okD : Rt → Prop} {inL : Fin e7Data.d → Prop}
    [DecidablePred inL] (hSok : ∀ β ∈ S, okD β) (hcl : ClosedL okD inL) {c : V K}
    (hc : c ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a}) (h : NOp K S c = 0) :
    ∃ w ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a},
      ∃ u ∈ Finsupp.supported K K {a : Fin e7Data.d | inL a ∧ perpWt S a}, c = NOp K S w + u := by
  obtain ⟨w₀, u₀, hu₀, hc₀⟩ := ker_NOp_le_aux S hS c h
  have hp : ∀ β ∈ S, ∀ b, pr b β = 1 → (inL (shift (-β) b) ↔ inL b) :=
    fun β hβ b hb => hcl β (hS.1 β hβ) (hSok β hβ) b hb
  have hPc : projP K inL c = c := by
    ext b
    rw [projP_apply]
    by_cases hb : inL b
    · rw [if_pos hb]
    · rw [if_neg hb]
      exact ((Finsupp.mem_supported' K c).1 hc b hb).symm
  refine ⟨projP K inL w₀, ?_, projP K inL u₀, ?_, ?_⟩
  · rw [Finsupp.mem_supported']
    intro x hx
    have hx' : ¬ inL x := hx
    rw [projP_apply, if_neg hx']
  · rw [Finsupp.mem_supported']
    intro x hx
    rw [projP_apply]
    by_cases hxl : inL x
    · rw [if_pos hxl]
      exact (Finsupp.mem_supported' K u₀).1 hu₀ x (fun hperp => hx ⟨hxl, hperp⟩)
    · rw [if_neg hxl]
  · have := congrArg (projP K inL) hc₀
    rwa [hPc, map_add, projP_NOp_apply hS.1 inL hp] at this

end Derived

end CFSG.RankThree.GF2n.Smith81.MinuscT
