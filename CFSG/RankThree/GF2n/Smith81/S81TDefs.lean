module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


abbrev Rt : Type := Fin (Tag.rank .E7) → ℤ

abbrev ipR (α β : Rt) : ℤ := MinData.toWeight α ⬝ᵥ β

abbrev rt (k : Fin 126) : Rt := (Tag.rootCertificate .E7).root k

@[expose] def SOrth (S : List Rt) : Prop :=
  (∀ β ∈ S, IsRoot .E7 β) ∧ S.Nodup ∧ ∀ β ∈ S, ∀ γ ∈ S, β ≠ γ → ipR β γ = 0

section Defs

variable (K : Type) [Field K]

@[expose] def tOp (S : List Rt) : Module.End K (V K) :=
  (S.map fun β => (1 : Module.End K (V K)) + e7Data.rootOp K β).prod

@[expose] def NOp (S : List Rt) : Module.End K (V K) := tOp K S - 1

@[expose] def tS (S : List Rt) : (Module.End K (V K))ˣ :=
  (S.map fun β => e7Data_valid.xu K β 1).prod

end Defs

@[expose] def cntW : List Rt → Fin e7Data.d → (Fin (Tag.rank .E7) → ℤ) → ℕ
  | [], a, w => if e7Data.wt a = w then 1 else 0
  | β :: S, a, w => cntW S a w + if w ⬝ᵥ β = 1 then cntW S a (w - MinData.toWeight β) else 0

abbrev perpWt (S : List Rt) (a : Fin e7Data.d) : Prop := ∀ β ∈ S, pr a β = 0

@[expose] def ClosedL (okD : Rt → Prop) (inL : Fin e7Data.d → Prop) : Prop :=
  ∀ γ : Rt, IsRoot .E7 γ → okD γ → ∀ b : Fin e7Data.d, pr b γ = 1 → (inL (shift (-γ) b) ↔ inL b)

@[expose] def GrpR (K : Type) [Field K] (okD : Rt → Prop) : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ β : Rt, IsRoot .E7 β ∧ okD β ∧ ∃ c : K, g = e7Data_valid.xu K β c}

section Basic

variable {K : Type} [Field K]

theorem tOp_nil : tOp K [] = 1 := by simp [tOp]

theorem tOp_cons (β : Rt) (S : List Rt) :
    tOp K (β :: S) = (1 + e7Data.rootOp K β) * tOp K S := by simp [tOp]

theorem tS_nil : tS K [] = 1 := by simp [tS]

theorem tS_cons (β : Rt) (S : List Rt) :
    tS K (β :: S) = e7Data_valid.xu K β 1 * tS K S := by simp [tS]

theorem tS_val (S : List Rt) :
    ((tS K S : (Module.End K (V K))ˣ) : Module.End K (V K)) = tOp K S := by
  induction S with
  | nil => rw [tS_nil, tOp_nil]; rfl
  | cons β S ih => rw [tS_cons, tOp_cons, Units.val_mul, ih, e7Data_valid.xu_val, one_smul]

theorem tS_mem (S : List Rt) : tS K S ∈ EGrp K := by
  induction S with
  | nil => rw [tS_nil]; exact one_mem _
  | cons β S ih => rw [tS_cons]; exact mul_mem (e7Data_valid.xu_mem K β 1) ih

theorem SOrth.cons {β : Rt} {S : List Rt} (h : SOrth (β :: S)) : SOrth S := by
  obtain ⟨hr, hnd, ho⟩ := h
  exact ⟨fun γ hγ => hr γ (List.mem_cons_of_mem _ hγ), (List.nodup_cons.1 hnd).2,
    fun γ hγ δ hδ hne => ho γ (List.mem_cons_of_mem _ hγ) δ (List.mem_cons_of_mem _ hδ) hne⟩

theorem SOrth.head_root {β : Rt} {S : List Rt} (h : SOrth (β :: S)) : IsRoot .E7 β :=
  h.1 β (List.mem_cons_self ..)

theorem SOrth.head_orth {β : Rt} {S : List Rt} (h : SOrth (β :: S)) {γ : Rt} (hγ : γ ∈ S) :
    ipR β γ = 0 := by
  obtain ⟨-, hnd, ho⟩ := h
  have hne : β ≠ γ := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hγ)
  exact ho β (List.mem_cons_self ..) γ (List.mem_cons_of_mem _ hγ) hne

theorem SOrth.root {S : List Rt} (h : SOrth S) {β : Rt} (hβ : β ∈ S) : IsRoot .E7 β := h.1 β hβ

theorem ipR_self {α : Rt} (hα : IsRoot .E7 α) : ipR α α = 2 := form_self_root posDef_cartan_E7 hα

theorem ipR_comm (α β : Rt) : ipR α β = ipR β α := form_comm posDef_cartan_E7 α β

theorem ipR_neg_right (α β : Rt) : ipR α (-β) = - ipR α β := by simp [ipR]

theorem not_isRoot_add_of_ipR {α β : Rt} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (h : 0 ≤ ipR α β) :
    ¬ IsRoot .E7 (α + β) := by
  intro hr
  have h1 := form_self_root posDef_cartan_E7 hr
  rw [form_add_self posDef_cartan_E7, form_self_root posDef_cartan_E7 hα,
    form_self_root posDef_cartan_E7 hβ] at h1
  have h2 : MinData.toWeight α ⬝ᵥ β = ipR α β := rfl
  omega

theorem add_ne_zero_of_ipR {α β : Rt} (hα : IsRoot .E7 α) (h : 0 ≤ ipR α β) : α + β ≠ 0 := by
  intro h0
  have hβ : β = -α := eq_neg_of_add_eq_zero_right h0
  rw [hβ, ipR_neg_right, ipR_self hα] at h
  omega

theorem rootOp_comm {α β : Rt} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (h : 0 ≤ ipR α β) :
    e7Data.rootOp K α * e7Data.rootOp K β = e7Data.rootOp K β * e7Data.rootOp K α :=
  (e7Data_valid.pairRel (R := K) hα hβ (add_ne_zero_of_ipR hα h)).2 (not_isRoot_add_of_ipR hα hβ h)

theorem rootOp_comm_tOp {α : Rt} (hα : IsRoot .E7 α) {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β)
    (h : ∀ β ∈ S, 0 ≤ ipR α β) : e7Data.rootOp K α * tOp K S = tOp K S * e7Data.rootOp K α := by
  induction S with
  | nil => simp [tOp_nil]
  | cons β S ih =>
    rw [tOp_cons]
    have h1 : e7Data.rootOp K α * (1 + e7Data.rootOp K β) =
        (1 + e7Data.rootOp K β) * e7Data.rootOp K α := by
      rw [mul_add, add_mul, mul_one, one_mul,
        rootOp_comm hα (hS β (List.mem_cons_self ..)) (h β (List.mem_cons_self ..))]
    rw [← mul_assoc, h1, mul_assoc,
      ih (fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ)) (fun γ hγ => h γ (List.mem_cons_of_mem _ hγ)),
      ← mul_assoc]

theorem NOp_eq (S : List Rt) : NOp K S = tOp K S - 1 := rfl

theorem rootOp_comm_NOp {α : Rt} (hα : IsRoot .E7 α) {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β)
    (h : ∀ β ∈ S, 0 ≤ ipR α β) : e7Data.rootOp K α * NOp K S = NOp K S * e7Data.rootOp K α := by
  rw [NOp_eq, mul_sub, sub_mul, mul_one, one_mul, rootOp_comm_tOp hα hS h]

variable [CharP K 2]

theorem add_self_eq_zero_of_charTwo {M : Type*} [AddCommGroup M] [Module K M] (x : M) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

theorem one_add_rootOp_mul_self (β : Rt) :
    ((1 : Module.End K (V K)) + e7Data.rootOp K β) * (1 + e7Data.rootOp K β) = 1 := by
  have h := e7Data_valid.xu_add K β 1 1
  rw [one_add_one_eq_two, CharTwo.two_eq_zero, e7Data_valid.xu_zero] at h
  have h2 := congrArg (fun u : (Module.End K (V K))ˣ => (u : Module.End K (V K))) h
  simp only [Units.val_mul, Units.val_one, e7Data_valid.xu_val, one_smul] at h2
  rw [← h2]

theorem tOp_mul_self {S : List Rt} (hS : SOrth S) : tOp K S * tOp K S = 1 := by
  induction S with
  | nil => simp [tOp_nil]
  | cons β S ih =>
    have hS' := hS.cons
    have hβ := hS.head_root
    have hc : e7Data.rootOp K β * tOp K S = tOp K S * e7Data.rootOp K β :=
      rootOp_comm_tOp hβ hS'.1 (fun γ hγ => (hS.head_orth hγ).ge)
    have h1 : (1 + e7Data.rootOp K β) * tOp K S = tOp K S * (1 + e7Data.rootOp K β) := by
      rw [add_mul, mul_add, one_mul, mul_one, hc]
    have h2 := one_add_rootOp_mul_self (K := K) β
    have h3 : tOp K S * (1 + e7Data.rootOp K β) = (1 + e7Data.rootOp K β) * tOp K S := by
      rw [mul_add, add_mul, mul_one, one_mul, hc]
    calc tOp K (β :: S) * tOp K (β :: S)
        = (1 + e7Data.rootOp K β) * (tOp K S * ((1 + e7Data.rootOp K β) * tOp K S)) := by
          rw [tOp_cons, mul_assoc]
      _ = (1 + e7Data.rootOp K β) * ((1 + e7Data.rootOp K β) * (tOp K S * tOp K S)) := by
          rw [← mul_assoc (tOp K S), h3, mul_assoc]
      _ = 1 := by rw [ih hS', mul_one, h2]

theorem NOp_mul_self {S : List Rt} (hS : SOrth S) : NOp K S * NOp K S = 0 := by
  have h := tOp_mul_self (K := K) hS
  have hneg : ∀ x : Module.End K (V K), -x = x := fun x =>
    neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo (K := K) x)
  have h1 : NOp K S = tOp K S + 1 := by rw [NOp_eq, sub_eq_add_neg, hneg]
  have key : (tOp K S + 1) * (tOp K S + 1) = (1 + 1) + (tOp K S + tOp K S) := by
    rw [add_mul, mul_add, mul_add, h, mul_one, one_mul, one_mul]
    abel
  rw [h1, key, add_self_eq_zero_of_charTwo (K := K) (1 : Module.End K (V K)),
    add_self_eq_zero_of_charTwo (K := K) (tOp K S), add_zero]

theorem tOp_single_apply {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (a b : Fin e7Data.d) :
    (tOp K S (Finsupp.single a 1)) b = (cntW S a (e7Data.wt b) : K) := by
  induction S generalizing b with
  | nil =>
    rw [tOp_nil, Module.End.one_apply, Finsupp.single_apply]
    simp only [cntW]
    by_cases h : a = b
    · subst h; simp
    · have h' : e7Data.wt a ≠ e7Data.wt b := fun e => h (wt_injective e)
      simp [h, h']
  | cons β S ih =>
    have hβ := hS β (List.mem_cons_self ..)
    have hS' : ∀ γ ∈ S, IsRoot .E7 γ := fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ)
    rw [tOp_cons, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, Finsupp.add_apply,
      rootOp_apply hβ, ih hS' b]
    simp only [cntW]
    by_cases h : pr b β = 1
    · have h' : e7Data.wt b ⬝ᵥ β = 1 := h
      have hw : e7Data.wt (shift (-β) b) = e7Data.wt b - MinData.toWeight β := by
        have := wt_shift (isRoot_neg hβ) (show pr b (-β) = -1 by rw [pr_neg, h])
        rw [this, MinData.toWeight_neg, sub_eq_add_neg]
      rw [if_pos h, if_pos h', ih hS' (shift (-β) b), hw]
      push_cast
      rfl
    · have h' : ¬ (e7Data.wt b ⬝ᵥ β = 1) := h
      rw [if_neg h, if_neg h']
      push_cast
      simp

@[expose] def projP (K : Type) [Field K] (p : Fin e7Data.d → Prop) [DecidablePred p] :
    Module.End K (V K) where
  toFun v := Finsupp.filter p v
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem projP_apply (p : Fin e7Data.d → Prop) [DecidablePred p] (v : V K) (b : Fin e7Data.d) :
    projP K p v b = if p b then v b else 0 := Finsupp.filter_apply p v b

theorem projP_rootOp {γ : Rt} (hγ : IsRoot .E7 γ) (p : Fin e7Data.d → Prop) [DecidablePred p]
    (hp : ∀ b, pr b γ = 1 → (p (shift (-γ) b) ↔ p b)) (v : V K) :
    projP K p (e7Data.rootOp K γ v) = e7Data.rootOp K γ (projP K p v) := by
  ext b
  rw [projP_apply, rootOp_apply hγ, rootOp_apply hγ, projP_apply]
  by_cases h : pr b γ = 1
  · simp only [if_pos h]
    by_cases hpb : p b
    · rw [if_pos hpb, if_pos ((hp b h).2 hpb)]
    · rw [if_neg hpb, if_neg (fun hh => hpb ((hp b h).1 hh))]
  · simp only [if_neg h]
    split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem projP_mul_rootOp {γ : Rt} (hγ : IsRoot .E7 γ) (p : Fin e7Data.d → Prop) [DecidablePred p]
    (hp : ∀ b, pr b γ = 1 → (p (shift (-γ) b) ↔ p b)) :
    projP K p * e7Data.rootOp K γ = e7Data.rootOp K γ * projP K p :=
  LinearMap.ext fun v => projP_rootOp hγ p hp v

theorem projP_mul_tOp {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (p : Fin e7Data.d → Prop)
    [DecidablePred p] (hp : ∀ β ∈ S, ∀ b, pr b β = 1 → (p (shift (-β) b) ↔ p b)) :
    projP K p * tOp K S = tOp K S * projP K p := by
  induction S with
  | nil => simp [tOp_nil]
  | cons β S ih =>
    have hβ := hS β (List.mem_cons_self ..)
    have hc := projP_mul_rootOp (K := K) hβ p (hp β (List.mem_cons_self ..))
    have h1 : projP K p * (1 + e7Data.rootOp K β) = (1 + e7Data.rootOp K β) * projP K p := by
      rw [mul_add, add_mul, mul_one, one_mul, hc]
    rw [tOp_cons, ← mul_assoc, h1, mul_assoc,
      ih (fun γ hγ => hS γ (List.mem_cons_of_mem _ hγ))
        (fun γ hγ => hp γ (List.mem_cons_of_mem _ hγ)),
      ← mul_assoc]

theorem projP_mul_NOp {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (p : Fin e7Data.d → Prop)
    [DecidablePred p] (hp : ∀ β ∈ S, ∀ b, pr b β = 1 → (p (shift (-β) b) ↔ p b)) :
    projP K p * NOp K S = NOp K S * projP K p := by
  rw [NOp_eq, mul_sub, sub_mul, mul_one, one_mul, projP_mul_tOp hS p hp]

set_option maxRecDepth 20000 in
theorem rootOp_tOp_apply {α : Rt} (hα : IsRoot .E7 α) {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β)
    (h : ∀ β ∈ S, 0 ≤ ipR α β) (v : V K) :
    e7Data.rootOp K α (tOp K S v) = tOp K S (e7Data.rootOp K α v) :=
  LinearMap.congr_fun (rootOp_comm_tOp hα hS h) v

set_option maxRecDepth 20000 in
theorem rootOp_NOp_apply {α : Rt} (hα : IsRoot .E7 α) {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β)
    (h : ∀ β ∈ S, 0 ≤ ipR α β) (v : V K) :
    e7Data.rootOp K α (NOp K S v) = NOp K S (e7Data.rootOp K α v) :=
  LinearMap.congr_fun (rootOp_comm_NOp hα hS h) v

set_option maxRecDepth 20000 in
theorem tOp_tOp_apply {S : List Rt} (hS : SOrth S) (v : V K) : tOp K S (tOp K S v) = v := by
  have h := LinearMap.congr_fun (tOp_mul_self (K := K) hS) v
  rw [Module.End.mul_apply, Module.End.one_apply] at h
  exact h

set_option maxRecDepth 20000 in
theorem projP_tOp_apply {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (p : Fin e7Data.d → Prop)
    [DecidablePred p] (hp : ∀ β ∈ S, ∀ b, pr b β = 1 → (p (shift (-β) b) ↔ p b)) (v : V K) :
    projP K p (tOp K S v) = tOp K S (projP K p v) :=
  LinearMap.congr_fun (projP_mul_tOp hS p hp) v

set_option maxRecDepth 20000 in
theorem projP_NOp_apply {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) (p : Fin e7Data.d → Prop)
    [DecidablePred p] (hp : ∀ β ∈ S, ∀ b, pr b β = 1 → (p (shift (-β) b) ↔ p b)) (v : V K) :
    projP K p (NOp K S v) = NOp K S (projP K p v) :=
  LinearMap.congr_fun (projP_mul_NOp hS p hp) v

end Basic

end CFSG.RankThree.GF2n.Smith81.MinuscT
