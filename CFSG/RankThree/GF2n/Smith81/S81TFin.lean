module

public import CFSG.RankThree.GF2n.Smith81.S81TDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


abbrev posR (α : Rt) : Prop := ∀ i, 0 ≤ α i

abbrev inAS (S : List Rt) (α : Rt) : Prop := ∀ β ∈ S, 0 ≤ ipR α β

abbrev inAplus (S : List Rt) (α : Rt) : Prop :=
  (∀ β ∈ S, ipR α β = 0 ∨ ipR α β = 1) ∧ ∃ β ∈ S, ipR α β = 1

abbrev inPerpS (S : List Rt) (α : Rt) : Prop := ∀ β ∈ S, ipR α β = 0

abbrev StarProp (okD : Rt → Prop) (inL : Fin e7Data.d → Prop) (S : List Rt) : Prop :=
  ∀ a : Fin e7Data.d, inL a → perpWt S a →
    ∃ k : Fin 126, okD (rt k) ∧ inAplus S (rt k) ∧ pr a (rt k) = -1

abbrev Star2Prop (okD : Rt → Prop) (inL : Fin e7Data.d → Prop) (S : List Rt) : Prop :=
  ∀ a : Fin e7Data.d, inL a → perpWt S a →
    ∃ k : Fin 126, okD (rt k) ∧ inPerpS S (rt k) ∧ pr a (rt k) = 1

abbrev cover1 (okD : Rt → Prop) (S : List Rt) (α : Rt) : Prop :=
  ∃ k₁ : Fin 126, ∃ k₂ : Fin 126, rt k₁ + rt k₂ = α ∧ okD (rt k₁) ∧ okD (rt k₂) ∧
    inAS S (rt k₁) ∧ inAS S (rt k₂)

@[expose] def A2list (okD : Rt → Prop) [DecidablePred okD] (S : List Rt) : List Rt :=
  ((List.finRange 126).filter fun k =>
    decide (okD (rt k) ∧ posR (rt k) ∧ inAS S (rt k) ∧ (cover1 okD S (rt k) ∨ inPerpS S (rt k)))).map rt

theorem mem_A2list {okD : Rt → Prop} [DecidablePred okD] {S : List Rt} {α : Rt} :
    α ∈ A2list okD S ↔ ∃ k : Fin 126, rt k = α ∧ okD α ∧ posR α ∧ inAS S α ∧
      (cover1 okD S α ∨ inPerpS S α) := by
  unfold A2list
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, rfl, hk⟩
  · rintro ⟨k, rfl, hk⟩
    exact ⟨k, hk, rfl⟩

abbrev inM (inL : Fin e7Data.d → Prop) (A2 S : List Rt) (a : Fin e7Data.d) : Prop :=
  inL a ∧ (∃ β ∈ S, pr a β ≠ 0) ∧ ∀ α ∈ A2, pr a α ≠ -1

abbrev inMtop (inL : Fin e7Data.d → Prop) (A2 S : List Rt) (a : Fin e7Data.d) : Prop :=
  inM inL A2 S a ∧ ∀ β ∈ S, pr a β ≠ -1

abbrev NoMixed (inL : Fin e7Data.d → Prop) (A2 S : List Rt) : Prop :=
  ∀ a a' : Fin e7Data.d, inM inL A2 S a → inM inL A2 S a' → ∀ β ∈ S, ∀ γ ∈ S,
    pr a β = 1 → pr a γ = -1 →
      e7Data.wt a' ≠ e7Data.wt a - MinData.toWeight β + MinData.toWeight γ

abbrev CliqueOK (inL : Fin e7Data.d → Prop) (A2 S : List Rt) : Prop :=
  ∀ a a' : Fin e7Data.d, inMtop inL A2 S a → inMtop inL A2 S a' → a ≠ a' →
    ∃ k : Fin 126, MinData.toWeight (rt k) = e7Data.wt a' - e7Data.wt a ∧
      ∀ ξ : Fin e7Data.d, inMtop inL A2 S ξ → ξ ≠ a → ξ ≠ a' → pr ξ (rt k) = 0

abbrev Two (inL : Fin e7Data.d → Prop) (S : List Rt) : Prop :=
  ∀ a : Fin e7Data.d, inL a → (S.filter fun β => decide (pr a β ≠ 0)).length ≤ 2

abbrev rho2 : Rt := ![34, 49, 66, 96, 75, 52, 27]

theorem hgt_pos : ∀ k : Fin 126, posR (rt k) → 0 < MinData.toWeight (rt k) ⬝ᵥ rho2 := by
  unfold posR
  decide +kernel

abbrev okD5 : Rt → Prop := fun _ => True

abbrev inL5 : Fin e7Data.d → Prop := fun _ => True

abbrev okD4 : Rt → Prop := fun α => α node1 = 0

abbrev inL4 : Fin e7Data.d → Prop := fun a => a ∈ idx0

abbrev K12Cond (okD : Rt → Prop) [DecidablePred okD] (inL : Fin e7Data.d → Prop) (S : List Rt) : Prop :=
  (∀ β ∈ S, ∃ k : Fin 126, rt k = β) ∧ S.Nodup ∧ (∀ β ∈ S, ∀ γ ∈ S, β ≠ γ → ipR β γ = 0) ∧
  (∀ β ∈ S, okD β) ∧ StarProp okD inL S ∧ Star2Prop okD inL S ∧ Two inL S ∧
  NoMixed inL (A2list okD S) S ∧ CliqueOK inL (A2list okD S) S ∧
  (∀ a : Fin e7Data.d, inL a → cntW S a (-(e7Data.wt a)) % 2 = 0)

abbrev K3Cond (okD : Rt → Prop) (inL : Fin e7Data.d → Prop) (S : List Rt) : Prop :=
  (∀ β ∈ S, ∃ k : Fin 126, rt k = β) ∧ S.Nodup ∧ (∀ β ∈ S, ∀ γ ∈ S, β ≠ γ → ipR β γ = 0) ∧
  (∀ β ∈ S, okD β) ∧ (∀ a : Fin e7Data.d, inL a → ∃ β ∈ S, pr a β ≠ 0) ∧
  (∃ b : Fin e7Data.d, inL b ∧ cntW S b (-(e7Data.wt b)) % 2 = 1)

end CFSG.RankThree.GF2n.Smith81.MinuscT
