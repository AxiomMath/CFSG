module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalCodes
import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

private def plex_vec (K : Type) [Field K] (a : K) : Fin 2 → K :=
  fun i => if i = 0 then (1 : K) else a

private theorem plex_vec_apply_zero (K : Type) [Field K] (a : K) :
    plex_vec K a 0 = 1 := by
  show (if (0 : Fin 2) = 0 then (1 : K) else a) = 1
  rw [if_pos rfl]

private theorem plex_vec_apply_one (K : Type) [Field K] (a : K) :
    plex_vec K a 1 = a := by
  show (if (1 : Fin 2) = 0 then (1 : K) else a) = a
  rw [if_neg (by decide)]

private theorem plex_vec_ne_zero (K : Type) [Field K] (a : K) : plex_vec K a ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [plex_vec_apply_zero] at h0
  exact (one_ne_zero (α := K)) (by simpa using h0)

private abbrev plex_pt (K : Type) [Field K] (a : K) : Submodule K (Fin 2 → K) :=
  Submodule.span K {plex_vec K a}

private theorem plex_pt_finrank (K : Type) [Field K] (a : K) :
    finrank K (plex_pt K a) = 1 :=
  finrank_span_singleton (plex_vec_ne_zero K a)

private theorem plex_pt_injective (K : Type) [Field K] :
    Function.Injective (plex_pt K) := by
  intro a b h
  have hb : plex_vec K b ∈ Submodule.span K {plex_vec K a} := by
    rw [show Submodule.span K {plex_vec K a} = Submodule.span K {plex_vec K b} from h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hb
  have hc0 : c = 1 := by
    have h0 := congrFun hc 0
    simpa [Pi.smul_apply, smul_eq_mul, plex_vec_apply_zero] using h0
  have h1 := congrFun hc 1
  rw [hc0] at h1
  simpa [plex_vec_apply_one] using h1

private noncomputable def plex_rep (K : Type) [Field K]
    (V : Submodule K (Fin 2 → K)) : K :=
  by classical exact if h : ∃ a : K, plex_pt K a = V then h.choose else 0

private theorem plex_rep_spec (K : Type) [Field K] {V : Submodule K (Fin 2 → K)}
    (h : ∃ a : K, plex_pt K a = V) : plex_pt K (plex_rep K V) = V := by
  unfold plex_rep
  rw [dif_pos h]
  exact h.choose_spec

private theorem plex_eq_rep (K : Type) [Field K] {V : Submodule K (Fin 2 → K)} {a : K}
    (ha : plex_pt K a = V) : a = plex_rep K V := by
  by_cases h : ∃ b : K, plex_pt K b = V
  · exact plex_pt_injective K (ha.trans (plex_rep_spec K h).symm)
  · exact absurd ⟨a, ha⟩ h

private theorem plex_exists_pt_avoid (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (V₁ V₂ : Submodule K (Fin 2 → K)) :
    ∃ a : K, plex_pt K a ≠ V₁ ∧ plex_pt K a ≠ V₂ := by
  obtain ⟨a, _, ha1, ha2⟩ := exists_sg_fixed_avoid (K := K) (f := f) hK hq
    (plex_rep K V₁) (plex_rep K V₂)
  exact ⟨a, fun h => ha1 (plex_eq_rep K h), fun h => ha2 (plex_eq_rep K h)⟩

private noncomputable def plex_flag (K : Type) [Field K] (a : K) : FlagK K 2 where
  E j := if j = 0 then ⊥ else if j = 1 then plex_pt K a else ⊤
  mono := by
    refine monotone_nat_of_le_succ fun j => ?_
    rcases j with _ | _ | k
    · simp
    · simp
    · have h1 : ¬ (k + 2 = 0) := by omega
      have h2 : ¬ (k + 2 + 1 = 0) := by omega
      have h3 : ¬ (k + 2 = 1) := by omega
      have h4 : ¬ (k + 2 + 1 = 1) := by omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      exact le_top
  dim := by
    intro j hj
    interval_cases j <;> simp [plex_pt_finrank, Module.finrank_fin_fun, finrank_top]
  top := by
    intro j hj
    rw [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j = 1)]

private theorem plex_flag_E_one (K : Type) [Field K] (a : K) :
    (plex_flag K a).E 1 = plex_pt K a := by
  show (if (1 : ℕ) = 0 then ⊥ else if (1 : ℕ) = 1 then plex_pt K a else ⊤) =
    plex_pt K a
  rw [if_neg (by norm_num : ¬ (1 : ℕ) = 0), if_pos rfl]

theorem exchA1A1_connected (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((PhanCode.exchA1A1.sys K).restrict (PhanCode.exchA1A1.set K f)).Connected := by
  classical
  intro x y
  obtain ⟨a, hax, hay⟩ := plex_exists_pt_avoid K f hK hq
    (sgS K f 2 (x.1.2.E 1)) (sgS K f 2 (y.1.2.E 1))
  let x₁ : FlagK K 2 := plex_flag K a
  have hx₁ : x₁.E 1 = plex_pt K a := plex_flag_E_one K a
  let c₁ : PhanCode.exchA1A1.set K f := ⟨(x₁, x.1.2), by
    show x₁.E 1 ≠ sgS K f 2 (x.1.2.E 1)
    rw [hx₁]
    exact hax⟩
  let c₂ : PhanCode.exchA1A1.set K f := ⟨(x₁, y.1.2), by
    show x₁.E 1 ≠ sgS K f 2 (y.1.2.E 1)
    rw [hx₁]
    exact hay⟩
  refine ⟨[(Sum.inl (0 : Fin 1), c₁), (Sum.inr (0 : Fin 1), c₂),
    (Sum.inl (0 : Fin 1), y)], ?_, rfl⟩
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact ⟨flagSys_one_adj K x.1.1 x₁ 0, rfl⟩
  · exact ⟨rfl, flagSys_one_adj K x.1.2 y.1.2 0⟩
  · exact ⟨flagSys_one_adj K x₁ y.1.1 0, rfl⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
