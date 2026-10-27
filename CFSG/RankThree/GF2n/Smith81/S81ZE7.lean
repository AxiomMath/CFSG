module

public import CFSG.RankThree.GF2n.Smith81.S81ZField
public import CFSG.RankThree.GF2n.Smith81.S81ZLayE

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement

variable {K : Type} [Field K]

open _root_.Classical in
@[expose] def Rpos : Finset Rt := (rootFinset .E7).filter fun γ => 0 < ht γ

theorem mem_Rpos {γ : Rt} : γ ∈ Rpos ↔ IsRoot .E7 γ ∧ 0 < ht γ := by
  classical
  simp [Rpos, mem_rootFinset]

theorem ht_le_seventeen : ∀ α ∈ Rpos, ht α ≤ 17 := by
  intro α hα
  have h : ∀ γ, IsRoot .E7 γ → ht γ ≤ 17 :=
    (forall_isRoot_iff fun γ => ht γ ≤ 17).2 (by decide +kernel)
  exact h α (mem_Rpos.1 hα).1

theorem chars_Rpos [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : Chars K Rpos :=
  ⟨fun α hα => chi_surjective (mem_Rpos.1 hα).1,
   fun α hα β hβ hne σ => chi_ne hq (mem_Rpos.1 hα).1 (mem_Rpos.1 hα).2 (mem_Rpos.1 hβ).1
     (mem_Rpos.1 hβ).2 hne σ⟩

theorem URge_comm [CharP K 2] {R : Finset Rt} (hR : Closed R)
    (hab : ∀ α ∈ R, ∀ β ∈ R, ¬ IsRoot .E7 (α + β)) {x y : Gp K} (hx : x ∈ URge K R 1)
    (hy : y ∈ URge K R 1) : x * y = y * x := by
  have key : ∀ x : Gp K, x ∈ URge K R 1 → ∀ y : Gp K, y ∈ URge K R 1 → x * y = y * x := by
    intro x hx
    refine URge_induction (C := fun x => ∀ y : Gp K, y ∈ URge K R 1 → x * y = y * x) hx ?_ ?_ ?_
    · intro α hα _ c y hy
      refine URge_induction (C := fun y => xE α c * y = y * xE α c) hy ?_ ?_ ?_
      · intro β hβ _ d
        have hne : α + β ≠ 0 := add_ne_zero_of_pos hR hα hβ
        have h1 := comm_xE (K := K) (hR.root α hα) (hR.root β hβ) hne c d
        rw [if_neg (hab α hα β hβ)] at h1
        exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
      · simp
      · intro y y' hy hy'
        calc xE α c * (y * y') = (xE α c * y) * y' := by group
          _ = (y * xE α c) * y' := by rw [hy]
          _ = y * (xE α c * y') := by group
          _ = y * (y' * xE α c) := by rw [hy']
          _ = (y * y') * xE α c := by group
    · intro y _
      simp
    · intro x x' hx hx' y hy
      calc x * x' * y = x * (x' * y) := by group
        _ = x * (y * x') := by rw [hx' y hy]
        _ = (x * y) * x' := by group
        _ = (y * x) * x' := by rw [hx y hy]
        _ = y * (x * x') := by group
  exact key x hx y hy

theorem isStab_URge [CharP K 2] {R : Finset Rt} (hR : Closed R)
    (hab : ∀ α ∈ R, ∀ β ∈ R, ¬ IsRoot .E7 (α + β)) : IsStab R (URge K R 1) where
  le := le_rfl
  tau t e he := conj_tau_mem_URge hR t he
  norm u hu e he := conj_mem_URge hR hu he
  comm e he e' he' := URge_comm hR hab he he'

end CFSG.RankThree.GF2n.Smith81.S81Z
