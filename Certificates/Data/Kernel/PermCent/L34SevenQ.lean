module

public import Certificates.Data.Kernel.PermCent.L34Twin
public import Certificates.Data.Kernel.PermCent.SplitC

public section

namespace CFSG.Certificates.Kernel.PkCV.L34T

open CFSG.GH74.KGroups.L34

@[expose] noncomputable def sevenF (l7 : List (CV 42)) (sf : CV 42 → Bool) (a : CV 42) : Bool :=
  !powOneC a 2 || sf a || l7.any fun q => eq22C a q q a || eq3C a q a q

@[expose] noncomputable def l7P : List (CV 42) :=
  (elemsC QP).filter fun q => powOneC q 7 && !powOneC q 1

@[expose] noncomputable def sevenQ : Bool := (elemsC QA).all (sevenF l7P fun a => siftC QP a 0)

@[expose] noncomputable def sevenH : Bool :=
  allSplit (levelsC QA) fun t r =>
    !(sqPt t r 0 && sqPt t r 41) || sevenF l7P (fun a => siftC QP a 0) (t * r)

theorem conj_inv_iff {G : Type*} [Group G] (a q : G) : a * q * a⁻¹ = q⁻¹ ↔ a = q * a * q := by
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq, ← mul_assoc, eq_comm]

theorem sevenG_eq (SA SP : List (CV 42)) (sf : CV 42 → Bool) :
    (SA.all fun a => decide (a * a ≠ 1) || sf a ||
      (SP.filter fun q => orderIsP q 7 [7]).any fun q =>
        decide (a * q = q * a) || decide (a * q * a⁻¹ = q⁻¹)) =
      SA.all (sevenF (SP.filter fun q => powOneC q 7 && !powOneC q 1) sf) := by
  have h7 : ∀ q : CV 42, orderIsP q 7 [7] = (powOneC q 7 && !powOneC q 1) := by
    intro q
    rw [orderIsP, pow_fast, List.all_cons, List.all_nil, Bool.and_true, pow_fast]
  have hi : ∀ a q : CV 42, decide (a * q * a⁻¹ = q⁻¹) = eq3C a q a q := by
    intro a q
    rw [eq3C_eq]
    exact decide_eq_decide.mpr (conj_inv_iff a q)
  simp only [h7, hi, comm_fast, ne_eq, decide_not, sq_fast]
  rfl

theorem sevenC_eq_sevenQ : sevenC = sevenQ :=
  sevenG_eq (elemsC QA) (elemsC QP) fun a => siftC QP a 0

theorem sevenH_gen (L : List (List (CV 42))) (l7 : List (CV 42)) (sf : CV 42 → Bool) :
    allSplit L (fun t r => !(sqPt t r 0 && sqPt t r 41) || sevenF l7 sf (t * r)) =
      (productsC L).all (sevenF l7 sf) := by
  apply allSplit_pre
  intro t r h
  cases e : powOneC (t * r) 2
  · simp only [sevenF, e, Bool.not_false, Bool.true_or]
  · rw [sqPt_of (p := 0) (by norm_num) e, sqPt_of (p := 41) (by norm_num) e] at h
    exact absurd h (by decide)

theorem sevenH_eq : sevenH = sevenQ :=
  sevenH_gen (levelsC QA) l7P fun a => siftC QP a 0

end CFSG.Certificates.Kernel.PkCV.L34T

end
