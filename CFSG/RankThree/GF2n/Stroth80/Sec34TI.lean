module

public import CFSG.RankThree.GF2n.Stroth80.Sec36

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_LB_eq_of_le_sup_Z (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M)
    (hle : conjSubgroup m B ≤ B ⊔ Z) : conjSubgroup m (LB M Q B) = LB M Q B := by
  have hle' : conjSubgroup m B ≤ Z ⊔ B := by rwa [sup_comm]
  obtain ⟨p, hp, hpB⟩ := hc.exists_conj_of_le_ZB (hc.conj_of_mem hm) hle'
  have hpL : p ∈ LB M Q B := Subgroup.mem_sup_left hp
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hp
  have hLp : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpL)
  rw [← hc.LB_conj hm, ← hpB, hc.LB_conj hpM, hLp]

theorem Ctx.LB_inf_conj_eq_Q (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M)
    (hnc : ∃ x ∈ conjSubgroup m B, ∃ y ∈ B, x * y ≠ y * x) :
    LB M Q B ⊓ conjSubgroup m (LB M Q B) = Q := by
  have hc' := hc.conj_of_mem hm
  rw [← hc.LB_conj hm]
  refine le_antisymm (fun t ht => ?_)
    (le_inf (fun x hx => Subgroup.mem_sup_left hx) (fun x hx => Subgroup.mem_sup_left hx))
  by_contra htQ
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ht.1
  have hsQ : s ∉ Q := fun h' => htQ (Q.mul_mem h' hy)
  have hsL : s ∈ LB M Q (conjSubgroup m B) := by
    have hyL : y⁻¹ ∈ LB M Q (conjSubgroup m B) := Subgroup.mem_sup_left (Q.inv_mem hy)
    have := (LB M Q (conjSubgroup m B)).mul_mem ht.2 hyL
    rwa [mul_inv_cancel_right] at this
  exact hc'.core_3_6 hc hnc hs.1 hs.2 hsQ fun b hb => hc'.comm_B_mem_Z hsL hb

theorem Ctx.isTIMod_LB_of_orth (hc : Ctx M Q Z B)
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z) : IsTIMod M Q (LB M Q B) := by
  intro m hm
  by_cases hle : conjSubgroup m B ≤ B ⊔ Z
  · right
    rw [hc.conj_LB_eq_of_le_sup_Z hm hle, inf_idem]
  · left
    refine hc.LB_inf_conj_eq_Q hm ?_
    by_contra hcon
    push Not at hcon
    exact hle (horth m hm hcon)

theorem Ctx.isTIMod_LB (hc : Ctx M Q Z B) {n : ℕ} (_hw : Width Q Z n) (_hn : 2 < n)
    (_hno : NoA2 Q Z (LB M Q B))
    (horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z) : IsTIMod M Q (LB M Q B) :=
  hc.isTIMod_LB_of_orth horth

end CFSG.RankThree.GF2n.Stroth80
