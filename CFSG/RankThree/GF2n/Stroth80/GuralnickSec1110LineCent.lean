module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line
import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

omit [Finite G] [(Q.subgroupOf M).Normal] in
private theorem Ctx.Z_le_centralizer_Q (hc : Ctx M Q Z B) :
    Z ≤ Subgroup.centralizer (Q : Set G) := by
  rw [hc.hyp.hZ, cen_eq]
  exact inf_le_right

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.conj_mem_sup_Z_of_commutator_mem_Z (hc : Ctx M Q Z B) {k l : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hlM : l ∈ M)
    (hB : B ≤ ⁅Q, Subgroup.zpowers l⁆ ⊔ Z)
    (hfix : ∀ x ∈ ⁅Q, Subgroup.zpowers l⁆, ⁅k, x⁆ ∈ Z) :
    conjSubgroup k B ≤ B ⊔ Z := by
  have hQM : ⁅Q, Subgroup.zpowers l⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hc.comm_mem_Q (M.zpow_mem hlM n) hx
  have hZN : ⁅Q, Subgroup.zpowers l⁆ ≤ Subgroup.normalizer (Z : Set G) :=
    hQM.trans (hc.hyp.Q_normal.1.trans hc.hyp.Z_normal.2)
  intro y hy
  have hy' : k⁻¹ * y * k ∈ B := mem_conjSubgroup.mp hy
  obtain ⟨x, hx, w, hw, hxw⟩ := exists_mul_of_mem_sup_of_le_normalizer hZN (hB hy')
  have hBxw : x * w ∈ B := hxw.symm ▸ hy'
  have hye : y = k * (x * w) * k⁻¹ := by
    rw [hxw]
    group
  rw [hye]
  have hwk : k * w * k⁻¹ = w := by
    have h1 : k * w = w * k := (Subgroup.mem_centralizer_iff.mp hkZ w hw).symm
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  have e : k * (x * w) * k⁻¹ = ⁅k, x⁆ * (x * w) := by
    have h2 : k * (x * w) * k⁻¹ = (k * x * k⁻¹) * (k * w * k⁻¹) := by group
    rw [h2, hwk, commutatorElement_def]
    group
  rw [e]
  exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right (hfix x hx)) (Subgroup.mem_sup_left hBxw)

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.comm_mem_Q_of_mul_comm_mem_Q (hc : Ctx M Q Z B) {c x b : G} (hcM : c ∈ M)
    (hcb : ⁅c, b⁆ ∈ Q) (hcxb : ⁅c * x, b⁆ ∈ Q) : ⁅x, b⁆ ∈ Q := by
  have h1 : ⁅c * x, b⁆ = c * ⁅x, b⁆ * c⁻¹ * ⁅c, b⁆ := commutatorElement_mul_left_eq_conj_mul c x b
  have h2 : c * ⁅x, b⁆ * c⁻¹ ∈ Q := by
    have h3 := Q.mul_mem hcxb (Q.inv_mem hcb)
    rw [h1] at h3
    have e : (c * ⁅x, b⁆ * c⁻¹ * ⁅c, b⁆) * ⁅c, b⁆⁻¹ = c * ⁅x, b⁆ * c⁻¹ := by group
    rwa [e] at h3
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hcM) ⁅x, b⁆).mpr h2

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.exists_mem_normalizer_of_fix (hc : Ctx M Q Z B) {l : G}
    (hl : l ∈ LB M Q B) (hA : IsA2 Q Z l) {k : G} (hk : k ∈ H0 M Z)
    (hfix : ∀ x ∈ ⁅Q, Subgroup.zpowers l⁆, ⁅k, x⁆ ∈ Z) :
    ∃ (k' p : G), p ∈ Q ∧ k = p * k' ∧ k' ∈ H0 M Z ∧
      k' ∈ Subgroup.normalizer (B : Set G) := by
  have hkM : k ∈ M := hk.1
  have hB'le : conjSubgroup k B ≤ B ⊔ Z :=
    hc.conj_mem_sup_Z_of_commutator_mem_Z hk.2 (hc.LB_le_M hl) (hc.B_le_commutator_of_a2 hl hA)
      hfix
  obtain ⟨p, hpQ, hpB⟩ :=
    hc.exists_conj_of_le_ZB (hc.conj_of_mem hkM) (by rwa [sup_comm] at hB'le)
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have hk'Z : p⁻¹ * k ∈ Subgroup.centralizer (Z : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hpz : p⁻¹ * z = z * p⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hc.Z_le_centralizer_Q hz) p⁻¹ (Q.inv_mem hpQ)
    have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hk.2 z hz).symm
    calc z * (p⁻¹ * k) = z * p⁻¹ * k := by group
      _ = p⁻¹ * z * k := by rw [← hpz]
      _ = p⁻¹ * (z * k) := by group
      _ = p⁻¹ * (k * z) := by rw [← hkz]
      _ = p⁻¹ * k * z := by group
  have hk'B : p⁻¹ * k ∈ Subgroup.normalizer (B : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    show conjSubgroup (p⁻¹ * k) B = B
    rw [conjSubgroup_mul, ← hpB, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  exact ⟨p⁻¹ * k, p, hpQ, by group, ⟨M.mul_mem (M.inv_mem hpM) hkM, hk'Z⟩, hk'B⟩

omit [(Q.subgroupOf M).Normal] in
private theorem Ctx.comm_mem_Q_of_eq_mul (hc : Ctx M Q Z B) {k k' p b : G} (hpQ : p ∈ Q)
    (hbM : b ∈ M) (hk : k = p * k') (h : ⁅k', b⁆ ∈ Q) : ⁅k, b⁆ ∈ Q := by
  have h1 : ⁅k, b⁆ = p * ⁅k', b⁆ * p⁻¹ * ⁅p, b⁆ := by
    rw [hk, commutatorElement_mul_left_eq_conj_mul]
  rw [h1]
  exact Q.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.hyp.Q_normal.1 hpQ)) _).mp h)
    (hc.comm_mem_Q hbM hpQ)

namespace IsLBTorus

private theorem comm_conj_pow_mem_Q {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) {k' : G} (hk'M : k' ∈ M)
    (hk'Z : k' ∈ Subgroup.centralizer (Z : Set G))
    (hk'B : k' ∈ Subgroup.normalizer (B : Set G)) (hk'l : ⁅k', l⁆ ∈ Q) (i : ℕ) :
    ⁅k', y ^ i * l * (y ^ i)⁻¹⁆ ∈ Q := by
  induction i with
  | zero => simpa using hk'l
  | succ j ih =>
    have haLB : y ^ j * l * (y ^ j)⁻¹ ∈ LB M Q B :=
      hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hy.mem_M j)
        (Subgroup.pow_mem _ hy.normalizes_B j) hl
    have hbLB : y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹ ∈ LB M Q B :=
      hc.conj_mem_LB_of_mem_normalizer hy.mem_M hy.normalizes_B haLB
    have hb : y ^ (j + 1) * l * (y ^ (j + 1))⁻¹ =
        y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹ := by
      rw [pow_succ]
      group
    rw [hb]
    have h1 : ⁅y * k' * y⁻¹, y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹⁆ ∈ Q := by
      have e : ⁅y * k' * y⁻¹, y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹⁆ =
          y * ⁅k', y ^ j * l * (y ^ j)⁻¹⁆ * y⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy.mem_M) _).mp ih
    have h2 : ⁅y * k' * y⁻¹ * k'⁻¹, y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹⁆ ∈ Q :=
      hy.comm_centralizes k' hk'Z hk'B (y * (y ^ j * l * (y ^ j)⁻¹) * y⁻¹) hbLB
    have hcM : y * k' * y⁻¹ * k'⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hy.mem_M hk'M) (M.inv_mem hy.mem_M)) (M.inv_mem hk'M)
    refine hc.comm_mem_Q_of_mul_comm_mem_Q hcM h2 ?_
    have e : y * k' * y⁻¹ * k'⁻¹ * k' = y * k' * y⁻¹ := by group
    rw [e]
    exact h1

theorem comm_conj_mem_Q_of_fix {y : G} (hy : IsLBTorus M Q Z B y)
    (hc : Ctx M Q Z B) {l : G} (hl : l ∈ LB M Q B) (hA : IsA2 Q Z l)
    {k : G} (hk : k ∈ H0 M Z) (hkl : ⁅k, l⁆ ∈ Q)
    (hfix : ∀ x ∈ ⁅Q, Subgroup.zpowers l⁆, ⁅k, x⁆ ∈ Z) (i : ℕ) :
    ⁅k, y ^ i * l * (y ^ i)⁻¹⁆ ∈ Q := by
  obtain ⟨k', p, hpQ, hk_eq, hk'H, hk'B⟩ :=
    hc.exists_mem_normalizer_of_fix hl hA hk hfix
  have hk'l : ⁅k', l⁆ ∈ Q :=
    hc.comm_mem_Q_of_mul_comm_mem_Q (hc.hyp.Q_normal.1 hpQ)
      (hc.comm_mem_Q (hc.LB_le_M hl) hpQ) (by rw [← hk_eq]; exact hkl)
  have haLB : y ^ i * l * (y ^ i)⁻¹ ∈ LB M Q B :=
    hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hy.mem_M i)
      (Subgroup.pow_mem _ hy.normalizes_B i) hl
  exact hc.comm_mem_Q_of_eq_mul hpQ (hc.LB_le_M haLB) hk_eq
    (hy.comm_conj_pow_mem_Q hc hl hk'H.1 hk'H.2 hk'B hk'l i)

end IsLBTorus

end CFSG.RankThree.GF2n.Stroth80
