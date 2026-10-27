module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_Q1_iff (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) {x : G} :
    x ∈ Q1 hc t ↔ x ∈ Q ∧ ⁅t, x⁆ ∈ Z := by
  constructor
  · rintro ⟨hxQ, hx⟩
    exact ⟨hxQ, hx t (Subgroup.mem_zpowers t)⟩
  · rintro ⟨hxQ, hx⟩
    refine ⟨hxQ, fun s hs => ?_⟩
    let S : Subgroup G :=
      { carrier := {s | s ∈ M ∧ ⁅s, x⁆ ∈ Z}
        mul_mem' := by
          rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
          refine ⟨M.mul_mem haM hbM, ?_⟩
          have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          refine Z.mul_mem ?_ ha
          have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 haM) _).mp hb
          simpa using this
        one_mem' := ⟨M.one_mem, by simpa [commutatorElement_def] using Z.one_mem⟩
        inv_mem' := by
          rintro a ⟨haM, ha⟩
          refine ⟨M.inv_mem haM, ?_⟩
          have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [e]
          have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem haM)) _).mp
            (Z.inv_mem ha)
          simpa using this }
    have htS : t ∈ S := ⟨htM, hx⟩
    exact (Subgroup.zpowers_le.mpr htS hs).2

theorem Ctx.comm_mem_Q (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) {x : G} (hx : x ∈ Q) :
    ⁅x, t⁆ ∈ Q := by
  have h1 : t * x⁻¹ * t⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) _).mp
    (Q.inv_mem hx)
  rw [show ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) by rw [commutatorElement_def]; group]
  exact Q.mul_mem hx h1

theorem Ctx.comm_mul_mem_Z (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) : ⁅x * y, t⁆ * (⁅x, t⁆ * ⁅y, t⁆)⁻¹ ∈ Z := by
  set x' := t * x * t⁻¹ with hx'
  set y' := t * y * t⁻¹ with hy'
  have hx'Q : x' ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) _).mp hx
  have hy'Q : y' ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) _).mp hy
  have hcomm : ⁅y * y'⁻¹, x'⁻¹⁆ ∈ Z :=
    hc.hyp.toHyp79.comm_mem_V (Q.mul_mem hy (Q.inv_mem hy'Q)) (Q.inv_mem hx'Q)
  have e : ⁅x * y, t⁆ * (⁅x, t⁆ * ⁅y, t⁆)⁻¹ = x * ⁅y * y'⁻¹, x'⁻¹⁆ * x⁻¹ := by
    simp only [commutatorElement_def, hx', hy']
    group
  rw [e]
  have h1 := hc.conj_Z_of_mem_Q hx hcomm
  have e2 : x * ⁅y * y'⁻¹, x'⁻¹⁆ * x⁻¹ = x * ⁅y * y'⁻¹, x'⁻¹⁆ * x⁻¹ := rfl
  rw [e2, h1]
  exact hcomm

theorem Ctx.comm_conj_mem_Z (hc : Ctx M Q Z B) {t r : G} (htM : t ∈ M) (hrM : r ∈ M)
    (hrt : ⁅r⁻¹, t⁆ ∈ Q) {x : G} (hx : x ∈ Q) :
    ⁅r * x * r⁻¹, t⁆ * (r * ⁅x, t⁆ * r⁻¹)⁻¹ ∈ Z := by
  set d := ⁅r⁻¹, t⁆ with hd
  set x' := t * x * t⁻¹ with hx'
  have hx'Q : x' ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) _).mp hx
  have hcomm : ⁅d, x'⁻¹⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hrt (Q.inv_mem hx'Q)
  have e : ⁅r * x * r⁻¹, t⁆ * (r * ⁅x, t⁆ * r⁻¹)⁻¹ = r * (x * ⁅d, x'⁻¹⁆ * x⁻¹) * r⁻¹ := by
    simp only [commutatorElement_def, hd, hx']
    group
  rw [e, hc.conj_Z_of_mem_Q hx hcomm]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) _).mp hcomm

end CFSG.RankThree.GF2n.Stroth80
