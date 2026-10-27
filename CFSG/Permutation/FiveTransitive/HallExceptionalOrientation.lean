module

public import CFSG.Permutation.FiveTransitive.HallExceptionalContradiction

public section

namespace CFSG

namespace FiveTransitive.Research.HallExceptionalOrientation

open MulAction
open Research.OddFourInvolutionGeometry
open Research.HallExceptionalContradiction

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_oriented_quarterTurn
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q r : X) (hap : a • p = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hD : MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r})
    (y : X) (hya : a • y ≠ y)
    (u : G)
    (huY : u • y = b • y)
    (huAY : u • (a • y) = (a * b) • y)
    (huSq : u ^ 2 = a)
    (hua : u * a = a * u)
    (hub : u * b = (a * b) * u) :
    ∃ u' : G,
      (u' = u ∨ u' = a * u) ∧
      u' • e 0 = e 0 ∧ u' • e 1 = e 1 ∧ u' • r = r ∧
      u' • e 2 = q ∧ u' • q = e 3 ∧
      u' • e 3 = p ∧ u' • p = e 2 := by
  classical
  have ha0 : a • e 0 = e 0 := by rw [haBase]; rfl
  have ha1 : a • e 1 = e 1 := by rw [haBase]; rfl
  have ha2 : a • e 2 = e 3 := by rw [haBase]; rfl
  have ha3 : a • e 3 = e 2 := by rw [haBase]; rfl
  have hb0 : b • e 0 = e 1 := by rw [hbBase]; rfl
  have hb1 : b • e 1 = e 0 := by rw [hbBase]; rfl
  have hb2 : b • e 2 = e 3 := by rw [hbBase]; rfl
  have hb3 : b • e 3 = e 2 := by rw [hbBase]; rfl
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have hrD : r ∈ MulAction.fixedBy X a ∩ MulAction.fixedBy X b := by
    rw [hD]
    simp
  have har : a • r = r := hrD.1
  have hbr : b • r = r := hrD.2
  have haq : a • q = p := by
    calc
      a • q = a • (a • p) := congrArg (fun z : X ↦ a • z) hap.symm
      _ = (a ^ 2) • p := by rw [pow_two, mul_smul]
      _ = p := by rw [haTwo, one_smul]
  have hbu : b * u = u * (a * b) := by
    calc
      b * u = (a * (a * b)) * u := by
        rw [← mul_assoc, ← pow_two, haTwo, one_mul]
      _ = a * ((a * b) * u) := by rw [mul_assoc]
      _ = a * (u * b) := by rw [hub]
      _ = (a * u) * b := by rw [mul_assoc]
      _ = (u * a) * b := by rw [← hua]
      _ = u * (a * b) := by rw [mul_assoc]
  have hur : u • r = r := by
    have haUr : a • (u • r) = u • r := by
      calc
        a • (u • r) = (a * u) • r := (mul_smul _ _ _).symm
        _ = (u * a) • r := by rw [← hua]
        _ = u • (a • r) := mul_smul _ _ _
        _ = u • r := by rw [har]
    have hbUr : b • (u • r) = u • r := by
      calc
        b • (u • r) = (b * u) • r := (mul_smul _ _ _).symm
        _ = (u * (a * b)) • r := by rw [hbu]
        _ = u • ((a * b) • r) := mul_smul _ _ _
        _ = u • r := by rw [mul_smul, hbr, har]
    have huD : u • r ∈
        MulAction.fixedBy X a ∩ MulAction.fixedBy X b := ⟨haUr, hbUr⟩
    rw [hD] at huD
    simpa using huD
  have he0r : e 0 ≠ r := by
    intro h
    have := hb0
    rw [h, hbr] at this
    exact h01 (h.trans this)
  have he1r : e 1 ≠ r := by
    intro h
    have := hb1
    rw [h, hbr] at this
    exact h01 (this.symm.trans h.symm)
  have he2r : e 2 ≠ r := by
    intro h
    have := ha2
    rw [h, har] at this
    exact h23 (h.trans this)
  have hu0mem : u • e 0 ∈ MulAction.fixedBy X a := by
    change a • (u • e 0) = u • e 0
    calc
      a • (u • e 0) = (a * u) • e 0 := (mul_smul _ _ _).symm
      _ = (u * a) • e 0 := by rw [← hua]
      _ = u • (a • e 0) := mul_smul _ _ _
      _ = u • e 0 := by rw [ha0]
  have hu1mem : u • e 1 ∈ MulAction.fixedBy X a := by
    change a • (u • e 1) = u • e 1
    calc
      a • (u • e 1) = (a * u) • e 1 := (mul_smul _ _ _).symm
      _ = (u * a) • e 1 := by rw [← hua]
      _ = u • (a • e 1) := mul_smul _ _ _
      _ = u • e 1 := by rw [ha1]
  have hnotSwap : u • e 0 ≠ e 1 := by
    intro hu0
    have hu1 : u • e 1 = e 0 := by
      calc
        u • e 1 = u • (u • e 0) := congrArg (fun z : X ↦ u • z) hu0.symm
        _ = (u ^ 2) • e 0 := by rw [pow_two, mul_smul]
        _ = e 0 := by rw [huSq, ha0]
    let v : G := b * u
    have hvTwo : v ^ 2 = 1 := by
      dsimp only [v]
      rw [pow_two]
      calc
        (b * u) * (b * u) = b * (u * b) * u := by group
        _ = b * ((a * b) * u) * u := by rw [hub]
        _ = (b * (a * b)) * (u * u) := by group
        _ = a * (u ^ 2) := by
          rw [show b * (a * b) = a by
            calc
              b * (a * b) = a * (b * b) := by
                rw [← mul_assoc, ← hab.eq, mul_assoc]
              _ = a := by rw [← pow_two, hbTwo, mul_one], pow_two]
        _ = 1 := by rw [huSq, ← pow_two, haTwo]
    have hvNe : v ≠ 1 := by
      intro hv
      have huEq : u = b := by
        calc
          u = 1 * u := by rw [one_mul]
          _ = (b * b) * u := by rw [← pow_two, hbTwo]
          _ = b * (b * u) := by rw [mul_assoc]
          _ = b := by rw [show b * u = v from rfl, hv, mul_one]
      have haOne : a = 1 := by rw [← huSq, huEq, hbTwo]
      have := ha2
      rw [haOne, one_smul] at this
      exact h23 this
    have hv0 : v • e 0 = e 0 := by
      simp only [v, mul_smul, hu0, hb1]
    have hv1 : v • e 1 = e 1 := by
      simp only [v, mul_smul, hu1, hb0]
    have hvY : v • y = y := by
      simp only [v, mul_smul, huY]
      rw [← mul_smul, ← pow_two, hbTwo, one_smul]
    have hvAY : v • (a • y) = a • y := by
      calc
        v • (a • y) = b • (u • (a • y)) := by
          simp only [v, mul_smul]
        _ = b • ((a * b) • y) := by rw [huAY]
        _ = a • y := by
          rw [← mul_smul]
          congr 1
          calc
            b * (a * b) = a * (b * b) := by
              rw [← mul_assoc, ← hab.eq, mul_assoc]
            _ = a := by rw [← pow_two, hbTwo, mul_one]
    have hyay : y ≠ a • y := hya.symm
    have h0y : e 0 ≠ y := by
      intro h
      apply hya
      rw [← h, ha0, h]
    have h1y : e 1 ≠ y := by
      intro h
      apply hya
      rw [← h, ha1, h]
    have h0ay : e 0 ≠ a • y := by
      intro h
      apply h0y
      calc
        e 0 = a • (a • y) := by rw [← h, ha0]
        _ = (a ^ 2) • y := by rw [pow_two, mul_smul]
        _ = y := by rw [haTwo, one_smul]
    have h1ay : e 1 ≠ a • y := by
      intro h
      apply h1y
      calc
        e 1 = a • (a • y) := by rw [← h, ha1]
        _ = (a ^ 2) • y := by rw [pow_two, mul_smul]
        _ = y := by rw [haTwo, one_smul]
    let T : Set X := {e 0, e 1, y, a • y}
    have hTcard : T.ncard = 4 := by
      apply Set.ncard_eq_four.mpr
      exact ⟨e 0, e 1, y, a • y, h01, h0y, h0ay,
        h1y, h1ay, hyay, rfl⟩
    have hTsub : T ⊆ MulAction.fixedBy X v := by
      intro x hx
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hv0
      · exact hv1
      · exact hvY
      · exact hvAY
    have hfour : 4 ≤ (MulAction.fixedBy X v).ncard := by
      have hle := Set.ncard_le_ncard hTsub
      rwa [hTcard] at hle
    have hthree := involution_fixedBy_ncard_le_three h4 e hodd v hvTwo hvNe
    omega
  have hu0 : u • e 0 = e 0 := by
    rw [hFa] at hu0mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu0mem
    rcases hu0mem with hu0 | hu0 | hu0
    · exact hu0
    · exact (hnotSwap hu0).elim
    · exact (he0r ((MulAction.injective u)
        (hu0.trans hur.symm))).elim
  have hu1 : u • e 1 = e 1 := by
    rw [hFa] at hu1mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu1mem
    rcases hu1mem with hu1 | hu1 | hu1
    · exact (h01.symm ((MulAction.injective u)
        (hu1.trans hu0.symm))).elim
    · exact hu1
    · exact (he1r ((MulAction.injective u)
        (hu1.trans hur.symm))).elim
  have hc2 : (a * b) • e 2 = e 2 := by rw [mul_smul, hb2, ha3]
  have hu2mem : u • e 2 ∈ MulAction.fixedBy X b := by
    change b • (u • e 2) = u • e 2
    calc
      b • (u • e 2) = (b * u) • e 2 := (mul_smul _ _ _).symm
      _ = (u * (a * b)) • e 2 := by rw [hbu]
      _ = u • ((a * b) • e 2) := mul_smul _ _ _
      _ = u • e 2 := by rw [hc2]
  rw [hFb] at hu2mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2mem
  rcases hu2mem with hu2p | hu2q | hu2r
  · have hup3 : u • p = e 3 := by
      calc
        u • p = u • (u • e 2) := congrArg (fun z : X ↦ u • z) hu2p.symm
        _ = (u ^ 2) • e 2 := by rw [pow_two, mul_smul]
        _ = e 3 := by rw [huSq, ha2]
    have hu3q : u • e 3 = q := by
      calc
        u • e 3 = u • (a • e 2) := by rw [ha2]
        _ = (u * a) • e 2 := (mul_smul _ _ _).symm
        _ = (a * u) • e 2 := by rw [hua]
        _ = a • (u • e 2) := mul_smul _ _ _
        _ = q := by rw [hu2p, hap]
    have huq2 : u • q = e 2 := by
      calc
        u • q = u • (u • e 3) := congrArg (fun z : X ↦ u • z) hu3q.symm
        _ = (u ^ 2) • e 3 := by rw [pow_two, mul_smul]
        _ = e 2 := by rw [huSq, ha3]
    refine ⟨a * u, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul, hu0, ha0]
    · rw [mul_smul, hu1, ha1]
    · rw [mul_smul, hur, har]
    · rw [mul_smul, hu2p, hap]
    · rw [mul_smul, huq2, ha2]
    · rw [mul_smul, hu3q, haq]
    · rw [mul_smul, hup3, ha3]
  · have huq3 : u • q = e 3 := by
      calc
        u • q = u • (u • e 2) := congrArg (fun z : X ↦ u • z) hu2q.symm
        _ = (u ^ 2) • e 2 := by rw [pow_two, mul_smul]
        _ = e 3 := by rw [huSq, ha2]
    have hu3p : u • e 3 = p := by
      calc
        u • e 3 = u • (a • e 2) := by rw [ha2]
        _ = (u * a) • e 2 := (mul_smul _ _ _).symm
        _ = (a * u) • e 2 := by rw [hua]
        _ = a • (u • e 2) := mul_smul _ _ _
        _ = p := by rw [hu2q, haq]
    have hup2 : u • p = e 2 := by
      calc
        u • p = u • (u • e 3) := congrArg (fun z : X ↦ u • z) hu3p.symm
        _ = (u ^ 2) • e 3 := by rw [pow_two, mul_smul]
        _ = e 2 := by rw [huSq, ha3]
    exact ⟨u, Or.inl rfl, hu0, hu1, hur, hu2q, huq3, hu3p, hup2⟩
  · exact (he2r ((MulAction.injective u)
      (hu2r.trans hur.symm))).elim

theorem exists_oriented_quarterTurn_six
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hap : a • p = q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (_hFc : MulAction.fixedBy X (a * b) = {e 2, e 3})
    (y : X) (hya : a • y ≠ y)
    (u : G)
    (huY : u • y = b • y)
    (huAY : u • (a • y) = (a * b) • y)
    (huSq : u ^ 2 = a)
    (hua : u * a = a * u)
    (hub : u * b = (a * b) * u) :
    ∃ u' : G,
      (u' = u ∨ u' = a * u) ∧
      u' • e 0 = e 0 ∧ u' • e 1 = e 1 ∧
      u' • e 2 = q ∧ u' • q = e 3 ∧
      u' • e 3 = p ∧ u' • p = e 2 := by
  classical
  have ha0 : a • e 0 = e 0 := by rw [haBase]; rfl
  have ha1 : a • e 1 = e 1 := by rw [haBase]; rfl
  have ha2 : a • e 2 = e 3 := by rw [haBase]; rfl
  have ha3 : a • e 3 = e 2 := by rw [haBase]; rfl
  have hb0 : b • e 0 = e 1 := by rw [hbBase]; rfl
  have hb1 : b • e 1 = e 0 := by rw [hbBase]; rfl
  have hb2 : b • e 2 = e 3 := by rw [hbBase]; rfl
  have hb3 : b • e 3 = e 2 := by rw [hbBase]; rfl
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have haq : a • q = p := by
    calc
      a • q = a • (a • p) := congrArg (fun z : X ↦ a • z) hap.symm
      _ = (a ^ 2) • p := by rw [pow_two, mul_smul]
      _ = p := by rw [haTwo, one_smul]
  have hbu : b * u = u * (a * b) := by
    calc
      b * u = (a * (a * b)) * u := by
        rw [← mul_assoc, ← pow_two, haTwo, one_mul]
      _ = a * ((a * b) * u) := by rw [mul_assoc]
      _ = a * (u * b) := by rw [hub]
      _ = (a * u) * b := by rw [mul_assoc]
      _ = (u * a) * b := by rw [← hua]
      _ = u * (a * b) := by rw [mul_assoc]
  have hu0mem : u • e 0 ∈ MulAction.fixedBy X a := by
    change a • (u • e 0) = u • e 0
    calc
      a • (u • e 0) = (a * u) • e 0 := (mul_smul _ _ _).symm
      _ = (u * a) • e 0 := by rw [← hua]
      _ = u • (a • e 0) := mul_smul _ _ _
      _ = u • e 0 := by rw [ha0]
  have hu1mem : u • e 1 ∈ MulAction.fixedBy X a := by
    change a • (u • e 1) = u • e 1
    calc
      a • (u • e 1) = (a * u) • e 1 := (mul_smul _ _ _).symm
      _ = (u * a) • e 1 := by rw [← hua]
      _ = u • (a • e 1) := mul_smul _ _ _
      _ = u • e 1 := by rw [ha1]
  have hnotSwap : u • e 0 ≠ e 1 := by
    intro hu0
    have hu1 : u • e 1 = e 0 := by
      calc
        u • e 1 = u • (u • e 0) := congrArg (fun z : X ↦ u • z) hu0.symm
        _ = (u ^ 2) • e 0 := by rw [pow_two, mul_smul]
        _ = e 0 := by rw [huSq, ha0]
    let v : G := b * u
    have hvTwo : v ^ 2 = 1 := by
      dsimp only [v]
      rw [pow_two]
      calc
        (b * u) * (b * u) = b * (u * b) * u := by group
        _ = b * ((a * b) * u) * u := by rw [hub]
        _ = (b * (a * b)) * (u * u) := by group
        _ = a * (u ^ 2) := by
          rw [show b * (a * b) = a by
            calc
              b * (a * b) = a * (b * b) := by
                rw [← mul_assoc, ← hab.eq, mul_assoc]
              _ = a := by rw [← pow_two, hbTwo, mul_one], pow_two]
        _ = 1 := by rw [huSq, ← pow_two, haTwo]
    have hvNe : v ≠ 1 := by
      intro hv
      have huEq : u = b := by
        calc
          u = 1 * u := by rw [one_mul]
          _ = (b * b) * u := by rw [← pow_two, hbTwo]
          _ = b * (b * u) := by rw [mul_assoc]
          _ = b := by rw [show b * u = v from rfl, hv, mul_one]
      have haOne : a = 1 := by rw [← huSq, huEq, hbTwo]
      have := ha2
      rw [haOne, one_smul] at this
      exact h23 this
    have hv0 : v • e 0 = e 0 := by
      simp only [v, mul_smul, hu0, hb1]
    have hv1 : v • e 1 = e 1 := by
      simp only [v, mul_smul, hu1, hb0]
    have hvY : v • y = y := by
      simp only [v, mul_smul, huY]
      rw [← mul_smul, ← pow_two, hbTwo, one_smul]
    have hvAY : v • (a • y) = a • y := by
      calc
        v • (a • y) = b • (u • (a • y)) := by
          simp only [v, mul_smul]
        _ = b • ((a * b) • y) := by rw [huAY]
        _ = a • y := by
          rw [← mul_smul]
          congr 1
          calc
            b * (a * b) = a * (b * b) := by
              rw [← mul_assoc, ← hab.eq, mul_assoc]
            _ = a := by rw [← pow_two, hbTwo, mul_one]
    have hyay : y ≠ a • y := hya.symm
    have h0y : e 0 ≠ y := by
      intro h
      apply hya
      rw [← h, ha0, h]
    have h1y : e 1 ≠ y := by
      intro h
      apply hya
      rw [← h, ha1, h]
    have h0ay : e 0 ≠ a • y := by
      intro h
      apply h0y
      calc
        e 0 = a • (a • y) := by rw [← h, ha0]
        _ = (a ^ 2) • y := by rw [pow_two, mul_smul]
        _ = y := by rw [haTwo, one_smul]
    have h1ay : e 1 ≠ a • y := by
      intro h
      apply h1y
      calc
        e 1 = a • (a • y) := by rw [← h, ha1]
        _ = (a ^ 2) • y := by rw [pow_two, mul_smul]
        _ = y := by rw [haTwo, one_smul]
    let T : Set X := {e 0, e 1, y, a • y}
    have hTcard : T.ncard = 4 := by
      apply Set.ncard_eq_four.mpr
      exact ⟨e 0, e 1, y, a • y, h01, h0y, h0ay,
        h1y, h1ay, hyay, rfl⟩
    have hTsub : T ⊆ MulAction.fixedBy X v := by
      intro x hx
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hv0
      · exact hv1
      · exact hvY
      · exact hvAY
    have hfour : 4 ≤ (MulAction.fixedBy X v).ncard := by
      have hle := Set.ncard_le_ncard hTsub
      rwa [hTcard] at hle
    have hthree := involution_fixedBy_ncard_le_three h4 e hodd v hvTwo hvNe
    omega
  have hu0 : u • e 0 = e 0 := by
    rw [hFa] at hu0mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu0mem
    rcases hu0mem with hu0 | hu0
    · exact hu0
    · exact (hnotSwap hu0).elim
  have hu1 : u • e 1 = e 1 := by
    rw [hFa] at hu1mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu1mem
    rcases hu1mem with hu1 | hu1
    · exact (h01.symm ((MulAction.injective u)
        (hu1.trans hu0.symm))).elim
    · exact hu1
  have hc2 : (a * b) • e 2 = e 2 := by rw [mul_smul, hb2, ha3]
  have hu2mem : u • e 2 ∈ MulAction.fixedBy X b := by
    change b • (u • e 2) = u • e 2
    calc
      b • (u • e 2) = (b * u) • e 2 := (mul_smul _ _ _).symm
      _ = (u * (a * b)) • e 2 := by rw [hbu]
      _ = u • ((a * b) • e 2) := mul_smul _ _ _
      _ = u • e 2 := by rw [hc2]
  rw [hFb] at hu2mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2mem
  rcases hu2mem with hu2p | hu2q
  · have hup3 : u • p = e 3 := by
      calc
        u • p = u • (u • e 2) := congrArg (fun z : X ↦ u • z) hu2p.symm
        _ = (u ^ 2) • e 2 := by rw [pow_two, mul_smul]
        _ = e 3 := by rw [huSq, ha2]
    have hu3q : u • e 3 = q := by
      calc
        u • e 3 = u • (a • e 2) := by rw [ha2]
        _ = (u * a) • e 2 := (mul_smul _ _ _).symm
        _ = (a * u) • e 2 := by rw [hua]
        _ = a • (u • e 2) := mul_smul _ _ _
        _ = q := by rw [hu2p, hap]
    have huq2 : u • q = e 2 := by
      calc
        u • q = u • (u • e 3) := congrArg (fun z : X ↦ u • z) hu3q.symm
        _ = (u ^ 2) • e 3 := by rw [pow_two, mul_smul]
        _ = e 2 := by rw [huSq, ha3]
    refine ⟨a * u, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul, hu0, ha0]
    · rw [mul_smul, hu1, ha1]
    · rw [mul_smul, hu2p, hap]
    · rw [mul_smul, huq2, ha2]
    · rw [mul_smul, hu3q, haq]
    · rw [mul_smul, hup3, ha3]
  · have huq3 : u • q = e 3 := by
      calc
        u • q = u • (u • e 2) := congrArg (fun z : X ↦ u • z) hu2q.symm
        _ = (u ^ 2) • e 2 := by rw [pow_two, mul_smul]
        _ = e 3 := by rw [huSq, ha2]
    have hu3p : u • e 3 = p := by
      calc
        u • e 3 = u • (a • e 2) := by rw [ha2]
        _ = (u * a) • e 2 := (mul_smul _ _ _).symm
        _ = (a * u) • e 2 := by rw [hua]
        _ = a • (u • e 2) := mul_smul _ _ _
        _ = p := by rw [hu2q, haq]
    have hup2 : u • p = e 2 := by
      calc
        u • p = u • (u • e 3) := congrArg (fun z : X ↦ u • z) hu3p.symm
        _ = (u ^ 2) • e 3 := by rw [pow_two, mul_smul]
        _ = e 2 := by rw [huSq, ha3]
    exact ⟨u, Or.inl rfl, hu0, hu1, hu2q, huq3, hu3p, hup2⟩

omit [Finite G] [Fintype X] in
theorem oriented_quarterTurn_reflection_action
    (e : Fin 4 ↪ X) (b u : G)
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hbp : b • p = p) (hbq : b • q = q)
    (hu0 : u • e 0 = e 0) (hu1 : u • e 1 = e 1)
    (hu2 : u • e 2 = q) (huq : u • q = e 3)
    (hu3 : u • e 3 = p) (hup : u • p = e 2) :
    (b * u) • e 0 = e 1 ∧ (b * u) • e 1 = e 0 ∧
      (b * u) • e 2 = q ∧ (b * u) • q = e 2 ∧
      (b * u) • e 3 = p ∧ (b * u) • p = e 3 := by
  have hb0 : b • e 0 = e 1 := by rw [hbBase]; rfl
  have hb1 : b • e 1 = e 0 := by rw [hbBase]; rfl
  have hb2 : b • e 2 = e 3 := by rw [hbBase]; rfl
  have hb3 : b • e 3 = e 2 := by rw [hbBase]; rfl
  simp only [mul_smul, hu0, hu1, hu2, huq, hu3, hup,
    hb0, hb1, hb2, hb3, hbp, hbq, and_self]

end FiveTransitive.Research.HallExceptionalOrientation

end CFSG
