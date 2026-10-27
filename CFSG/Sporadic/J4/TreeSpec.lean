module

public import CFSG.Sporadic.J4.Walk
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Global

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

structure TreeFacts (n : ℕ) (ta tb tc par dep : ByteArray) : Prop where
  dep_lt : ∀ j < n, depOf dep j < 64
  root : depOf dep 0 = 0
  step : ∀ j < n, j ≠ 0 → parOf par j < n ∧ 1 ≤ labOf par j ∧ labOf par j ≤ 3 ∧
    rdU32 (letter3 ta tb tc (labOf par j)) (parOf par j) = j ∧
    depOf dep (parOf par j) + 1 = depOf dep j

theorem treeFacts_of {ta tb tc par dep : ByteArray} {c : ℕ} (hn : 0 < n)
    (h : treeOK n ta tb tc par dep c = true) : TreeFacts n ta tb tc par dep := by
  have hall := parAllS_eq_true h
  refine ⟨fun j hj => ?_, ?_, fun j hj hj0 => ?_⟩
  · have := hall j hj
    simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := hall 0 hn
    simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, ite_true,
      beq_iff_eq] at this
    exact this.2
  · have := hall j hj
    simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hj0, ite_false] at this
    obtain ⟨-, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩ := this
    exact ⟨h1, h2, h3, h4, h5⟩

section Tree

variable {ta tb tc par dep : ByteArray} (hT : TreeFacts n ta tb tc par dep)
include hT

omit [MulAction G (Fin n)] hT in
theorem treeElt_succ_of_ne {L1 L2 L3 : G} (f : ℕ) {j : ℕ} (hj : j ≠ 0) :
    treeElt par L1 L2 L3 (f + 1) j =
      letterG L1 L2 L3 (labOf par j) * treeElt par L1 L2 L3 f (parOf par j) := by
  rw [treeElt, ite_eq_right hj]; rfl

omit [MulAction G (Fin n)] in
theorem treeElt_fuel {L1 L2 L3 : G} : ∀ d j, j < n → depOf dep j = d → ∀ f₁ f₂, d < f₁ → d < f₂ →
    treeElt par L1 L2 L3 f₁ j = treeElt par L1 L2 L3 f₂ j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hj hd f₁ f₂ h₁ h₂
    obtain ⟨f₁, rfl⟩ : ∃ f, f₁ = f + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨f₂, rfl⟩ : ∃ f, f₂ = f + 1 := ⟨f₂ - 1, by omega⟩
    by_cases hj0 : j = 0
    · rw [treeElt, ite_eq_left hj0, treeElt, ite_eq_left hj0]
    · obtain ⟨hp, -, -, -, hdp⟩ := hT.step j hj hj0
      rw [treeElt_succ_of_ne f₁ hj0, treeElt_succ_of_ne f₂ hj0,
        ih (depOf dep (parOf par j)) (by omega) _ hp rfl f₁ f₂ (by omega) (by omega)]

theorem idx_treeElt {L1 L2 L3 : G} (h1 : RepT n ta L1) (h2 : RepT n tb L2) (h3 : RepT n tc L3) :
    ∀ d j, j < n → depOf dep j = d → ∀ f, d < f →
      idx n (treeElt par L1 L2 L3 f j) 0 = j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hj hd f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    by_cases hj0 : j = 0
    · rw [treeElt, ite_eq_left hj0, idx_one, hj0]
    · obtain ⟨hp, -, -, hl, hdp⟩ := hT.step j hj hj0
      rw [treeElt_succ_of_ne f hj0, idx_mul,
        ih (depOf dep (parOf par j)) (by omega) _ hp rfl f (by omega),
        ← RepT.letter3 h1 h2 h3 (labOf par j) _ hp, hl]

omit [MulAction G (Fin n)] in
theorem treeElt_of_treeEdge {L1 L2 L3 : G} {l i j : ℕ} (hj : j < n) (h : treeEdge par l i j = true) :
    treeElt par L1 L2 L3 64 j = letterG L1 L2 L3 l * treeElt par L1 L2 L3 64 i := by
  simp only [treeEdge, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hj0, hp⟩, hl⟩ := h
  obtain ⟨hpn, -, -, -, hdp⟩ := hT.step j hj hj0
  have hdj := hT.dep_lt j hj
  rw [treeElt_succ_of_ne 63 hj0, hl, hp]
  congr 1
  rw [← hp]
  exact treeElt_fuel hT _ _ hpn rfl 63 64 (by omega) (by omega)

end Tree

theorem pairLetters_pairIdx {l1 l2 : ℕ} (h : pairIdx l1 l2 < 6) :
    pairLetters[pairIdx l1 l2]! = (l1, l2) := by
  unfold pairIdx at h ⊢
  split_ifs at h ⊢ <;> first | omega | (subst_vars; rfl)

@[expose] def bwd2Elt (par : ByteArray) (L1 L2 L3 : G) : ℕ → ℕ → G
  | 0, _ => 1
  | f + 1, j =>
    if j = 0 then 1 else
    if rdU32 par j &&& 0x3FFFFFFF = 0 then (letterG L1 L2 L3 (rdU32 par j >>> 30))⁻¹ else
    if pairIdx (rdU32 par j >>> 30) (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) >>> 30) < 6 then
      bwd2Elt par L1 L2 L3 f (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) &&& 0x3FFFFFFF) *
        ((letterG L1 L2 L3 (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) >>> 30))⁻¹ *
          (letterG L1 L2 L3 (rdU32 par j >>> 30))⁻¹)
    else bwd2Elt par L1 L2 L3 f (rdU32 par j &&& 0x3FFFFFFF) *
      (letterG L1 L2 L3 (rdU32 par j >>> 30))⁻¹

theorem bwd2_spec {par t1 t2 t3 : ByteArray} {pairs : Array ByteArray} {L1 L2 L3 : G}
    (h1 : RepT n t1 L1⁻¹) (h2 : RepT n t2 L2⁻¹) (h3 : RepT n t3 L3⁻¹)
    (hp : ∀ k < 6, RepT n (pairs[k]?.getD .empty)
      ((letterG L1 L2 L3 pairLetters[k]!.2)⁻¹ * (letterG L1 L2 L3 pairLetters[k]!.1)⁻¹))
    {q0 : Array ℕ} (hq0 : ∀ j < q0.size, q0[j]! < n) (f j : ℕ) {q : Array ℕ} {g : G}
    (hq : TupRep n q0 q g) :
    TupRep n q0 (bwd2 par t1 t2 t3 pairs f j q) (bwd2Elt par L1 L2 L3 f j * g) := by
  have hl : ∀ l, RepT n (letter3 t1 t2 t3 l) (letterG L1 L2 L3 l)⁻¹ := by
    intro l
    have := RepT.letter3 h1 h2 h3 l
    convert this using 2
    unfold letterG; split_ifs <;> rfl
  induction f generalizing j q g with
  | zero => simpa [bwd2, bwd2Elt] using hq
  | succ f ih =>
    rw [bwd2, bwd2Elt]
    by_cases hj : j = 0
    · simp only [hj, beq_self_eq_true, ite_true, one_mul]; exact hq
    · simp only [beq_iff_eq, hj, ite_false]
      by_cases hp0 : rdU32 par j &&& 0x3FFFFFFF = 0
      · simp only [hp0, ite_true]
        exact hq.apTab hq0 (hl _)
      · simp only [hp0, ite_false]
        split_ifs with hk
        · have := ih (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) &&& 0x3FFFFFFF) (hq.apTab hq0 (by
            have e := hp _ hk
            rwa [pairLetters_pairIdx hk] at e))
          simpa only [mul_assoc] using this
        · have := ih (rdU32 par j &&& 0x3FFFFFFF) (hq.apTab hq0 (hl (rdU32 par j >>> 30)))
          simpa only [mul_assoc] using this

theorem parOf_eq (par : ByteArray) (j : ℕ) : rdU32 par j &&& 0x3FFFFFFF = parOf par j := rfl

theorem labOf_eq (par : ByteArray) (j : ℕ) : rdU32 par j >>> 30 = labOf par j := rfl

omit [MulAction G (Fin n)] in
theorem bwd2Elt_eq {ta tb tc par dep : ByteArray} (hT : TreeFacts n ta tb tc par dep)
    {L1 L2 L3 : G} : ∀ d j, j < n → depOf dep j = d → ∀ f, d < f →
      bwd2Elt par L1 L2 L3 f j = (treeElt par L1 L2 L3 64 j)⁻¹ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hj hd f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hdj := hT.dep_lt j hj
    by_cases hj0 : j = 0
    · rw [bwd2Elt, ite_eq_left hj0, hj0, treeElt, ite_eq_left rfl, inv_one]
    · obtain ⟨hp, -, -, -, hdp⟩ := hT.step j hj hj0
      have hTj : treeElt par L1 L2 L3 64 j =
          letterG L1 L2 L3 (labOf par j) * treeElt par L1 L2 L3 64 (parOf par j) := by
        rw [treeElt_succ_of_ne 63 hj0,
          treeElt_fuel hT _ _ hp rfl 63 64 (by omega) (by omega)]
      rw [bwd2Elt, ite_eq_right hj0]
      by_cases hp0 : parOf par j = 0
      · have hp0' : rdU32 par j &&& 0x3FFFFFFF = 0 := hp0
        simp only [hp0', ite_true]
        rw [hTj, hp0, treeElt, ite_eq_left rfl, mul_one]
        rfl
      · have hp0' : ¬rdU32 par j &&& 0x3FFFFFFF = 0 := hp0
        simp only [hp0', ite_false]
        obtain ⟨hgp, -, -, -, hdgp⟩ := hT.step _ hp hp0
        have hTp : treeElt par L1 L2 L3 64 (parOf par j) =
            letterG L1 L2 L3 (labOf par (parOf par j)) *
              treeElt par L1 L2 L3 64 (parOf par (parOf par j)) := by
          rw [treeElt_succ_of_ne 63 hp0,
            treeElt_fuel hT _ _ hgp rfl 63 64 (by omega) (by omega)]
        by_cases hk : pairIdx (labOf par j) (labOf par (parOf par j)) < 6
        · have hk' : pairIdx (rdU32 par j >>> 30) (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) >>> 30)
              < 6 := hk
          simp only [hk', ite_true]
          have e := ih _ (by omega) _ hgp rfl f (by omega)
          change bwd2Elt par L1 L2 L3 f (parOf par (parOf par j)) *
            ((letterG L1 L2 L3 (labOf par (parOf par j)))⁻¹ *
              (letterG L1 L2 L3 (labOf par j))⁻¹) = _
          rw [e, hTj, hTp]
          simp only [mul_inv_rev, mul_assoc]
        · have hk' : ¬pairIdx (rdU32 par j >>> 30)
              (rdU32 par (rdU32 par j &&& 0x3FFFFFFF) >>> 30) < 6 := hk
          simp only [hk', ite_false]
          have e := ih _ (by omega) _ hp rfl f (by omega)
          change bwd2Elt par L1 L2 L3 f (parOf par j) * (letterG L1 L2 L3 (labOf par j))⁻¹ = _
          rw [e, hTj, mul_inv_rev]

end CFSG.Sporadic.J4
