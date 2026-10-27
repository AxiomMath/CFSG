module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

namespace TwE6TB

@[expose] def cartanE6 : Fin 6 → Fin 6 → ℤ :=
  ![![2, 0, -1, 0, 0, 0], ![0, 2, 0, -1, 0, 0], ![-1, 0, 2, -1, 0, 0],
    ![0, -1, -1, 2, -1, 0], ![0, 0, 0, -1, 2, -1], ![0, 0, 0, 0, -1, 2]]

variable (p : ℕ)

@[expose] def pairE6 (i : Fin 6) (v : Fin 6 → ZMod p) : ZMod p :=
  ∑ j, v j * (cartanE6 j i : ZMod p)

@[expose] def reflE6 (i : Fin 6) (v : Fin 6 → ZMod p) : Fin 6 → ZMod p :=
  v - pairE6 p i v • Pi.single i 1

variable {p}

theorem pairE6_smul (i : Fin 6) (c : ZMod p) (v : Fin 6 → ZMod p) :
    pairE6 p i (c • v) = c * pairE6 p i v := by
  simp only [pairE6, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem pairE6_single (i j : Fin 6) (c : ZMod p) :
    pairE6 p i (Pi.single j c) = c * (cartanE6 j i : ZMod p) := by
  simp [pairE6, Pi.single_apply]

theorem reflE6_apply (i : Fin 6) (v : Fin 6 → ZMod p) :
    reflE6 p i v = v - pairE6 p i v • Pi.single i 1 := rfl

theorem reflE6_single_self (i : Fin 6) : reflE6 p i (Pi.single i 1) = - Pi.single i 1 := by
  have h : (cartanE6 i i : ℤ) = 2 := by fin_cases i <;> rfl
  rw [reflE6_apply, pairE6_single, h]
  have : ((1 : ZMod p) * ((2 : ℤ) : ZMod p)) • (Pi.single i 1 : Fin 6 → ZMod p) =
      (2 : ZMod p) • Pi.single i 1 := by simp
  rw [this]
  rw [sub_eq_iff_eq_add, two_smul]
  abel

theorem reflE6_single_adj {i j : Fin 6} (h : cartanE6 i j = -1) :
    reflE6 p j (Pi.single i 1) = Pi.single i 1 + Pi.single j 1 := by
  rw [reflE6_apply, pairE6_single, h]
  simp

theorem reflE6_smul (i : Fin 6) (c : ZMod p) (v : Fin 6 → ZMod p) :
    reflE6 p i (c • v) = c • reflE6 p i v := by
  simp only [reflE6, pairE6_smul, smul_sub, smul_smul]

theorem eq_zero_of_pairE6_eq_zero [Fact p.Prime] (hp3 : p ≠ 3) {v : Fin 6 → ZMod p}
    (h : ∀ i, pairE6 p i v = 0) : v = 0 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp this)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3' := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [pairE6, Fin.sum_univ_six, cartanE6] at h0 h1 h2 h3' h4 h5
  simp at h0 h1 h2 h3' h4 h5
  funext k
  rw [Pi.zero_apply]
  refine (mul_eq_zero.mp ?_).resolve_left h3
  fin_cases k
  · simp only [Fin.zero_eta]
    linear_combination 4 * h0 + 3 * h1 + 5 * h2 + 6 * h3' + 4 * h4 + 2 * h5
  · simp only [Fin.mk_one]
    linear_combination 3 * h0 + 6 * h1 + 6 * h2 + 9 * h3' + 6 * h4 + 3 * h5
  · simp only [Fin.reduceFinMk]
    linear_combination 5 * h0 + 6 * h1 + 10 * h2 + 12 * h3' + 8 * h4 + 4 * h5
  · simp only [Fin.reduceFinMk]
    linear_combination 6 * h0 + 9 * h1 + 12 * h2 + 18 * h3' + 12 * h4 + 6 * h5
  · simp only [Fin.reduceFinMk]
    linear_combination 4 * h0 + 6 * h1 + 8 * h2 + 12 * h3' + 10 * h4 + 5 * h5
  · simp only [Fin.reduceFinMk]
    linear_combination 2 * h0 + 3 * h1 + 4 * h2 + 6 * h3' + 5 * h4 + 4 * h5

theorem smul_mem_of_mem [NeZero p] (G : AddSubgroup (Fin 6 → ZMod p)) {v : Fin 6 → ZMod p}
    (hv : v ∈ G) (c : ZMod p) : c • v ∈ G := by
  have h : c • v = c.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  rw [h]
  exact G.nsmul_mem hv _

theorem pi_eq_sum_single (w : Fin 6 → ZMod p) :
    w = ∑ j, w j • (Pi.single j 1 : Fin 6 → ZMod p) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem cartanE6_adj : cartanE6 0 2 = -1 ∧ cartanE6 2 0 = -1 ∧ cartanE6 2 3 = -1 ∧
    cartanE6 3 2 = -1 ∧ cartanE6 3 4 = -1 ∧ cartanE6 4 3 = -1 ∧ cartanE6 4 5 = -1 ∧
    cartanE6 5 4 = -1 ∧ cartanE6 1 3 = -1 ∧ cartanE6 3 1 = -1 := by
  decide

theorem eq_bot_or_eq_top_of_reflE6 [Fact p.Prime] (hp5 : 5 ≤ p)
    (G : AddSubgroup (Fin 6 → ZMod p)) (hG : ∀ i, ∀ v ∈ G, reflE6 p i v ∈ G) :
    G = ⊥ ∨ G = ⊤ := by
  have hp3 : p ≠ 3 := by omega
  by_cases hbot : G = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨v, hvG, hv0⟩ : ∃ v ∈ G, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((AddSubgroup.eq_bot_iff_forall G).mpr hcon)
  obtain ⟨i, hi⟩ : ∃ i, pairE6 p i v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (eq_zero_of_pairE6_eq_zero hp3 hcon)
  have hδi : (Pi.single i 1 : Fin 6 → ZMod p) ∈ G := by
    have h1 : reflE6 p i v - v ∈ G := G.sub_mem (hG i v hvG) hvG
    have e : reflE6 p i v - v = (-(pairE6 p i v)) • (Pi.single i 1 : Fin 6 → ZMod p) := by
      rw [reflE6_apply, neg_smul]
      abel
    rw [e] at h1
    have h2 := smul_mem_of_mem G h1 (-(pairE6 p i v))⁻¹
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hi), one_smul] at h2
  have hadj : ∀ j k, cartanE6 j k = -1 → ((Pi.single j 1 : Fin 6 → ZMod p) ∈ G ↔
      (Pi.single k 1 : Fin 6 → ZMod p) ∈ G) := by
    intro j k hjk
    have hkj : cartanE6 k j = -1 := by revert hjk; revert j k; decide
    constructor
    · intro hj
      have h1 := hG k _ hj
      rw [reflE6_single_adj hjk] at h1
      simpa using G.sub_mem h1 hj
    · intro hk
      have h1 := hG j _ hk
      rw [reflE6_single_adj hkj] at h1
      simpa using G.sub_mem h1 hk
  obtain ⟨a02, -, a23, -, a34, -, a45, -, a13, -⟩ := cartanE6_adj
  have e02 := hadj _ _ a02
  have e23 := hadj _ _ a23
  have e34 := hadj _ _ a34
  have e45 := hadj _ _ a45
  have e13 := hadj _ _ a13
  have h0 : (Pi.single 0 1 : Fin 6 → ZMod p) ∈ G := by
    fin_cases i
    · exact hδi
    · exact e02.mpr (e23.mpr (e13.mp hδi))
    · exact e02.mpr hδi
    · exact e02.mpr (e23.mpr hδi)
    · exact e02.mpr (e23.mpr (e34.mpr hδi))
    · exact e02.mpr (e23.mpr (e34.mpr (e45.mpr hδi)))
  have hall : ∀ j : Fin 6, (Pi.single j 1 : Fin 6 → ZMod p) ∈ G := by
    have h2 := e02.mp h0
    have h3 := e23.mp h2
    have h4 := e34.mp h3
    have h5 := e45.mp h4
    have h1 := e13.mpr h3
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_single w]
  exact G.sum_mem fun j _ => smul_mem_of_mem G (hall j) (w j)

theorem exists_smul_of_commute_reflE6 [Fact p.Prime] (hp5 : 5 ≤ p)
    (f : (Fin 6 → ZMod p) → (Fin 6 → ZMod p)) (hadd : ∀ v w, f (v + w) = f v + f w)
    (hcomm : ∀ i v, f (reflE6 p i v) = reflE6 p i (f v)) :
    ∃ c : ZMod p, ∀ v, f v = c • v := by
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set F : (Fin 6 → ZMod p) →+ (Fin 6 → ZMod p) := AddMonoidHom.mk' f hadd with hF
  have hfs : ∀ (c : ZMod p) v, f (c • v) = c • f v := by
    intro c v
    have h : c • v = c.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    have h' : c • f v = c.val • f v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [h, h']
    exact map_nsmul F _ v
  have hδ : ∀ i, ∃ μ : ZMod p, f (Pi.single i 1) = μ • (Pi.single i 1 : Fin 6 → ZMod p) := by
    intro i
    refine ⟨(2 : ZMod p)⁻¹ * pairE6 p i (f (Pi.single i 1)), ?_⟩
    have h1 := hcomm i (Pi.single i 1)
    rw [reflE6_single_self, reflE6_apply] at h1
    have h2 : f (- Pi.single i 1) = - f (Pi.single i 1) := map_neg F _
    rw [h2] at h1
    have h3 : (2 : ZMod p) • f (Pi.single i 1) =
        pairE6 p i (f (Pi.single i 1)) • (Pi.single i 1 : Fin 6 → ZMod p) := by
      rw [two_smul]
      have h4 := h1
      rw [eq_sub_iff_add_eq, neg_add_eq_iff_eq_add] at h4
      exact h4.symm
    calc f (Pi.single i 1) = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • f (Pi.single i 1)) := by
          rw [smul_smul, inv_mul_cancel₀ hp2, one_smul]
      _ = _ := by rw [h3, smul_smul]
  choose μ hμ using hδ
  have hedge : ∀ i j, cartanE6 i j = -1 → μ j = μ i := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      revert hij
      revert i
      decide
    have h1 := hcomm j (Pi.single i 1)
    rw [reflE6_single_adj hij, hadd, hμ i, hμ j, reflE6_smul, reflE6_single_adj hij] at h1
    have h2 := congrFun h1 j
    simp [Pi.single_apply, hne.symm] at h2
    exact h2
  obtain ⟨a02, -, a23, -, a34, -, a45, -, a13, -⟩ := cartanE6_adj
  have e02 := hedge _ _ a02
  have e23 := hedge _ _ a23
  have e34 := hedge _ _ a34
  have e45 := hedge _ _ a45
  have e13 := hedge _ _ a13
  have hμall : ∀ j, μ j = μ 0 := by
    intro j
    fin_cases j
    · rfl
    · exact e13.symm.trans (e23.trans e02)
    · exact e02
    · exact e23.trans e02
    · exact e34.trans (e23.trans e02)
    · exact e45.trans (e34.trans (e23.trans e02))
  refine ⟨μ 0, fun v => ?_⟩
  have hsum : f (∑ j, v j • (Pi.single j 1 : Fin 6 → ZMod p)) =
      ∑ j, f (v j • (Pi.single j 1 : Fin 6 → ZMod p)) :=
    map_sum F (fun j => v j • (Pi.single j 1 : Fin 6 → ZMod p)) Finset.univ
  calc f v = f (∑ j, v j • (Pi.single j 1 : Fin 6 → ZMod p)) := by rw [← pi_eq_sum_single v]
    _ = ∑ j, f (v j • (Pi.single j 1 : Fin 6 → ZMod p)) := hsum
    _ = ∑ j, (μ 0 * v j) • (Pi.single j 1 : Fin 6 → ZMod p) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hfs, hμ j, hμall j, smul_smul, mul_comm]
    _ = μ 0 • v := by
        conv_rhs => rw [pi_eq_sum_single v]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]

end TwE6TB

end CFSG.StandardType

end
