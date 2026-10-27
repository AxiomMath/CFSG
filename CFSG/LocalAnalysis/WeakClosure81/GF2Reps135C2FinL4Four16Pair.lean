module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.LieType.SpecialLinear.SLModel.Models
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.SLModel CFSG.LieType.SpecialLinear.ExteriorModel
open Module
open scoped TensorProduct

private theorem w183_mul_pred_le_orbitSize {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (h2 : 2 ≤ S.card) :
    n * (n - 1) ≤ orbitSize S := by
  classical
  have hn0 : 0 < n := by omega
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  exact multinomial_lower (b := blocks S) hb hsum hl

theorem card_endField_eq_two_of_card_eq_two_pow_sixteen {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] {ε : Fin 2 → Finset (Fin 4)} (hε : HasTwistedLabel ρ ε)
    (hne : ∃ r, ε r ≠ ∅) (hcard : Nat.card W = 2 ^ 16) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
      ρ.asModule) = 2 := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K)) ρ.asModule
  obtain ⟨s, hs_pos, hEcard⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  have hEcard' : Nat.card E = 2 ^ s := hEcard
  have hε' : HasTwistedLabel ρ ε := hε
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, y, χ, J, h0, ht, hχ, hJ, β, hβ⟩ := hε'
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have hEle : Nat.card E ≤ Nat.card K := card_endField_le_of_hasTwistedLabel (ρ := ρ) hε
  have hKcard : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card, hK]
  have hs2 : s ≤ 2 := by
    have h : 2 ^ s ≤ 2 ^ 2 := by
      calc 2 ^ s = Nat.card E := hEcard'.symm
        _ ≤ Nat.card K := hEle
        _ = 4 := hKcard
        _ = 2 ^ 2 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  by_cases hs_one : s = 1
  · rw [hs_one, pow_one] at hEcard'
    exact hEcard'
  · have hs_eq : s = 2 := by omega
    exfalso
    have hdim : s * finrank k (BModel k ε) = 16 := by
      have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
      rw [hEcard', ← pow_mul, hcard] at h1
      have h2 : finrank k (k ⊗[E] ρ.asModule) = finrank k (BModel k ε) := β.finrank_eq
      rw [h2] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    have hd8 : finrank k (BModel k ε) = 8 := by
      rw [hs_eq] at hdim
      omega
    let T := (Finset.univ : Finset (Fin 2)).filter (fun r => ε r ≠ ∅)
    have hTpos : 0 < T.card := by
      obtain ⟨r, hr⟩ := hne
      exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
    have hTle : T.card ≤ 2 := by
      calc T.card ≤ (Finset.univ : Finset (Fin 2)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 := by simp
    have hprod_le : ∏ r ∈ T, orbitSize (ε r) ≤ finrank k (BModel k ε) := by
      simpa only [T] using prod_orbitSize_le_finrank (k := k) (n := 4) (τ := Fin 2) ε
    rcases (by omega : T.card = 1 ∨ T.card = 2) with hT1 | hT2
    · obtain ⟨r₀, hTr₀⟩ := Finset.card_eq_one.mp hT1
      have hr₀ : ε r₀ ≠ ∅ := by
        have : r₀ ∈ T := by rw [hTr₀]; exact Finset.mem_singleton_self r₀
        exact (Finset.mem_filter.mp this).2
      have hrest : ∀ r, r ≠ r₀ → ε r = ∅ := by
        intro r hr
        by_contra hcon
        have : r ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hcon⟩
        rw [hTr₀] at this
        exact hr (Finset.mem_singleton.mp this)
      have hprod_single : ∏ r ∈ T, orbitSize (ε r) = orbitSize (ε r₀) := by
        rw [hTr₀]
        exact Finset.prod_singleton _ _
      have hle8 : orbitSize (ε r₀) ≤ 8 := by
        rw [hprod_single, hd8] at hprod_le
        exact hprod_le
      have hcard_ne2 : ¬ 2 ≤ (ε r₀).card := by
        intro h2
        have h12 : 12 ≤ orbitSize (ε r₀) := by
          have h := w183_mul_pred_le_orbitSize (n := 4) (by norm_num) (h0 r₀) h2
          norm_num at h
          exact h
        omega
      have hcard1 : (ε r₀).card = 1 := by
        have hpos : 0 < (ε r₀).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr₀)
        omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard1
      have hchoose8 : Nat.choose 4 j.val = 8 := by
        obtain ⟨β', -⟩ :=
          exists_equiv_single (F := K) (k := k) (m := 3) (f := 2) ε hj hrest
        have hd_choose : finrank k (BModel k ε) = Nat.choose 4 j.val := by
          rw [β'.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
            Set.powersetCard.card]
          simp [Nat.card_fin]
        rw [← hd_choose]
        exact hd8
      have hj0 : j ≠ 0 := by
        intro h0j
        rw [h0j] at hj
        exact h0 r₀ (by rw [hj]; exact Finset.mem_singleton_self (0 : Fin 4))
      have hc1 : Nat.choose 4 1 = 4 := by decide
      have hc2 : Nat.choose 4 2 = 6 := by decide
      have hc3 : Nat.choose 4 3 = 4 := by decide
      have hjval : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
        have hlt : j.val < 4 := j.isLt
        have hne : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        omega
      rcases hjval with h | h | h
      · rw [h, hc1] at hchoose8
        omega
      · rw [h, hc2] at hchoose8
        omega
      · rw [h, hc3] at hchoose8
        omega
    · have hTuniv : T = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        rw [hT2]
        simp
      have hall : ∀ r : Fin 2, ε r ≠ ∅ := by
        intro r
        have : r ∈ T := by rw [hTuniv]; exact Finset.mem_univ r
        exact (Finset.mem_filter.mp this).2
      have hge : 4 * 4 ≤ ∏ r ∈ T, orbitSize (ε r) := by
        rw [hTuniv, Fin.prod_univ_two]
        exact Nat.mul_le_mul
          (n_le_orbitSize (n := 4) (by norm_num) (h0 0) (hall 0))
          (n_le_orbitSize (n := 4) (by norm_num) (h0 1) (hall 1))
      have hcontr : (16 : ℕ) ≤ 8 := by
        calc 16 = 4 * 4 := by norm_num
          _ ≤ ∏ r ∈ T, orbitSize (ε r) := hge
          _ ≤ finrank k (BModel k ε) := hprod_le
          _ = 8 := hd8
      omega

theorem eq_pair_of_card_endField_eq_two {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] {ε : Fin 2 → Finset (Fin 4)} (hε : HasTwistedLabel ρ ε)
    (hne : ∃ r, ε r ≠ ∅) (hcard : Nat.card W = 2 ^ 16)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
      ρ.asModule) = 2) :
    ∃ j : Fin 4, ((j : ℕ) = 1 ∨ (j : ℕ) = 3) ∧ ε 0 = {j} ∧ ε 1 = {j} := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K)) ρ.asModule
  obtain ⟨s, hs_pos, hEcard⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  have hEcard' : Nat.card E = 2 ^ s := hEcard
  have hε' : HasTwistedLabel ρ ε := hε
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, y, χ, J, h0, ht, hχ, hJ, β, hβ⟩ := hε'
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have hs1 : s = 1 := by
    have h : 2 ^ s = 2 ^ 1 := by
      rw [pow_one, ← hEcard']
      exact hE
    exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h
  have hE' : Nat.card E = 2 ^ 1 := by
    rw [pow_one]
    exact hE
  have hdim : s * finrank k (BModel k ε) = 16 := by
    have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
    rw [hEcard', ← pow_mul, hcard] at h1
    have h2 : finrank k (k ⊗[E] ρ.asModule) = finrank k (BModel k ε) := β.finrank_eq
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hd16 : finrank k (BModel k ε) = 16 := by
    rw [hs1] at hdim
    omega
  have hK' : Fintype.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hboth : ∀ a : Fin 4, a ∈ ε 0 ∨ a ∈ ε 1 → a ∈ ε 0 ∧ a ∈ ε 1 := by
    intro a ha
    have ha0 : a ≠ 0 := by
      intro h
      rcases ha with ha | ha
      · exact h0 0 (by rwa [h] at ha)
      · exact h0 1 (by rwa [h] at ha)
    obtain ⟨i, hi_eq⟩ := Fin.exists_succ_eq_of_ne_zero ha0
    have hi : ∃ r, i.succ ∈ ε r := by
      rcases ha with ha | ha
      · exact ⟨0, by rw [hi_eq]; exact ha⟩
      · exact ⟨1, by rw [hi_eq]; exact ha⟩
    have hle := le_mul_card_node_of_hasTwistedLabel (hK := hK') (ρ := ρ) hε hE' i hi
    have hS2 : (Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r)).card = 2 := by
      have hle2 : 2 ≤ (Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r)).card := by
        simpa using hle
      have hle3 : (Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r)).card ≤ 2 := by
        calc _ ≤ (Finset.univ : Finset (Fin 2)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 := by simp
      omega
    have huniv : Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hS2]
      simp
    have hmem0 : i.succ ∈ ε 0 := by
      have : (0 : Fin 2) ∈ Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r) := by
        rw [huniv]; exact Finset.mem_univ 0
      exact (Finset.mem_filter.mp this).2
    have hmem1 : i.succ ∈ ε 1 := by
      have : (1 : Fin 2) ∈ Finset.univ.filter (fun r : Fin 2 => i.succ ∈ ε r) := by
        rw [huniv]; exact Finset.mem_univ 1
      exact (Finset.mem_filter.mp this).2
    rw [hi_eq] at hmem0 hmem1
    exact ⟨hmem0, hmem1⟩
  have hpair : ε 0 = ε 1 := by
    ext a
    constructor
    · intro ha
      exact (hboth a (Or.inl ha)).2
    · intro ha
      exact (hboth a (Or.inr ha)).1
  have hSne : ε 0 ≠ ∅ := by
    obtain ⟨r, hr⟩ := hne
    fin_cases r
    · exact hr
    · rw [hpair]; exact hr
  have hSne1 : ε 1 ≠ ∅ := by rw [← hpair]; exact hSne
  have hprod2 : orbitSize (ε 0) * orbitSize (ε 0) ≤ finrank k (BModel k ε) := by
    have h := prod_orbitSize_le_finrank (k := k) (n := 4) (τ := Fin 2) ε
    have hfilter : (Finset.univ.filter (fun r : Fin 2 => ε r ≠ ∅)) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro r
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
      fin_cases r
      · exact hSne
      · exact hSne1
    rw [hfilter, Fin.prod_univ_two, ← hpair] at h
    exact h
  have hle4 : orbitSize (ε 0) ≤ 4 := by
    have hsq : orbitSize (ε 0) * orbitSize (ε 0) ≤ 4 * 4 := by
      norm_num
      exact hprod2.trans (le_of_eq hd16)
    exact (mul_self_le_mul_self_iff (Nat.zero_le _) (by norm_num)).mpr hsq
  have h4le : 4 ≤ orbitSize (ε 0) :=
    n_le_orbitSize (n := 4) (by norm_num) (h0 0) hSne
  have horb : orbitSize (ε 0) = 4 := le_antisymm hle4 h4le
  have hcard_le1 : (ε 0).card ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ (ε 0).card := by omega
    have h12 : 12 ≤ orbitSize (ε 0) := by
      have h := w183_mul_pred_le_orbitSize (n := 4) (by norm_num) (h0 0) h2
      norm_num at h
      exact h
    omega
  have hcard1 : (ε 0).card = 1 := by
    have hpos : 0 < (ε 0).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard1
  have horbj : orbitSize ({j} : Finset (Fin 4)) = 4 := by rw [← hj]; exact horb
  have hchoose : Nat.choose 4 j.val = 4 := by
    rw [← orbitSize_singleton (n := 4) j]
    exact horbj
  have hj0 : j ≠ 0 := by
    intro h0j
    rw [h0j] at hj
    exact h0 0 (by rw [hj]; exact Finset.mem_singleton_self (0 : Fin 4))
  have hjval : j.val = 1 ∨ j.val = 3 := by
    have hc1 : Nat.choose 4 1 = 4 := by decide
    have hc2 : Nat.choose 4 2 = 6 := by decide
    have hc3 : Nat.choose 4 3 = 4 := by decide
    fin_cases j
    · exact absurd rfl hj0
    · exact Or.inl rfl
    · rw [hc2] at hchoose
      omega
    · exact Or.inr rfl
  exact ⟨j, hjval, hj, by rw [← hpair]; exact hj⟩

theorem exists_pair_label {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] (hne : ∃ x, ρ x ≠ 1) (hcard : Nat.card W = 2 ^ 16) :
    ∃ (ε : Fin 2 → Finset (Fin 4)) (j : Fin 4), HasTwistedLabel ρ ε ∧
      Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
        ρ.asModule) = 2 ∧ ((j : ℕ) = 1 ∨ (j : ℕ) = 3) ∧ ε 0 = {j} ∧ ε 1 = {j} := by
  obtain ⟨ε, hε, hne'⟩ := exists_hasTwistedLabel (f := 2) (m := 3) (by rw [hK]; norm_num) ρ hne
  have hE := card_endField_eq_two_of_card_eq_two_pow_sixteen hK ρ hε hne' hcard
  obtain ⟨j, hj, h0, h1⟩ := eq_pair_of_card_endField_eq_two hK ρ hε hne' hcard hE
  exact ⟨ε, j, hε, hE, hj, h0, h1⟩

end CFSG.LocalAnalysis.WeakClosure81
