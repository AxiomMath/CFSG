module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

namespace Plane

variable {K : Type} [Field K]

theorem finrank_E_one (x : FlagK K 3) : finrank K (x.E 1) = 1 :=
  x.dim 1 (by norm_num)

theorem finrank_E_two (x : FlagK K 3) : finrank K (x.E 2) = 2 :=
  x.dim 2 (by norm_num)

theorem E_one_le_two (x : FlagK K 3) : x.E 1 ≤ x.E 2 :=
  x.mono (by norm_num)

theorem ext {x y : FlagK K 3} (h1 : x.E 1 = y.E 1) (h2 : x.E 2 = y.E 2) : x = y := by
  apply FlagK.ext_of_mid
  intro j hj1 hj3
  interval_cases j
  exacts [h1, h2]

@[expose] noncomputable def ofChain (p L : Submodule K (Fin 3 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hpL : p ≤ L) : FlagK K 3 where
  E j := if j = 0 then ⊥ else if j = 1 then p else if j = 2 then L else ⊤
  mono := by
    refine monotone_nat_of_le_succ (fun j => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp
    · simpa using hpL
    · simp
    · simp
    · simp
  dim := by
    intro j hj
    interval_cases j <;> simp [hp, hL, Module.finrank_fin_fun]
  top := by
    intro j hj
    change (if j = 0 then ⊥ else if j = 1 then p else if j = 2 then L else ⊤) = ⊤
    rw [if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j = 1 by omega),
      if_neg (show ¬ j = 2 by omega)]

theorem ofChain_E_one (p L : Submodule K (Fin 3 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hpL : p ≤ L) : (ofChain p L hp hL hpL).E 1 = p := by
  simp [ofChain]

theorem ofChain_E_two (p L : Submodule K (Fin 3 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hpL : p ≤ L) : (ofChain p L hp hL hpL).E 2 = L := by
  simp [ofChain]

theorem adj_zero (x y : FlagK K 3) : (flagSys K 2).adj 0 x y ↔ x.E 2 = y.E 2 := by
  show (∀ j, j ≠ 1 → x.E j = y.E j) ↔ x.E 2 = y.E 2
  constructor
  · intro h
    exact h 2 (by norm_num)
  · intro h j hj
    obtain hlt | hge := lt_or_ge j 3
    · interval_cases j
      · exact (FlagK.E_zero x).trans (FlagK.E_zero y).symm
      · exact absurd rfl hj
      · exact h
    · rw [x.top j hge, y.top j hge]

theorem adj_one (x y : FlagK K 3) : (flagSys K 2).adj 1 x y ↔ x.E 1 = y.E 1 := by
  show (∀ j, j ≠ 2 → x.E j = y.E j) ↔ x.E 1 = y.E 1
  constructor
  · intro h
    exact h 1 (by norm_num)
  · intro h j hj
    obtain hlt | hge := lt_or_ge j 3
    · interval_cases j
      · exact (FlagK.E_zero x).trans (FlagK.E_zero y).symm
      · exact h
      · exact absurd rfl hj
    · rw [x.top j hge, y.top j hge]

@[expose] def HasFl (A : Set (FlagK K 3)) (p L : Submodule K (Fin 3 → K)) : Prop :=
  ∃ x ∈ A, x.E 1 = p ∧ x.E 2 = L

theorem hasFl_ofChain {A : Set (FlagK K 3)} {p L : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hpL : p ≤ L)
    (h : ofChain p L hp hL hpL ∈ A) : HasFl A p L :=
  ⟨ofChain p L hp hL hpL, h, ofChain_E_one p L hp hL hpL, ofChain_E_two p L hp hL hpL⟩

theorem connected_of_common_nbr (A : Set (FlagK K 3))
    (h : ∀ x ∈ A, ∀ y ∈ A, ∃ (z m m' : Submodule K (Fin 3 → K)),
      HasFl A (x.E 1) m ∧ HasFl A z m ∧ HasFl A z m' ∧ HasFl A (y.E 1) m') :
    ((flagSys K 2).restrict A).Connected := by
  intro x y
  obtain ⟨z, m, m', hxm, hzm, hzm', hym'⟩ := h x.1 x.2 y.1 y.2
  obtain ⟨a, haA, ha1, ha2⟩ := hxm
  obtain ⟨b, hbA, hb1, hb2⟩ := hzm
  obtain ⟨c, hcA, hc1, hc2⟩ := hzm'
  obtain ⟨d, hdA, hd1, hd2⟩ := hym'
  refine ⟨[(1, ⟨a, haA⟩), (0, ⟨b, hbA⟩), (1, ⟨c, hcA⟩), (0, ⟨d, hdA⟩), (1, y)], ?_, ?_⟩
  · simp only [ChamberSystem.isGallery_cons, ChamberSystem.isGallery_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (flagSys K 2).adj 1 (x : FlagK K 3) a
      rw [adj_one]
      exact ha1.symm
    · show (flagSys K 2).adj 0 a b
      rw [adj_zero]
      exact ha2.trans hb2.symm
    · show (flagSys K 2).adj 1 b c
      rw [adj_one]
      exact hb1.trans hc1.symm
    · show (flagSys K 2).adj 0 c d
      rw [adj_zero]
      exact hc2.trans hd2.symm
    · show (flagSys K 2).adj 1 d (y : FlagK K 3)
      rw [adj_one]
      exact hd1
  · rfl

end Plane

variable {K : Type} [Field K] [Finite K]

theorem exists_not_mem_union {n : ℕ} (hK : 3 < Nat.card K) (U₁ U₂ U₃ : Submodule K (Fin n → K))
    (h₁ : U₁ ≠ ⊤) (h₂ : U₂ ≠ ⊤) (h₃ : U₃ ≠ ⊤) : ∃ v : Fin n → K, v ∉ U₁ ∧ v ∉ U₂ ∧ v ∉ U₃ := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let p : Fin 3 → Submodule K (Fin n → K) := ![U₁, U₂, U₃]
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    fin_cases i
    · simpa [p] using h₁
    · simpa [p] using h₂
    · simpa [p] using h₃
  have hcard : (Finset.univ : Finset (Fin 3)).card < ENat.card K := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hc : ENat.card K = (Nat.card K : ℕ∞) := by
      rw [ENat.card_eq_coe_fintype_card, Nat.card_eq_fintype_card]
    rw [hc]
    exact_mod_cast hK
  have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
    (Finset.univ : Finset (Fin 3)) p hp hcard
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hsub
  refine ⟨v, ?_, ?_, ?_⟩ <;> intro hmem
  · exact hv (Set.mem_iUnion.mpr ⟨(0 : Fin 3), Set.mem_iUnion.mpr
      ⟨Finset.mem_univ 0, by simpa [p] using hmem⟩⟩)
  · exact hv (Set.mem_iUnion.mpr ⟨(1 : Fin 3), Set.mem_iUnion.mpr
      ⟨Finset.mem_univ 1, by simpa [p] using hmem⟩⟩)
  · exact hv (Set.mem_iUnion.mpr ⟨(2 : Fin 3), Set.mem_iUnion.mpr
      ⟨Finset.mem_univ 2, by simpa [p] using hmem⟩⟩)

end CFSG.ClassicalInvolution.Phan.PhanE

end
