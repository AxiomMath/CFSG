module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] {n : ℕ}

namespace FlagK

theorem ext {x y : FlagK K n} (h : ∀ j, x.E j = y.E j) : x = y := by
  obtain ⟨xE, xm, xd, xt⟩ := x
  obtain ⟨yE, ym, yd, yt⟩ := y
  have hE : xE = yE := funext h
  cases hE
  rfl

theorem E_zero (x : FlagK K n) : x.E 0 = ⊥ := by
  have h := x.dim 0 (Nat.zero_le n)
  exact (Submodule.finrank_eq_zero).mp h

theorem ext_of_mid {x y : FlagK K n} (h : ∀ j, 1 ≤ j → j < n → x.E j = y.E j) : x = y := by
  apply ext
  intro j
  by_cases hj0 : j = 0
  · subst hj0
    rw [E_zero, E_zero]
  · by_cases hjn : n ≤ j
    · rw [x.top j hjn, y.top j hjn]
    · exact h j (by omega) (by omega)

@[expose] noncomputable def ofChain4 (p L H : Submodule K (Fin 4 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hH : finrank K H = 3) (hpL : p ≤ L) (hLH : L ≤ H) : FlagK K 4 where
  E j := if j = 0 then ⊥ else if j = 1 then p else if j = 2 then L else if j = 3 then H else ⊤
  mono := by
    refine monotone_nat_of_le_succ (fun j => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp
    · simpa using hpL
    · simpa using hLH
    · simp
    · simp
  dim := by
    intro j hj
    interval_cases j <;> simp [hp, hL, hH, Module.finrank_fin_fun]
  top := by
    intro j hj
    change (if j = 0 then ⊥ else if j = 1 then p else if j = 2 then L
      else if j = 3 then H else ⊤) = ⊤
    rw [if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j = 1 by omega),
      if_neg (show ¬ j = 2 by omega), if_neg (show ¬ j = 3 by omega)]

theorem ofChain4_E_one (p L H : Submodule K (Fin 4 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hH : finrank K H = 3) (hpL : p ≤ L) (hLH : L ≤ H) :
    (ofChain4 p L H hp hL hH hpL hLH).E 1 = p := by
  show (if (1 : ℕ) = 0 then ⊥ else if (1 : ℕ) = 1 then p else if (1 : ℕ) = 2 then L
    else if (1 : ℕ) = 3 then H else ⊤) = p
  simp

theorem ofChain4_E_two (p L H : Submodule K (Fin 4 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hH : finrank K H = 3) (hpL : p ≤ L) (hLH : L ≤ H) :
    (ofChain4 p L H hp hL hH hpL hLH).E 2 = L := by
  show (if (2 : ℕ) = 0 then ⊥ else if (2 : ℕ) = 1 then p else if (2 : ℕ) = 2 then L
    else if (2 : ℕ) = 3 then H else ⊤) = L
  simp

theorem ofChain4_E_three (p L H : Submodule K (Fin 4 → K)) (hp : finrank K p = 1)
    (hL : finrank K L = 2) (hH : finrank K H = 3) (hpL : p ≤ L) (hLH : L ≤ H) :
    (ofChain4 p L H hp hL hH hpL hLH).E 3 = H := by
  show (if (3 : ℕ) = 0 then ⊥ else if (3 : ℕ) = 1 then p else if (3 : ℕ) = 2 then L
    else if (3 : ℕ) = 3 then H else ⊤) = H
  simp

theorem finrank_E_one (x : FlagK K 4) : finrank K (x.E 1) = 1 :=
  x.dim 1 (by norm_num)

theorem finrank_E_two (x : FlagK K 4) : finrank K (x.E 2) = 2 :=
  x.dim 2 (by norm_num)

theorem finrank_E_three (x : FlagK K 4) : finrank K (x.E 3) = 3 :=
  x.dim 3 (by norm_num)

theorem E_one_le_two (x : FlagK K 4) : x.E 1 ≤ x.E 2 :=
  x.mono (by norm_num)

theorem E_two_le_three (x : FlagK K 4) : x.E 2 ≤ x.E 3 :=
  x.mono (by norm_num)

theorem ext4 {x y : FlagK K 4} (h1 : x.E 1 = y.E 1) (h2 : x.E 2 = y.E 2) (h3 : x.E 3 = y.E 3) :
    x = y := by
  apply ext_of_mid
  intro j hj1 hj4
  interval_cases j
  exacts [h1, h2, h3]

end FlagK

theorem flagSys_adj_zero (x y : FlagK K 4) :
    (flagSys K 3).adj 0 x y ↔ x.E 2 = y.E 2 ∧ x.E 3 = y.E 3 := by
  show (∀ j, j ≠ 1 → x.E j = y.E j) ↔ x.E 2 = y.E 2 ∧ x.E 3 = y.E 3
  constructor
  · intro h
    exact ⟨h 2 (by norm_num), h 3 (by norm_num)⟩
  · rintro ⟨h2, h3⟩ j hj
    obtain hlt | hge := lt_or_ge j 4
    · interval_cases j
      · exact (FlagK.E_zero x).trans (FlagK.E_zero y).symm
      · exact absurd rfl hj
      · exact h2
      · exact h3
    · rw [x.top j hge, y.top j hge]

theorem flagSys_adj_one (x y : FlagK K 4) :
    (flagSys K 3).adj 1 x y ↔ x.E 1 = y.E 1 ∧ x.E 3 = y.E 3 := by
  show (∀ j, j ≠ 2 → x.E j = y.E j) ↔ x.E 1 = y.E 1 ∧ x.E 3 = y.E 3
  constructor
  · intro h
    exact ⟨h 1 (by norm_num), h 3 (by norm_num)⟩
  · rintro ⟨h1, h3⟩ j hj
    obtain hlt | hge := lt_or_ge j 4
    · interval_cases j
      · exact (FlagK.E_zero x).trans (FlagK.E_zero y).symm
      · exact h1
      · exact absurd rfl hj
      · exact h3
    · rw [x.top j hge, y.top j hge]

theorem flagSys_adj_two (x y : FlagK K 4) :
    (flagSys K 3).adj 2 x y ↔ x.E 1 = y.E 1 ∧ x.E 2 = y.E 2 := by
  show (∀ j, j ≠ 3 → x.E j = y.E j) ↔ x.E 1 = y.E 1 ∧ x.E 2 = y.E 2
  constructor
  · intro h
    exact ⟨h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h1, h2⟩ j hj
    obtain hlt | hge := lt_or_ge j 4
    · interval_cases j
      · exact (FlagK.E_zero x).trans (FlagK.E_zero y).symm
      · exact h1
      · exact h2
      · exact absurd rfl hj
    · rw [x.top j hge, y.top j hge]

private def plh_VsubMap (n c : ℕ) : (Fin c → K) →ₗ[K] (Fin n → K) where
  toFun v := fun j => if h : j.val < c then v ⟨j.val, h⟩ else 0
  map_add' v w := by
    funext j
    by_cases h : j.val < c <;> simp [h]
  map_smul' a v := by
    funext j
    by_cases h : j.val < c <;> simp [h]

private theorem plh_VsubMap_apply (n c : ℕ) (v : Fin c → K) (j : Fin n) :
    plh_VsubMap (K := K) n c v j = if h : j.val < c then v ⟨j.val, h⟩ else 0 := rfl

private theorem plh_VsubMap_injective (n c : ℕ) (hc : c ≤ n) :
    Function.Injective (plh_VsubMap (K := K) n c) := by
  intro v w hvw
  funext i
  have h := congrFun hvw ⟨i.val, lt_of_lt_of_le i.isLt hc⟩
  simpa [plh_VsubMap_apply] using h

private theorem plh_VsubMap_range (n c : ℕ) :
    LinearMap.range (plh_VsubMap (K := K) n c) = Vsub (K := K) n c := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ j hj
    rw [plh_VsubMap_apply, dif_neg (not_lt_of_ge hj)]
  · intro hv
    refine ⟨fun i => if h : i.val < n then v ⟨i.val, h⟩ else 0, ?_⟩
    funext j
    rw [plh_VsubMap_apply]
    by_cases hj : j.val < c
    · rw [dif_pos hj, dif_pos j.isLt]
    · rw [dif_neg hj, hv j (le_of_not_gt hj)]

theorem finrank_Vsub {c : ℕ} (hc : c ≤ n) : finrank K (Vsub (K := K) n c) = c := by
  rw [← plh_VsubMap_range (K := K) n c,
    LinearMap.finrank_range_of_inj (plh_VsubMap_injective (K := K) n c hc)]
  exact Module.finrank_fin_fun K

theorem Vsub_zero : Vsub (K := K) n 0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  funext j
  exact hv j (Nat.zero_le _)

theorem Vsub_self : Vsub (K := K) n n = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v j hj
  exact absurd hj (not_le_of_gt j.isLt)

theorem Vsub_mono {c c' : ℕ} (h : c ≤ c') : Vsub (K := K) n c ≤ Vsub n c' := by
  intro v hv j hj
  exact hv j (le_trans h hj)

theorem mem_farSet_iff {d : List ℕ} (hd : ∀ i, i < d.length → d.getD i 0 ≤ n) {x : FlagK K n} :
    x ∈ farSet n d ↔ ∀ i, i < d.length → ∀ j, j ≤ n →
      (j + d.getD i 0 ≤ n → x.E j ⊓ Vsub n (d.getD i 0) = ⊥) ∧
      (n ≤ j + d.getD i 0 → x.E j ⊔ Vsub n (d.getD i 0) = ⊤) := by
  simp only [farSet, Set.mem_setOf_eq]
  constructor
  · intro hfar i hi j hj
    have hc : d.getD i 0 ≤ n := hd i hi
    have hS : finrank K (x.E j) = j := x.dim j hj
    have hV : finrank K (Vsub (K := K) n (d.getD i 0)) = d.getD i 0 := finrank_Vsub hc
    have hf := hfar i hi j hj
    constructor
    · intro hjc
      have hzero : finrank K ↥(x.E j ⊓ Vsub n (d.getD i 0)) = 0 := by
        rw [hf]
        omega
      exact (Submodule.finrank_eq_zero).mp hzero
    · intro hnjc
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E j)
        (Vsub (K := K) n (d.getD i 0))
      have htop : finrank K ↥(x.E j ⊔ Vsub n (d.getD i 0)) = n := by
        have hsum' := hsum
        rw [hS, hV] at hsum'
        omega
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [Module.finrank_fin_fun]
      exact htop
  · intro h i hi j hj
    have hc : d.getD i 0 ≤ n := hd i hi
    have hS : finrank K (x.E j) = j := x.dim j hj
    have hV : finrank K (Vsub (K := K) n (d.getD i 0)) = d.getD i 0 := finrank_Vsub hc
    have hcl := h i hi j hj
    by_cases hjc : j + d.getD i 0 ≤ n
    · have hbot : x.E j ⊓ Vsub n (d.getD i 0) = ⊥ := hcl.1 hjc
      rw [hbot, finrank_bot]
      omega
    · have hge : n ≤ j + d.getD i 0 := by omega
      have htop : x.E j ⊔ Vsub n (d.getD i 0) = ⊤ := hcl.2 hge
      have hfintop : finrank K ↥(x.E j ⊔ Vsub n (d.getD i 0)) = n := by
        rw [htop, finrank_top K (Fin n → K), Module.finrank_fin_fun K]
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E j)
        (Vsub (K := K) n (d.getD i 0))
      have hsum' := hsum
      rw [hS, hV] at hsum'
      omega

end CFSG.ClassicalInvolution.Phan.PhanE

end
