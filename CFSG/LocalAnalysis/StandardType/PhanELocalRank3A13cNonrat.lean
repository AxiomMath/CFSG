module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalSelVolU
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem finrank_Vtail : finrank K (Vtail : Submodule K (Fin 4 → K)) = 3 := by
  have hsup : (Vtail : Submodule K (Fin 4 → K)) ⊔ Vsub 4 1 = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = tailProj v + (v - tailProj v) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (tailProj_mem v) ?_
    rw [← ker_tailProj, LinearMap.mem_ker]
    funext j
    by_cases hj : j = 0
    · subst hj; simp [tailProj]
    · simp [tailProj, hj]
  have hinf : (Vtail : Submodule K (Fin 4 → K)) ⊓ Vsub 4 1 = ⊥ := Vtail_inf_Vsub
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (Vtail : Submodule K (Fin 4 → K)) (Vsub 4 1)
  rw [hsup, hinf, finrank_top, finrank_bot, Module.finrank_fin_fun,
      finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)] at hfin
  omega

theorem card_rat_le (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card {v : Fin 4 → K // v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
      sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}} ≤ (2 ^ f) ^ 5 := by
  classical
  let Fx := {a : K // sg K f a = a}
  let φ : K × (Fin 3 → Fx) → (Fin 4 → K) := fun p =>
    p.1 • (![0, (p.2 0).1, (p.2 1).1, (p.2 2).1] : Fin 4 → K)
  have hsub : {v : Fin 4 → K | v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
      sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}} ⊆ Set.range φ := by
    intro v hv
    obtain ⟨hvtail, hvfix⟩ := hv
    by_cases hv0 : v = 0
    · refine ⟨(0, fun _ => ⟨0, map_zero (sg K f)⟩), ?_⟩
      simp [φ, hv0]
    · obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
        by_contra h
        rw [not_exists] at h
        exact hv0 (funext fun j => by simpa using h j)
      have hsgv_in : sgv K f 4 v ∈ sgS K f 4 (Submodule.span K {v}) := by
        rw [mem_sgS, sgv_sgv hK]
        exact Submodule.mem_span_singleton_self v
      rw [hvfix] at hsgv_in
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsgv_in
      have hcoord : ∀ j : Fin 4, c * v j = sg K f (v j) := fun j => by
        have := congrFun hc j
        simpa [sgv_apply] using this
      have hsgvi_ne : sg K f (v i) ≠ 0 := fun h => hi ((sg K f).map_eq_zero_iff.mp h)
      have hci_ne : c * v i ≠ 0 := by rw [hcoord i]; exact hsgvi_ne
      have hc_ne : c ≠ 0 := fun h => hci_ne (by rw [h, zero_mul])
      let w : Fin 3 → Fx := fun j =>
        ⟨v (Fin.succ j) / v i, by
          rw [map_div₀, ← hcoord (Fin.succ j), ← hcoord i]
          exact mul_div_mul_left _ _ hc_ne
        ⟩
      refine ⟨(v i, w), ?_⟩
      have hv0' : v 0 = 0 := by simpa [Vtail] using hvtail
      funext j
      fin_cases j <;> simp [φ, w, hv0'] <;> field_simp [hi]
  have hcard1 : Nat.card {v : Fin 4 → K // v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
      sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}} ≤
      Nat.card (Set.range φ) :=
    Nat.card_le_card_of_injective
      (fun x : {v : Fin 4 → K // v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
          sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}} =>
        ⟨x.1, hsub x.2⟩)
      (fun a b h => Subtype.ext (congrArg (fun x : Set.range φ => (x : Fin 4 → K)) h))
  have hcard2 : Nat.card (Set.range φ) ≤ Nat.card (K × (Fin 3 → Fx)) :=
    Nat.card_le_card_of_surjective (Set.rangeFactorization φ)
      Set.rangeFactorization_surjective
  have hcard3 : Nat.card (K × (Fin 3 → Fx)) = Nat.card K * (Nat.card Fx) ^ 3 := by
    rw [Nat.card_prod, Nat.card_pi]
    simp [Finset.prod_const, Nat.card_fin]
  calc
    Nat.card {v : Fin 4 → K // v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
        sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}}
        ≤ Nat.card (Set.range φ) := hcard1
    _ ≤ Nat.card (K × (Fin 3 → Fx)) := hcard2
    _ = Nat.card K * (Nat.card Fx) ^ 3 := hcard3
    _ ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 3 := by
      rw [hK]
      gcongr
      exact card_sg_fixed_le (K := K) (f := f) hK
    _ = (2 ^ f) ^ 5 := by ring

theorem exists_nonrat_point_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : Finset (Submodule K (Fin 4 → K))) (hS : ∀ T ∈ S, T ≤ Vtail ∧ finrank K T = 2)
    (hcard : S.card ≤ 6) :
    ∃ t : Submodule K (Fin 4 → K), t ≤ Vtail ∧ finrank K t = 1 ∧ sgS K f 4 t ≠ t ∧
      ∀ T ∈ S, ¬ t ≤ T := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let R : Finset (Fin 4 → K) :=
    Finset.univ.filter (fun v => v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
      sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v})
  have hRcard : R.card ≤ (2 ^ f) ^ 5 := by
    have hReq : R.card = Nat.card {v : Fin 4 → K // v ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
        sgS K f 4 (Submodule.span K {v}) = Submodule.span K {v}} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hReq]
    exact card_rat_le (K := K) (f := f) hK
  have h0R : (0 : Fin 4 → K) ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Submodule.zero_mem _, ?_⟩
    rw [Submodule.span_zero_singleton, sgS_bot hK]
  have hsum : ∑ T ∈ S, Nat.card K ^ finrank K T = S.card * (2 ^ f) ^ 4 := by
    have hfin : ∀ T ∈ S, finrank K T = 2 := fun T hT => (hS T hT).2
    calc
      ∑ T ∈ S, Nat.card K ^ finrank K T = ∑ T ∈ S, (2 ^ f) ^ 4 := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [hfin T hT, hK]
        ring
      _ = S.card * (2 ^ f) ^ 4 := by rw [Finset.sum_const, smul_eq_mul]
  have hlt : ∑ T ∈ S, Nat.card K ^ finrank K T + R.card
      < Nat.card K ^ finrank K (Vtail : Submodule K (Fin 4 → K)) := by
    rw [hsum, finrank_Vtail]
    have hquad : 6 + 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
    have hlt2 : 6 * (2 ^ f) ^ 4 + (2 ^ f) ^ 5 < (2 ^ f) ^ 6 := by
      calc
        6 * (2 ^ f) ^ 4 + (2 ^ f) ^ 5 = (2 ^ f) ^ 4 * (6 + 2 ^ f) := by ring
        _ < (2 ^ f) ^ 4 * (2 ^ f) ^ 2 := by
          gcongr
        _ = (2 ^ f) ^ 6 := by ring
    calc
      S.card * (2 ^ f) ^ 4 + R.card ≤ 6 * (2 ^ f) ^ 4 + (2 ^ f) ^ 5 := by
        gcongr
      _ < (2 ^ f) ^ 6 := hlt2
      _ = Nat.card K ^ 3 := by rw [hK]; ring
  obtain ⟨u, huU, hu_notin, huR⟩ := exists_mem_notMem_affine_of_sum_lt_exc
    (V := Fin 4 → K) (U := (Vtail : Submodule K (Fin 4 → K))) (s := S) (T := id)
    (c := fun _ => 0) (R := R) (fun T hT => (hS T hT).1)
    (fun _ _ => Submodule.zero_mem _) hlt
  have hu_ne : u ≠ 0 := by
    intro h
    apply huR
    rw [h]
    exact h0R
  refine ⟨Submodule.span K {u}, ?_, ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU)
  · exact finrank_span_singleton hu_ne
  · intro h
    apply huR
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨huU, h⟩
  · intro T hT hle
    have huT : u ∈ T := hle (Submodule.mem_span_singleton_self u)
    exact hu_notin T hT (by simpa using huT)

end CFSG.ClassicalInvolution.Phan.PhanE

end
