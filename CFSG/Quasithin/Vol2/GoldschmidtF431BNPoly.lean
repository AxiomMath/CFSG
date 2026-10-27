module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNAct
public import CFSG.GH74.BNPair.Lemma309
public import CFSG.Quasithin.Recognition.F4Basic

public section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Quasithin

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem uniqueGeod : UniqueGeod (Γ D) n := by
  intro m p q hp hq h0 hm hmn
  have lp : IsGLSPath D.graph ((List.range (m + 1)).map p) :=
    isGLSPath_map_range p m p.adj (GPath.noBack_of_dist_eq D.polyHyp.connected p hp)
  have lq : IsGLSPath D.graph ((List.range (m + 1)).map q) :=
    isGLSPath_map_range q m q.adj (GPath.noBack_of_dist_eq D.polyHyp.connected q hq)
  have hlast : ∀ r : GPath (Γ D) m, ((List.range (m + 1)).map r).getLast? = some (r m) := by
    intro r
    simp [List.range_succ]
  have hhead : ∀ r : GPath (Γ D) m, ((List.range (m + 1)).map r).head? = some (r 0) := by
    intro r
    simp [List.range_succ_eq_map]
  have heq := D.polyHyp.unique lp lq (hhead p) (by rw [hhead q, h0]) (hlast p)
    (by rw [hlast q, hm]) (by simp; omega) (by simp; omega)
  refine GPath.ext' fun i hi => ?_
  have := congrArg (fun l : List D.Vertex => l[i]?) heq
  simpa [List.getElem?_map, List.getElem?_range (show i < m + 1 by omega)] using this

section Apartment

variable {D}
variable (m₁ m₂ : D.N) (hm₁ : (m₁ : D.Weyl) = D.w₁) (hm₂ : (m₂ : D.Weyl) = D.w₂) (first : Bool)

theorem stType_add_two (k : ℕ) : stType first (k + 2) = stType first k := by
  rw [stType_succ, stType_succ, Bool.not_not]

theorem stType_add_two_mul (k t : ℕ) : stType first (k + 2 * t) = stType first k := by
  induction t with
  | zero => rfl
  | succ t ih => rw [show k + 2 * (t + 1) = (k + 2 * t) + 2 by ring, stType_add_two, ih]

theorem chainElt_add_two_mul (k t : ℕ) :
    chainElt (D.lifts m₁ m₂) first (k + 2 * t) =
      (D.lifts m₁ m₂ (!stType first k) * D.lifts m₁ m₂ (stType first k)) ^ t *
        chainElt (D.lifts m₁ m₂) first k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show k + 2 * (t + 1) = (k + 2 * t) + 2 by ring]
    simp only [chainElt, stType_succ, stType_add_two_mul, pow_succ', mul_assoc] at ih ⊢
    rw [ih]

include hm₁ hm₂ in
theorem lifts_mem_pgen (s : Bool) :
    D.lifts m₁ m₂ s ∈ pgen D.B D.N D.w₁ D.w₂ s :=
  (mem_parabolic_single_iff D.rank2.tits (D.rank2.gen_mem s)).2
    (Or.inr (D.lifts_mem_dc m₁ m₂ hm₁ hm₂ s))

include hm₁ hm₂ in
theorem lifts_pow_mem_B (s : Bool) :
    (D.lifts m₁ m₂ (!s) * D.lifts m₁ m₂ s) ^ n ∈ D.B := by
  have h1 : (((D.liftsN m₁ m₂ (!s) * D.liftsN m₁ m₂ s) ^ n : D.N) : D.Weyl) = 1 := by
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, D.liftsN_mk m₁ m₂ hm₁ hm₂,
      D.liftsN_mk m₁ m₂ hm₁ hm₂]
    have := (D.rank2.dih_gen (!s)).pow_eq_one
    rwa [Bool.not_not] at this
  have h2 := (mk_eq_one_iff (B := D.B) (N := D.N)).1 h1
  simpa [D.lifts_eq m₁ m₂] using h2

include hm₁ hm₂ in
theorem chainElt_period (j : ℕ) :
    chainElt (D.lifts m₁ m₂) first (j + 2 * n) * (chainElt (D.lifts m₁ m₂) first j)⁻¹ ∈ D.B := by
  rw [chainElt_add_two_mul, mul_assoc, mul_inv_cancel, mul_one]
  exact lifts_pow_mem_B m₁ m₂ hm₁ hm₂ _

include hm₁ hm₂ in
theorem vv_period (k : ℕ) :
    D.vv m₁ m₂ first (k + 2 * n) = D.vv m₁ m₂ first k := by
  cases k with
  | zero =>
    obtain ⟨j, hj⟩ : ∃ j, 0 + 2 * n = j + 1 := ⟨2 * n - 1, by have := D.three_le; omega⟩
    have hodd : ¬ Even j := by
      intro he
      have h2 : Even (j + 1) := by rw [← hj]; exact ⟨n, by ring⟩
      exact (Nat.even_add_one.1 h2) he
    have hs : stType first j = !first := by simp [stType, hodd]
    rw [hj, D.vv_succ, D.vv_zero, hs]
    refine vtx_eq_vtx ?_
    have hB : chainElt (D.lifts m₁ m₂) first (j + 1) ∈ D.B := by
      have := chainElt_period m₁ m₂ hm₁ hm₂ first 0
      rw [hj] at this
      simpa [chainElt] using this
    have e : chainElt (D.lifts m₁ m₂) first j * (1 : X)⁻¹ =
        (D.lifts m₁ m₂ (!first))⁻¹ * chainElt (D.lifts m₁ m₂) first (j + 1) := by
      simp only [chainElt, hs, inv_one, mul_one]
      group
    rw [e]
    exact (pgen D.B D.N D.w₁ D.w₂ (!first)).mul_mem
      ((pgen D.B D.N D.w₁ D.w₂ (!first)).inv_mem (lifts_mem_pgen m₁ m₂ hm₁ hm₂ _))
      (D.rank2.B_le_pgen _ hB)
  | succ j =>
    rw [show j + 1 + 2 * n = (j + 2 * n) + 1 by ring, D.vv_succ, D.vv_succ, stType_add_two_mul]
    exact vtx_eq_vtx (D.rank2.B_le_pgen _ (chainElt_period m₁ m₂ hm₁ hm₂ first j))

end Apartment

theorem isGenPolygon : IsGenPolygon (Γ D) n := by
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  have hconn := D.polyHyp.connected
  have hc : ∀ a b : V D, (Γ D).Adj a b →
      vtype D.B D.N D.w₁ D.w₂ a ≠ vtype D.B D.N D.w₁ D.w₂ b :=
    fun a b h => D.rank2.vtype_ne_of_adj h
  have hn : 2 ≤ n := by have := D.three_le; omega
  refine
    { connected := hconn
      bipartite := ⟨_, hc⟩
      diam_le := fun u v => (D.polyHyp.reach_dist u v).2
      diam_eq := ⟨D.vv m₁ m₂ true 0, D.vv m₁ m₂ true n,
        D.polyHyp.dist_eq_of_path (D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ true)
          (D.basePath_head m₁ m₂ true) ?_ (D.basePath_length m₁ m₂ true)⟩
      uniqueGeod := uniqueGeod D
      polygon := ⟨_, GPath.isPolygon_of_periodic hconn hc hn (uniqueGeod D) _
        (fun i => D.vv_adj m₁ m₂ hm₁ hm₂ true i) (fun i => D.vv_ne m₁ m₂ hm₁ hm₂ true i)
        (fun i => vv_period m₁ m₂ hm₁ hm₂ true i)⟩
      valence := fun v => le_trans (by norm_num) (D.polyHyp.valency v) }
  simp [RankTwoSystem.basePath, List.range_succ]

theorem three_le_card_neighborSet [Finite X] (v : V D) : 3 ≤ Nat.card ((Γ D).neighborSet v) := by
  have hfin : ((Γ D).neighborSet v).Finite := Set.toFinite _
  have h3 := D.polyHyp.valency v
  rw [← hfin.cast_ncard_eq] at h3
  rw [Nat.card_coe_set_eq]
  exact_mod_cast h3

end CFSG.Quasithin.H13.F431.BN
