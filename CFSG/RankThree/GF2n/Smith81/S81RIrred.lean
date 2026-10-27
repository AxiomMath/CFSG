module

public import CFSG.RankThree.GF2n.Smith81.S81NModel1

open CFSG.RankThree.GF2n.Smith81.A5Cube

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private theorem m2_move_023_024 [CharP K 2] (c : K) :
    rho K (transvGL K 4 3 (by decide) c) (ub K 0 2 3) - ub K 0 2 3 = c • ub K 0 2 4 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 4 3 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_move_024_025 [CharP K 2] (c : K) :
    rho K (transvGL K 5 4 (by decide) c) (ub K 0 2 4) - ub K 0 2 4 = c • ub K 0 2 5 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 5 4 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_move_024_034 [CharP K 2] (c : K) :
    rho K (transvGL K 3 2 (by decide) c) (ub K 0 2 4) - ub K 0 2 4 = c • ub K 0 3 4 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 3 2 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_move_024_023 [CharP K 2] (c : K) :
    rho K (transvGL K 3 4 (by decide) c) (ub K 0 2 4) - ub K 0 2 4 = c • ub K 0 2 3 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 3 4 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_move_025_045 [CharP K 2] (c : K) :
    rho K (transvGL K 4 2 (by decide) c) (ub K 0 2 5) - ub K 0 2 5 = c • ub K 0 4 5 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 4 2 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_move_034_035 [CharP K 2] (c : K) :
    rho K (transvGL K 5 4 (by decide) c) (ub K 0 3 4) - ub K 0 3 4 = c • ub K 0 3 5 := by
  apply cfm_ext
  intro m hm
  rw [cfm_sub, cfm_rho_transv 5 4 (by decide) c _ m hm, cfm_smul]
  interval_cases m <;> simp (config := {decide := true}) [cfm_ub]

private theorem m2_line {S : AddSubgroup (Cube K)} {k l : Fin 6} (hkl : k ≠ l)
    (hstab : ∀ c : K, ∀ s ∈ S, rho K (transvGL K k l hkl c) s ∈ S)
    {u v : Cube K} (hmove : ∀ c : K, rho K (transvGL K k l hkl c) u - u = c • v)
    {a : K} (ha : a ≠ 0) (hu : a • u ∈ S) : ∀ x : K, x • v ∈ S := by
  intro x
  have h1 := S.sub_mem (hstab (x / a) (a • u) hu) hu
  have hax : a * (x / a) = x := by field_simp
  have h2 : rho K (transvGL K k l hkl (x / a)) (a • u) - a • u = x • v := by
    have e1 : rho K (transvGL K k l hkl (x / a)) (a • u) =
        a • rho K (transvGL K k l hkl (x / a)) u := map_smul _ _ _
    rw [e1]
    calc a • rho K (transvGL K k l hkl (x / a)) u - a • u
        = a • (rho K (transvGL K k l hkl (x / a)) u - u) := (smul_sub _ _ _).symm
      _ = a • ((x / a) • v) := by rw [hmove (x / a)]
      _ = (a * (x / a)) • v := smul_smul _ _ _
      _ = x • v := by rw [hax]
  rwa [h2] at h1

theorem irred_range_tInv1 [Finite K] [CharP K 2] (S : AddSubgroup (Cube K)) (hS : S ≠ ⊥)
    (hSR : ∀ s ∈ S, s ∈ LinearMap.range (rho K (tInv1 K) - 1))
    (hstab : ∀ (i j : Fin 6) (hij : i ≠ j) (c : K), 2 ≤ i.val → 2 ≤ j.val →
      ∀ s ∈ S, rho K (transvGL K i j hij c) s ∈ S) :
    ∀ r ∈ LinearMap.range (rho K (tInv1 K) - 1), r ∈ S := by
  obtain ⟨s, hsS, hs0, hsfix⟩ := exists_fixed_vec_of_gens (K := K) ![0, 0, 0, 1, 2, 3]
    (by decide) (fun i j => 2 ≤ i.val ∧ i.val < j.val) (by decide) S hS
    (fun i j hij c hP s hs => hstab i j hij c hP.1
      (by obtain ⟨h1, h2⟩ := hP; omega) s hs)
  have hr := (ker_range_eq1 (K := K)).2
  have hsR : s ∈ Submodule.span K (Set.range (ranG1 K)) := by
    rw [← hr]
    exact hSR s hsS
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hsR
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), (2 ≤ i.val ∧ i.val < j.val) →
      rho K (transvGL K i j hij 1) s = s := fun i j hij hp => hsfix i j hij 1 hp
  have hs_eq : s = cfm K s 13 • ub K 0 2 3 := by
    apply cfm_ext3
    intro m hm hc'
    rcases exists_mask3 hm hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (rw [cfm_zero_of_fixed (fun i j => 2 ≤ i.val ∧ i.val < j.val) hz _ hm (by decide)]
       simp [cfm_smul, cfm_ub_mask]; done)
    | (simp [cfm_smul, cfm_ub_mask]; done)
    | (rw [← hc]; simp [ranG1, cfm_add, cfm_smul, cfm_ub_mask, Fin.sum_univ_succ, cfm_zero]; done)
  have hc0 : cfm K s 13 ≠ 0 := by
    intro h
    apply hs0
    rw [hs_eq, h, zero_smul]
  have hv : cfm K s 13 • ub K 0 2 3 ∈ S := by
    rw [← hs_eq]
    exact hsS
  have L024 : ∀ x : K, x • ub K 0 2 4 ∈ S :=
    m2_line (k := 4) (l := 3) (by decide)
      (fun x t ht => hstab 4 3 (by decide) x (by decide) (by decide) t ht)
      m2_move_023_024 hc0 hv
  have L025 : ∀ x : K, x • ub K 0 2 5 ∈ S :=
    m2_line (k := 5) (l := 4) (by decide)
      (fun x t ht => hstab 5 4 (by decide) x (by decide) (by decide) t ht)
      m2_move_024_025 one_ne_zero (L024 1)
  have L034 : ∀ x : K, x • ub K 0 3 4 ∈ S :=
    m2_line (k := 3) (l := 2) (by decide)
      (fun x t ht => hstab 3 2 (by decide) x (by decide) (by decide) t ht)
      m2_move_024_034 one_ne_zero (L024 1)
  have L023 : ∀ x : K, x • ub K 0 2 3 ∈ S :=
    m2_line (k := 3) (l := 4) (by decide)
      (fun x t ht => hstab 3 4 (by decide) x (by decide) (by decide) t ht)
      m2_move_024_023 one_ne_zero (L024 1)
  have L045 : ∀ x : K, x • ub K 0 4 5 ∈ S :=
    m2_line (k := 4) (l := 2) (by decide)
      (fun x t ht => hstab 4 2 (by decide) x (by decide) (by decide) t ht)
      m2_move_025_045 one_ne_zero (L025 1)
  have L035 : ∀ x : K, x • ub K 0 3 5 ∈ S :=
    m2_line (k := 5) (l := 4) (by decide)
      (fun x t ht => hstab 5 4 (by decide) x (by decide) (by decide) t ht)
      m2_move_034_035 one_ne_zero (L034 1)
  have hL : ∀ (i : Fin 6) (x : K), x • ranG1 K i ∈ S := by
    intro i x
    fin_cases i
    · exact L023 x
    · exact L024 x
    · exact L025 x
    · exact L034 x
    · exact L035 x
    · exact L045 x
  intro r hr'
  rw [hr] at hr'
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hr'
  rw [← hc']
  exact S.sum_mem fun i _ => hL i (c' i)

end CFSG.RankThree.GF2n.Smith81.A5Cube
