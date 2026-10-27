module

public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
  CFSG.Assembly.LowTwoRank

section Index

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail in
theorem card_orthogonalGroup_eq_two_mul (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (hPP' : P.Orth P') (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card (elementaryGroup Q) := by
  classical
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  set E := elementaryGroup Q
  have hEO : E ≤ O := elementaryGroup_le_orthogonalGroup Q
  set v₀ := P.e + P.f
  have hv₀ : Q v₀ = 1 := by
    rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hv₀
    exact zero_ne_one hv₀
  set s₀ := reflect Q v₀
  have hs₀O : s₀ ∈ O := reflect_mem_orthogonalGroup Q v₀
  have hs₀inv : s₀⁻¹ = s₀ := reflect_inv Q v₀
  have hs₀2 : s₀ * s₀ = 1 := reflect_mul_self Q v₀
  obtain ⟨-, -, -, hsep⟩ := orthogonal_geometry_char_two_reflection_separation hQ hT
  have hs₀E : s₀ ∉ E := hsep v₀ (by rw [hv₀]; exact one_ne_zero)
  have hrefl : ∀ v, Q v ≠ 0 → reflect Q v * s₀ ∈ E := by
    intro v hv
    obtain ⟨c, hc⟩ := exists_sq_eq_of_charTwo (Q v)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv (by rw [← hc]; ring)
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv (QuadraticMap.map_zero Q)
    obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hQ hPP' (smul_ne_zero hc0 hv₀0)
      hv0 (by rw [map_smul_eq_sq, hv₀, mul_one, hc])
    have hgO := hEO hg
    have hconj : reflect Q v = g * s₀ * g⁻¹ := by
      rw [← hgv, ← reflect_conj hgO, reflect_smul hc0]
    have hmem := conj_mem_elementaryGroup hs₀O (inv_mem hg)
    rw [hs₀inv] at hmem
    rw [hconj, mul_assoc, mul_assoc]
    rw [mul_assoc] at hmem
    exact mul_mem hg hmem
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | g ∈ O ∧ (g ∈ E ∨ g * s₀ ∈ E)}
      mul_mem' := by
        rintro g h ⟨hgO, hg⟩ ⟨hhO, hh⟩
        refine ⟨mul_mem hgO hhO, ?_⟩
        rcases hg with hg | hg <;> rcases hh with hh | hh
        · exact Or.inl (mul_mem hg hh)
        · right
          rw [mul_assoc]
          exact mul_mem hg hh
        · right
          have : g * h * s₀ = g * s₀ * (s₀⁻¹ * h * s₀⁻¹⁻¹) := by group
          rw [this]
          exact mul_mem hg (conj_mem_elementaryGroup (inv_mem hs₀O) hh)
        · left
          have : g * h = g * s₀ * (s₀ * (h * s₀) * s₀⁻¹) := by
            calc g * h = g * (s₀ * s₀) * h := by rw [hs₀2, mul_one]
              _ = g * s₀ * (s₀ * (h * s₀) * s₀⁻¹) := by group
          rw [this]
          exact mul_mem hg (conj_mem_elementaryGroup hs₀O hh)
      one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
      inv_mem' := by
        rintro g ⟨hgO, hg⟩
        refine ⟨inv_mem hgO, ?_⟩
        rcases hg with hg | hg
        · exact Or.inl (inv_mem hg)
        · right
          have : g⁻¹ * s₀ = s₀ * (g * s₀)⁻¹ * s₀⁻¹ := by
            calc g⁻¹ * s₀ = g⁻¹ * s₀⁻¹ := by rw [hs₀inv]
              _ = s₀ * (g * s₀)⁻¹ * s₀⁻¹ := by group
          rw [this]
          exact conj_mem_elementaryGroup hs₀O (inv_mem hg) }
  have hOH : O ≤ H := hgen.trans ((Subgroup.closure_le _).mpr fun x hx => by
    rcases hx with ⟨v, rfl⟩ | hx
    · refine ⟨reflect_mem_orthogonalGroup Q v, ?_⟩
      by_cases hv : Q v = 0
      · rw [reflect_of_map_eq_zero hv]
        exact Or.inl (one_mem _)
      · exact Or.inr (hrefl v hv)
    · exact ⟨hEO hx, Or.inl hx⟩)
  have hidx : (E.subgroupOf O).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s₀, hs₀O⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : V ≃ₗ[K] V) ∈ E
    · refine Or.inr ⟨hb, fun hbs => hs₀E ?_⟩
      have := mul_mem (inv_mem hb) hbs
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact Or.inl ⟨((hOH b.2).2.resolve_left hb), hb⟩
  have hcard := (E.subgroupOf O).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEO).toEquiv] at hcard
  rw [← hcard, mul_comm]

end Index

theorem map_add_eq_one_of_hypPair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : Q (P.e + P.f) = 1 := by
  rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_elementaryGroup_quadPlus (hn : 4 ≤ n) :
    (Nat.card (elementaryGroup (quadPlus n K)) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : 0 < m + 1 := by omega
  have hnd := nondegenerate_polarBilin_quadPlus (m + 1) K
  have hidx := card_orthogonalGroup_eq_two_mul hnd
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (regular_quadPlus (by omega)).2
    (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega))
  have hO := (card_quadPlus (K := K) m).2
  rw [hidx] at hO
  push_cast at hO
  rw [Nat.add_sub_cancel, show (m + 1) * m = m * (m + 1) by ring]
  linarith

theorem card_elementaryGroup_quadMinus (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card (elementaryGroup (quadMinus n K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n + 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : 0 < m + 1 - 1 := by omega
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
  have hidx := card_orthogonalGroup_eq_two_mul hnd
    (minusPair_orth (K := K) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]))
    (regular_quadMinus hn hirr).2
    (orthogonalGroup_le_closure_of_two_eq_zero (minusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx hQ => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hx hQ)
      (fun x hx hx0 y hy hxy => exists_eq_smul_of_mem_tailSpace_minusFamily
        CharTwo.two_eq_zero hirr hn0 hx hx0 hy hxy) (by omega))
  have hO := (card_quadMinus (K := K) m hirr).2
  rw [hidx] at hO
  push_cast at hO
  show (Nat.card (elementaryGroup (quadMinus (m + 1) K b c)) : ℤ) =
    (Nat.card K : ℤ) ^ ((m + 1) * m) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1)
  rw [show (m + 1) * m = m * (m + 1) by ring]
  linarith

omit [Finite K] in
theorem card_statedProj_statedOmega {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K} (hQ₀ : ⇑Q = Q₀) (hv : ∃ v, Q v ≠ 0) :
    Nat.card (StatedProj (StatedOmega Q₀)) = Nat.card (StatedOmega Q₀) := by
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ₀ hv
  have h1 : Nat.card ((StatedScalars σ K).subgroupOf (StatedOmega Q₀)) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars σ K).subgroupOf (StatedOmega Q₀))
  rw [h1, mul_one] at hc
  exact hc.symm

theorem card_statedProj_statedOmega_quadPlus (hn : 4 ≤ n) :
    (Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have P := plusPair K (⟨0, by omega⟩ : Fin n)
  rw [card_statedProj_statedOmega (coe_quadPlus n K) ⟨P.e + P.f, by
      rw [map_add_eq_one_of_hypPair P]; exact one_ne_zero⟩,
    statedOmega_quadPlus_eq_map (by omega), Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact card_elementaryGroup_quadPlus hn

theorem card_statedProj_statedOmega_quadMinus (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card (StatedProj (StatedOmega (StatedQuadMinus n K b c))) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n + 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have P := minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))
  rw [card_statedProj_statedOmega (coe_quadMinus n K b c) ⟨P.e + P.f, by
      rw [map_add_eq_one_of_hypPair P]; exact one_ne_zero⟩,
    statedOmega_quadMinus_eq_map hn hirr, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact card_elementaryGroup_quadMinus hn hirr

end Models

end CFSG.Timmesfeld.ClassicalOrders
