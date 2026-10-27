module

public import CFSG.Timmesfeld.ARS.CaseHHexagon
public import CFSG.Timmesfeld.ARS.CaseHOrder
public import CFSG.CharacterTheory.Wreathed.FourPointUnitaryRecognitionCore

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.Combinatorics.HexagonStabilizerFaithful CFSG.GroupTheory.InvolutionHexagon
  CFSG.Wreathed.FourPointUnitaryRecognition CFSG.Blueprint

namespace CaseH

theorem isSolvable_perm_of_card_le_three {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α ≤ 3) : Group.IsSolvable (Equiv.Perm α) := by
  have : Group.IsSolvable (alternatingGroup α) := by
    rcases (Fintype.card α).lt_or_ge 2 with h2 | h2
    · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 (by omega)
      infer_instance
    · have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      have hc := two_mul_card_alternatingGroup (α := α)
      rw [Fintype.card_perm] at hc
      have h3 : Fintype.card (alternatingGroup α) = 1 ∨ Fintype.card (alternatingGroup α) = 3 := by
        have h23 : Fintype.card α = 2 ∨ Fintype.card α = 3 := by omega
        rcases h23 with h23 | h23
        · rw [h23] at hc
          left
          simp only [Nat.factorial] at hc
          omega
        · rw [h23] at hc
          right
          simp only [Nat.factorial] at hc
          omega
      rcases h3 with h3 | h3
      · have : Subsingleton (alternatingGroup α) :=
          Fintype.card_le_one_iff_subsingleton.1 h3.le
        infer_instance
      · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsCyclic (alternatingGroup α) :=
          isCyclic_of_prime_card (by rw [Nat.card_eq_fintype_card, h3])
        infer_instance
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩)

theorem eq_top_of_index_le_three {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (H : Subgroup K) (hH : H.index ≤ 3) : H = ⊤ := by
  classical
  have := Fintype.ofFinite (K ⧸ H)
  set φ := MulAction.toPermHom K (K ⧸ H) with hφ
  have hcard : Fintype.card (K ⧸ H) ≤ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hH
  have := isSolvable_perm_of_card_le_three hcard
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  refine eq_top_iff.2 fun k _ => ?_
  have h1 : φ k = 1 := congrArg Subtype.val (Subsingleton.elim (⟨φ k, k, rfl⟩ : φ.range) 1)
  have h2 : k • ((1 : K) : K ⧸ H) = ((1 : K) : K ⧸ H) := by
    have := congrArg (fun σ : Equiv.Perm (K ⧸ H) => σ ((1 : K) : K ⧸ H)) h1
    simpa [hφ] using this
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one,
    inv_mem_iff] at h2
  exact h2

theorem nonempty_mulEquiv_statedSU_of_hexagon_action_of_le {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] (hG : 6048 ≤ 3 * Nat.card G) {V : Type*} [Fintype V] (Δ : SimpleGraph V)
    [DecidableRel Δ.Adj] (hcard : Fintype.card V = 126) (hconn : Δ.Connected)
    (hdeg : ∀ v, Δ.degree v = 3) (col : Δ.Coloring Bool)
    (hcyc : ∀ (v : V) (c : Δ.Walk v v), c.IsCycle → 12 ≤ c.length)
    (ρ : G →* (Δ ≃g Δ)) (hρ : Function.Injective ρ) (hρcol : ∀ g v, col (ρ g v) = col v)
    {F : Type} [Field F] (hF : Nat.card F = 9) : Nonempty (G ≃* StatedSU 3 3 F) := by
  classical
  have := finite_nonisoLine hF
  have := finite_hexLine hF
  have : Fintype (NonisoLine F ⊕ HexLine F) := Fintype.ofFinite _
  have hcardF : Fintype.card (NonisoLine F ⊕ HexLine F) = 126 := by
    rw [← Nat.card_eq_fintype_card, card_incGraph_vertices hF]
  obtain ⟨hconnF, -⟩ := hexagon_facts hF
  have hdegF : ∀ v, (incGraph F).degree v = 3 := fun v => by
    rw [degree_eq_ncard, ncard_neighborSet hF]
  have hcycF : ∀ (v : NonisoLine F ⊕ HexLine F) (c : (incGraph F).Walk v v), c.IsCycle →
      12 ≤ c.length := fun v c hc => twelve_le_length hF c hc
  obtain ⟨ε₁, ε₂, ψ, h1, h2⟩ :=
    CFSG.Combinatorics.HexagonUniqueDuality.order_two_generalized_hexagons_unique_up_to_duality
      Δ hcard hconn hdeg col hcyc (incGraph F) hcardF hconnF hdegF (incColoring F) hcycF
  have hψ := colour_relation h1 h2
  have hΩ :=
    (CFSG.Combinatorics.HexagonAutomorphismBound.order_two_generalized_hexagon_automorphism_bound
      Δ hcard hconn hdeg col hcyc).2
  have := finite_iso Δ
  let ρ' : G →* partAut Δ col := ρ.codRestrict (partAut Δ col) fun g => mem_partAut.mpr (hρcol g)
  have hρ' : Function.Injective ρ' := fun g g' h => hρ (congrArg Subtype.val h)
  let κ := incAction hF
  let σ₀ : StatedSU 3 3 F →* (Δ ≃g Δ) :=
    { toFun := fun k => (ψ.trans (κ k)).trans ψ.symm
      map_one' := RelIso.ext fun v => by
        show ψ.symm (κ 1 (ψ v)) = v
        rw [map_one, RelIso.one_apply, RelIso.symm_apply_apply]
      map_mul' := fun k k' => RelIso.ext fun v => by
        show ψ.symm (κ (k * k') (ψ v)) = ψ.symm (κ k (ψ (ψ.symm (κ k' (ψ v)))))
        rw [map_mul, RelIso.mul_apply, RelIso.apply_symm_apply] }
  have hσ₀ : ∀ k v, σ₀ k v = ψ.symm (κ k (ψ v)) := fun k v => rfl
  have hσcol : ∀ k, σ₀ k ∈ partAut Δ col := fun k => mem_partAut.mpr fun v => by
    have hu := hψ (σ₀ k v)
    rw [hσ₀, RelIso.apply_symm_apply, incColoring_incAction, hψ v] at hu
    rw [hσ₀]
    generalize col (ψ.symm (κ k (ψ v))) = b at hu ⊢
    generalize col v = b' at hu ⊢
    revert hu
    cases b <;> cases b' <;> cases ε₁ <;> cases ε₂ <;> decide
  let σ : StatedSU 3 3 F →* partAut Δ col := σ₀.codRestrict (partAut Δ col) hσcol
  have hσ : Function.Injective σ := by
    intro k k' h
    have h' : σ₀ k = σ₀ k' := congrArg Subtype.val h
    apply incAction_injective hF
    refine RelIso.ext fun w => ?_
    have := DFunLike.congr_fun h' (ψ.symm w)
    rw [hσ₀, hσ₀, RelIso.apply_symm_apply] at this
    exact ψ.symm.injective this
  have : Group.IsPerfect (StatedSU 3 3 F) := isPerfect_statedSU_three_three hF
  have : Finite (StatedSU 3 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  have hS : σ.range = commutator (partAut Δ col) :=
    perfect_embedding_range_eq_commutator_of_card_le_twice σ hσ
      (by rw [card_statedSU hF]; omega)
  have hGle : ρ'.range ≤ σ.range := by
    rw [hS, MonoidHom.range_eq_map, ← (Group.isPerfect_def.mp ‹Group.IsPerfect G›),
      commutator_def, Subgroup.map_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  set H := ρ'.range.comap σ with hHdef
  have hHcard : Nat.card H = Nat.card G := by
    rw [← Subgroup.card_map_of_injective hσ, Subgroup.map_comap_eq, inf_of_le_right hGle]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ').toEquiv).symm
  have hHidx : H.index ≤ 3 := by
    have h1 := H.card_mul_index
    rw [card_statedSU hF, hHcard] at h1
    by_contra h4
    push Not at h4
    nlinarith
  have hHtop := eq_top_of_index_le_three H hHidx
  have heq : ρ'.range = σ.range := by
    refine le_antisymm hGle ?_
    rintro _ ⟨k, rfl⟩
    have hk : k ∈ H := hHtop ▸ Subgroup.mem_top k
    exact hk
  exact ⟨(MonoidHom.ofInjective hρ').trans
    ((MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hσ).symm)⟩

end CaseH

open CaseH in
theorem lieModel_PSU_of_caseH {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    (hH : SigmaEqLambda R) {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (hL : (linesThrough R A).ncard = 3) : LieModel G .PSU 3 3 1 := by
  classical
  have := h.finite
  have hR := h.root
  have H₀ := hexagonData h hH hA hq hL
  have : Fintype (Pt R ⊕ Ln R) := Fintype.ofFinite _
  have hcard : Fintype.card (Pt R ⊕ Ln R) = 126 := by
    rw [← Nat.card_eq_fintype_card, H₀.card_vertices]
  obtain ⟨-, hconn, -⟩ := H₀.hexagon
  have hdeg : ∀ v, (incidenceGraph (inc R)).degree v = 3 := fun v => by
    rw [degree_eq_ncard, H₀.ncard_neighborSet]
  have : Group.IsPerfect G := isPerfect h
  have hG := two_thousand_sixteen_le_card h hH hA hq hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF9 : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨f⟩ := nonempty_mulEquiv_statedSU_of_hexagon_action_of_le (by omega)
    (incidenceGraph (inc R)) hcard hconn hdeg (incidenceColoring (inc R))
    (fun v c hc => H₀.twelve_le_length c hc) (conjAction hR)
    (conjAction_injective h fun B hB => (hR.card_eq hB hA).trans hq)
    (incidenceColoring_conjAction hR) hF9
  obtain ⟨hadm, K, hK, hKfin, hKcard, ⟨e'⟩⟩ := classicalModel_statedSU hF9
  exact Or.inl ⟨by decide, hadm, K, hK, hKfin, hKcard, ⟨f.trans e'⟩⟩

end CFSG.Timmesfeld.ARS
