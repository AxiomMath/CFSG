module

public import CFSG.Quasithin.MS93.Q2GSp

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin.MS93.MSP
open scoped Matrix

variable {K : Type} [Field K]

theorem transv_one_mulVec_eq_iff {x : V4 K} (hx : x ≠ 0) {v : V4 K} :
    mat (transv x 1) *ᵥ v = v ↔ form K x v = 0 := by
  rw [transv_mulVec, one_mul, add_eq_left, smul_eq_zero]
  exact ⟨fun h => h.resolve_right hx, Or.inl⟩

theorem transv_one_not_mem_commutator (hK : Nat.card K = 2) {x : V4 K} (hx : x ≠ 0) :
    transv x 1 ∉ commutator (Sp4 K) := by
  intro hmem
  have hp : IsPoint (K ∙ x) := finrank_span_singleton hx
  refine xPoint_not_le_commutator hK hp fun g hg => ?_
  obtain ⟨c, rfl⟩ := (mem_xPoint_span hx).1 hg
  rcases eq_zero_or_eq_one hK c with rfl | rfl
  · rw [transv_zero]
    exact Subgroup.one_mem _
  · exact hmem

theorem exists_ne_ne_mem_line {l : Submodule K (V4 K)} (hl : IsLine l) :
    ∃ x ∈ l, ∃ x' ∈ l, x ≠ 0 ∧ x' ≠ 0 ∧ x ≠ x' := by
  have hl0 : l ≠ ⊥ := by
    rintro rfl
    have := hl.1
    rw [finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hl0
  have hlt : K ∙ x < l := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem x l).2 hxl) fun heq => ?_
    have h1 := finrank_span_singleton (K := K) hx0
    rw [heq, hl.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x', hx'l, hx'⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, hxl, x', hx'l, hx0, fun h0 => hx' (h0 ▸ Submodule.zero_mem _), fun he => hx' ?_⟩
  rw [← he]
  exact Submodule.mem_span_singleton_self x

theorem exists_form_eq_zero_ne (hK : Nat.card K = 2) {x x' : V4 K} (hx : x ≠ 0) (hx' : x' ≠ 0)
    (hxx : x ≠ x') : ∃ v : V4 K, form K x' v = 0 ∧ form K x v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : perp (K ∙ x') ≤ perp (K ∙ x) := fun v hv =>
    mem_perp_span.2 (hcon v (mem_perp_span.1 hv))
  have h3 : Module.finrank K (perp (K ∙ x')) = Module.finrank K (perp (K ∙ x)) := by
    have h1 := finrank_perp (K ∙ x')
    have h2 := finrank_perp (K ∙ x)
    rw [finrank_span_singleton hx'] at h1
    rw [finrank_span_singleton hx] at h2
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle h3
  have hspan : K ∙ x' = K ∙ x := by
    have := congrArg perp heq
    rwa [perp_perp, perp_perp] at this
  have hmem : x' ∈ K ∙ x := hspan ▸ Submodule.mem_span_singleton_self x'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rcases eq_zero_or_eq_one hK c with rfl | rfl
  · exact hx' (by rw [← hc, zero_smul])
  · exact hxx (by rw [← hc, one_smul])

theorem form_sub_eq_zero (hK : Nat.card K = 2) {x v w : V4 K} (hv : form K x v ≠ 0)
    (hw : form K x w ≠ 0) : form K x (v - w) = 0 := by
  rw [map_sub]
  rcases eq_zero_or_eq_one hK (form K x v) with h | h
  · exact absurd h hv
  rcases eq_zero_or_eq_one hK (form K x w) with h' | h'
  · exact absurd h' hw
  rw [h, h', sub_self]

theorem exists_two_ne_one [Finite K] (hK : Nat.card K = 2) {l : Submodule K (V4 K)}
    (hl : IsLine l) : ∃ e ∈ qLine l ⊓ commutator (Sp4 K), ∃ e' ∈ qLine l ⊓ commutator (Sp4 K),
      e ≠ 1 ∧ e' ≠ 1 ∧ e' ≠ e ∧ e * e' ≠ 1 := by
  obtain ⟨e, he, he1⟩ := exists_ne_one hK hl
  refine ⟨e, he, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : ((qLine l ⊓ commutator (Sp4 K) : Subgroup (Sp4 K)) : Set (Sp4 K)) ⊆
      {1, e, e⁻¹} := fun f hf => by
    by_cases hf1 : f = 1
    · exact Or.inl hf1
    by_cases hfe : f = e
    · exact Or.inr (Or.inl hfe)
    · exact Or.inr (Or.inr (eq_inv_of_mul_eq_one_right (hcon f hf he1 hf1 hfe)))
  have h4 : Nat.card ↥(qLine l ⊓ commutator (Sp4 K)) = 4 := card_qLine_inf_commutator hK hl
  have h3 : ({1, e, e⁻¹} : Set (Sp4 K)).ncard ≤ 3 := by
    calc ({1, e, e⁻¹} : Set (Sp4 K)).ncard ≤ ({e, e⁻¹} : Set (Sp4 K)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (({e⁻¹} : Set (Sp4 K)).ncard + 1) + 1 := by
          gcongr
          exact Set.ncard_insert_le _ _
      _ = 3 := by rw [Set.ncard_singleton]
  have hle : Nat.card ↥(qLine l ⊓ commutator (Sp4 K)) ≤ 3 := by
    have h1 : Nat.card ↥(qLine l ⊓ commutator (Sp4 K)) =
        ((qLine l ⊓ commutator (Sp4 K) : Subgroup (Sp4 K)) : Set (Sp4 K)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h3
  omega

theorem eq_of_qLine_inf_commutator_le_stab [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {l l₀ : Submodule K (V4 K)} (hl : IsLine l) (hl₀ : IsLine l₀)
    (hle : qLine l ⊓ commutator (Sp4 K) ≤ MSP.stab l₀) : l₀ = l := by
  by_contra hne
  set E := qLine l ⊓ commutator (Sp4 K) with hE
  have hE4 : Nat.card E = 4 := card_qLine_inf_commutator hK hl
  have hE2 : IsPGroup 2 E := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hE4]
    norm_num
  have hl₀0 : l₀ ≠ ⊥ := by
    rintro rfl
    have := hl₀.1
    rw [finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨p₀, hp₀l₀, hp₀0, hp₀fix⟩ := exists_fixed_ne_zero hE2 hl₀0
    fun e he w hw => mulVec_mem_of_mem_stab (hle he) hw
  have hp₀l : p₀ ∈ l := by
    rw [← fixSp_qLine_inf_commutator hK hl]
    exact fun e he => hp₀fix e he
  obtain ⟨w, hwl₀, hwl⟩ : ∃ w ∈ l₀, w ∉ l := by
    by_contra hcon
    push Not at hcon
    exact hne (Submodule.eq_of_le_of_finrank_eq hcon (by rw [hl₀.1, hl.1]))
  have hdim : Module.finrank K ↥(l ⊓ l₀) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h2 : Module.finrank K ↥(l ⊓ l₀) ≤ 2 := by
      have := Submodule.finrank_mono (inf_le_left : l ⊓ l₀ ≤ l)
      rwa [hl.1] at this
    have heq := Submodule.eq_of_le_of_finrank_eq (inf_le_right : l ⊓ l₀ ≤ l₀)
      (by rw [hl₀.1]; omega)
    have hw' : w ∈ l ⊓ l₀ := by
      rw [heq]
      exact hwl₀
    exact hwl hw'.1
  have hspan : K ∙ p₀ = l ⊓ l₀ := by
    refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2
      ⟨hp₀l, hp₀l₀⟩) ?_
    rw [finrank_span_singleton hp₀0]
    have : 0 < Module.finrank K ↥(l ⊓ l₀) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨p₀, hp₀l, hp₀l₀⟩, fun h0 => hp₀0 (congrArg Subtype.val h0)⟩
    omega
  have hew : ∀ e ∈ E, e ≠ 1 → mat e *ᵥ w = w + p₀ := by
    intro e he he1
    have hd : mat e *ᵥ w - w ∈ l ⊓ l₀ := by
      refine ⟨?_, sub_mem (mulVec_mem_of_mem_stab (hle he) hwl₀) hwl₀⟩
      have he' : e ∈ fixer (perp l) := by rw [hl.perp_eq]; exact he.1
      exact sub_mem_of_mem_fixer_perp he' w
    rw [← hspan] at hd
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hd
    rcases eq_zero_or_eq_one hK c with rfl | rfl
    · exfalso
      apply hwl
      rw [← fixSp_zpowers_eq_of_mem hK hl he he1, mem_fixSp_zpowers]
      rw [zero_smul] at hc
      exact (sub_eq_zero.1 hc.symm)
    · rw [one_smul] at hc
      rw [hc]
      abel
  obtain ⟨e, he, e', he', he1, he'1, -, hee1⟩ := exists_two_ne_one hK hl
  have hfix : mat (e * e') *ᵥ w = w := by
    rw [mat_mul, ← Matrix.mulVec_mulVec, hew e' he' he'1, Matrix.mulVec_add, hew e he he1,
      hp₀fix e he]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  apply hwl
  rw [← fixSp_zpowers_eq_of_mem hK hl (E.mul_mem he he') hee1, mem_fixSp_zpowers]
  exact hfix

end CFSG.Quasithin.MS93.Q2G
