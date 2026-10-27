module

public import CFSG.RankThree.PartOne.CTP.UnitaryNode

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SUid conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg (embSUid)
open CFSG.ClassicalGroups.Unitary (herm herm_eq_zero_comm isUnitaryInvolution_unitaryInvolution)
open scoped MatrixGroups

section Spans

theorem span_pair_smul_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (x y : V)
    {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    Submodule.span F {c • x, d • y} = Submodule.span F {x, y} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]
      have := Submodule.smul_mem (Submodule.span F {c • x, d • y}) c⁻¹
        (Submodule.subset_span (Set.mem_insert (c • x) _))
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    · rw [h]
      have := Submodule.smul_mem (Submodule.span F {c • x, d • y}) d⁻¹
        (Submodule.subset_span (by simp : d • y ∈ ({c • x, d • y} : Set V)))
      rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at this

theorem span_single_smul_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (x : V)
    {c : F} (hc : c ≠ 0) : Submodule.span F {c • x} = Submodule.span F {x} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have := Submodule.smul_mem (Submodule.span F {c • x}) c⁻¹
      (Submodule.subset_span (Set.mem_singleton (c • x)))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Spans

section Conj

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def suConj
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    SUid (unitaryInvolution K 2 f) 3 ≃* SUid (unitaryInvolution K 2 f) 3 :=
  (suEquiv h).trans ((primeFormConjSU h _ A).trans (suEquiv h).symm)

theorem suProj_suConj (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (g : SUid (unitaryInvolution K 2 f) 3) :
    suProj h (suConj h A g) = primeFormConjHom h _ A (suProj h g) := by
  change QuotientGroup.mk (suEquiv h ((suEquiv h).symm
    (primeFormConjSU h _ A (suEquiv h g)))) = _
  rw [MulEquiv.apply_symm_apply]
  change _ = primeFormConjAut h _ A (QuotientGroup.mk (suEquiv h g))
  rw [primeFormConjAut_mk]

end Conj

section Core

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem unitary_edge_core (hq : 4 ≤ 2 ^ f) {KA KB : Type} [Field KA] [Field KB] [Finite KA]
    [Finite KB] (hKA : Nat.card KA = 2 ^ f) (hKB : Nat.card KB = 2 ^ f) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (φA : SL(2, KA) →* SUid (unitaryInvolution K 2 f) 3) (hφA : Function.Injective φA)
    (φB : SL(2, KB) →* SUid (unitaryInvolution K 2 f) 3) (hφB : Function.Injective φB)
    (αA αB : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    (hαA : αA ^ r = 1) (hαB : αB ^ r = 1)
    (hAfix : ∀ a, αA (suProj h (φA a)) = suProj h (φA a))
    (hBfix : ∀ b, αB (suProj h (φB b)) = suProj h (φB b))
    (hAB : ∀ b, ∃ b', αA (suProj h (φB b)) = suProj h (φB b'))
    (hBA : ∀ a, ∃ a', αB (suProj h (φA a)) = suProj h (φA a'))
    (hmovB : ∃ b, αA (suProj h (φB b)) ≠ suProj h (φB b))
    (hmovA : ∃ a, αB (suProj h (φA a)) ≠ suProj h (φA a)) :
    ∃ b : Module.Basis (Fin 3) K (Fin 3 → K),
      (∀ i j, herm (unitaryInvolution K 2 f) (b i) (b j) = if i = j then 1 else 0) ∧
      φA.range = ublkGroup (unitaryInvolution K 2 f) (Submodule.span K {b 0, b 1})
        (Submodule.span K {b 2}) ∧
      φB.range = ublkGroup (unitaryInvolution K 2 f) (Submodule.span K {b 1, b 2})
        (Submodule.span K {b 0}) := by
  classical
  have hαA1 : αA ≠ 1 := by
    rintro rfl
    obtain ⟨b, hb⟩ := hmovB
    exact hb rfl
  have hαB1 : αB ≠ 1 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hmovA
    exact ha rfl
  obtain ⟨MA, WA, ℓA, a₁, b₁, hαA', hcA, hdA, hab₁, hWA, hℓA, hoA, hrA⟩ :=
    unitary_node_lemma h hq hKA hr hr2 hrq φA hφA αA hαA hαA1 hAfix
  obtain ⟨MB, WB, ℓB, a₂, b₂, hαB', hcB, hdB, hab₂, hWB, hℓB, hoB, hrB⟩ :=
    unitary_node_lemma h hq hKB hr hr2 hrq φB hφB αB hαB hαB1 hBfix
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hperfA : Group.IsPerfect SL(2, KA) := isPerfect_sl2 (by rw [hKA]; exact hq)
  have hperfB : Group.IsPerfect SL(2, KB) := isPerfect_sl2 (by rw [hKB]; exact hq)
  have hπk : (suProj h).ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 3) :=
    (suProj_ker h hq).le
  have hNB : φB.range.map (suConj h MA).toMonoidHom = φB.range :=
    map_range_eq_of_central hπk φB (suConj h MA) (fun b => by
      obtain ⟨b', hb'⟩ := hAB b
      exact ⟨b', by rw [suProj_suConj, ← hαA']; exact hb'⟩)
  have hNA : φA.range.map (suConj h MB).toMonoidHom = φA.range :=
    map_range_eq_of_central hπk φA (suConj h MB) (fun a => by
      obtain ⟨a', ha'⟩ := hBA a
      exact ⟨a', by rw [suProj_suConj, ← hαB']; exact ha'⟩)
  have conj_step : ∀ (M : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (R : Subgroup (SUid (unitaryInvolution K 2 f) 3)), R.map (suConj h M).toMonoidHom = R →
      ∀ g ∈ R, ∃ g' ∈ R, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro M R hR g hg
    rw [← hR] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    refine ⟨g', hg', ?_⟩
    have e : ((M : GL (Fin 3) K) * (g' : GL (Fin 3) K) * (M : GL (Fin 3) K)⁻¹) *
        (M : GL (Fin 3) K) = (M : GL (Fin 3) K) * (g' : GL (Fin 3) K) := by group
    have e2 := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) e
    simp only [Units.val_mul] at e2
    have e3 : (((suConj h M).toMonoidHom g' : SUid (unitaryInvolution K 2 f) 3) : GL (Fin 3) K) =
        (M : GL (Fin 3) K) * (g' : GL (Fin 3) K) * (M : GL (Fin 3) K)⁻¹ := rfl
    rw [e3, Units.val_mul, Units.val_mul]
    exact e2
  have h2B := conj_step MA (ublkGroup (unitaryInvolution K 2 f) WB ℓB)
    (by rw [← hrB]; exact hNB)
  have h2A := conj_step MB (ublkGroup (unitaryInvolution K 2 f) WA ℓA)
    (by rw [← hrA]; exact hNA)
  obtain ⟨hMAℓ, hMAW⟩ := normalizer_ublk hσU hcB hdB hoB (unitary_conjTr_mul h MA) h2B
  obtain ⟨hMBℓ, hMBW⟩ := normalizer_ublk hσU hcA hdA hoA (unitary_conjTr_mul h MB) h2A
  have hne : ¬ (WA = WB ∧ ℓA = ℓB) := by
    rintro ⟨hW, hℓ⟩
    obtain ⟨b, hb⟩ := hmovB
    apply hb
    have hmem : φB b ∈ φA.range := by
      have h0 : φB b ∈ φB.range := ⟨b, rfl⟩
      rw [hrB, ← hW, ← hℓ, ← hrA] at h0
      exact h0
    obtain ⟨a, ha⟩ := hmem
    rw [← ha]
    exact hAfix a
  obtain ⟨b, h1, h2, h3, h4⟩ := exists_basis_of_position WA ℓA WB ℓB hcA hdA hcB hdB hne
    ((MA : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    ((MB : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a₁ b₁ a₂ b₂ hab₁ hab₂
    hWA hℓA hWB hℓB hMAW hMAℓ hMBW hMBℓ
  have m0A : b 0 ∈ WA := h1 ▸ Submodule.subset_span (by simp)
  have m1A : b 1 ∈ WA := h1 ▸ Submodule.subset_span (by simp)
  have m2A : b 2 ∈ ℓA := h2 ▸ Submodule.subset_span (by simp)
  have m1B : b 1 ∈ WB := h3 ▸ Submodule.subset_span (by simp)
  have m0B : b 0 ∈ ℓB := h4 ▸ Submodule.subset_span (by simp)
  have o02 : herm (unitaryInvolution K 2 f) (b 0) (b 2) = 0 := hoA _ m0A _ m2A
  have o12 : herm (unitaryInvolution K 2 f) (b 1) (b 2) = 0 := hoA _ m1A _ m2A
  have o10 : herm (unitaryInvolution K 2 f) (b 1) (b 0) = 0 := hoB _ m1B _ m0B
  have horth : ∀ i j, i ≠ j → herm (unitaryInvolution K 2 f) (b i) (b j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact herm_eq_zero_comm _ hσU.invol o10
    · exact o02
    · exact o10
    · exact absurd rfl hij
    · exact o12
    · exact herm_eq_zero_comm _ hσU.invol o02
    · exact herm_eq_zero_comm _ hσU.invol o12
    · exact absurd rfl hij
  obtain ⟨b', hb', hscal⟩ := exists_orthonormal_of_orthogonal hσU b horth
  obtain ⟨c₀, hc₀, e₀⟩ := hscal 0
  obtain ⟨c₁, hc₁, e₁⟩ := hscal 1
  obtain ⟨c₂, hc₂, e₂⟩ := hscal 2
  have s01 : Submodule.span K {b' 0, b' 1} = Submodule.span K {b 0, b 1} := by
    rw [e₀, e₁]; exact span_pair_smul_eq _ _ hc₀ hc₁
  have s12 : Submodule.span K {b' 1, b' 2} = Submodule.span K {b 1, b 2} := by
    rw [e₁, e₂]; exact span_pair_smul_eq _ _ hc₁ hc₂
  have s2 : Submodule.span K {b' 2} = Submodule.span K {b 2} := by
    rw [e₂]; exact span_single_smul_eq _ hc₂
  have s0 : Submodule.span K {b' 0} = Submodule.span K {b 0} := by
    rw [e₀]; exact span_single_smul_eq _ hc₀
  exact ⟨b', hb', by rw [hrA, h1, h2, s01, s2], by rw [hrB, h3, h4, s12, s0]⟩

end Core

section Final

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G]

include h in
theorem unitary_edge_standardPair (hq : 4 ≤ 2 ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ 2 ^ f + 1) (θ : SUid (unitaryInvolution K 2 f) 3 →* G)
    (hker : θ.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 3)) {E A B : Subgroup G}
    [CFSG.IsElementaryAbelian r E] (hE : EdgeTorus r E A B) (hAB : A ⊔ B = θ.range)
    {KA KB : Type} [Field KA] [Field KB] [Finite KA] [Finite KB] [CharP KA 2] [CharP KB 2]
    (hKA : Nat.card KA = 2 ^ f) (hKB : Nat.card KB = 2 ^ f)
    (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B) :
    ∃ c : SUid (unitaryInvolution K 2 f) 3,
      ((embSUid (unitaryInvolution K 2 f) 2).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ =
        A ∧
      ((embSUid (unitaryInvolution K 2 f) 0).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ =
        B := by
  have hA : A ≤ θ.range := by rw [← hAB]; exact le_sup_left
  have hB : B ≤ θ.range := by rw [← hAB]; exact le_sup_right
  obtain ⟨φA, hφA⟩ := exists_sl2_lift_unitary h hq θ hker hA ρA.toMonoidHom
  obtain ⟨φB, hφB⟩ := exists_sl2_lift_unitary h hq θ hker hB ρB.toMonoidHom
  have hφA' : ∀ a, θ (φA a) = (ρA a : G) := fun a => hφA a
  have hφB' : ∀ b, θ (φB b) = (ρB b : G) := fun b => hφB b
  obtain ⟨αA, hαA, hAfix, hAB', hmovB⟩ := edge_half_unitary h hq θ hker hr hE hAB ρA ρB φA φB
    hφA' hφB'
  obtain ⟨αB, hαB, hBfix, hBA', hmovA⟩ := edge_half_unitary h hq θ hker hr hE.symm
    (by rw [sup_comm]; exact hAB) ρB ρA φB φA hφB' hφA'
  have hinjA : Function.Injective φA := fun a a' hh =>
    ρA.injective (Subtype.ext (by rw [← hφA' a, ← hφA' a', hh]))
  have hinjB : Function.Injective φB := fun b b' hh =>
    ρB.injective (Subtype.ext (by rw [← hφB' b, ← hφB' b', hh]))
  obtain ⟨b, hb, hbA, hbB⟩ := unitary_edge_core h hq hKA hKB hr hr2 hrq φA hinjA φB hinjB αA αB
    hαA hαB hAfix hBfix hAB' hBA' hmovB hmovA
  obtain ⟨c, hc1, hc2⟩ := exists_conj_of_orthonormal (unitaryInvolution K 2 f) b hb
  exact ⟨c, by rw [hc1, ← hbA]; exact map_range_eq θ ρA φA hφA',
    by rw [hc2, ← hbB]; exact map_range_eq θ ρB φB hφB'⟩

end Final

end CFSG.RankThree.PartOne.CTP
