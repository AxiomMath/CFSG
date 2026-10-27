module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviStab
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE6

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem e6st3_rep6_iff (k : Fin 72) :
    triPairing (τ := .E6) (vec3 [1, 0, 0, 0, 0, 1]) (Tag.E6.rootCertificate.root k) = 0 ↔
      (Tag.E6.rootCertificate.root k 0 = 0 ∧ Tag.E6.rootCertificate.root k 5 = 0) := by
  revert k
  decide +kernel

private theorem e6st3_hub :
    ∀ k : Fin 72, Tag.E6.rootCertificate.root k 0 = 0 → Tag.E6.rootCertificate.root k 5 = 0 →
      ∃ s ∈ ([1, 2, 3, 4] : List (Fin 6)),
        iform (τ := .E6) (Tag.E6.rootCertificate.root k) (Pi.single s (1 : ℤ)) ≠ 0 := by
  decide +kernel

private theorem e6st3_hubadj :
    ∀ s ∈ ([1, 2, 4] : List (Fin 6)),
      iform (τ := .E6) (Pi.single s (1 : ℤ)) (Pi.single 3 (1 : ℤ)) ≠ 0 := by
  decide +kernel

private theorem e6st3_K6 :
    kernelRoots (triChar (τ := .E6) (vec3 [1, 0, 0, 0, 0, 1])) =
      parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} := by
  ext α
  rw [mem_kernelRoots_triChar]
  constructor
  · rintro ⟨hα, hp⟩
    obtain ⟨k, rfl⟩ := isRoot_e6_iff_cert.1 hα
    obtain ⟨h0, h5⟩ := (e6st3_rep6_iff k).1 hp
    refine ⟨hα, fun j hj => ?_⟩
    have hj' : j = 0 ∨ j = 5 := by
      have hjF : j ∈ ({0, 5} : Finset (Fin 6)) := by
        by_contra hnot
        exact hj hnot
      rcases Finset.mem_insert.mp hjF with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hj' with rfl | rfl
    · exact h0
    · exact h5
  · rintro ⟨hα, hz⟩
    refine ⟨hα, ?_⟩
    obtain ⟨k, rfl⟩ := isRoot_e6_iff_cert.1 hα
    have h05 : ∀ j ∈ ({0, 5} : Finset (Fin 6)), j ∉ {j | j ∉ ({0, 5} : Finset (Fin 6))} :=
      fun j hj hnot => hnot hj
    exact (e6st3_rep6_iff k).2 ⟨hz 0 (h05 0 (by decide)), hz 5 (h05 5 (by decide))⟩

private theorem e6st3_mem_D4 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) (h0 : α 0 = 0)
    (h5 : α 5 = 0) : α ∈ parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} := by
  refine ⟨hα, fun j hj => ?_⟩
  have hjF : j ∈ ({0, 5} : Finset (Fin 6)) := by
    by_contra hnot
    exact hj hnot
  rcases Finset.mem_insert.mp hjF with h | h
  · rw [h]
    exact h0
  · rw [Finset.mem_singleton.mp h]
    exact h5

private theorem e6st3_D4_coords {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) : α 0 = 0 ∧ α 5 = 0 := by
  have h05 : ∀ j ∈ ({0, 5} : Finset (Fin 6)), j ∉ {j | j ∉ ({0, 5} : Finset (Fin 6))} :=
    fun j hj hnot => hnot hj
  exact ⟨hα.2 0 (h05 0 (by decide)), hα.2 5 (h05 5 (by decide))⟩

private theorem e6st3_simple_coords :
    ∀ s ∈ ([1, 2, 3, 4] : List (Fin 6)),
      (Pi.single s (1 : ℤ) : Fin 6 → ℤ) 0 = 0 ∧ (Pi.single s (1 : ℤ) : Fin 6 → ℤ) 5 = 0 := by
  decide

private theorem e6st3_mem124 :
    ∀ s : Fin 6, s ∈ ([1, 2, 3, 4] : List (Fin 6)) → s ≠ 3 → s ∈ ([1, 2, 4] : List (Fin 6)) := by
  decide

private theorem e6st3_oneClass
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M}
    (t : WeylGroup .E6)
    (hK : kernelRoots χ = (fun α => t • α) ''
      parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))})
    (i : KernelComponent χ) : componentRoots χ i = kernelRoots χ := by
  classical
  have hsimple : ∀ s ∈ ([1, 2, 3, 4] : List (Fin 6)),
      (Pi.single s (1 : ℤ) : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} := fun s hs =>
    e6st3_mem_D4 (isRoot_single .E6 s) (e6st3_simple_coords s hs).1 (e6st3_simple_coords s hs).2
  have hker : ∀ x ∈ parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))},
      t • x ∈ kernelRoots χ := fun x hx => by
    rw [hK]
    exact ⟨x, hx, rfl⟩
  let hubK : kernelRoots χ := ⟨t • (Pi.single 3 (1 : ℤ) : Fin Tag.E6.rank → ℤ),
    hker _ (hsimple 3 (by decide))⟩
  have toHub : ∀ γ : kernelRoots χ, (⟦γ⟧ : KernelComponent χ) = ⟦hubK⟧ := by
    intro γ
    obtain ⟨x, hx, hxγ⟩ := (Set.ext_iff.mp hK (γ : Fin Tag.E6.rank → ℤ)).1 γ.2
    obtain ⟨k, hk⟩ := isRoot_e6_iff_cert.1 hx.1
    have hx0 : Tag.E6.rootCertificate.root k 0 = 0 := by rw [hk]; exact (e6st3_D4_coords hx).1
    have hx5 : Tag.E6.rootCertificate.root k 5 = 0 := by rw [hk]; exact (e6st3_D4_coords hx).2
    obtain ⟨s, hs, hne⟩ := e6st3_hub k hx0 hx5
    let σ : kernelRoots χ := ⟨t • (Pi.single s (1 : ℤ) : Fin Tag.E6.rank → ℤ),
      hker _ (hsimple s hs)⟩
    have h1 : (⟦γ⟧ : KernelComponent χ) = ⟦σ⟧ := by
      apply mk_eq_of_iform_ne_zero
      show iform (γ : Fin Tag.E6.rank → ℤ) (t • (Pi.single s (1 : ℤ) : Fin Tag.E6.rank → ℤ)) ≠ 0
      rw [← hxγ, iform_smul, ← hk]
      exact hne
    by_cases hs3 : s = 3
    · subst hs3
      exact h1
    · have hmem : s ∈ ([1, 2, 4] : List (Fin 6)) := e6st3_mem124 s hs hs3
      have h2 : (⟦σ⟧ : KernelComponent χ) = ⟦hubK⟧ := by
        apply mk_eq_of_iform_ne_zero
        show iform (t • (Pi.single s (1 : ℤ) : Fin Tag.E6.rank → ℤ))
          (t • (Pi.single 3 (1 : ℤ) : Fin Tag.E6.rank → ℤ)) ≠ 0
        rw [iform_smul]
        exact e6st3_hubadj s hmem
      exact h1.trans h2
  refine Set.Subset.antisymm (fun α hα => hα.1) fun α hα => ?_
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep i
  exact ⟨hα, (toHub ⟨α, hα⟩).trans (toHub ⟨β, hβ⟩).symm⟩

private theorem e6st3_noD4
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (i : KernelComponent (rootCharHom a))
    (hD4 : ∀ v : WeylGroup .E6, componentRoots (rootCharHom a) i ≠
      (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) :
    ∀ t : WeylGroup .E6, kernelRoots (rootCharHom3 a) ≠
      (fun α => t • α) '' kernelRoots (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 6 []))) := by
  intro t heq
  have hrep : kernelRoots (triChar (τ := .E6) (vec3 (e6ThreeReps.getD 6 []))) =
      parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))} := e6st3_K6
  rw [hrep] at heq
  have hone := e6st3_oneClass (χ := rootCharHom a) t heq i
  exact hD4 t (hone.trans heq)

private abbrev e6st3_inA1 (x : Fin 6 → ℤ) : Prop := x 1 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0

private abbrev e6st3_inA2 (x : Fin 6 → ℤ) : Prop := x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0

private theorem e6st3_arms :
    ∀ k l : Fin 72,
      triPairing (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0]) (Tag.E6.rootCertificate.root k) = 0 →
      triPairing (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0]) (Tag.E6.rootCertificate.root l) = 0 →
      iform (τ := .E6) (Tag.E6.rootCertificate.root k) (Tag.E6.rootCertificate.root l) ≠ 0 →
      ((e6st3_inA1 (Tag.E6.rootCertificate.root k) ↔ e6st3_inA1 (Tag.E6.rootCertificate.root l)) ∧
        (e6st3_inA2 (Tag.E6.rootCertificate.root k) ↔ e6st3_inA2 (Tag.E6.rootCertificate.root l))) := by
  decide +kernel

private def e6st3_θ : Fin 6 → ℤ := ![1, 1, 2, 3, 2, 1]

private def e6st3_θ' : Fin Tag.E6.rank → ℤ := e6st3_θ

private def e6st3_root (k : Fin 72) : Fin 6 → ℤ := Tag.E6.rootCertificate.root k

private theorem e6st3_armSpan :
    ∀ k : Fin 72,
      triPairing (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0]) (Tag.E6.rootCertificate.root k) = 0 →
      ((e6st3_inA1 (e6st3_root k) →
        ∃ m ∈ ([-1, 0, 1] : List ℤ), ∃ n ∈ ([-1, 0, 1] : List ℤ),
          e6st3_root k = m • (Pi.single 0 1 : Fin 6 → ℤ) + n • (Pi.single 2 1 : Fin 6 → ℤ)) ∧
      (e6st3_inA2 (e6st3_root k) →
        ∃ m ∈ ([-1, 0, 1] : List ℤ), ∃ n ∈ ([-1, 0, 1] : List ℤ),
          e6st3_root k = m • (Pi.single 4 1 : Fin 6 → ℤ) + n • (Pi.single 5 1 : Fin 6 → ℤ)) ∧
      (¬ e6st3_inA1 (e6st3_root k) → ¬ e6st3_inA2 (e6st3_root k) →
        ∃ m ∈ ([-1, 0, 1] : List ℤ), ∃ n ∈ ([-1, 0, 1] : List ℤ),
          e6st3_root k = m • (Pi.single 1 1 : Fin 6 → ℤ) + n • e6st3_θ)) := by
  decide +kernel

private theorem e6st3_eqvGen_iff {X : Type*} {r : X → X → Prop} {Q : X → Prop}
    (h : ∀ a c, r a c → (Q a ↔ Q c)) {a c : X} (hac : Relation.EqvGen r a c) : Q a ↔ Q c := by
  induction hac with
  | rel a c hr => exact h a c hr
  | refl a => exact Iff.rfl
  | symm a c _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

private theorem e6st3_smul_lin (t : WeylGroup .E6) (m n : ℤ) (u v : Fin Tag.E6.rank → ℤ) :
    t • (m • u + n • v) = m • (t • u) + n • (t • v) := by
  rw [smul_add]
  exact congrArg₂ (· + ·) (map_zsmul (DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) t) m u)
    (map_zsmul (DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) t) n v)

private theorem e6st3_compRank_le_two (C : Set (Fin Tag.E6.rank → ℤ)) (u v : Fin Tag.E6.rank → ℤ)
    (h : ∀ γ ∈ C, ∃ m n : ℤ, γ = m • u + n • v) : compRank C ≤ 2 := by
  let f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℚ) := fun γ i => (γ i : ℚ)
  let b : Fin 2 → (Fin Tag.E6.rank → ℚ) := ![f u, f v]
  have hle : Submodule.span ℚ (f '' C) ≤ Submodule.span ℚ (Set.range b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨m, n, rfl⟩ := h γ hγ
    have hf : f (m • u + n • v) = (m : ℚ) • b 0 + (n : ℚ) • b 1 := by
      funext j
      simp [f, b]
    rw [SetLike.mem_coe, hf]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h2 := finrank_range_le_card (R := ℚ) b
  rw [Fintype.card_fin] at h2
  exact (Submodule.finrank_mono hle).trans h2

private theorem e6st3_rank_le_two
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M}
    (t : WeylGroup .E6)
    (hK : kernelRoots χ = (fun α => t • α) ''
      kernelRoots (triChar (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0])))
    (i : KernelComponent χ) : compRank (componentRoots χ i) ≤ 2 := by
  classical
  have hpull : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ kernelRoots χ → ∃ k : Fin 72,
      Tag.E6.rootCertificate.root k = t⁻¹ • γ ∧
      triPairing (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0]) (Tag.E6.rootCertificate.root k) = 0 := by
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := (Set.ext_iff.mp hK γ).1 hγ
    obtain ⟨hxr, hxp⟩ := mem_kernelRoots_triChar.1 hx
    obtain ⟨k, hk⟩ := isRoot_e6_iff_cert.1 hxr
    exact ⟨k, by rw [inv_smul_smul, hk], by rw [hk]; exact hxp⟩
  have hinv : ∀ γ δ : kernelRoots χ,
      iform (γ : Fin Tag.E6.rank → ℤ) (δ : Fin Tag.E6.rank → ℤ) ≠ 0 →
      ((e6st3_inA1 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA1 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ))) ∧
        (e6st3_inA2 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA2 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ)))) := by
    intro γ δ hne
    obtain ⟨k, hk, hkp⟩ := hpull γ γ.2
    obtain ⟨l, hl, hlp⟩ := hpull δ δ.2
    have hif : iform (τ := .E6) (Tag.E6.rootCertificate.root k) (Tag.E6.rootCertificate.root l) ≠ 0 := by
      rw [hk, hl, iform_smul]
      exact hne
    have hkk : e6st3_root k = t⁻¹ • (γ : Fin Tag.E6.rank → ℤ) := hk
    have hll : e6st3_root l = t⁻¹ • (δ : Fin Tag.E6.rank → ℤ) := hl
    rw [← hkk, ← hll]
    exact e6st3_arms k l hkp hlp hif
  have hstep : ∀ γ δ : kernelRoots χ,
      dotProduct (γ : Fin Tag.E6.rank → ℤ)
        (Matrix.mulVec Tag.E6.symmetrizedCartan (δ : Fin Tag.E6.rank → ℤ)) ≠ 0 →
      ((e6st3_inA1 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA1 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ))) ∧
        (e6st3_inA2 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA2 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ)))) := by
    intro γ δ h
    exact hinv γ δ (by rwa [← dotProduct_mulVec_eq_iform])
  have hclass : ∀ γ δ : kernelRoots χ, (kernelRootSetoid χ).r γ δ →
      ((e6st3_inA1 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA1 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ))) ∧
        (e6st3_inA2 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ)) ↔
          e6st3_inA2 (t⁻¹ • (δ : Fin Tag.E6.rank → ℤ)))) := by
    intro γ δ h
    have h' : Relation.EqvGen (fun α β : kernelRoots χ =>
        dotProduct (α : Fin Tag.E6.rank → ℤ)
          (Matrix.mulVec Tag.E6.symmetrizedCartan (β : Fin Tag.E6.rank → ℤ)) ≠ 0)
        γ δ := h
    exact ⟨e6st3_eqvGen_iff (Q := fun γ : kernelRoots χ =>
        e6st3_inA1 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ))) (fun a c hr => (hstep a c hr).1) h',
      e6st3_eqvGen_iff (Q := fun γ : kernelRoots χ =>
        e6st3_inA2 (t⁻¹ • (γ : Fin Tag.E6.rank → ℤ))) (fun a c hr => (hstep a c hr).2) h'⟩
  obtain ⟨β0, rfl⟩ := Quotient.exists_rep i
  have hCmem : ∀ γ ∈ componentRoots χ (⟦β0⟧ : KernelComponent χ), ∃ hγ : γ ∈ kernelRoots χ,
      (kernelRootSetoid χ).r ⟨γ, hγ⟩ β0 := fun γ hγ => ⟨hγ.1, Quotient.exact hγ.2⟩
  have hrecover : ∀ (γ : Fin Tag.E6.rank → ℤ) (u v : Fin Tag.E6.rank → ℤ) (m n : ℤ),
      t⁻¹ • γ = m • u + n • v → γ = m • (t • u) + n • (t • v) := by
    intro γ u v m n h
    rw [← e6st3_smul_lin, ← h, smul_inv_smul]
  by_cases h1 : e6st3_inA1 (t⁻¹ • (β0 : Fin Tag.E6.rank → ℤ))
  · refine e6st3_compRank_le_two _ (t • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ))
      (t • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) ?_
    intro γ hγ
    obtain ⟨hγk, hr⟩ := hCmem γ hγ
    have hA1 : e6st3_inA1 (t⁻¹ • γ) := ((hclass _ _ hr).1).2 h1
    obtain ⟨k, hk, hkp⟩ := hpull γ hγk
    have hkk : e6st3_root k = t⁻¹ • γ := hk
    obtain ⟨m, -, n, -, hmn⟩ := ((e6st3_armSpan k hkp).1) (by rw [hkk]; exact hA1)
    have hmn' : t⁻¹ • γ = m • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) +
        n • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← hkk]
      exact hmn
    exact ⟨m, n, hrecover γ _ _ m n hmn'⟩
  by_cases h2 : e6st3_inA2 (t⁻¹ • (β0 : Fin Tag.E6.rank → ℤ))
  · refine e6st3_compRank_le_two _ (t • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ))
      (t • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ?_
    intro γ hγ
    obtain ⟨hγk, hr⟩ := hCmem γ hγ
    have hA2 : e6st3_inA2 (t⁻¹ • γ) := ((hclass _ _ hr).2).2 h2
    obtain ⟨k, hk, hkp⟩ := hpull γ hγk
    have hkk : e6st3_root k = t⁻¹ • γ := hk
    obtain ⟨m, -, n, -, hmn⟩ := ((e6st3_armSpan k hkp).2.1) (by rw [hkk]; exact hA2)
    have hmn' : t⁻¹ • γ = m • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) +
        n • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← hkk]
      exact hmn
    exact ⟨m, n, hrecover γ _ _ m n hmn'⟩
  · refine e6st3_compRank_le_two _ (t • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ))
      (t • e6st3_θ') ?_
    intro γ hγ
    obtain ⟨hγk, hr⟩ := hCmem γ hγ
    have hN1 : ¬ e6st3_inA1 (t⁻¹ • γ) := fun h => h1 (((hclass _ _ hr).1).1 h)
    have hN2 : ¬ e6st3_inA2 (t⁻¹ • γ) := fun h => h2 (((hclass _ _ hr).2).1 h)
    obtain ⟨k, hk, hkp⟩ := hpull γ hγk
    have hkk : e6st3_root k = t⁻¹ • γ := hk
    obtain ⟨m, -, n, -, hmn⟩ := ((e6st3_armSpan k hkp).2.2) (by rw [hkk]; exact hN1)
      (by rw [hkk]; exact hN2)
    have hmn' : t⁻¹ • γ = m • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) + n • e6st3_θ' := by
      rw [← hkk]
      exact hmn
    exact ⟨m, n, hrecover γ _ _ m n hmn'⟩

theorem mem_closure_rootReflection_of_fix_E6_three
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha : ∀ i, a i ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i))
    (hD4 : ∀ v : WeylGroup .E6, componentRoots (rootCharHom a) i ≠
      (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ ({0, 5} : Finset (Fin 6))})
    {w : WeylGroup .E6} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
      ∀ j, ((w • c) j : ZMod 3) = (c j : ZMod 3)) :
    w ∈ Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) := by
  have hstab : rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
    rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_three a ha (e6st3_noD4 a i hD4)
      fun t heq => by
        have hK7 : kernelRoots (rootCharHom a) = (fun α => t • α) ''
            kernelRoots (triChar (τ := .E6) (vec3 [0, 0, 0, 1, 0, 0])) := heq
        have hle := e6st3_rank_le_two (χ := rootCharHom a) t hK7 i
        omega
  exact mem_closure_rootReflection_of_fix_E6_of_stab Nat.prime_three (by norm_num) hstab i hw hfix

end CFSG.StandardType

end
