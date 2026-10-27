module

public import CFSG.RankThree.GF2n.Smith81.OrthMaxTS

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Prelim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem nondeg_polarBilin_of_forall (h : ∀ v, (∀ w, polar Q v w = 0) → v = 0) :
    (polarBilin Q).Nondegenerate :=
  ⟨fun v hv => h v fun w => by simpa using hv w,
    fun w hw => h w fun v => by rw [polar_comm]; simpa using hw v⟩

private theorem polar_self_eq_zero_charTwo [CharP K 2] (Q : QuadraticForm K V) (v : V) :
    polar Q v v = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

end Prelim

section Irreducible

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem eq_span_or_eq_orth_of_eichlerStable_of_map_ne_zero [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ Module.finrank K V) {u : V}
    (hQu : Q u ≠ 0) (X : Submodule K V) (hLX : Submodule.span K {u} ≤ X)
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hX : EichlerStable Q u X) :
    X = Submodule.span K {u} ∨
      X = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
  by_cases hXL : X = Submodule.span K {u}
  · exact Or.inl hXL
  refine Or.inr (le_antisymm hXP ?_)
  obtain ⟨y, hyX, hyL⟩ : ∃ y ∈ X, y ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    exact hXL (le_antisymm hcon hLX)
  have hyu : polar Q u y = 0 := mem_orth_span_single_iff.mp (hXP hyX)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha⟩ : IsSquare (Q y / Q u) := FiniteField.isSquare_of_char_two (ringChar.eq K 2) _
  have hay : a ^ 2 * Q u = Q y := by
    have h1 : a * a * Q u = Q y / Q u * Q u := by rw [← ha]
    rw [div_mul_cancel₀ _ hQu] at h1
    rw [pow_two]
    exact h1
  have hau : a • u ∈ X := X.smul_mem a (hLX (Submodule.mem_span_singleton_self u))
  have hsX : y + a • u ∈ X := X.add_mem hyX hau
  have hs : Q (y + a • u) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, polar_comm Q y u, hyu, hay]
    linear_combination (Q y) * h2
  have hus : polar Q u (y + a • u) = 0 := by
    rw [polar_add_right, polar_smul_right_eq, hyu, polar_self_eq_zero_charTwo Q u]
    ring
  have hsL : y + a • u ∉ Submodule.span K {u} := by
    intro hs'
    apply hyL
    have := Submodule.sub_mem _ hs' (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u))
    simpa using this
  exact orth_le_of_eichlerStable hQ h5 hX hsX hs hus hsL

end Irreducible

section Counting

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem card_le_sq_of_fixes_perp [FiniteDimensional K V]
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) {u : V} (hu0 : u ≠ 0)
    (Γ : Finset (K × (V ≃ₗ[K] V)))
    (hΓ : ∀ t ∈ Γ, (∀ x, Q (t.2 x) = Q x) ∧ ∀ a, polar Q a u = 0 → t.2 a = a) :
    Γ.card ≤ Nat.card K ^ 2 := by
  have hQ := nondeg_polarBilin_of_forall hnd
  obtain ⟨a₀, ha₀⟩ : ∃ a, polar Q u a ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd u h)
  have ha₀' : polar Q a₀ u ≠ 0 := by rwa [polar_comm]
  have hshift : ∀ t ∈ Γ, ∃ φ : K, t.2 a₀ = a₀ + φ • u := by
    intro t ht
    obtain ⟨hiso, hfix⟩ := hΓ t ht
    have hpo := polar_map_of_mem (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso)
    have hδ : t.2 a₀ - a₀ ∈ Submodule.span K {u} := by
      by_contra hδ
      obtain ⟨z, hz, hδz⟩ := exists_polar_ne_zero_of_not_mem hQ hδ
      have hzu : polar Q z u = 0 := by rw [polar_comm]; exact mem_orth_span_single_iff.mp hz
      apply hδz
      have h1 : polar Q (t.2 a₀) z = polar Q a₀ z := by
        have := hpo a₀ z
        rwa [hfix z hzu] at this
      rw [polar_sub_left, h1, sub_self]
    obtain ⟨φ, hφ⟩ := Submodule.mem_span_singleton.mp hδ
    exact ⟨φ, by rw [hφ]; abel⟩
  letI := Fintype.ofFinite K
  have hcard : Γ.card ≤ (Finset.univ : Finset (K × K)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t.1, polar Q (t.2 a₀) a₀))
      (fun _ _ => Finset.mem_univ _) ?_
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨φ₁, hφ₁⟩ := hshift t₁ ht₁
    obtain ⟨φ₂, hφ₂⟩ := hshift t₂ ht₂
    have h1 : t₁.1 = t₂.1 := (Prod.ext_iff.mp h).1
    have h2 : polar Q (t₁.2 a₀) a₀ = polar Q (t₂.2 a₀) a₀ := (Prod.ext_iff.mp h).2
    rw [hφ₁, hφ₂, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq] at h2
    have hφ : φ₁ = φ₂ := by
      have h3 : (φ₁ - φ₂) * polar Q u a₀ = 0 := by linear_combination h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha₀)
    have ho : t₁.2 = t₂.2 := by
      refine LinearEquiv.ext fun x => ?_
      obtain ⟨l, hl⟩ : ∃ l : K, l * polar Q a₀ u = polar Q x u :=
        ⟨polar Q x u / polar Q a₀ u, div_mul_cancel₀ _ ha₀'⟩
      have hx : polar Q (x - l • a₀) u = 0 := by
        rw [polar_sub_left, polar_smul_left_eq, hl, sub_self]
      have hxx : x = (x - l • a₀) + l • a₀ := by abel
      have e1 := hΓ t₁ ht₁
      have e2 := hΓ t₂ ht₂
      calc t₁.2 x = t₁.2 ((x - l • a₀) + l • a₀) := congrArg _ hxx
        _ = (x - l • a₀) + l • t₁.2 a₀ := by rw [map_add, map_smul, e1.2 _ hx]
        _ = (x - l • a₀) + l • t₂.2 a₀ := by rw [hφ₁, hφ₂, hφ]
        _ = t₂.2 ((x - l • a₀) + l • a₀) := by rw [map_add, map_smul, e2.2 _ hx]
        _ = t₂.2 x := (congrArg _ hxx).symm
    exact Prod.ext h1 ho
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, _root_.sq]

variable [CharP K 2] [FiniteDimensional K V]

theorem card_le_sq_of_fix_pair_of_map_ne_zero
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hn : Module.finrank K V = 4) {u b g : V} (hu : Q u ≠ 0)
    (hub : polar Q u b = 0) (hbu : b ∉ Submodule.span K {u}) (Γ : Finset (K × (V ≃ₗ[K] V)))
    (hΓ : ∀ t ∈ Γ, (∀ v, Q (t.2 v) = Q v) ∧ t.2 u = u ∧ t.2 b = b ∧
      ∃ k : K, t.2 g + t.1 • b - g = k • u) :
    Γ.card ≤ Nat.card K ^ 2 := by
  have hQ := nondeg_polarBilin_of_forall hnd
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu0 : u ≠ 0 := fun h => hu (by rw [h, QuadraticMap.map_zero])
  have hbb : polar Q b b = 0 := polar_self_eq_zero_charTwo Q b
  have huu : polar Q u u = 0 := polar_self_eq_zero_charTwo Q u
  have hbu' : polar Q b u = 0 := by rw [polar_comm]; exact hub
  have hli : LinearIndependent K ![u, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hbu
      have h1 : t • b = -(s • u) := eq_neg_of_add_eq_zero_right hst
      have : b = (-(t⁻¹ * s)) • u := by
        calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hu0, rfl⟩
  obtain ⟨g', hg'⟩ := exists_dual_family hQ hli
  have h00 : polar Q u (g' 0) = 1 := by simpa using hg' 0 0
  have h01 : polar Q u (g' 1) = 0 := by simpa using hg' 0 1
  have h10 : polar Q b (g' 0) = 0 := by simpa using hg' 1 0
  have h11 : polar Q b (g' 1) = 1 := by simpa using hg' 1 1
  set d := g' 1 with hd
  set c := g' 0 + polar Q (g' 0) d • b with hc
  have hud : polar Q u d = 0 := h01
  have hbd : polar Q b d = 1 := h11
  have hcu : polar Q u c = 1 := by
    rw [hc, polar_add_right, polar_smul_right_eq, h00, hub]; ring
  have hcb : polar Q b c = 0 := by
    rw [hc, polar_add_right, polar_smul_right_eq, h10, hbb]; ring
  have hcd : polar Q c d = 0 := by
    rw [hc, polar_add_left, polar_smul_left_eq, hbd]
    linear_combination (polar Q (g' 0) d) * h2
  have hcc : polar Q c c = 0 := polar_self_eq_zero_charTwo Q c
  have hdd : polar Q d d = 0 := polar_self_eq_zero_charTwo Q d
  have hdu : polar Q d u = 0 := by rw [polar_comm]; exact hud
  have hdb : polar Q d b = 1 := by rw [polar_comm]; exact hbd
  have hcu' : polar Q c u = 1 := by rw [polar_comm]; exact hcu
  have hcb' : polar Q c b = 0 := by rw [polar_comm]; exact hcb
  clear_value c d
  have hN : ∀ v, polar Q u v = 0 → polar Q b v = 0 → ∃ α β : K, α • u + β • b = v := by
    intro v h1 h2'
    set N : Submodule K V := Submodule.span K {u, b} with hNdef
    have hNdim : Module.finrank K N = 2 := by
      have h := finrank_span_eq_card hli
      have hr : Set.range ![u, b] = {u, b} := by
        ext x; simp [Fin.exists_fin_two, or_comm]
      rw [hr, Fintype.card_fin] at h
      exact h
    have hle : N ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) N := by
      intro x hx
      rw [mem_orth_iff]
      intro y hy
      obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨e, e', rfl⟩ := Submodule.mem_span_pair.mp hy
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, huu,
        hub, hbu', hbb]
      ring
    have hfin := LinearMap.BilinForm.finrank_orthogonal hQ N
    have heq : N = LinearMap.BilinForm.orthogonal (polarBilin Q) N :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hv : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N :=
      mem_orth_span_pair_iff.mpr ⟨h1, h2'⟩
    rw [← heq] at hv
    obtain ⟨a, a', h⟩ := Submodule.mem_span_pair.mp hv
    exact ⟨a, a', h⟩
  have hspan : Submodule.span K ({u, b, c, d} : Set V) = ⊤ := by
    set M := Submodule.span K ({u, b, c, d} : Set V) with hM
    have hM0 : LinearMap.BilinForm.orthogonal (polarBilin Q) M = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [mem_orth_iff] at hv
      have hu' := hv u (Submodule.subset_span (by simp))
      have hb' := hv b (Submodule.subset_span (by simp))
      have hc' := hv c (Submodule.subset_span (by simp))
      have hd' := hv d (Submodule.subset_span (by simp))
      obtain ⟨α, β, rfl⟩ := hN v hu' hb'
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hcu', hcb'] at hc'
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hdu, hdb] at hd'
      have hα : α = 0 := by linear_combination hc'
      have hβ : β = 0 := by linear_combination hd'
      rw [hα, hβ, zero_smul, zero_smul, add_zero]
      exact Submodule.zero_mem _
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ M
    have h3 := Submodule.finrank_le M
    rw [hM0, finrank_bot] at h1
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hQuad : ∀ x y : K, Q (x • u + y • b) = x ^ 2 * Q u + y ^ 2 * Q b := by
    intro x y
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, hub]
    ring
  have hcoord : ∀ o : V ≃ₗ[K] V, (∀ x, Q (o x) = Q x) → o u = u → o b = b →
      o c = c + polar Q (o c) c • u + polar Q (o c) d • b ∧
      o d = d + polar Q (o c) d • u + polar Q (o d) d • b ∧
      polar Q (o c) d ^ 2 * Q u + polar Q (o d) d ^ 2 * Q b + polar Q (o d) d = 0 := by
    intro o ho hou hob
    have hpo := polar_map_of_mem (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ho)
    have e1 : ∀ x, polar Q u (o x) = polar Q u x := fun x => by
      simpa [hou] using hpo u x
    have e2 : ∀ x, polar Q b (o x) = polar Q b x := fun x => by
      simpa [hob] using hpo b x
    obtain ⟨α, β, hαβ⟩ := hN (o c - c) (by rw [polar_sub_right, e1, sub_self])
      (by rw [polar_sub_right, e2, sub_self])
    obtain ⟨α', β', hαβ'⟩ := hN (o d - d) (by rw [polar_sub_right, e1, sub_self])
      (by rw [polar_sub_right, e2, sub_self])
    have hoc : o c = c + (α • u + β • b) := by rw [hαβ]; abel
    have hod : o d = d + (α' • u + β' • b) := by rw [hαβ']; abel
    have hα : polar Q (o c) c = α := by
      rw [hoc, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hcc, hcu,
        hcb]
      ring
    have hβ : polar Q (o c) d = β := by
      rw [hoc, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hcd, hud,
        hbd]
      ring
    have hβ' : polar Q (o d) d = β' := by
      rw [hod, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hdd, hud,
        hbd]
      ring
    have hα' : α' = β := by
      have h := hpo c d
      rw [hoc, hod, hcd] at h
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, hcd,
        hcu', hcb', hud, hbd, huu, hub, hbu', hbb] at h
      linear_combination h - β * h2
    have hE2 : α' ^ 2 * Q u + β' ^ 2 * Q b + β' = 0 := by
      have h := ho d
      rw [hod, QuadraticMap.map_add Q, hQuad, polar_add_right, polar_smul_right_eq,
        polar_smul_right_eq, hdu, hdb] at h
      linear_combination h
    refine ⟨?_, ?_, ?_⟩
    · rw [hα, hβ, hoc]; abel
    · rw [hβ, hβ', ← hα', hod]; abel
    · rw [hβ, hβ', ← hα']; exact hE2
  letI := Fintype.ofFinite K
  have hcard : Γ.card ≤ (Finset.univ : Finset (K × K)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => (polar Q (t.2 c) c, polar Q (t.2 d) d)) (fun _ _ => Finset.mem_univ _) ?_
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨hQ₁, hu₁, hb₁, k₁, hk₁⟩ := hΓ t₁ ht₁
    obtain ⟨hQ₂, hu₂, hb₂, k₂, hk₂⟩ := hΓ t₂ ht₂
    have h1 : polar Q (t₁.2 c) c = polar Q (t₂.2 c) c := congrArg Prod.fst h
    have h2' : polar Q (t₁.2 d) d = polar Q (t₂.2 d) d := congrArg Prod.snd h
    obtain ⟨hc₁, hd₁, hE₁⟩ := hcoord t₁.2 hQ₁ hu₁ hb₁
    obtain ⟨hc₂, hd₂, hE₂⟩ := hcoord t₂.2 hQ₂ hu₂ hb₂
    have hβ : polar Q (t₁.2 c) d = polar Q (t₂.2 c) d := by
      have h3 : polar Q (t₁.2 c) d ^ 2 * Q u = polar Q (t₂.2 c) d ^ 2 * Q u := by
        rw [h2'] at hE₁
        linear_combination hE₁ - hE₂
      have h4 := mul_right_cancel₀ hu h3
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with h5 | h5
      · exact h5
      · rw [h5, CharTwo.neg_eq]
    have hoc : t₁.2 c = t₂.2 c := by rw [hc₁, hc₂, h1, hβ]
    have hod : t₁.2 d = t₂.2 d := by rw [hd₁, hd₂, hβ, h2']
    have ho : t₁.2 = t₂.2 := by
      have hfun : (t₁.2 : V →ₗ[K] V) = (t₂.2 : V →ₗ[K] V) := by
        refine LinearMap.ext_on hspan ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact (hu₁.trans hu₂.symm)
        · exact (hb₁.trans hb₂.symm)
        · exact hoc
        · exact hod
      exact LinearEquiv.ext fun x => LinearMap.congr_fun hfun x
    have hμ : ∀ (t : K × (V ≃ₗ[K] V)) (k : K), t.2 g + t.1 • b - g = k • u →
        t.1 = polar Q g d - polar Q (t.2 g) d := by
      intro t k hk
      have := congrArg (fun z => polar Q z d) hk
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, hbd, hud] at this
      linear_combination this
    refine Prod.ext ?_ ho
    rw [hμ t₁ k₁ hk₁, hμ t₂ k₂ hk₂, ho]
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, _root_.sq]

end Counting

section Main

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {ι : Type*} [Fintype ι]

theorem snd_mem_span_of_eichlerStable_of_map_ne_zero {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (h5 : 5 ≤ Fintype.card ι) {u : ι → K}
    (hu : qU u ≠ 0) {D : Submodule K ((ι → K) × (ι → K))}
    (hSu : ∀ p ∈ D, polar qU u p.2 = 0) (hSS : ∀ p ∈ D, ∀ p' ∈ D, polar qU p.2 p'.2 = 0)
    (hE : ∀ s w : ι → K, qU s = 0 → polar qU s w = 0 → polar qU s u = 0 → polar qU w u = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D) :
    ∀ p ∈ D, p.2 ∈ Submodule.span K {u} := by
  have hu0 : u ≠ 0 := fun h => hu (by rw [h, QuadraticMap.map_zero])
  have hQ := nondeg_polarBilin_of_forall hnd
  have hfin : 5 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card K]; exact h5
  set S : Submodule K (ι → K) := D.map (LinearMap.snd K (ι → K) (ι → K)) with hS
  have hSmem : ∀ x, x ∈ S ↔ ∃ p ∈ D, p.2 = x := fun x => by simp [hS]
  set X : Submodule K (ι → K) := S ⊔ Submodule.span K {u} with hX
  have hLX : Submodule.span K {u} ≤ X := le_sup_right
  have hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin qU) (Submodule.span K {u}) := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := (hSmem x).mp hx
      exact mem_orth_span_single_iff.mpr (hSu p hp)
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [mem_orth_span_single_iff, polar_smul_right_eq, polar_self_eq_zero_charTwo qU u, mul_zero]
  have hXst : EichlerStable qU u X := by
    intro a w ha haw hua huw x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    refine X.add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · obtain ⟨p, hp, rfl⟩ := (hSmem s).mp hs
      exact (hSmem _).mpr ⟨_, hE a w ha haw (by rw [polar_comm]; exact hua)
        (by rw [polar_comm]; exact huw) p hp, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
      rw [map_smul, eichler_apply_of_polar_eq_zero hua huw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  rcases eq_span_or_eq_orth_of_eichlerStable_of_map_ne_zero hQ hfin hu X hLX hXP hXst with
    hX1 | hX1
  · intro p hp
    rw [← hX1]
    exact Submodule.mem_sup_left ((hSmem _).mpr ⟨p, hp, rfl⟩)
  · exfalso
    have hN : Module.finrank K (Submodule.span K {u}) ≤ 2 := by
      rw [finrank_span_singleton hu0]; norm_num
    obtain ⟨m₁, hm₁, m₂, hm₂, hm⟩ := exists_polar_ne_zero_of_finrank hQ hN hfin
    rw [← hX1] at hm₁ hm₂
    obtain ⟨s₁, hs₁, t₁, ht₁, rfl⟩ := Submodule.mem_sup.mp hm₁
    obtain ⟨s₂, hs₂, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp hm₂
    obtain ⟨p₁, hp₁, rfl⟩ := (hSmem s₁).mp hs₁
    obtain ⟨p₂, hp₂, rfl⟩ := (hSmem s₂).mp hs₂
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp ht₁
    obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp ht₂
    apply hm
    rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_left_eq, hSS p₁ hp₁ p₂ hp₂,
      polar_comm qU p₁.2 u, hSu p₁ hp₁, polar_self_eq_zero_charTwo qU u, hSu p₂ hp₂]
    ring

private theorem stable_basic {qU : QuadraticForm K (ι → K)} {u : ι → K}
    {D : Submodule K ((ι → K) × (ι → K))} (huD : ((u, 0) : (ι → K) × (ι → K)) ∈ D)
    (hts : ∀ p ∈ D, polar qU p.1 p.2 = 0) (hT : ∀ μ : K, ∀ p ∈ D, (p.1 + μ • p.2, p.2) ∈ D) :
    (∀ p ∈ D, ∀ p' ∈ D, polar qU p.1 p'.2 + polar qU p'.1 p.2 = 0) ∧
      (∀ p ∈ D, polar qU u p.2 = 0) ∧ (∀ p ∈ D, ∀ p' ∈ D, polar qU p.2 p'.2 = 0) := by
  have hpol : ∀ p ∈ D, ∀ p' ∈ D, polar qU p.1 p'.2 + polar qU p'.1 p.2 = 0 := by
    intro p hp p' hp'
    have h := hts _ (D.add_mem hp hp')
    simp only [Prod.fst_add, Prod.snd_add, polar_add_left, polar_add_right, hts p hp,
      hts p' hp'] at h
    linear_combination h
  have hSb : ∀ p ∈ D, (p.2, (0 : ι → K)) ∈ D := by
    intro p hp
    have h := D.sub_mem (hT 1 p hp) hp
    have e : ((p.1 + (1 : K) • p.2, p.2) - p : (ι → K) × (ι → K)) = (p.2, 0) := by
      refine Prod.ext ?_ ?_ <;> simp
    rwa [e] at h
  refine ⟨hpol, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · simpa using hpol p hp _ huD
  · simpa using hpol p' hp' _ (hSb p hp)

theorem false_of_stable_nonsingular_of_sq_lt {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (hn : 4 ≤ Fintype.card ι) {v : ι → K}
    (hv : qU v ≠ 0) {D : Submodule K ((ι → K) × (ι → K))}
    (hvD : ((v, 0) : (ι → K) × (ι → K)) ∈ D) (hts : ∀ p ∈ D, polar qU p.1 p.2 = 0)
    (hdim : Fintype.card ι ≤ Module.finrank K D)
    (hT : ∀ μ : K, ∀ p ∈ D, (p.1 + μ • p.2, p.2) ∈ D)
    (hE : ∀ s w : ι → K, qU s = 0 → polar qU s w = 0 → polar qU s v = 0 → polar qU w v = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D)
    (hΓ : ∃ Γ : Finset (K × ((ι → K) ≃ₗ[K] (ι → K))), Nat.card K ^ 2 < Γ.card ∧
      ∀ t ∈ Γ, (∀ x, qU (t.2 x) = qU x) ∧ t.2 v = v ∧
        ∀ p ∈ D, ∃ c : K, (t.2 p.1 + t.1 • t.2 p.2 - p.1, t.2 p.2 - p.2) = c • ((v, 0) : _)) :
    False := by
  obtain ⟨Γ, hΓcard, hΓ⟩ := hΓ
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  have hfinι : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  obtain ⟨hpol, hSv, hSS⟩ := stable_basic hvD hts hT
  have hSK : ∀ p ∈ D, p.2 ∈ Submodule.span K {v} := by
    rcases (by omega : Fintype.card ι = 4 ∨ 5 ≤ Fintype.card ι) with h4 | h5
    · by_contra hcon
      push Not at hcon
      obtain ⟨p, hp, hpK⟩ := hcon
      have hle := card_le_sq_of_fix_pair_of_map_ne_zero (Q := qU) (g := p.1) hnd
        (by rw [hfinι, h4]) hv (hSv p hp) hpK Γ ?_
      · omega
      · intro t ht
        obtain ⟨hiso, hfixv, hc⟩ := hΓ t ht
        obtain ⟨k, hk⟩ := hc p hp
        rw [Prod.ext_iff] at hk
        simp only [Prod.smul_fst, Prod.smul_snd, smul_zero] at hk
        have hb : t.2 p.2 = p.2 := sub_eq_zero.mp hk.2
        refine ⟨hiso, hfixv, hb, k, ?_⟩
        rw [← hk.1, hb]
    · exact snd_mem_span_of_eichlerStable_of_map_ne_zero hnd h5 hv hSv hSS hE
  have hD0 : ∀ a : ι → K, polar qU a v = 0 → ((a, (0 : ι → K)) : (ι → K) × (ι → K)) ∈ D := by
    intro a ha
    refine mem_of_forall_polar_prod_eq_zero hnd hpol (by rw [hfinι]; exact hdim) ?_
    intro p hp
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hSK p hp)
    show polar qU p.1 0 + polar qU a p.2 = 0
    rw [polar_zero_right, ← hc, polar_smul_right_eq, ha]
    ring
  have hfix : ∀ t ∈ Γ, ∀ a, polar qU a v = 0 → t.2 a = a := by
    intro t ht a ha
    obtain ⟨k, hk⟩ := (hΓ t ht).2.2 (a, 0) (hD0 a ha)
    rw [Prod.ext_iff] at hk
    simp only [Prod.smul_fst, map_zero, smul_zero, add_zero] at hk
    have h1 : t.2 a = a + k • v := by rw [← hk.1]; abel
    have h2 := (hΓ t ht).1 a
    rw [h1, QuadraticMap.map_add qU, map_smul_eq_sq, polar_smul_right_eq, ha] at h2
    have h3 : k ^ 2 * qU v = 0 := by linear_combination h2
    have hk0 : k = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.mp h
      · exact absurd h hv
    rw [h1, hk0, zero_smul, add_zero]
  have hle := card_le_sq_of_fixes_perp hnd hv0 Γ fun t ht => ⟨(hΓ t ht).1, hfix t ht⟩
  omega

theorem false_of_stable_nonsingular {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, QuadraticMap.polar qU v w = 0) → v = 0) (hn : 4 ≤ Fintype.card ι)
    (hq : 4 ≤ Nat.card K) {v : ι → K} (hv : qU v ≠ 0) {D : Submodule K ((ι → K) × (ι → K))}
    (hvD : ((v, 0) : (ι → K) × (ι → K)) ∈ D)
    (hts : ∀ p ∈ D, QuadraticMap.polar qU p.1 p.2 = 0)
    (hdim : Fintype.card ι ≤ Module.finrank K D)
    (hT : ∀ μ : K, ∀ p ∈ D, (p.1 + μ • p.2, p.2) ∈ D)
    (hE : ∀ s w : ι → K, qU s = 0 → QuadraticMap.polar qU s w = 0 →
      QuadraticMap.polar qU s v = 0 → QuadraticMap.polar qU w v = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D)
    (hΓ : ∃ Γ : Finset (K × ((ι → K) ≃ₗ[K] (ι → K))),
      Nat.card K ^ (Fintype.card ι - 1) ≤ Γ.card ∧
      ∀ t ∈ Γ, (∀ x, qU (t.2 x) = qU x) ∧ t.2 v = v ∧
        ∀ p ∈ D, ∃ c : K, (t.2 p.1 + t.1 • t.2 p.2 - p.1, t.2 p.2 - p.2) = c • ((v, 0) : _)) :
    False := by
  obtain ⟨Γ, hcard, hΓ⟩ := hΓ
  refine false_of_stable_nonsingular_of_sq_lt hnd hn hv hvD hts hdim hT hE ⟨Γ, ?_, hΓ⟩
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) (by omega)) hcard

end Main

end CFSG.RankThree.GF2n.Smith81
