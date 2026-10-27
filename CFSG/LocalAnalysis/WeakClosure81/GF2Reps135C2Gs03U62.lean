module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03PermModel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Glue
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62Classes
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62Sound
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Fischer CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RankTwoHypIICover.U62

private lemma gs03_u62_u62AutConj_conj (t : ↥T46) :
    u62AutConj ⟨t, T46_le_u62AutW t.2⟩ = MulAut.conj t := by
  ext g
  simp [u62AutConj_apply, MulAut.conj_apply]

private lemma gs03_u62_isConj_map_iff {α β : Type*} [Group α] [Group β] (e : α ≃* β)
    (a b : α) : IsConj (e a) (e b) ↔ IsConj a b := by
  refine ⟨fun h => ?_, fun h => e.toMonoidHom.map_isConj h⟩
  have h' := e.symm.toMonoidHom.map_isConj h
  simpa using h'

private lemma gs03_u62_isConj_symm_map {α β : Type*} [Group α] [Group β] (e : α ≃* β)
    (x : β) (a : α) : IsConj (e.symm x) a ↔ IsConj x (e a) := by
  have h := gs03_u62_isConj_map_iff e (e.symm x) a
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

@[expose] def U62HGen : Prop :=
  ∀ g ∈ u62AutW, g * g = 1 → g ≠ 1 → (True → g ∉ T46.subtype.range) →
    ∃ s : Fin 6 → ↥T46, T46.subtype.range ≤
      Subgroup.closure (Set.range fun i => (T46.subtype (s i))⁻¹ * g * T46.subtype (s i))

theorem gs03_u62_classes_W
    (hF : U62Facts) :
    ∃ r₁ r₂ : ↥u62AutW, ∀ a : ↥u62AutW, a * a = 1 → (a : Equiv.Perm (Fin 693)) ∉ T46 →
      IsConj r₁ a ∨ IsConj r₂ a := by
  classical
  have hQ : CFSG.Blueprint.LieModel ↥T46 .PSU 6 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_T46⟩
  obtain ⟨ρ₁, ρ₂, hρ⟩ := gs03_u62_outer_classes hQ
  refine ⟨(u62AutEquiv hF).symm ρ₁, (u62AutEquiv hF).symm ρ₂, ?_⟩
  intro a ha2 haT
  have ha2' : u62AutEquiv hF a * u62AutEquiv hF a = 1 := by
    rw [← map_mul, ha2, map_one]
  have hane : u62AutEquiv hF a ∉ inner ↥T46 := by
    intro hmem
    have hmem' : u62AutEquiv hF a ∈ (MulAut.conj : ↥T46 →* MulAut ↥T46).range := hmem
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hmem'
    have hEq : u62AutEquiv hF ⟨t, T46_le_u62AutW t.2⟩ = u62AutEquiv hF a := by
      change u62AutConj ⟨t, T46_le_u62AutW t.2⟩ = u62AutConj a
      rw [gs03_u62_u62AutConj_conj t]
      exact ht
    have hsub : a = ⟨t, T46_le_u62AutW t.2⟩ := ((u62AutEquiv hF).injective hEq).symm
    exact haT (by rw [hsub]; exact t.2)
  rcases hρ (u62AutEquiv hF a) ha2' hane with h | h
  · exact Or.inl ((gs03_u62_isConj_symm_map (u62AutEquiv hF) ρ₁ a).mpr h)
  · exact Or.inr ((gs03_u62_isConj_symm_map (u62AutEquiv hF) ρ₂ a).mpr h)

theorem gs03_u62_hcov
    (hF : U62Facts) {g₀ g₁ : Equiv.Perm (Fin 693)}
    (hf : U62RepFacts g₀ g₁) :
    ∀ g ∈ u62AutW, g * g = 1 → g ∉ T46 →
      ∃ r ∈ [g₀, g₁], ∃ h ∈ u62AutW, g = h * r * h⁻¹ := by
  classical
  simp only [U62RepFacts] at hf
  obtain ⟨⟨t₀, ht₀, hg₀eq⟩, ⟨t₁, ht₁, hg₁eq⟩, hg₀sq, hg₁sq, hfix, -, -⟩ := hf
  have hg₀W : g₀ ∈ u62AutW := by
    rw [hg₀eq]
    exact u62AutW.mul_mem (T46_le_u62AutW ht₀) u62Phi_mem_u62AutW
  have hg₁W : g₁ ∈ u62AutW := by
    rw [hg₁eq]
    exact u62AutW.mul_mem (T46_le_u62AutW ht₁) u62Phi_mem_u62AutW
  have hg₀not : g₀ ∉ T46 := by
    intro h
    apply u62Phi_not_mem_T46 hF
    rw [hg₀eq] at h
    have hmem : t₀⁻¹ * (t₀ * u62Phi) ∈ T46 := T46.mul_mem (T46.inv_mem ht₀) h
    have he : t₀⁻¹ * (t₀ * u62Phi) = u62Phi := by group
    rwa [he] at hmem
  have hg₁not : g₁ ∉ T46 := by
    intro h
    apply u62Phi_not_mem_T46 hF
    rw [hg₁eq] at h
    have hmem : t₁⁻¹ * (t₁ * u62Phi) ∈ T46 := T46.mul_mem (T46.inv_mem ht₁) h
    have he : t₁⁻¹ * (t₁ * u62Phi) = u62Phi := by group
    rwa [he] at hmem
  obtain ⟨r₁, r₂, hcover⟩ := gs03_u62_classes_W hF
  let X : Set ↥u62AutW := {a | a * a = 1 ∧ (a : Equiv.Perm (Fin 693)) ∉ T46}
  have hX : ∀ a ∈ X, IsConj r₁ a ∨ IsConj r₂ a := fun a ha => hcover a ha.1 ha.2
  have h0 : (⟨g₀, hg₀W⟩ : ↥u62AutW) ∈ X := by
    refine ⟨?_, hg₀not⟩
    apply Subtype.ext
    simp [hg₀sq]
  have h1 : (⟨g₁, hg₁W⟩ : ↥u62AutW) ∈ X := by
    refine ⟨?_, hg₁not⟩
    apply Subtype.ext
    simp [hg₁sq]
  have hn : ¬ IsConj (⟨g₀, hg₀W⟩ : ↥u62AutW) ⟨g₁, hg₁W⟩ := by
    intro hconj
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    have hc' : (c : Equiv.Perm (Fin 693)) * g₀ * (c : Equiv.Perm (Fin 693))⁻¹ = g₁ := by
      have := congrArg (fun x : ↥u62AutW => (x : Equiv.Perm (Fin 693))) hc
      simpa using this
    have hfixc := gs03FixCount_conj (c : Equiv.Perm (Fin 693)) g₀
    rw [hc'] at hfixc
    exact hfix hfixc.symm
  have hcover2 := gs03_two_class_cover (X := X) hX h0 h1 hn
  intro g hg hg2 hgT
  have hgX : (⟨g, hg⟩ : ↥u62AutW) ∈ X := by
    refine ⟨?_, hgT⟩
    apply Subtype.ext
    simpa using hg2
  rcases hcover2 ⟨g, hg⟩ hgX with h | h
  · rw [isConj_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨g₀, by simp, (c : Equiv.Perm (Fin 693)), c.2, ?_⟩
    have := congrArg (fun x : ↥u62AutW => (x : Equiv.Perm (Fin 693))) hc
    simpa using this.symm
  · rw [isConj_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨g₁, by simp, (c : Equiv.Perm (Fin 693)), c.2, ?_⟩
    have := congrArg (fun x : ↥u62AutW => (x : Equiv.Perm (Fin 693))) hc
    simpa using this.symm

theorem gs03_u62_hgen
    (hF : U62Facts) {g₀ g₁ : Equiv.Perm (Fin 693)}
    (hf : U62RepFacts g₀ g₁) : U62HGen := by
  classical
  intro g hg hg2 _ hout
  have hgT : g ∉ T46 := by
    have h := hout trivial
    rwa [Subgroup.range_subtype] at h
  obtain ⟨r, hr, c, hc, hgc⟩ := gs03_u62_hcov hF hf g hg hg2 hgT
  simp only [U62RepFacts] at hf
  obtain ⟨-, -, -, -, -, hgen₀, hgen₁⟩ := hf
  have hh' : ∀ s : ↥T46, c * T46.subtype s * c⁻¹ ∈ T46.subtype.range := by
    intro s
    rw [Subgroup.range_subtype]
    exact (Subgroup.mem_normalizer_iff.mp hc (T46.subtype s)).mp s.2
  have hhi' : ∀ s : ↥T46, c⁻¹ * T46.subtype s * c ∈ T46.subtype.range := by
    intro s
    rw [Subgroup.range_subtype]
    exact (Subgroup.mem_normalizer_iff.mp (u62AutW.inv_mem hc) (T46.subtype s)).mp s.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hrg₀ | hrg₁
  · rw [hrg₀] at hgc
    obtain ⟨w', hw'⟩ := hgen_conj_of_normalizes (ι := T46.subtype) T46.subtype_injective hh' hhi'
      (gs03_witness_pad (ι := T46.subtype) (g := g₀) (k := 4) (k' := 6)
        (by norm_num) (by norm_num) hgen₀)
    exact ⟨w', by rwa [← hgc] at hw'⟩
  · rw [hrg₁] at hgc
    obtain ⟨w', hw'⟩ := hgen_conj_of_normalizes (ι := T46.subtype) T46.subtype_injective hh' hhi'
      (gs03_witness_pad (ι := T46.subtype) (g := g₁) (k := 3) (k' := 6)
        (by norm_num) (by norm_num) hgen₁)
    exact ⟨w', by rwa [← hgc] at hw'⟩

theorem gs03_u62_autGenBound
    (hF : U62Facts) (hgen : U62HGen) :
    AutGenBound ↥T46 6 fun a => True → a ∉ inner ↥T46 := by
  refine autGenBound_of_permModel (S := ↥T46) (Ω := Fin 693)
    (ι := T46.subtype) T46.subtype_injective ?_ u62AutW
    (by rw [Subgroup.range_subtype]; exact T46_le_u62AutW) ?_ ?_ True ?_
  · intro τ hτ
    have hmem : τ ∈ Subgroup.centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      simpa using (hτ ⟨s, hs⟩).symm
    rw [centralizer_T46 hF, Subgroup.mem_bot] at hmem
    exact hmem
  · intro g hg s
    rw [Subgroup.range_subtype]
    exact (Subgroup.mem_normalizer_iff.mp hg (T46.subtype s)).mp s.2
  · exact le_of_eq (Nat.card_congr (u62AutEquiv hF).toEquiv).symm
  · exact hgen

end CFSG.LocalAnalysis.WeakClosure81
