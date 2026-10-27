module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingModule
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.GroupTheory SemidirectProduct

theorem finrank_add_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]
    {s t u : Submodule K V} (hs : s ≤ u) (ht : t ≤ u) (hd : s ⊓ t = ⊥) :
    Module.finrank K s + Module.finrank K t ≤ Module.finrank K u := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq s t
  rw [hd, finrank_bot, add_zero] at h
  rw [← h]
  exact Submodule.finrank_mono (sup_le hs ht)

section NoSecondAtom

variable {p d q : ℕ} [Fact q.Prime] {S : Type*} [Group S] [Finite S] [IsElementaryAbelian 2 S]
  {A : Type*} [Group A] {φ : A →* MulAut S} {M : Type*} [AddCommGroup M] [Module (ZMod q) M]
  [Finite M]

theorem false_of_two_atoms (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) (hS : Nat.card S = 2 ^ d)
    (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq2 : (2 : ZMod q) ≠ 0) (σ : Representation (ZMod q) (S ⋊[φ] A) M)
    (hdim4 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (σ (inl s)) 1) ≤ 4)
    {W W' : Subrepresentation σ} (hW : IsAtom W) (hW' : IsAtom W') (hdisj : W ⊓ W' = ⊥)
    (hnt : ∃ s : S, ∃ w ∈ W, σ (inl s) w ≠ w) (hnt' : ∃ s : S, ∃ w ∈ W', σ (inl s) w ≠ w) :
    False := by
  classical
  have hf := faithful_of_nontrivial hirr σ W hnt
  have hf' := faithful_of_nontrivial hirr σ W' hnt'
  obtain ⟨e, he1, hdimW, h7, h5, -, -⟩ := sb_of_atom hpd hS hφ hirr hq2 σ hW hf
  obtain ⟨e', he1', hdimW', h7', h5', -, -⟩ := sb_of_atom hpd hS hφ hirr hq2 σ hW' hf'
  have hsum : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) +
      Module.finrank (ZMod q) ↥(W'.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) ≤ 4 := by
    intro s hs
    have h1 : (W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) ⊓
        (W'.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hv1 : v ∈ W := hv.1.1
      have hv2 : v ∈ W' := hv.2.1
      have : v ∈ W ⊓ W' := ⟨hv1, hv2⟩
      rw [hdisj] at this
      exact this
    exact (finrank_add_le inf_le_right inf_le_right h1).trans (hdim4 s hs)
  have hS1 : ∃ s : S, s ≠ 1 := by
    have : 1 < Nat.card S := by
      rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hS] <;> norm_num
    obtain ⟨a, b, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp this |>.exists_pair_ne
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  rcases hpd with ⟨hp7, hd⟩ | ⟨hp5, hd⟩
  · obtain ⟨s, hs⟩ := hS1
    have := hsum s hs
    rw [h7 hp7 s hs] at this
    rw [h7' hp7 s hs] at this
    omega
  · obtain ⟨c1, c2, c3⟩ := h5 hp5
    obtain ⟨c1', c2', c3'⟩ := h5' hp5
    set T := {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
      ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 * e} with hT
    set T' := {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
      ↥(W'.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 * e'} with hT'
    have hcard : ({s : S | s ≠ 1} : Set S).ncard = 15 := by
      have h1 := Set.ncard_add_ncard_compl ({1} : Set S)
      rw [Set.ncard_singleton, hS, hd] at h1
      have h2 : ({s : S | s ≠ 1} : Set S) = ({1} : Set S)ᶜ := by ext; simp
      rw [h2]
      omega
    have hsub : T ∪ T' ⊆ {s : S | s ≠ 1} := fun s hs => by
      rcases hs with hs | hs
      · exact hs.1
      · exact hs.1
    have hle : (T ∪ T').ncard ≤ 15 := hcard ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
    have hint := Set.ncard_union_add_ncard_inter T T' (Set.toFinite _) (Set.toFinite _)
    have hne : (T ∩ T').Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Set.ncard_empty] at hint
      omega
    obtain ⟨s, ⟨hs1, hs3⟩, ⟨-, hs3'⟩⟩ := hne
    have := hsum s hs1
    rw [hs3, hs3'] at this
    omega

end NoSecondAtom

section Structure

variable {p d q : ℕ} [Fact q.Prime] {S : Type*} [Group S] [Finite S] [IsElementaryAbelian 2 S]
  {A : Type*} [Group A] {φ : A →* MulAut S} {M : Type*} [AddCommGroup M] [Module (ZMod q) M]
  [Finite M]

instance finite_semidirect [Finite A] : Finite (S ⋊[φ] A) :=
  Finite.of_equiv (S × A) SemidirectProduct.equivProd.symm

instance range_inl_normal : ((inl : S →* S ⋊[φ] A).range).Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

omit [Finite S] [IsElementaryAbelian 2 S] [Finite M] in
theorem mem_sup_subrep {σ : Representation (ZMod q) (S ⋊[φ] A) M} {X Y : Subrepresentation σ}
    {v : M} (h : v ∈ X ⊔ Y) : ∃ a ∈ X, ∃ b ∈ Y, a + b = v := by
  have h' : v ∈ X.toSubmodule ⊔ Y.toSubmodule := by
    rw [← Subrepresentation.toSubmodule_sup]; exact h
  exact Submodule.mem_sup.mp h'

theorem rep_structure [Finite A] (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4))
    (hS : Nat.card S = 2 ^ d) (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq2 : (2 : ZMod q) ≠ 0) [NeZero (Nat.card (S ⋊[φ] A) : ZMod q)]
    (σ : Representation (ZMod q) (S ⋊[φ] A) M)
    (hdim4 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (σ (inl s)) 1) ≤ 4)
    (hnt : ∃ s : S, ∃ v : M, σ (inl s) v ≠ v) :
    ∃ W F₀ : Subrepresentation σ, IsAtom W ∧ IsCompl F₀ W ∧
      (∀ s : S, ∀ v ∈ F₀, σ (inl s) v = v) ∧
      (∀ w ∈ W, (∀ s : S, σ (inl s) w = w) → w = 0) ∧
      (∃ s : S, ∃ w ∈ W, σ (inl s) w ≠ w) := by
  classical
  set N : Subgroup (S ⋊[φ] A) := (inl : S →* S ⋊[φ] A).range with hN
  obtain ⟨F₁, hF₁⟩ := ComplementedLattice.exists_isCompl (fixedSub σ N)
  have hF₁nt : ∃ n ∈ N, ∃ v ∈ F₁, σ n v ≠ v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, v, hv⟩ := hnt
    have hvtop : v ∈ fixedSub σ N ⊔ F₁ := by
      rw [hF₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_subrep hvtop
    apply hv
    rw [← hab, map_add, ha (inl s) ⟨s, rfl⟩, hcon (inl s) ⟨s, rfl⟩ b hb]
  obtain ⟨W, hWatom, hWF₁, hWnt⟩ := exists_atom_nontrivial_le σ N F₁ hF₁nt
  obtain ⟨C, hC⟩ := ComplementedLattice.exists_isCompl W
  have hF₁eq : F₁ = W ⊔ F₁ ⊓ C := by
    have h1 : W ⊔ C = ⊤ := hC.sup_eq_top
    have h2 : (W ⊔ C) ⊓ F₁ = W ⊔ C ⊓ F₁ := sup_inf_assoc_of_le C hWF₁
    rw [h1, top_inf_eq] at h2
    rw [inf_comm F₁ C]
    exact h2
  have hF₂triv : ∀ n ∈ N, ∀ v ∈ F₁ ⊓ C, σ n v = v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn, v, hv, hnv⟩ := hcon
    obtain ⟨W', hW'atom, hW'le, hW'nt⟩ := exists_atom_nontrivial_le σ N (F₁ ⊓ C) ⟨n, hn, v, hv, hnv⟩
    have hdisj : W ⊓ W' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxC : x ∈ C := (hW'le hx.2).2
      have : x ∈ W ⊓ C := ⟨hx.1, hxC⟩
      rw [hC.inf_eq_bot] at this
      exact this
    obtain ⟨n', hn', w', hw', hnw'⟩ := hW'nt
    obtain ⟨s', rfl⟩ := hn'
    obtain ⟨n₀, hn₀, w₀, hw₀, hnw₀⟩ := hWnt
    obtain ⟨s₀, rfl⟩ := hn₀
    exact false_of_two_atoms hpd hS hφ hirr hq2 σ hdim4 hWatom hW'atom hdisj ⟨s₀, w₀, hw₀, hnw₀⟩
      ⟨s', w', hw', hnw'⟩
  have hF₂bot : F₁ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ fixedSub σ N := fun n hn => hF₂triv n hn v hv
    have : v ∈ fixedSub σ N ⊓ F₁ := ⟨h1, hv.1⟩
    rw [hF₁.inf_eq_bot] at this
    exact this
  rw [hF₂bot, sup_bot_eq] at hF₁eq
  refine ⟨W, fixedSub σ N, hWatom, ?_, ?_, ?_, ?_⟩
  · rw [← hF₁eq]
    exact hF₁
  · intro s v hv
    exact hv (inl s) ⟨s, rfl⟩
  · intro w hw hfix
    have h1 : w ∈ fixedSub σ N := by
      rintro _ ⟨s, rfl⟩
      exact hfix s
    have h2 : w ∈ F₁ := hWF₁ hw
    have : w ∈ fixedSub σ N ⊓ F₁ := ⟨h1, h2⟩
    rw [hF₁.inf_eq_bot] at this
    exact this
  · obtain ⟨n, hn, w, hw, hnw⟩ := hWnt
    obtain ⟨s, rfl⟩ := hn
    exact ⟨s, w, hw, hnw⟩

theorem rep_summary [Finite A] (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4))
    (hS : Nat.card S = 2 ^ d) (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq2 : (2 : ZMod q) ≠ 0) [NeZero (Nat.card (S ⋊[φ] A) : ZMod q)]
    (σ : Representation (ZMod q) (S ⋊[φ] A) M)
    (hdim4 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (σ (inl s)) 1) ≤ 4)
    (hnt : ∃ s : S, ∃ v : M, σ (inl s) v ≠ v) :
    ∃ W F₀ : Subrepresentation σ, IsAtom W ∧ IsCompl F₀ W ∧
      (∀ s : S, ∀ v ∈ F₀, σ (inl s) v = v) ∧
      Module.finrank (ZMod q) W.toSubmodule = p ∧ Module.finrank (ZMod q) F₀.toSubmodule ≤ 1 ∧
      (∃ s : S, s ≠ 1 ∧ Module.finrank (ZMod q)
        ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3) ∧
      (∀ s : S, s ≠ 1 → 1 ≤ Module.finrank (ZMod q)
        ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1)) ∧
      (p = 7 → ∀ s : S, s ≠ 1 → Module.finrank (ZMod q)
        ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3) ∧
      (p = 5 →
        Set.ncard {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3} = 10 ∧
        Set.ncard {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 1} = 5) ∧
      ∃ (n : ℕ) (v : Option (Fin n) → M) (c : Option (Fin n) → S → ZMod q),
        ⊤ ≤ Submodule.span (ZMod q) (Set.range v) ∧
        (∀ i s, σ (inl s) (v i) = c i s • v i) ∧ (∀ i s, c i s = 1 ∨ c i s = -1) ∧
        (∀ i j, i ≠ j → ∃ s, c i s ≠ c j s) := by
  classical
  obtain ⟨W, F₀, hWatom, hcompl, hF₀triv, hCW, hnt'⟩ :=
    rep_structure hpd hS hφ hirr hq2 σ hdim4 hnt
  have hf := faithful_of_nontrivial hirr σ W hnt'
  obtain ⟨e, he1, hdimW, h7, h5, hle, hfam⟩ := sb_of_atom hpd hS hφ hirr hq2 σ hWatom hf
  have he : e = 1 := hle (fun s hs =>
    (Submodule.finrank_mono inf_le_right).trans (hdim4 s hs))
  subst he
  have hS1 : ∃ s : S, s ≠ 1 := by
    have : 1 < Nat.card S := by
      rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hS] <;> norm_num
    obtain ⟨a, b, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp this |>.exists_pair_ne
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have h3 : ∃ s : S, s ≠ 1 ∧ Module.finrank (ZMod q)
      ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 := by
    rcases hpd with ⟨hp7, -⟩ | ⟨hp5, -⟩
    · obtain ⟨s, hs⟩ := hS1
      exact ⟨s, hs, by simpa using h7 hp7 s hs⟩
    · obtain ⟨hc, -, -⟩ := h5 hp5
      obtain ⟨s, hs, hd⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hc]; norm_num)
      exact ⟨s, hs, by simpa using hd⟩
  have h1 : ∀ s : S, s ≠ 1 → 1 ≤ Module.finrank (ZMod q)
      ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) := by
    intro s hs
    rcases hpd with ⟨hp7, -⟩ | ⟨hp5, -⟩
    · rw [h7 hp7 s hs]; norm_num
    · obtain ⟨-, -, hh⟩ := h5 hp5
      rcases hh s hs with hh | hh <;> omega
  have hF₀dim : Module.finrank (ZMod q) F₀.toSubmodule ≤ 1 := by
    obtain ⟨s, hs, hd⟩ := h3
    have hdisj : (W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) ⊓ F₀.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ W ⊓ F₀ := ⟨hv.1.1, hv.2⟩
      rw [inf_comm, hcompl.inf_eq_bot] at this
      exact this
    have hF₀le : F₀.toSubmodule ≤ Module.End.eigenspace (σ (inl s)) 1 := by
      intro v hv
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact hF₀triv s v hv
    have := finrank_add_le (inf_le_right : W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1 ≤
      Module.End.eigenspace (σ (inl s)) 1) hF₀le hdisj
    have h4 := hdim4 s hs
    omega
  obtain ⟨n, v₁, c₁, hv₁W, hv₁0, hv₁span, hv₁eig, hv₁sign, hv₁dist⟩ := hfam rfl
  have : Module.Finite (ZMod q) F₀.toSubmodule := Module.Finite.of_finite
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hF₀dim
  refine ⟨W, F₀, hWatom, hcompl, hF₀triv, by simpa using hdimW, hF₀dim, h3, h1, h7, ?_, ?_⟩
  · intro hp5
    obtain ⟨hc1, hc2, -⟩ := h5 hp5
    exact ⟨by simpa using hc1, by simpa using hc2⟩
  refine ⟨n, fun o => o.elim (v₀ : M) v₁, fun o => o.elim (fun _ => 1) c₁, ?_, ?_, ?_, ?_⟩
  · intro m _
    have hm : m ∈ F₀ ⊔ W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_subrep hm
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨c, hc⟩ := hv₀ ⟨a, ha⟩
      have : a = c • (v₀ : M) := (congrArg Subtype.val hc).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
    · refine Submodule.span_mono ?_ (hv₁span hb)
      rintro _ ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
  · intro o t
    cases o with
    | none => simpa using hF₀triv t v₀ v₀.2
    | some i => exact hv₁eig i t
  · intro o t
    cases o with
    | none => exact Or.inl rfl
    | some i => exact hv₁sign i t
  · intro o o' hoo'
    cases o with
    | none =>
      cases o' with
      | none => exact absurd rfl hoo'
      | some j =>
        by_contra hcon
        push Not at hcon
        simp only [Option.elim] at hcon
        refine hv₁0 j (hCW (v₁ j) (hv₁W j) fun t => ?_)
        rw [hv₁eig, ← hcon t, one_smul]
    | some i =>
      cases o' with
      | none =>
        by_contra hcon
        push Not at hcon
        simp only [Option.elim] at hcon
        refine hv₁0 i (hCW (v₁ i) (hv₁W i) fun t => ?_)
        rw [hv₁eig, hcon t, one_smul]
      | some j => exact hv₁dist i j (fun h => hoo' (by rw [h]))

end Structure

end CFSG.RankThree.PartOne.Lifting36
