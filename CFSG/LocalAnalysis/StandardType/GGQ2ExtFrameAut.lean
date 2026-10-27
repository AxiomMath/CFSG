module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def ExtCasesVx (R : RawFrameData) (vx : R.V) : Prop :=
  vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ →
    (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∉ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k : R.Code, Candidate R vx j z k →
    R.inside j ≤ R.inside k →
    TwoNodeLabels 3 (R.label ℓ) (R.label j) ∨ TwoNodeLabels 3 (R.label k) (R.label j) ∨
    InLLeafAt R vx z ℓ k ∨ ExtE6At R vx z ℓ k ∨ ExtInnerAt R z k ∨ ExtDetAt R z k ∨
    ExtAmbDAt R vx z ℓ k ∨ ExtD5At R vx z ℓ j k

theorem extCases_iff_forall (R : RawFrameData) : ExtCases R ↔ ∀ vx, ExtCasesVx R vx :=
  Iff.rfl

section LinMap

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose, reducible] def GGQ2LinOn.map (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) :
    GGQ2LinOn p V where
  ι := W.ι
  coxeter := W.coxeter
  cartan := W.cartan
  coroot i := g (W.coroot i)
  root i := (W.root i).comp (g.symm : V →ₗ[ZMod p] V)
  a := W.a
  b := W.b
  a_ne_b := W.a_ne_b
  a_leaf := W.a_leaf
  isWeyl := W.isWeyl
  isCartan := W.isCartan
  pairing i j := by simp [W.pairing]

theorem span_singleton_map_equiv (g : V ≃ₗ[ZMod p] V) (x : V) :
    (Submodule.span (ZMod p) {x}).map (g : V →ₗ[ZMod p] V) = Submodule.span (ZMod p) {g x} := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem GGQ2LinOn.map_simpleRefl (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) (i : W.ι) :
    (W.map g).toLin.simpleRefl i = MulAut.conj g (W.toLin.simpleRefl i) := by
  ext v
  simp [GGQ2Lin.simpleRefl, Module.reflection_apply, MulAut.conj_apply]

theorem GGQ2LinOn.map_parab (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) (S : Set W.ι) :
    (W.map g).toLin.parab S = (W.toLin.parab S).map (MulAut.conj g).toMonoidHom := by
  rw [GGQ2Lin.parab, GGQ2Lin.parab, MonoidHom.map_closure, Set.image_image]
  congr 1
  exact Set.image_congr fun i _ => W.map_simpleRefl g i

theorem GGQ2LinOn.map_parab_eq (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) {S : Set W.ι}
    {N : Subgroup (V ≃ₗ[ZMod p] V)} (h : W.toLin.parab S = N) :
    (W.map g).toLin.parab S = N.map (MulAut.conj g).toMonoidHom := by
  rw [W.map_parab g S, h]

theorem GGQ2LinOn.map_weyl_eq (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V)
    {N : Subgroup (V ≃ₗ[ZMod p] V)} (h : W.toLin.weyl = N) :
    (W.map g).toLin.weyl = N.map (MulAut.conj g).toMonoidHom :=
  W.map_parab_eq g h

theorem GGQ2LinOn.map_simpleRefl_mem (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) {i : W.ι}
    {N : Subgroup (V ≃ₗ[ZMod p] V)} (h : W.toLin.simpleRefl i ∈ N) :
    (W.map g).toLin.simpleRefl i ∈ N.map (MulAut.conj g).toMonoidHom := by
  rw [W.map_simpleRefl g i]
  exact Subgroup.mem_map_of_mem _ h

theorem GGQ2LinOn.map_ker (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) (P : W.ι → Prop) {x : V}
    (h : ∀ v, (∀ i, P i → W.root i v = 0) ↔ v ∈ Submodule.span (ZMod p) {x}) (v : V) :
    (∀ i, P i → (W.map g).root i v = 0) ↔ v ∈ Submodule.span (ZMod p) {g x} := by
  rw [← span_singleton_map_equiv, Submodule.mem_map_equiv]
  exact h (g.symm v)

theorem GGQ2LinOn.map_root_apply (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) (i : W.ι) (v : V) :
    (W.map g).root i (g v) = W.root i v := by
  simp

theorem GGQ2LinOn.map_linearIndependent (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) :
    LinearIndependent (ZMod p) (W.map g).coroot ↔ LinearIndependent (ZMod p) W.coroot :=
  LinearMap.linearIndependent_iff (g : V →ₗ[ZMod p] V) g.ker

theorem GGQ2LinOn.map_basis (W : GGQ2LinOn p V) (g : V ≃ₗ[ZMod p] V) (h : W.toLin.Basis) :
    (W.map g).toLin.Basis :=
  ⟨(W.map_linearIndependent g).mpr h.1, h.2⟩

end LinMap

structure FrameAut (R : RawFrameData) where
  g : R.V ≃ₗ[ZMod 3] R.V
  σ : R.Code ≃ R.Code
  admissible_iff : ∀ c, R.admissible (σ c) ↔ R.admissible c
  occurs_iff : ∀ U c, R.occurs (U.map (g : R.V →ₗ[ZMod 3] R.V)) (σ c) ↔ R.occurs U c
  cent_eq : ∀ c, R.cent (σ c) = (R.cent c).map (g : R.V →ₗ[ZMod 3] R.V)
  inside_eq : ∀ c, R.inside (σ c) = (R.inside c).map (g : R.V →ₗ[ZMod 3] R.V)
  normalizerGroup_eq : ∀ c,
    R.normalizerGroup (σ c) = (R.normalizerGroup c).map (MulAut.conj g).toMonoidHom
  label_eq : ∀ c, R.label (σ c) = R.label c

namespace FrameAut

variable {R : RawFrameData} (A : FrameAut R)

theorem mem_map_iff (x : R.V) (P : Submodule (ZMod 3) R.V) :
    A.g x ∈ P.map (A.g : R.V →ₗ[ZMod 3] R.V) ↔ x ∈ P := by
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem map_eq_map_iff (P Q : Submodule (ZMod 3) R.V) :
    P.map (A.g : R.V →ₗ[ZMod 3] R.V) = Q.map (A.g : R.V →ₗ[ZMod 3] R.V) ↔ P = Q :=
  (Submodule.map_injective_of_injective A.g.injective).eq_iff

theorem map_le_map_iff (P Q : Submodule (ZMod 3) R.V) :
    P.map (A.g : R.V →ₗ[ZMod 3] R.V) ≤ Q.map (A.g : R.V →ₗ[ZMod 3] R.V) ↔ P ≤ Q :=
  Submodule.map_le_map_iff_of_injective A.g.injective P Q

theorem inside_le_iff (c d : R.Code) :
    R.inside (A.σ c) ≤ R.inside (A.σ d) ↔ R.inside c ≤ R.inside d := by
  rw [A.inside_eq, A.inside_eq, A.map_le_map_iff]

theorem normalizerGroup_le_iff (c d : R.Code) :
    R.normalizerGroup (A.σ c) ≤ R.normalizerGroup (A.σ d) ↔
      R.normalizerGroup c ≤ R.normalizerGroup d := by
  rw [A.normalizerGroup_eq, A.normalizerGroup_eq]
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj A.g).injective

theorem cent_eq_span_iff (c : R.Code) (x : R.V) :
    R.cent (A.σ c) = Submodule.span (ZMod 3) {A.g x} ↔
      R.cent c = Submodule.span (ZMod 3) {x} := by
  rw [A.cent_eq, ← span_singleton_map_equiv, A.map_eq_map_iff]

theorem occurs_span_iff (c : R.Code) (x : R.V) :
    R.occurs (Submodule.span (ZMod 3) {A.g x}) (A.σ c) ↔
      R.occurs (Submodule.span (ZMod 3) {x}) c := by
  rw [← span_singleton_map_equiv, A.occurs_iff]

theorem mem_span_iff (x y : R.V) :
    A.g x ∈ Submodule.span (ZMod 3) {A.g y} ↔ x ∈ Submodule.span (ZMod 3) {y} := by
  rw [← span_singleton_map_equiv, A.mem_map_iff]

theorem candidate_iff (vx z : R.V) (j k : R.Code) :
    Candidate R (A.g vx) (A.σ j) (A.g z) (A.σ k) ↔ Candidate R vx j z k := by
  unfold Candidate
  rw [A.admissible_iff, A.occurs_span_iff, A.cent_eq_span_iff, A.normalizerGroup_le_iff,
    A.cent_eq, A.mem_map_iff]

theorem normalizerGroup_sup (c d : R.Code) :
    R.normalizerGroup (A.σ c) ⊔ R.normalizerGroup (A.σ d) =
      (R.normalizerGroup c ⊔ R.normalizerGroup d).map (MulAut.conj A.g).toMonoidHom := by
  rw [A.normalizerGroup_eq, A.normalizerGroup_eq, Subgroup.map_sup]

theorem inLLeafAt (vx z : R.V) (ℓ k : R.Code) (h : InLLeafAt R vx z ℓ k) :
    InLLeafAt R (A.g vx) (A.g z) (A.σ ℓ) (A.σ k) := by
  obtain ⟨W, hL, hK, hx, hz, hleaf⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hx, W.map_ker A.g _ hz, hleaf⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hL
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hK

theorem extE6At (vx z : R.V) (ℓ k : R.Code) (h : ExtE6At R vx z ℓ k) :
    ExtE6At R (A.g vx) (A.g z) (A.σ ℓ) (A.σ k) := by
  obtain ⟨W, hL, hK, hx, hz, he⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hx, W.map_ker A.g _ hz, he⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hL
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hK

theorem nbrLinAt (z : R.V) (k : R.Code) (W : GGQ2LinOn 3 R.V) (h : NbrLinAt R z k W) :
    NbrLinAt R (A.g z) (A.σ k) (W.map A.g) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_weyl_eq A.g h.1
  · have := W.map_ker A.g (fun _ => True) (x := z) (fun v => by simpa using h.2 v) v
    simpa using this

theorem extInnerAt (z : R.V) (k : R.Code) (h : ExtInnerAt R z k) :
    ExtInnerAt R (A.g z) (A.σ k) := by
  obtain ⟨W, hW, hdet, rest⟩ := h
  exact ⟨W.map A.g, A.nbrLinAt z k W hW, hdet, rest⟩

theorem extDetAt (z : R.V) (k : R.Code) (h : ExtDetAt R z k) :
    ExtDetAt R (A.g z) (A.σ k) := by
  obtain ⟨W, hW, hdet, hpos⟩ := h
  refine ⟨W.map A.g, A.nbrLinAt z k W hW, hdet, ?_⟩
  rcases hpos with hli | hfr
  · exact Or.inl ((W.map_linearIndependent A.g).mpr hli)
  · exact Or.inr hfr

theorem extAmbDAt (vx z : R.V) (ℓ k : R.Code) (h : ExtAmbDAt R vx z ℓ k) :
    ExtAmbDAt R (A.g vx) (A.g z) (A.σ ℓ) (A.σ k) := by
  obtain ⟨W, hK, ha, hz, hx, hB, rest⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hz, fun i hia hib => ?_, W.map_basis A.g hB, rest⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hK
  · rw [A.normalizerGroup_sup]
    exact W.map_simpleRefl_mem A.g ha
  · rw [W.map_root_apply A.g i vx]
    exact hx i hia hib

theorem extD5At (vx z : R.V) (ℓ j k : R.Code) (h : ExtD5At R vx z ℓ j k) :
    ExtD5At R (A.g vx) (A.g z) (A.σ ℓ) (A.σ j) (A.σ k) := by
  obtain ⟨W, hK, ha, hz, hx, hB, he, hJ, lab, hlab, hiso, hinf, hsup, hfin⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hz, fun i hia hib => ?_, W.map_basis A.g hB, he, ?_,
    lab, hlab, by rwa [A.label_eq], ?_, ?_, ?_⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hK
  · rw [A.normalizerGroup_sup]
    exact W.map_simpleRefl_mem A.g ha
  · rw [W.map_root_apply A.g i vx]
    exact hx i hia hib
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hJ
  · rw [A.inside_eq, A.cent_eq, ← Submodule.map_inf _ A.g.injective, hinf, Submodule.map_bot]
  · rw [A.inside_eq, A.cent_eq, ← Submodule.map_sup, hsup, Submodule.map_top, LinearEquiv.range]
  · rw [A.inside_eq, LinearEquiv.finrank_map_eq]
    exact hfin

theorem extCasesVx_map {vx : R.V} (h : ExtCasesVx R vx) : ExtCasesVx R (A.g vx) := by
  intro hvx ℓ' hℓ hlab hocc hcent hins U' hU hxU j' hj hjocc hjcent hjins hjN z' hzU hzx k' hk
    hkins
  obtain ⟨ℓ, rfl⟩ := A.σ.surjective ℓ'
  obtain ⟨j, rfl⟩ := A.σ.surjective j'
  obtain ⟨k, rfl⟩ := A.σ.surjective k'
  obtain ⟨z, rfl⟩ := A.g.surjective z'
  obtain ⟨U, rfl⟩ : ∃ U : Submodule (ZMod 3) R.V, U' = U.map (A.g : R.V →ₗ[ZMod 3] R.V) :=
    ⟨U'.map (A.g.symm : R.V →ₗ[ZMod 3] R.V), ((Submodule.map_symm_eq_iff A.g).mp rfl).symm⟩
  rw [A.label_eq] at hlab
  rw [A.admissible_iff] at hℓ hj
  rw [A.occurs_span_iff] at hocc
  rw [A.cent_eq_span_iff] at hcent
  rw [A.inside_eq, A.mem_map_iff] at hins
  rw [LinearEquiv.finrank_map_eq] at hU
  rw [A.mem_map_iff] at hxU hzU
  rw [A.occurs_iff] at hjocc
  rw [A.cent_eq, A.map_eq_map_iff] at hjcent
  rw [A.inside_le_iff] at hjins hkins
  rw [A.normalizerGroup_le_iff] at hjN
  rw [A.mem_span_iff] at hzx
  rw [A.candidate_iff] at hk
  rcases h (fun h0 => hvx (by rw [h0, map_zero])) ℓ hℓ hlab hocc hcent hins U hU hxU j hj hjocc
    hjcent hjins hjN z hzU hzx k hk hkins with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact Or.inl (by rwa [A.label_eq, A.label_eq])
  · exact Or.inr (Or.inl (by rwa [A.label_eq, A.label_eq]))
  · exact Or.inr (Or.inr (Or.inl (A.inLLeafAt _ _ _ _ h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (A.extE6At _ _ _ _ h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (A.extInnerAt _ _ h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (A.extDetAt _ _ h6))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (A.extAmbDAt _ _ _ _ h7)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (A.extD5At _ _ _ _ _ h8)))))))

end FrameAut

end CFSG.StandardType.GGQ2Frame

end
