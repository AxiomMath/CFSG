module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreOrbit

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem lineAction_mk (g : V ≃ₗ[F] V) {v : V} (hv : v ≠ 0) :
    lineAction F V g (Projectivization.mk F v hv) =
      Projectivization.mk F (g v) ((LinearEquiv.map_ne_zero_iff g).2 hv) := rfl

theorem exists_smul_rep {g : V ≃ₗ[F] V} {p q : ℙ F V} (h : lineAction F V g p = q) :
    ∃ c : F, c ≠ 0 ∧ g p.rep = c • q.rep := by
  have h1 : lineAction F V g p = Projectivization.mk F (g p.rep)
      ((LinearEquiv.map_ne_zero_iff g).2 p.rep_nonzero) := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    exact lineAction_mk g p.rep_nonzero
  rw [h1] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ q.rep_nonzero).1
    (h.trans (Projectivization.mk_rep q).symm)
  refine ⟨a, fun h0 => ?_, ha.symm⟩
  rw [h0, zero_smul] at ha
  exact (LinearEquiv.map_ne_zero_iff g).2 p.rep_nonzero ha.symm

theorem IsSixOrbit.exists_mem_embedding (hO : IsSixOrbit L pt) {n : ℕ} (hn : n ≤ 4)
    (u v : Fin n ↪ Fin 6) : ∃ g ∈ L, ∀ i, lineAction F V g (pt (u i)) = pt (v i) := by
  have hmt : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 4 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 6)
  have hmt' : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) n :=
    MulAction.isMultiplyPretransitive_of_le hn (by simp)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) u v
  obtain ⟨g, hg, hgσ⟩ := (hO.alt σ).1 σ.2
  refine ⟨g, hg, fun i => ?_⟩
  rw [hgσ]
  have := congrArg (fun f : Fin n ↪ Fin 6 => f i) hσ
  simp only [Function.Embedding.smul_apply] at this
  rw [← this]
  rfl

@[expose] def triple (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Fin 3 ↪ Fin 6 :=
  ⟨![i, j, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩

theorem indep_transport {i j k i' j' k' : Fin 6} {g : V ≃ₗ[F] V}
    (h1 : lineAction F V g (pt i) = pt i') (h2 : lineAction F V g (pt j) = pt j')
    (h3 : lineAction F V g (pt k) = pt k')
    (hind : LinearIndependent F ![(pt i').rep, (pt j').rep, (pt k').rep]) :
    LinearIndependent F ![(pt i).rep, (pt j).rep, (pt k).rep] := by
  obtain ⟨c₁, hc₁, e₁⟩ := exists_smul_rep h1
  obtain ⟨c₂, hc₂, e₂⟩ := exists_smul_rep h2
  obtain ⟨c₃, hc₃, e₃⟩ := exists_smul_rep h3
  have hw := hind.units_smul ![Units.mk0 c₁ hc₁, Units.mk0 c₂ hc₂, Units.mk0 c₃ hc₃]
  refine LinearIndependent.of_comp (g : V →ₗ[F] V) ?_
  convert hw using 1
  funext a
  fin_cases a <;> simp [e₁, e₂, e₃, Units.smul_def]

theorem vec3_eq_snoc {M : Type*} (a b c : M) : ![a, b, c] = Fin.snoc ![a, b] c := by
  funext i
  fin_cases i <;> rfl

theorem IsSixOrbit.linearIndependent_three [FiniteDimensional F V] (hV : Module.finrank F V = 3)
    (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent F ![(pt i).rep, (pt j).rep, (pt k).rep] := by
  classical
  by_contra hdep
  have hall : ∀ {i' j' k' : Fin 6}, i' ≠ j' → i' ≠ k' → j' ≠ k' →
      ¬ LinearIndependent F ![(pt i').rep, (pt j').rep, (pt k').rep] := by
    intro i' j' k' h1 h2 h3 hind
    obtain ⟨g, -, hgl⟩ := hO.exists_mem_embedding (n := 3) (by norm_num)
      (triple i j k hij hik hjk) (triple i' j' k' h1 h2 h3)
    exact hdep (indep_transport (hgl 0) (hgl 1) (hgl 2) hind)
  have hpair : LinearIndependent F ![(pt 0).rep, (pt 1).rep] :=
    Projectivization.linearIndependent_pair_iff_ne.2 fun h => absurd (hO.inj h) (by decide)
  set W₂ : Submodule F V := Submodule.span F (↑({(pt 0).rep, (pt 1).rep} : Finset V)) with hW₂
  have hspan : ∀ l, (pt l).rep ∈ W₂ := by
    intro l
    by_cases h0 : l = 0
    · subst h0
      exact Submodule.subset_span (by simp)
    by_cases h1 : l = 1
    · subst h1
      exact Submodule.subset_span (by simp)
    have hd := hall (i' := 0) (j' := 1) (k' := l) (by decide) (Ne.symm h0) (Ne.symm h1)
    rw [vec3_eq_snoc, linearIndependent_finSnoc] at hd
    by_contra hnot
    apply hd
    refine ⟨hpair, fun hmem => hnot (Submodule.span_mono ?_ hmem)⟩
    rintro _ ⟨a, rfl⟩
    fin_cases a <;> simp
  set W₀ : Submodule F V := Submodule.span F (Set.range fun l => (pt l).rep) with hW₀
  have hinv : ∀ g ∈ L, ∀ w ∈ W₀, g w ∈ W₀ := by
    intro g hg w hw
    have hle : W₀.map (g : V →ₗ[F] V) ≤ W₀ := by
      rw [hW₀, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
      obtain ⟨m, hm⟩ := hO.mem g hg l
      obtain ⟨c, -, hc⟩ := exists_smul_rep hm
      change g (pt l).rep ∈ W₀
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    exact hle ⟨w, hw, rfl⟩
  have hle₂ : W₀ ≤ W₂ := by
    rw [hW₀, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact hspan l
  rcases hirr W₀ hinv with h | h
  · have : (pt 0).rep ∈ W₀ := Submodule.subset_span ⟨0, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact (pt 0).rep_nonzero this
  · have h2 : W₂ = ⊤ := top_le_iff.1 (h ▸ hle₂)
    have h3 : Module.finrank F W₂ ≤ 2 :=
      (finrank_span_finset_le_card _).trans Finset.card_le_two
    rw [h2, finrank_top, hV] at h3
    omega

end CFSG.Quasithin.D35Core
