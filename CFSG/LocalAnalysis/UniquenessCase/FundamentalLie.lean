module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.LieType.Steinberg

@[expose] def IsFundamentalOver (q : ℕ) {X : Type} [Group X] (Kb : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), p ≠ 2 ∧ q = p ^ e ∧
    CFSG.ClassicalInvolution.Generic.IsFundTag t ∧ StatedLieAdmissible t n p e ∧
    ∃ ψ : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K →* X,
      Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).K ∧
      ∃ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
          (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).D, Kb = R.map ψ

@[expose] def fundPred (q : ℕ) : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop :=
  fun _ Kb => IsFundamentalOver q Kb

theorem isFundamentalOver_map_mulEquiv {q : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) {Kb : Subgroup X} (h : IsFundamentalOver q Kb) :
    IsFundamentalOver q (Kb.map e.toMonoidHom) := by
  obtain ⟨t, n, p, e₀, hp, hp2, hq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := h
  refine ⟨t, n, p, e₀, hp, hp2, hq, hfund, hadm, e.toMonoidHom.comp ψ,
    e.surjective.comp hsurj, ?_, R, hR, ?_⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact hker (by
      rw [MonoidHom.mem_ker]
      exact e.injective (by simpa using hx))
  · rw [Subgroup.map_map]

theorem IsFundamentalOver.ne_bot {q : ℕ} {X : Type} [Group X] {Kb : Subgroup X}
    (h : IsFundamentalOver q Kb) : Kb ≠ ⊥ := by
  obtain ⟨t, n, p, e, hp, hp2, hq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := h
  have center_of_conj_map :
      ∀ {S : Subgroup (ModelFacts.modelUniv t n p e hp).K}
        {c : (ModelFacts.modelUniv t n p e hp).K},
        S.map (MulAut.conj c).toMonoidHom ≤
            Subgroup.center (ModelFacts.modelUniv t n p e hp).K →
          S ≤ Subgroup.center (ModelFacts.modelUniv t n p e hp).K := by
    intro S c hS x hx
    have hxZ : (MulAut.conj c) x ∈
        Subgroup.center (ModelFacts.modelUniv t n p e hp).K := hS ⟨x, hx, rfl⟩
    have hZ : (Subgroup.center (ModelFacts.modelUniv t n p e hp).K).map
          (MulAut.conj c⁻¹).toMonoidHom ≤
        Subgroup.center (ModelFacts.modelUniv t n p e hp).K :=
      Subgroup.map_center_le_center (MulAut.conj c⁻¹).surjective
    have hxZ' : (MulAut.conj c⁻¹) ((MulAut.conj c) x) ∈
        Subgroup.center (ModelFacts.modelUniv t n p e hp).K :=
      hZ ⟨_, hxZ, rfl⟩
    have hconj : (MulAut.conj c⁻¹) ((MulAut.conj c) x) = x := by
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    rwa [hconj] at hxZ'
  have root_not_center :
      ∀ {γ : Fin (ModelFacts.modelUniv t n p e hp).D.rank → ℤ},
        γ ∈ (ModelFacts.modelUniv t n p e hp).D.roots →
          ¬ (ModelFacts.modelUniv t n p e hp).D.rootGroup γ ≤
            Subgroup.center (ModelFacts.modelUniv t n p e hp).K := by
    obtain ⟨_, _, hct, hext⟩ :=
      ModelFacts.hasBruhatDatum t n p e hp hfund hadm
    intro γ hγ hle
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · have hsingle : (Pi.single i 1 : Fin (ModelFacts.modelUniv t n p e hp).D.rank → ℤ) ∈
          (ModelFacts.modelUniv t n p e hp).D.roots := Or.inl ⟨1, i, by simp⟩
      have hmap : (ModelFacts.modelUniv t n p e hp).D.rootGroup (Pi.single i 1) ≤
          Subgroup.center (ModelFacts.modelUniv t n p e hp).K := by
        apply center_of_conj_map
          (S := (ModelFacts.modelUniv t n p e hp).D.rootGroup (Pi.single i 1))
          (c := nrep hct w)
        rw [(actsAs_nrep hct w) (Pi.single i 1) hsingle]
        exact hle
      obtain ⟨x, hx1⟩ :=
        (Subgroup.ne_bot_iff_exists_ne_one).1 (hext.ne_bot _ hsingle)
      have hxZ : (x : (ModelFacts.modelUniv t n p e hp).K) ∈
          Subgroup.center (ModelFacts.modelUniv t n p e hp).K := hmap x.2
      have hnorm : (x : (ModelFacts.modelUniv t n p e hp).K) ∈
          Subgroup.normalizer
            ((ModelFacts.modelUniv t n p e hp).D.rootGroup (-Pi.single i 1) :
              Set (ModelFacts.modelUniv t n p e hp).K) :=
        Subgroup.center_le_normalizer _ hxZ
      exact hx1 (Subtype.ext
        (hext.eq_one_of_mem_normalizer i (x : (ModelFacts.modelUniv t n p e hp).K) x.2 hnorm))
    · have hsingle : (Pi.single i 1 : Fin (ModelFacts.modelUniv t n p e hp).D.rank → ℤ) ∈
          (ModelFacts.modelUniv t n p e hp).D.roots := Or.inl ⟨1, i, by simp⟩
      have hdouble : (2 • Pi.single i 1 :
          Fin (ModelFacts.modelUniv t n p e hp).D.rank → ℤ) ∈
          (ModelFacts.modelUniv t n p e hp).D.roots := Or.inr ⟨1, i, hi, by simp⟩
      have hmap : (ModelFacts.modelUniv t n p e hp).D.rootGroup (2 • Pi.single i 1) ≤
          Subgroup.center (ModelFacts.modelUniv t n p e hp).K := by
        apply center_of_conj_map
          (S := (ModelFacts.modelUniv t n p e hp).D.rootGroup (2 • Pi.single i 1))
          (c := nrep hct w)
        rw [(actsAs_nrep hct w) (2 • Pi.single i 1) hdouble, map_nsmul]
        exact hle
      obtain ⟨x, hx1⟩ :=
        (Subgroup.ne_bot_iff_exists_ne_one).1 (hext.ne_bot _ hdouble)
      have hxZ : (x : (ModelFacts.modelUniv t n p e hp).K) ∈
          Subgroup.center (ModelFacts.modelUniv t n p e hp).K := hmap x.2
      have hxs : (x : (ModelFacts.modelUniv t n p e hp).K) ∈
          (ModelFacts.modelUniv t n p e hp).D.rootGroup (Pi.single i 1) :=
        hext.two_smul_le (Pi.single i 1) hsingle hdouble x.2
      have hnorm : (x : (ModelFacts.modelUniv t n p e hp).K) ∈
          Subgroup.normalizer
            ((ModelFacts.modelUniv t n p e hp).D.rootGroup (-Pi.single i 1) :
              Set (ModelFacts.modelUniv t n p e hp).K) :=
        Subgroup.center_le_normalizer _ hxZ
      exact hx1 (Subtype.ext
        (hext.eq_one_of_mem_normalizer i (x : (ModelFacts.modelUniv t n p e hp).K) hxs hnorm))
  have hRnotcenter : ¬ R ≤ Subgroup.center (ModelFacts.modelUniv t n p e hp).K := by
    intro hRc
    obtain ⟨g, γ, hγ, rfl⟩ := ModelFacts.mem_roots_of_mem_fundamentalSubgroups hR
    exact root_not_center hγ (le_trans le_sup_left (center_of_conj_map hRc))
  intro hbot
  have hleker : R ≤ ψ.ker := (Subgroup.map_eq_bot_iff R).mp hbot
  exact hRnotcenter (hleker.trans hker)

end CFSG.LocalAnalysis.UniquenessCase
