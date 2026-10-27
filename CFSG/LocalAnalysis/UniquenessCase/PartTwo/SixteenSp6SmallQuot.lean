module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallRep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.SmithCurtis CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem s16sm_quot_nontrivial [Finite M] [Nontrivial M] (ρ : Representation (ZMod 2) G6 M)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0) :
    Nontrivial (M ⧸ ρ.invariants) := by
  rw [Submodule.Quotient.nontrivial_iff]
  intro htop
  obtain ⟨z, hz⟩ := exists_ne (0 : M)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  have hzero : ψ = 0 := hperf ψ fun g m => by
    have hm : m ∈ ρ.invariants := by rw [htop]; exact Submodule.mem_top
    rw [(Representation.mem_invariants ρ m).mp hm g]
  have h1 : ψ z = 0 := by rw [hzero, LinearMap.zero_apply]
  rw [hψ] at h1
  exact one_ne_zero h1

theorem s16sm_quot_no_invariant_functional (ρ : Representation (ZMod 2) G6 M)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0)
    (φ : (M ⧸ ρ.invariants) →ₗ[ZMod 2] ZMod 2) (hφ : ∀ g s, φ (s16smQ ρ g s) = φ s) : φ = 0 := by
  have hcomp : φ.comp (Submodule.mkQ ρ.invariants) = 0 := by
    apply hperf
    intro g m
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← s16smQ_mk]
    exact hφ g _
  apply LinearMap.ext
  intro s
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective ρ.invariants s
  have h := congrArg (fun f : M →ₗ[ZMod 2] ZMod 2 => f m) hcomp
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

theorem s16sm_exists_invariant_functional {S : Type} [AddCommGroup S] [Module (ZMod 2) S]
    [Finite S] (ρ : Representation (ZMod 2) G6 S) (T : Submodule (ZMod 2) S)
    (hT : ∀ g, T ≤ T.comap (ρ g)) (hfin : Module.finrank (ZMod 2) (S ⧸ T) ≤ 5) (hne : T ≠ ⊤) :
    ∃ φ : S →ₗ[ZMod 2] ZMod 2, φ ≠ 0 ∧ ∀ g s, φ (ρ g s) = φ s := by
  haveI : Finite (S ⧸ T) :=
    Finite.of_surjective (Submodule.mkQ T) (Submodule.mkQ_surjective T)
  let ρQ : Representation (ZMod 2) G6 (S ⧸ T) := ρ.quotient T hT
  have htriv : ∀ (g : G6) (v : S ⧸ T), ρQ g v = v :=
    s16sm_trivial_of_finrank_le_five ρQ hfin
  have hquot : ∀ (g : G6) (x : S), ρQ g (T.mkQ x) = T.mkQ (ρ g x) := by
    intro g x
    change (Submodule.mapQ T T (ρ g) (hT g)) (T.mkQ x) = T.mkQ (ρ g x)
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  haveI : Nontrivial (S ⧸ T) := Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨v, hv⟩ := exists_ne (0 : S ⧸ T)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  refine ⟨l.comp (Submodule.mkQ T), ?_, ?_⟩
  · intro hzero
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective T v
    have h0 : l (T.mkQ x) = 0 := by
      have := congrArg (fun f : S →ₗ[ZMod 2] ZMod 2 => f x) hzero
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using this
    rw [hx, hl] at h0
    exact one_ne_zero h0
  · intro g s
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hquot g s, htriv g]

theorem s16sm_sub_nontrivial_action (ρ : Representation (ZMod 2) G6 M)
    (T : Submodule (ZMod 2) (M ⧸ ρ.invariants))
    (hT : ∀ g, T ≤ T.comap (s16smQ ρ g)) (hne : T ≠ ⊥) :
    ∃ (g : G6) (t : T), (((s16smQ ρ).subrepresentation T hT) g) t ≠ t := by
  by_contra h
  have hfix : ∀ (g : G6) (t : T), (((s16smQ ρ).subrepresentation T hT) g) t = t := by
    intro g t
    by_contra hg
    exact h ⟨g, t, hg⟩
  have hcoe : ∀ (g : G6) (t : T),
      ((((s16smQ ρ).subrepresentation T hT) g) t : M ⧸ ρ.invariants) = s16smQ ρ g t := by
    intro g t
    rw [Representation.subrepresentation_apply]
    exact LinearMap.coe_restrict_apply _ t
  have hTbot : T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro t ht
    have hfixed : ∀ g : G6, s16smQ ρ g t = t := by
      intro g
      have hval := congrArg Subtype.val (hfix g ⟨t, ht⟩)
      rw [hcoe g ⟨t, ht⟩] at hval
      simpa using hval
    exact s16sm_fixed_quot ρ t hfixed
  exact hne hTbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
