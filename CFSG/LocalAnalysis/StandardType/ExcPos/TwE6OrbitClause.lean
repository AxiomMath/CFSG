module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelPi
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus


private theorem lk0xttorb_permCongr_one {R N : ℕ} (h : R = N) :
    (finCongr h).permCongr (1 : Equiv.Perm (Fin R)) = (1 : Equiv.Perm (Fin N)) := by
  subst h
  rfl

private theorem lk0xttorb_permLattice_one {τ : Tag} (u : Fin τ.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin τ.rank)) u = u :=
  rfl

private theorem lk0xttorb_permLattice_permCongr_one {τ : Tag} {R : ℕ}
    (h : R = τ.rank) (u : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) u = u := by
  rw [lk0xttorb_permCongr_one h, lk0xttorb_permLattice_one]

private theorem lk0xttorb_permCongr_apply_eq (f : ℕ)
    (h : (ggU (absTag .twistedE6) 6 f).D.rank = (langTag .twistedE6).rank)
    (π : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 f).D.rank))
    (i : Fin (langTag .twistedE6).rank) :
    ((finCongr h).permCongr π) i = π i := by
  rw [Equiv.permCongr_apply]
  have hs : (finCongr h).symm i = i := Fin.ext (finCongr_symm_apply_coe h i)
  rw [hs]
  exact Fin.ext (finCongr_apply_coe h (π i))

private theorem lk0xttorb_permLattice_permCongr_general (f : ℕ)
    (h : (ggU (absTag .twistedE6) 6 f).D.rank = (langTag .twistedE6).rank)
    (π : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 f).D.rank))
    (u : Fin (langTag .twistedE6).rank → ℤ) :
    permLattice (τ := langTag .twistedE6) ((finCongr h).permCongr π) u
      = permLattice (τ := langTag .twistedE6) π u := by
  have h1 : (finCongr h).permCongr π = π :=
    Equiv.ext (lk0xttorb_permCongr_apply_eq f h π)
  rw [h1]

private theorem lk0xttorb_isRoot_ggGraphLat {v : Fin (langTag .twistedE6).rank → ℤ}
    (hv : IsRoot (langTag .twistedE6) v) :
    IsRoot (langTag .twistedE6) (ggGraphLat .twistedE6 v) :=
  IsRoot.permLattice (TwistTag.cartan_perm .E6) hv

private theorem lk0xttorb_ggGraphLat_invol (u : Fin (langTag .twistedE6).rank → ℤ) :
    ggGraphLat .twistedE6 (ggGraphLat .twistedE6 u) = u := by
  show permLattice (TwistTag.perm .E6) (permLattice (TwistTag.perm .E6) u) = u
  ext j
  fin_cases j <;> rfl

theorem twE6_orbitLength_clause {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) (ht : GGExcFive .twistedE6)
    {w : WeylGroup (langTag .twistedE6)} (hw : GGWeylLaw .twistedE6 p f ht w)
    {ρ : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ)}
    (hρ : ∀ γ, IsRoot (langTag .twistedE6) γ → ρ γ = w • ggGraphLat .twistedE6 γ)
    (χ : Multiplicative (Fin (langTag .twistedE6).rank → ℤ) →* GGLˣ × GGLˣ)
    (i : KernelComponent χ) :
    componentOrbitLength ρ (componentRoots χ i) = 1 ∨
      (componentOrbitLength ρ (componentRoots χ i) = 2 ∧ p ∣ 2 ^ f - 1 ∧ w = 1) := by
  have hcomp : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  by_cases hp1 : p ∣ 2 ^ f + 1
  ·
    have he : eps p f = -1 := (eps_eq_neg_one_iff hp hp2 f hreg).2 hp1
    have hpi : piB .twistedE6 p f = 1 := piB_twistedE6_of_dvd f hp1
    have hρneg : ∀ γ, IsRoot (langTag .twistedE6) γ → ρ γ = -γ := by
      intro γ hγ
      rw [hρ γ hγ]
      have h := hw γ
      rw [he, hpi, lk0xttorb_permLattice_permCongr_one (rank_eq_langTag f ht),
        neg_one_smul] at h
      exact h
    have hstable : ρ '' componentRoots χ i = componentRoots χ i := by
      apply Set.Subset.antisymm
      · rintro x ⟨γ, hγ, rfl⟩
        rw [hρneg γ (hcomp.isRoot γ hγ)]
        exact hcomp.neg_mem γ hγ
      · intro y hy
        refine ⟨-y, hcomp.neg_mem y hy, ?_⟩
        rw [hρneg (-y) (hcomp.isRoot (-y) (hcomp.neg_mem y hy))]
        simp
    have h1mem : (1 : ℕ) ∈
        {s : ℕ | 0 < s ∧ ρ^[s] '' componentRoots χ i = componentRoots χ i} := by
      refine ⟨by norm_num, ?_⟩
      rw [Function.iterate_one]
      exact hstable
    have hne : ({s : ℕ | 0 < s ∧ ρ^[s] '' componentRoots χ i = componentRoots χ i} :
        Set ℕ).Nonempty := ⟨1, h1mem⟩
    have hle : componentOrbitLength ρ (componentRoots χ i) ≤ 1 := Nat.sInf_le h1mem
    have hge : 1 ≤ componentOrbitLength ρ (componentRoots χ i) :=
      Nat.succ_le_of_lt (Nat.sInf_mem hne).1
    exact Or.inl (le_antisymm hle hge)
  ·
    have h1 : p ∣ 2 ^ f - 1 := hreg.resolve_right hp1
    have he : eps p f = 1 := (eps_eq_one_iff p f).2 h1
    have hpi : piB .twistedE6 p f = TwistTag.perm .E6 := piB_twistedE6_of_not_dvd f hp1
    have hw' : ∀ u : Fin (langTag .twistedE6).rank → ℤ,
        w • ggGraphLat .twistedE6 u = ggGraphLat .twistedE6 u := by
      intro u
      have h := hw u
      rw [he] at h
      rw [lk0xttorb_permLattice_permCongr_general f (rank_eq_langTag f ht)
        (piB .twistedE6 p f) u] at h
      have hpid : permLattice (τ := langTag .twistedE6) (piB .twistedE6 p f) u
          = ggGraphLat .twistedE6 u := by
        rw [hpi]
        rfl
      rw [hpid] at h
      simpa using h
    have hfix : ∀ v : Fin (langTag .twistedE6).rank → ℤ, w • v = v := by
      intro v
      have h2 : ggGraphLat .twistedE6 (ggGraphLat .twistedE6 v) = v :=
        lk0xttorb_ggGraphLat_invol v
      rw [← h2, hw' (ggGraphLat .twistedE6 v)]
    have hw1 : w = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (fun v => by rw [hfix v, one_smul])
    have hρfix : ∀ γ, IsRoot (langTag .twistedE6) γ → ρ γ = ggGraphLat .twistedE6 γ := by
      intro γ hγ
      rw [hρ γ hγ, hw1, one_smul]
    have hsq : ∀ γ ∈ componentRoots χ i, ρ^[2] γ = γ := by
      intro γ hγ
      have hroot : IsRoot (langTag .twistedE6) γ := hcomp.isRoot γ hγ
      have hroot' : IsRoot (langTag .twistedE6) (ggGraphLat .twistedE6 γ) :=
        lk0xttorb_isRoot_ggGraphLat hroot
      change ρ (ρ γ) = γ
      rw [hρfix γ hroot, hρfix (ggGraphLat .twistedE6 γ) hroot',
        lk0xttorb_ggGraphLat_invol γ]
    have h2mem : (2 : ℕ) ∈
        {s : ℕ | 0 < s ∧ ρ^[s] '' componentRoots χ i = componentRoots χ i} := by
      refine ⟨by norm_num, ?_⟩
      apply Set.Subset.antisymm
      · rintro x ⟨γ, hγ, rfl⟩
        rw [hsq γ hγ]
        exact hγ
      · intro x hx
        exact ⟨x, hx, by rw [hsq x hx]⟩
    have hne : ({s : ℕ | 0 < s ∧ ρ^[s] '' componentRoots χ i = componentRoots χ i} :
        Set ℕ).Nonempty := ⟨2, h2mem⟩
    have hle : componentOrbitLength ρ (componentRoots χ i) ≤ 2 := Nat.sInf_le h2mem
    have hge : 1 ≤ componentOrbitLength ρ (componentRoots χ i) :=
      Nat.succ_le_of_lt (Nat.sInf_mem hne).1
    by_cases hcase : componentOrbitLength ρ (componentRoots χ i) = 1
    · exact Or.inl hcase
    · exact Or.inr ⟨by omega, h1, hw1⟩

end CFSG.StandardType.LieKnownR2.ExcPos
