module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
public import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem lk0xu7a_ggPhi_map_rootSubgroup_twistedE6 {f : ℕ}
    {γ : Fin (langTag .twistedE6).rank → ℤ} (hγ : IsRoot (langTag .twistedE6) γ) :
    (rootSubgroup (langTag .twistedE6) GGL γ).map (ggPhi .twistedE6 f) =
      rootSubgroup (langTag .twistedE6) GGL (ggGraphLat .twistedE6 γ) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)
      (α := γ)).1 hy
    refine (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)
      (α := ggGraphLat .twistedE6 γ)).2 ⟨c ^ 2 ^ f, ?_⟩
    exact (ggPhi_pinnedX_twistedE6 f hγ c).symm
  · intro hx
    obtain ⟨e, rfl⟩ := (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)
      (α := ggGraphLat .twistedE6 γ)).1 hx
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := GGL) e (n := 2 ^ f)
      (pow_pos (by norm_num) f)
    refine Subgroup.mem_map.2 ⟨pinnedX (langTag .twistedE6) GGL γ c,
      (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL) (α := γ)).2 ⟨c, rfl⟩, ?_⟩
    rw [← hc]
    exact ggPhi_pinnedX_twistedE6 f hγ c

private theorem lk0xu7a_image_eq_of_componentOrbitLength_eq_one {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : componentOrbitLength ρ Ψ = 1) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ := by
  let S : Set ℕ := {s : ℕ | 0 < s ∧
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ}
  have hS : componentOrbitLength ρ Ψ = sInf S := rfl
  have hne : S.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [hS, hc] at h
  have hmem := Nat.sInf_mem hne
  rw [← hS, h] at hmem
  simpa [S] using hmem.2

theorem excU7_orbit_data {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    {R Rm : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hb : P.b = 2) :
    P.Δ.n = 1 ∧ p ∣ 2 ^ f - 1 ∧ 2 ≤ f ∧
      ∀ γ, IsRoot Tag.E6 γ → P.ρ γ = permLattice (TwistTag.perm .E6) γ := by
  rcases P.orbit with h1 | ⟨h2, hdiag, hpq, hn⟩
  · have hb1 : P.b = 1 := by
      simpa [ExcPacket.b, ExcPacket.rootsJ, ExcPacket.chiD] using h1
    omega
  · have hqcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp P.one_le_f)
    have hpq' : p ∣ 2 ^ f - 1 := by
      rwa [hqcard] at hpq
    have hf2 : 2 ≤ f := by
      by_contra hcon
      have hf1 : f = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)) P.one_le_f
      have hdvd : p ∣ 1 := by simpa [hf1] using hpq'
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
      have hp2' : 2 ≤ p := hp.two_le
      omega
    obtain ⟨h, hdiag⟩ := hdiag
    have hFr : P.Fr = ggFrobT f := by
      ext c
      rw [P.hFr c, ggFrobT_apply f c, GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp P.one_le_f)]
    have hdiag' : P.diag = diagramAt (langTag .twistedE6) GGL TwistTag.E6 rfl := by
      rw [hdiag]
      exact congrArg (fun hh : TwistTag.E6.tag = Tag.E6 =>
        diagramAt Tag.E6 GGL TwistTag.E6 hh) (Subsingleton.elim h rfl)
    have hΦeq : P.Δ.Φ = ggPhi .twistedE6 f := by
      ext g
      rw [P.hΦ g, hdiag', hFr]
      rfl
    have hn1 : P.Δ.n = 1 := hn
    have hstep_eq : P.Δ.step = P.Δ.Φ := by
      ext g
      simp [LangDatum.step, hn1]
    refine ⟨hn, hpq', hf2, ?_⟩
    intro γ hγ
    have hρmap : (rootSubgroup (langTag .twistedE6) GGL γ).map P.Δ.step =
        rootSubgroup (langTag .twistedE6) GGL (P.ρ γ) :=
      P.frob.map_rootSubgroup γ hγ
    have hmap : (rootSubgroup (langTag .twistedE6) GGL γ).map P.Δ.step =
        rootSubgroup (langTag .twistedE6) GGL (permLattice (TwistTag.perm .E6) γ) := by
      rw [hstep_eq, hΦeq]
      exact lk0xu7a_ggPhi_map_rootSubgroup_twistedE6 (f := f) hγ
    exact rootSubgroup_injective_of_isRoot ((P.frob.isRoot_iff γ).2 hγ)
      (IsRoot.permLattice (TwistTag.cartan_perm .E6) hγ) (hρmap.symm.trans hmap)

theorem excU7_classes {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    {R Rm : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hb : P.b = 2) (h2 : 2 ≤ compRank P.rootsJ)
    {e : X} (he : e ∈ D) {iK : KernelComponent (P.chiAt e)}
    (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK)
    (horb : componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1) :
    ∃ i₂ : KernelComponent P.chiD, i₂ ≠ P.iJ ∧
      componentRoots P.chiD i₂ = (fun u => P.ρ u) '' P.rootsJ ∧
      compRank P.rootsJ = 2 ∧ compRank (componentRoots P.chiD i₂) = 2 ∧
      (fun u => P.ρ u) '' P.rootsJ ⊆ componentRoots (P.chiAt e) iK ∧
      Disjoint P.rootsJ ((fun u => P.ρ u) '' P.rootsJ) ∧
      (fun u => P.ρ u) '' componentRoots (P.chiAt e) iK = componentRoots (P.chiAt e) iK := by
  obtain ⟨i₂, hi₂⟩ := exists_image_componentRoots (χ := P.chiD) P.mapsTo_rho_chiD
    P.frob.iform_eq P.iJ
  have hi₂' : componentRoots P.chiD i₂ = (fun u => P.ρ u) '' P.rootsJ := by
    simpa [ExcPacket.rootsJ] using hi₂.symm
  have hne : i₂ ≠ P.iJ := by
    intro h
    refine P.image_rootsJ_ne_of_b_eq_two hb ?_
    simpa [ExcPacket.rootsJ] using hi₂.trans (congrArg (componentRoots P.chiD) h)
  have hcard : (componentRoots P.chiD P.iJ).ncard = (componentRoots P.chiD i₂).ncard := by
    rw [← hi₂, Set.ncard_image_of_injective _ P.ρ.injective]
  obtain ⟨hrJ, -, hrI₂, -⟩ := twE6_twoOrbit_is_A2_pair rfl P.chiD hne.symm h2 hcard
  have hstable : (fun u => P.ρ u) '' componentRoots (P.chiAt e) iK =
      componentRoots (P.chiAt e) iK :=
    lk0xu7a_image_eq_of_componentOrbitLength_eq_one horb
  have hsub₂ : (fun u => P.ρ u) '' P.rootsJ ⊆ componentRoots (P.chiAt e) iK := by
    rw [← hstable]
    exact Set.image_mono hsub
  have hdisj : Disjoint P.rootsJ ((fun u => P.ρ u) '' P.rootsJ) := by
    rw [Set.disjoint_left]
    intro α hα hα'
    exact hne (eq_of_mem_componentRoots hα (by rwa [← hi₂'] at hα')).symm
  exact ⟨i₂, hne, hi₂', hrJ, hrI₂, hsub₂, hdisj, hstable⟩

theorem excU7_proper {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    {R Rm : Subgroup X} (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hDB : D ≤ B₁)
    (hBC : B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) {e : X} (he : e ∈ D) (he1 : e ≠ 1)
    (iK : KernelComponent (P.chiAt e)) :
    componentRoots (P.chiAt e) iK ≠ {α | IsRoot Tag.E6 α} := by
  intro hAll
  have hker : ∀ γ, IsRoot Tag.E6 γ → P.chiAt e (Multiplicative.ofAdd γ) = 1 := by
    intro γ hγ
    have hmem : γ ∈ componentRoots (P.chiAt e) iK := by rw [hAll]; exact hγ
    simp only [componentRoots, Set.mem_setOf_eq] at hmem
    obtain ⟨hk, -⟩ := hmem
    exact hk.2
  have hcoord : P.coord e = 1 := by
    funext i
    have h1 : rootChar (P.coord e) (Pi.single i 1) = 1 := by
      have := hker (Pi.single i 1) (isRoot_single Tag.E6 i)
      simpa [ExcPacket.chiAt, CFSG.LieType.AlgebraicGroups.rootCharHom] using this
    rw [rootChar_single] at h1
    exact h1
  have hdiag : rootDiagUnit Tag.E6 (P.coord e) = 1 := by
    rw [hcoord]
    exact rootDiagUnit_one
  have hΘ : P.Θ ⟨e, hDB he⟩ = 1 := by
    rw [P.Θ_eq_coord ⟨e, hDB he⟩ he, hdiag]
  have hcent : e ∈ Subgroup.centralizer (G₀ : Set X) :=
    (P.Θ_eq_one ⟨e, hDB he⟩).1 hΘ
  have hbot : e ∈ (⊥ : Subgroup X) := by
    have hmem : e ∈ B₁ ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hDB he, hcent⟩
    rwa [hBC] at hmem
  exact he1 (Subgroup.mem_bot.1 hbot)

end CFSG.StandardType.LieKnownR2.ExcPos
