module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Orbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private lemma lk0xu7d_twistKind_eq_suN {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hnotinner : ¬ twistInner (componentRoots χ i) (fun u => ρ u))
    (hrk : compRank (componentRoots χ i) = 5)
    (hnc : (componentRoots χ i).ncard = 30)
    (horb : componentOrbitLength ρ (componentRoots χ i) = 1) :
    twistKind ρ χ i = .suN := by
  unfold twistKind
  have h1 : ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[
        componentOrbitLength ρ (componentRoots χ i)]) := by
    rw [horb, Function.iterate_one]
    simpa using hnotinner
  rw [if_neg h1]
  have h2 : ¬ ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[
            (2 * componentOrbitLength ρ (componentRoots χ i))]))) := by
    rintro (⟨h, _⟩ | ⟨h, _, _⟩) <;> omega
  rw [if_neg h2]
  have h3 : ¬ (4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)) := by
    rintro ⟨_, h⟩
    rw [hrk, hnc] at h
    omega
  rw [if_neg h3]
  have h4 : 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
    rw [hrk, hnc]
    norm_num
  rw [if_pos h4]

private lemma lk0xu7d_rootsJ_nonempty {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (h2 : 2 ≤ compRank P.rootsJ) :
    P.rootsJ.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  have hzero : compRank P.rootsJ = 0 := by
    rw [hempty]
    simp [compRank]
  omega

theorem excU7_suClass (hC1 : TwE6U7C1) (hC2 : TwE6U7C2) {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hb : P.b = 2) (h2 : 2 ≤ compRank P.rootsJ)
    (hDB : D ≤ B₁) (hBC : B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) {e : X} (he : e ∈ D)
    (he1 : e ≠ 1) {iK : KernelComponent (P.chiAt e)}
    (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK)
    (horb : componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK)) :
    ∃ S : LangSetup Tag.E6 GGL p, S.D = P.Δ ∧ S.ρ = P.ρ ∧ 2 ≤ f ∧
      ExcSuClass S (P.coord e) iK f p := by
  obtain ⟨_hΔn, _hp_dvd, hf2, hρgraph⟩ := excU7_orbit_data hp hp2 P hb
  obtain ⟨i₂, hi₂ne, hi₂roots, hrankJ, hrank2, hsub2, hdisj, hstable⟩ :=
    excU7_classes hp hp2 P hb h2 he hsub horb
  have hproper : componentRoots (P.chiAt e) iK ≠ {α | IsRoot Tag.E6 α} :=
    excU7_proper P hDB hBC he he1 iK
  have hC1res : compRank (componentRoots (P.chiAt e) iK) = 5 ∧
      (componentRoots (P.chiAt e) iK).ncard = 30 :=
    hC1 (M := (ExcOmega f)ˣ × (ExcOmega f)ˣ) (N := (ExcOmega f)ˣ)
      (χ := P.chiD) (χ' := P.chiAt e) (i₁ := P.iJ) (i₂ := i₂)
      (Ne.symm hi₂ne) hrankJ hrank2 (i' := iK) hsub
      (by rw [hi₂roots]; exact hsub2) hproper
  have hne : P.rootsJ.Nonempty := lk0xu7d_rootsJ_nonempty P h2
  have hnotinner : ¬ twistInner (componentRoots (P.chiAt e) iK) (fun u => P.ρ u) :=
    hC2 (χ := P.chiAt e) iK (ρ := P.ρ) hρgraph hsub hsub2 hne hdisj rfl hstable
  have hcard : P.Δ.q = 2 ^ f := by
    rw [P.hq, GaloisField.card 2 f (by omega : f ≠ 0)]
  have hq : 5 ≤ p ∨ 4 ≤ P.Δ.q := by
    right
    rw [hcard]
    simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hf2
  have hqpow : IsPrimePow P.Δ.q ∧ ((P.Δ.q : ℕ) : GGL) = 0 := by
    constructor
    · rw [hcard]
      exact (Nat.prime_two.isPrimePow).pow (by omega : f ≠ 0)
    · rw [hcard, Nat.cast_pow]
      have htwo : ((2 : ℕ) : GGL) = 0 :=
        (CharP.cast_eq_zero_iff GGL 2 2).mpr (by norm_num : 2 ∣ 2)
      rw [htwo, zero_pow (by omega : f ≠ 0)]
  have hpq : ¬ p ∣ P.Δ.q := by
    rw [hcard]
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) (hp.dvd_of_dvd_pow hdvd)
    have hlt : 1 < p := hp.one_lt
    omega
  refine ⟨(P.Δ.toSetup p P.ρ P.frob hp hq hqpow hpq P.finite : LangSetup Tag.E6 GGL p),
    rfl, rfl, hf2, ?_⟩
  refine ⟨P.coord_torus e he, hp, hp2, ?_, ?_, ?_, hC1res.1, horb, ?_⟩
  · have ha : (P.coord e) ^ p = 1 := by
      funext i
      rw [Pi.pow_apply, P.coord_pow e he i]
      rfl
    calc rootDiagUnit Tag.E6 (P.coord e) ^ p
        = (rootDiagUnitHom Tag.E6 GGL (P.coord e)) ^ p := rfl
      _ = rootDiagUnitHom Tag.E6 GGL ((P.coord e) ^ p) := (map_pow _ _ _).symm
      _ = 1 := by rw [ha, map_one]
  · change P.Δ.q = 2 ^ f
    exact hcard
  · exact lk0xu7d_twistKind_eq_suN P.ρ (P.chiAt e) iK hnotinner hC1res.1 hC1res.2 horb
  · exact hqs

end CFSG.StandardType.LieKnownR2.ExcPos
