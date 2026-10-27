module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StraightenTw
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

private theorem twLongest_rho_eq_smul
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5)
    (hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom .E6 Ω Fr)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    S.ρ γ = v • permLattice TwistTag.E6.perm γ := by
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  have hq : 0 < S.D.q := Nat.pos_of_ne_zero fun h => by
    have h0 := hFr 0
    rw [map_zero, h, pow_zero] at h0
    exact zero_ne_one h0
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have hstep : S.D.step = twFrob .E6 S.D.n Fr := by
    rw [LangDatum.step, hΦeq]
    rfl
  have h1 : (rootSubgroup .E6 Ω γ).map S.D.step = rootSubgroup .E6 Ω (S.ρ γ) :=
    S.frob.map_rootSubgroup γ hγ
  have h2 : (rootSubgroup .E6 Ω γ).map S.D.step =
      rootSubgroup .E6 Ω (v • permLattice TwistTag.E6.perm γ) := by
    rw [hstep, hv]
    exact map_twFrob_rootSubgroup .E6 hsurj v hγ
  have h3 : rootSubgroup .E6 Ω (S.ρ γ) =
      rootSubgroup .E6 Ω (v • permLattice TwistTag.E6.perm γ) := h1.symm.trans h2
  exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ)
    (IsRoot.smul (hγ.permLattice TwistTag.E6.cartan_perm) v) h3

private theorem twLongest_reversesSigns
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5)
    (hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom .E6 Ω Fr)
    (hs : ∀ α, S.ρ α = -α)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v) :
    ReversesSigns v := by
  intro α hα hpos
  have hγ : IsRoot Tag.E6 (permLattice TwistTag.E6.perm.symm α) :=
    IsRoot.permLattice (cartan_perm_symm TwistTag.E6.cartan_perm) hα
  have hρ := twLongest_rho_eq_smul S hΦ hv hγ
  have hσ : permLattice TwistTag.E6.perm
      (permLattice TwistTag.E6.perm.symm α) = α := permLattice_permLattice_symm _ _
  have hkey : v • α = -(permLattice TwistTag.E6.perm.symm α) := by
    have h1 : v • permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm.symm α) =
        -(permLattice TwistTag.E6.perm.symm α) := hρ.symm.trans (hs _)
    rwa [hσ] at h1
  rw [hkey, height_neg, height_permLattice]
  omega

theorem twisted_isLongest
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5)
    (hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom .E6 Ω Fr)
    (hs : ∀ α, S.ρ α = -α)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v) :
    TwE6RootKill.IsLongest v := by
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element TwistTag.E6.tag
  have hrev : ReversesSigns v := twLongest_reversesSigns S hΦ hs hv
  have hw0 : ReversesSigns w₀ := reversesSigns_of_forall_length_le hmax
  have heq : v = w₀ := hrev.eq hw0
  intro w
  rw [heq]
  exact hmax w

end CFSG.StandardType
