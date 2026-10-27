module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux1
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
import CFSG.LocalAnalysis.StandardType.GGLieOddCoverSplit
import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
import CFSG.LocalAnalysis.StandardType.GGExcKGSFFinite

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_tw_torus_fixed
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    {w' : WeylGroup Tag.E6}
    (hw' : ∀ γ ∈ rootsOfFam β Set.univ,
      w' • permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ) = ι (S.ρ γ))
    {h : ℕ} (hσ : ∀ c, ggFrobT h c = c ^ S.D.q)
    {b : ModGL τ GGL} (hb : b ∈ S.D.torus) :
    canonicalRep (coxeterSystem Tag.E6) GGL w' *
      (show ModGL Tag.E6 GGL from twistHom TwistTag.E6 GGL (ggFrobT h)
        (rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)))) *
      (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ =
    rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) := by
  classical
  have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
  have hb' : rootDiagUnit τ (rckTorusCoord b) = b := rck_rootDiagUnit_coord hbT
  have hbS : rootDiagUnit τ (rckTorusCoord b) ∈ S.D.torus := by rw [hb']; exact hb
  set c : Fin Tag.E6.rank → GGLˣ := fun k => rckRootVal b (β k) with hc
  have hΦ : (show ModGL Tag.E6 GGL from twistHom TwistTag.E6 GGL (ggFrobT h)
      (rootDiagUnit Tag.E6 c)) =
      rootDiagUnit Tag.E6 (fun i => Units.map (ggFrobT h).toMonoidHom
        (c (TwistTag.E6.perm.symm i))) :=
    twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := ggFrobT h) c
  rw [hΦ]
  refine Eq.symm ((rootDiagUnit_eq_conj_canonicalRep_iff c _ w').2 ?_)
  refine rootChar_smul_eq_rootChar_of_forall_isRoot fun α hα => ?_
  have hα' : IsRoot Tag.E6 (permLattice (τ := Tag.E6) TwistTag.E6.perm.symm α) :=
    hα.permLattice (cartan_perm_symm TwistTag.E6.cartan_perm)
  obtain ⟨γ, hγ, hιγ⟩ := hι.1.surjOn hα'
  have hpp : permLattice (τ := Tag.E6) TwistTag.E6.perm
      (permLattice (τ := Tag.E6) TwistTag.E6.perm.symm α) = α := by
    ext j
    exact congrArg α (Equiv.symm_apply_apply TwistTag.E6.perm.symm j)
  have hpp' : permLattice (τ := Tag.E6) TwistTag.E6.perm.symm
      (permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ)) = ι γ := by
    ext j
    exact congrArg (ι γ) (Equiv.symm_apply_apply TwistTag.E6.perm j)
  have hαι : α = permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ) := by
    rw [hιγ, hpp]
  have hval : ∀ δ ∈ rootsOfFam β Set.univ,
      rootChar c (ι δ) = rootChar (rckTorusCoord b) δ := by
    intro δ hδ
    have h1 := rckRet_torus_val hι hbT δ hδ
    unfold rckRootVal at h1
    rw [rck_coord_rootDiagUnit] at h1
    exact h1
  have hroot : IsRoot τ γ := hγ.1
  have h2 := S.frob.rootChar_eq (rckTorusCoord b) hbS γ hroot
  have hnat : ∀ v : Fin Tag.E6.rank → ℤ,
      rootChar (fun i => Units.map (ggFrobT h).toMonoidHom (c (TwistTag.E6.perm.symm i))) v =
        Units.map (ggFrobT h).toMonoidHom
          (rootChar c (permLattice (τ := Tag.E6) TwistTag.E6.perm.symm v)) := by
    intro v
    simp only [rootChar, map_prod, map_zpow]
    refine (Fintype.prod_equiv TwistTag.E6.perm _ _ (fun j => ?_)).symm
    simp only [Equiv.symm_apply_apply]
    rfl
  have hpow : ∀ u : GGLˣ, Units.map (ggFrobT h).toMonoidHom u = u ^ S.D.q := by
    intro u
    apply Units.ext
    simp [hσ]
  rw [hαι, hw' γ hγ, hval _ (hρΨ γ hγ), h2]
  refine Eq.trans ?_ (hnat (permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ))).symm
  rw [hpp', hval _ hγ, hpow]

theorem rckRet_tw_SKcent
    {h : ℕ} (hh : 0 < h) {p₁ : ℕ} (SK : LangSetup Tag.E6 GGL p₁)
    (hSKΦ : SK.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) :
    ∀ y ∈ SK.Γ, (∀ u ∈ SK.Γ, y * u = u * y) → y = 1 := by
  classical
  have hPkg := rckTw6_langPkg SK h hh hSKΦ
  have hΓ : SK.Γ = (show Subgroup (ModGL Tag.E6 GGL) from (rckTw6_iota h).range).map
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom := rckTw6_Gamma SK h hSKΦ hPkg
  intro y hy hc
  rw [hΓ] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hadj : y₀ ∈ adjointGroup TwistTag.E6.tag GGL :=
    ((LangDatum.mem_fix SK.D).1 (hPkg.desc.range_le hy₀)).1
  have hy₁ : y₀ = 1 := by
    refine hPkg.cent_triv y₀ hadj fun x => ?_
    let ιx : ModGL Tag.E6 GGL := rckTw6_iota h x
    have hu : (MulAut.conj SK.D.g0⁻¹).toMonoidHom ιx ∈ SK.Γ := by
      rw [hΓ]
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    have h1 := hc _ hu
    have h1' : (SK.D.g0⁻¹ * y₀ * SK.D.g0⁻¹⁻¹) * (SK.D.g0⁻¹ * ιx * SK.D.g0⁻¹⁻¹) =
        (SK.D.g0⁻¹ * ιx * SK.D.g0⁻¹⁻¹) * (SK.D.g0⁻¹ * y₀ * SK.D.g0⁻¹⁻¹) := h1
    have h2 : SK.D.g0⁻¹ * (y₀ * ιx) * SK.D.g0⁻¹⁻¹ =
        SK.D.g0⁻¹ * (ιx * y₀) * SK.D.g0⁻¹⁻¹ := by
      calc SK.D.g0⁻¹ * (y₀ * ιx) * SK.D.g0⁻¹⁻¹
          = (SK.D.g0⁻¹ * y₀ * SK.D.g0⁻¹⁻¹) * (SK.D.g0⁻¹ * ιx * SK.D.g0⁻¹⁻¹) := by group
        _ = (SK.D.g0⁻¹ * ιx * SK.D.g0⁻¹⁻¹) * (SK.D.g0⁻¹ * y₀ * SK.D.g0⁻¹⁻¹) := h1'
        _ = SK.D.g0⁻¹ * (ιx * y₀) * SK.D.g0⁻¹⁻¹ := by group
    have h3 : y₀ * ιx = ιx * y₀ := mul_left_cancel (mul_right_cancel h2)
    exact h3
  rw [hy₁, map_one]

theorem rckRet_tw_center_odd
    {h : ℕ} (hh : 0 < h) {X : Type} [Group X] {R : Subgroup X}
    (φ : twistedE6Group 2 h →* ↥R) (hφsurj : Function.Surjective φ)
    (hφker : φ.ker ≤ Subgroup.center (twistedE6Group 2 h)) :
    ∀ x ∈ Subgroup.center ↥R, Odd (orderOf x) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hφsurj x
  have hy : y ∈ Subgroup.center (twistedE6Group 2 h) :=
    rckA4_preimage_center φ (CFSG.StandardType.MpStdTwE6.commutator_twistedE6Group hh) hφker hx
  have h3 : y ^ 3 = 1 := CFSG.StandardType.TwE6Nonsplit.center_pow_three h hh hy
  have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  exact Odd.of_dvd_nat (by decide) ((orderOf_map_dvd φ y).trans h1)

theorem rckRet_tw_modelFacts
    {h : ℕ} (hh : 0 < h) :
    Finite (ggU .twistedE6 0 h).K ∧ Group.IsPerfect (ggU .twistedE6 0 h).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .twistedE6 0 h).K ∧
      StandardReturnAt (ggU .twistedE6 0 h) h ∧ RCKADEModel (ggU .twistedE6 0 h) h := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .twistedE6 0 2 h := ⟨Nat.prime_two, hh, rfl⟩
  have hrk : 2 ≤ (ggU .twistedE6 0 h).D.rank := by
    change 2 ≤ Tag.rank .F4
    decide
  refine ⟨ggU_finite_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ⟨hadm, hrk⟩, ?_, ?_, ?_, ?_⟩
  · exact Group.isPerfect_def.2 (CFSG.StandardType.MpStdTwE6.commutator_twistedE6Group hh)
  · exact CFSG.StandardType.LieOddCover.oddCentralSplit_ggU_pos (t := .twistedE6) (n := 0)
      (f := h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr rfl))))))))) hadm
  · exact Or.inl ⟨.twistedE6, 0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr rfl)))))))), hadm, rfl⟩
  · exact Or.inl ⟨.twistedE6, 0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
      hadm, rfl⟩

theorem rckRet_tw_longRoot
    (h : ℕ) :
    (Pi.single (0 : Fin 4) 1 : Fin (ggU .twistedE6 0 h).D.rank → ℤ) ∈
        (ggU .twistedE6 0 h).D.roots ∧
      GGLongRoot (ggU .twistedE6 0 h).D (Pi.single (0 : Fin 4) 1) := by
  refine ⟨(mem_roots_twistedE6 0 h _).2 (mem_rootFinset.2 (IsRoot.basis _)), ?_⟩
  exact (CFSG.StandardType.LieKnownR2.Short.f4_ggLongRoot_single_iff (GaloisField 2 1)
    ⟨0, by change 0 < Tag.rank .F4; decide⟩).2 (Nat.zero_le _)

end CFSG.StandardType.RCKRP

end
