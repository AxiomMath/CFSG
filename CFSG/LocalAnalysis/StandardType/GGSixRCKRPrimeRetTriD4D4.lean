module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriD4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.StandardType.F4ExplicitPos.CommonFactor

theorem twistInner_iterate_two {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hσ : Set.MapsTo σ Ψ Ψ) (h : twistInner Ψ σ) :
    twistInner Ψ (σ^[2]) := by
  obtain ⟨w, hw, hwγ⟩ := h
  refine ⟨w * w, mul_mem hw hw, fun γ hγ => ?_⟩
  calc σ (σ γ) = w • (σ γ) := hwγ (σ γ) (hσ hγ)
    _ = w • (w • γ) := by rw [hwγ γ hγ]
    _ = (w * w) • γ := (mul_smul w w γ).symm

theorem twistKind_eq_exc_of_triD4Shape
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4)
    (h24 : (componentRoots (rootCharHom a) i).ncard = 24)
    (hni2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    twistKind S.ρ (rootCharHom a) i = .exc := by
  classical
  obtain ⟨N, hN, hid⟩ := CFSG.StandardType.TableCRes.exists_iterate_rho_eq_id S
  have hne : ({s : ℕ | 0 < s ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i}).Nonempty := by
    refine ⟨N, hN, ?_⟩
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      rw [hid δ (isRoot_of_mem_componentRoots hδ)]
      exact hδ
    · intro hγ
      exact ⟨γ, hγ, hid γ (isRoot_of_mem_componentRoots hγ)⟩
  let s : ℕ := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  have hmem : 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i :=
    Nat.sInf_mem hne
  obtain ⟨-, himage⟩ := hmem
  have hmaps : Set.MapsTo ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])
      (componentRoots (rootCharHom a) i) (componentRoots (rootCharHom a) i) := by
    intro γ hγ
    exact himage ▸ Set.mem_image_of_mem _ hγ
  have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro hin
    apply hni2
    have h2 := twistInner_iterate_two hmaps hin
    have hfun : ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])^[2] =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[2 * s] := by
      rw [← Function.iterate_mul]
      congr 1
      omega
    rwa [hfun] at h2
  unfold twistKind
  rw [if_neg (show ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) from hni)]
  rw [if_pos (Or.inr ⟨h4, h24, hni2⟩)]


theorem exists_phi_eq_twistHom_D4 {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.D4 L p)
    (hout : ¬ twistInner {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      (S.ρ : (Fin Tag.D4.rank → ℤ) → _)) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr := by
  classical
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  have hPne : P ≠ 1 := by
    rintro rfl
    have hΦ1 : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext g
      rw [hΦ g, one_mul, inv_one, mul_one]
    exact hout
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_D4_twistInner_of_untwisted S hFr hΦ1)
  obtain ⟨t, ht, hPt⟩ := hP.resolve_left hPne
  have hP' : P = diagramMap TwistTag.D4 L := by
    cases t with
    | E6 => exact absurd ht (by decide)
    | D4 =>
      subst hPt
      rw [show ht = rfl from Subsingleton.elim _ _]
      rfl
  refine ⟨Fr, hFr, ?_⟩
  ext g
  rw [hΦ g, hP']
  rfl

theorem rckRetTriD4_D4_of_pair (hP : RCKPairTriD4) (S : LangSetup Tag.D4 GGL 5)
    (a : Fin Tag.D4.rank → GGLˣ) (haT : rootDiagUnit Tag.D4 a ∈ S.D.torus)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hap : rootDiagUnit Tag.D4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) (hq : S.D.q = 2 ^ h)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hshape : compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])) :
    RCKReturnedCover S a i h
      (fun M g => ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
          TriField F σ g ∧ M = triD4Universal F σ) := by
  classical
  obtain ⟨h4, h24, hni2⟩ := hshape
  have hΨ : componentRoots (rootCharHom a) i =
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} := by
    refine Set.eq_of_subset_of_ncard_le (fun γ hγ => isRoot_of_mem_componentRoots hγ) ?_
      (finite_setOf_isRoot Tag.D4)
    rw [ncard_setOf_isRoot, h24]
    exact le_rfl
  have hmaps : Set.MapsTo (S.ρ : (Fin Tag.D4.rank → ℤ) → _)
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} :=
    fun γ hγ => (S.frob.isRoot_iff γ).2 hγ
  have hstable : (S.ρ : (Fin Tag.D4.rank → ℤ) → _) ''
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} =
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} := by
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact hmaps hδ
    · intro hγ
      exact ⟨S.ρ.symm γ, (S.frob.isRoot_iff _).1 (by simpa using hγ), by simp⟩
  have hpos : 0 < componentOrbitLength S.ρ {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} := by
    rw [← hΨ]
    exact CFSG.StandardType.TableCRes.componentOrbitLength_pos S
      (fun γ hγ => isRoot_of_mem_componentRoots hγ)
  have hle : componentOrbitLength S.ρ {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} ≤ 1 := by
    unfold componentOrbitLength
    exact Nat.sInf_le ⟨Nat.one_pos, by rw [Function.iterate_one]; exact hstable⟩
  have hsroots : componentOrbitLength S.ρ {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} = 1 := by
    omega
  have hscomp : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    rw [hΨ]
    exact hsroots
  have hni2roots : ¬ twistInner {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}
      ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}]) := by
    rw [← hΨ]
    exact hni2
  have hniroots : ¬ twistInner {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} S.ρ := by
    intro hin
    apply hni2roots
    have h2 := twistInner_iterate_two hmaps hin
    have hfun : ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[2]) =
        (S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ}] := by
      rw [hsroots, mul_one]
    rwa [hfun] at h2
  have hexc : twistKind S.ρ (rootCharHom a) i = .exc :=
    twistKind_eq_exc_of_triD4Shape S i h4 h24 hni2
  obtain ⟨M, φ, hMod, -, hrange, hker, hfin, hperf, hsplit, hpairClause⟩ :=
    hP Tag.D4 5 S a haT p hp hp2 hap i h hq ⟨hexc, h4⟩ hqs
  obtain ⟨F, hFfield, hFfinite, σ, hTri, hM⟩ := hMod
  have hmodRet : (fun M g => ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
      TriField F σ g ∧ M = triD4Universal F σ) M
      (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    ⟨F, hFfield, hFfinite, σ, hTri, hM⟩
  subst hM
  have hcent : Subgroup.center (triD4Universal F σ).K = ⊥ := by
    change Subgroup.center
      ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥
    exact CFSG.ClassicalInvolution.RouteD.center_twistedGroup_eq_bot_of_card
      (p := 2) (e := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      σ Nat.prime_two hTri.1 hTri.2.1 hTri.2.2
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcent))
  let φ' : (triD4Universal F σ).K →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    φ.codRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i) (fun x => by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  let κ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →* ModGL Tag.D4 GGL :=
    Subgroup.subtype (rationalComponent S.ρ S.Γ (rootCharHom a) i)
  let ι : (Fin Tag.D4.rank → ℤ) → (Fin Tag.D4.rank → ℤ) := id
  have hcomp : κ.comp φ' = φ := MonoidHom.ext fun _ => rfl
  have hsurj' : Function.Surjective φ' := by
    intro y
    have hy : (y : ModGL Tag.D4 GGL) ∈ φ.range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hker' : φ'.ker ≤ Subgroup.center (triD4Universal F σ).K := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hkerbot' : φ'.ker = ⊥ := by
    rw [MonoidHom.ker_codRestrict]
    exact hkerbot
  have hinj' : Function.Injective φ' := (MonoidHom.ker_eq_bot_iff φ').mp hkerbot'
  have hZR : Subgroup.center
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := hsurj' z
    have hx : x ∈ Subgroup.center (triD4Universal F σ).K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hinj'
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp hz) (φ' y)
    rw [hcent, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact Subgroup.one_mem _
  have hperfmodel : Group.IsPerfect ↥S.D.model := by
    obtain ⟨Fr, hFr, hΦ⟩ := exists_phi_eq_twistHom_D4 (L := GGL) (p := 5) S hniroots
    haveI : CharP GGL 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) GGL).injective 2
    exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_D4_perfect_model S hFr hΦ
  haveI hperfI : Group.IsPerfect ↥S.D.model := hperfmodel
  have hΓ : S.Γ = S.D.model := by
    change ⁅S.D.model, S.D.model⁆ = S.D.model
    exact Subgroup.commutator_eq_self
  have hratroots : rationalRoots S.ρ (rootCharHom a) i =
      {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} :=
    (rationalRoots_eq_componentRoots_of_orbitLength_one i hscomp).trans hΨ
  have hspan : rootSpan Tag.D4 GGL (rationalRoots S.ρ (rootCharHom a) i) =
      adjointGroup Tag.D4 GGL := by
    rw [hratroots]
    exact (adjointGroup_eq_rootSpan (τ := Tag.D4) (K := GGL)).symm
  have hratspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = S.Γ := by
    unfold rationalSpan
    rw [hspan]
    exact inf_eq_right.mpr ((le_of_eq hΓ).trans inf_le_left)
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = S.Γ := by
    unfold rationalComponent
    rw [hratspan, hΓ]
    exact Subgroup.commutator_eq_self
  have hTle : S.D.torus ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hR, hΓ]
    exact S.D.torus_le_model
  let β : Fin (triD4Universal F σ).D.rank → ℤ := CFSG.SeitzReduction.highRoot Tag.G2
  have hβmem : β ∈ (triD4Universal F σ).D.roots := by
    change CFSG.SeitzReduction.highRoot Tag.G2 ∈
      (CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ).roots
    rw [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots]
    exact CFSG.SeitzReduction.isRoot_highRoot Tag.G2
  have hβlong : GGLongRoot (triD4Universal F σ).D β := by
    change GGLongRoot (CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ) β
    refine ⟨1, CFSG.SeitzReduction.highRoot Tag.G2, ?_, ?_, ?_⟩
    · rw [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots]
      exact CFSG.SeitzReduction.isRoot_highRoot Tag.G2
    · intro δ hδ
      rw [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots] at hδ
      exact CFSG.SeitzReduction.height_le_height_highRoot hδ
    · show CFSG.SeitzReduction.highRoot Tag.G2 =
          (CFSG.LieType.RootSystem.weylAction
            (CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ).isFiniteType
            (1 : GGWeyl (CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ)))
          (CFSG.SeitzReduction.highRoot Tag.G2)
      rw [map_one]
      rfl
  obtain ⟨γ₀, hγ₀Ψ, z₀, hz₀adj, hstablePos, hstableNeg, himgPos, himgNeg⟩ :=
    hpairClause hscomp β hβmem hβlong
  have hq' : S.D.q = 2 ^ (h * componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)) := by
    rw [hscomp, mul_one]
    exact hq
  have hbij : Set.BijOn ι (componentRoots (rootCharHom a) i)
      {γ' | IsRoot Tag.D4 γ'} := by
    rw [hΨ]
    exact Set.bijOn_id _
  have hpsi : ∀ b ∈ S.D.torus,
      GGPsiInnerDiag (triD4Universal F σ).D (κ.comp φ') b := by
    intro b hb
    apply ggPsiInnerDiag_of_mem_range
    obtain ⟨x, hx⟩ := hsurj' ⟨b, hTle hb⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  have htorus : ∀ b ∈ S.D.torus, ∃ t ∈ S.D.torus,
      (∀ (x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (hx : b * (x : ModGL Tag.D4 GGL) * b⁻¹ ∈
          rationalComponent S.ρ S.Γ (rootCharHom a) i),
        κ ⟨b * (x : ModGL Tag.D4 GGL) * b⁻¹, hx⟩ = t * κ x * t⁻¹) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal t (ι γ) = rckRootVal b γ := by
    intro b hb
    exact ⟨b, hb, fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨triD4Universal F σ, φ', Tag.D4, S, κ, ι, hmodRet, Or.inr hmodRet,
    hsurj', hker', hfin, hperf, hsplit, ?_, hpsi, Or.inl rfl, hq', ?_, ?_, hbij, ?_, ?_, ?_,
    htorus⟩
  · refine ⟨β, hβmem, hβlong, γ₀, isRoot_of_mem_componentRoots hγ₀Ψ, z₀,
      torus_sup_rootSpan_le_adjointGroup _ hz₀adj, hstablePos, hstableNeg, ?_, ?_⟩
    · rw [hcomp]
      exact himgPos
    · rw [hcomp]
      exact himgNeg
  · change (Subgroup.subtype
        (rationalComponent S.ρ S.Γ (rootCharHom a) i)).ker =
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
    rw [Subgroup.ker_subtype, hZR]
  · change (Subgroup.subtype
        (rationalComponent S.ρ S.Γ (rootCharHom a) i)).range = S.Γ
    rw [Subgroup.range_subtype, hR]
  · intro γ hγ
    rfl
  · intro γ hγ δ hδ
    rfl
  · intro γ hγ
    rw [hscomp, Function.iterate_one]
    rfl

end CFSG.StandardType.RCKRP

end
