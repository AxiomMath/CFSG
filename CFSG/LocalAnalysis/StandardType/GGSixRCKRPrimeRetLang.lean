module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRelOneUse
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelMinuscule
import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
import CFSG.LieType.Chevalley.DiagonalFieldActorData
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
import CFSG.RankThree.PartOne.KE.CTLang
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_step_pinnedX
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : GGL) :
    S.D.step (pinnedX τ GGL γ c) = pinnedX τ GGL (S.ρ γ) (c ^ S.D.q) := by
  classical
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨π, hπroot, -, -, hπ⟩ := exists_diagram_data (L := GGL) hP
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ε₁, hε₁, h₁⟩ := hπ γ hγ
  have hπγ : IsRoot τ (π γ) := (hπroot γ).2 hγ
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv GGL w hπγ
  have hsq : ∀ ε : GGL, ε * ε = 1 → ε = 1 := fun ε hε => by
    have h2 : (2 : GGL) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have e1 := hsq ε₁ hε₁
  have e2 := hsq ε₂ hε₂
  have hcalc : ∀ c : GGL, S.D.step (pinnedX τ GGL γ c) =
      pinnedX τ GGL (w • π γ) (c ^ S.D.q) := fun c => by
    have hs : S.D.step (pinnedX τ GGL γ c) =
        S.D.n * S.D.Φ (pinnedX τ GGL γ c) * S.D.n⁻¹ := by
      simp [LangDatum.step, MulAut.conj_apply]
    rw [hs, hΦ, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, hFr,
      h₁, hn, h₂, e1, e2]
    simp [mul_assoc]
  have hρ : w • π γ = S.ρ γ := by
    have hmap := S.frob.map_rootSubgroup γ hγ
    have hmem : S.D.step (pinnedX τ GGL γ 1) ∈ (rootSubgroup τ GGL γ).map S.D.step :=
      Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)
    rw [hmap, hcalc 1, one_pow] at hmem
    refine eq_of_pinnedX_one_mem_rootSubgroup ?_ ((S.frob.isRoot_iff γ).2 hγ) hmem
    rw [isRoot_smul_iff]
    exact hπγ
  rw [hcalc c, hρ]

theorem rckRet_orbit_one
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (h : τ.rank < 2 * compRank (componentRoots (rootCharHom a) i)) :
    S.ρ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  obtain ⟨hs0, hsper, -⟩ := outer_componentOrbitLength_spec S hT i
  have hle := CFSG.StandardType.LangRat.componentOrbitLength_mul_compRank_le S hT i
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    by_contra hne
    have h2 : 2 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by omega
    have := Nat.mul_le_mul_right (compRank (componentRoots (rootCharHom a) i)) h2
    omega
  rw [hs1, Function.iterate_one] at hsper
  exact hsper

theorem rckRet_theta_step
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    {w' : WeylGroup Tag.E6}
    (hw' : ∀ γ ∈ rootsOfFam β Set.univ, w' • ι γ = ι (S.ρ γ))
    {Fr : GGL →+* GGL} (hFr : ∀ c, Fr c = c ^ S.D.q) (x : ↥(RetH τ β)) :
    ∃ hx : S.D.step (x : ModGL τ GGL) ∈ RetH τ β,
      θ ⟨S.D.step (x : ModGL τ GGL), hx⟩ =
        canonicalRep (coxeterSystem Tag.E6) GGL w' * Units.map (entrywiseHom Fr) (θ x) *
          (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ := by
  classical
  obtain ⟨hgen, -, -, -⟩ := hθ
  obtain ⟨xv, hxv⟩ := x
  refine rckRet_rootSpan_induction (S := rootsOfFam β Set.univ)
    (P := fun y hy => ∃ hyb : S.D.step y ∈ RetH τ β,
      θ ⟨S.D.step y, hyb⟩ = canonicalRep (coxeterSystem Tag.E6) GGL w' *
        Units.map (entrywiseHom Fr) (θ ⟨y, hy⟩) *
          (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹) ?_ ?_ ?_ hxv
  · intro α hα c hm
    have hαr : IsRoot τ α := hα.1
    have hρα : S.ρ α ∈ rootsOfFam β Set.univ := hρΨ α hα
    rw [rckRet_step_pinnedX S hαr c]
    have hmem : pinnedX τ GGL (S.ρ α) (c ^ S.D.q) ∈ RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ)
        (S.ρ α) hρα le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
    refine ⟨hmem, ?_⟩
    rw [hgen (S.ρ α) hρα (c ^ S.D.q) hmem, hgen α hα c hm,
      CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, hFr, ← hw' α hα]
    exact (canonicalRep_conj_pinnedX_two w' (hι.1.mapsTo hα) _).symm
  · have h1 : S.D.step (1 : ModGL τ GGL) = 1 := map_one _
    have hmem1 : S.D.step (1 : ModGL τ GGL) ∈ RetH τ β := by rw [h1]; exact one_mem _
    refine ⟨hmem1, ?_⟩
    have e : (⟨S.D.step (1 : ModGL τ GGL), hmem1⟩ : ↥(RetH τ β)) = 1 := Subtype.ext h1
    have e' : (⟨(1 : ModGL τ GGL), one_mem _⟩ : ↥(RetH τ β)) = 1 := rfl
    rw [e, e', map_one, map_one]
    group
  · intro y z hy hz ⟨hyb, hθy⟩ ⟨hzb, hθz⟩
    have hyz : S.D.step (y * z) ∈ RetH τ β := by
      rw [map_mul]
      exact mul_mem hyb hzb
    refine ⟨hyz, ?_⟩
    have e : (⟨S.D.step (y * z), hyz⟩ : ↥(RetH τ β)) =
        ⟨S.D.step y, hyb⟩ * ⟨S.D.step z, hzb⟩ := Subtype.ext (map_mul _ _ _)
    have e' : (⟨y * z, mul_mem hy hz⟩ : ↥(RetH τ β)) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, hθy, hθz, e', map_mul, map_mul]
    group

theorem rckRet_theta_torus
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hι : RetIotaSpec β ι) (hθ : RetCompSpec β ι θ)
    {b : ModGL τ GGL} (hb : b ∈ torusGroup τ GGL) (x : ↥(RetH τ β)) :
    ∃ hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ RetH τ β,
      θ ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ =
        rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) * θ x *
          (rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)))⁻¹ := by
  classical
  obtain ⟨hgen, -, -, -⟩ := hθ
  obtain ⟨xv, hxv⟩ := x
  have hb' : rootDiagUnit τ (rckTorusCoord b) = b := rck_rootDiagUnit_coord hb
  have hval : ∀ α ∈ rootsOfFam β Set.univ,
      (rootChar (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) (ι α) : GGL) =
        (rootChar (rckTorusCoord b) α : GGL) := by
    intro α hα
    have h1 := rckRet_torus_val hι hb α hα
    unfold rckRootVal at h1
    rw [rck_coord_rootDiagUnit] at h1
    exact congrArg (fun u : GGLˣ => (u : GGL)) h1
  generalize (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) = c' at hval ⊢
  refine rckRet_rootSpan_induction (S := rootsOfFam β Set.univ)
    (P := fun y hy => ∃ hyb : b * y * b⁻¹ ∈ RetH τ β,
      θ ⟨b * y * b⁻¹, hyb⟩ = rootDiagUnit Tag.E6 c' * θ ⟨y, hy⟩ * (rootDiagUnit Tag.E6 c')⁻¹)
    ?_ ?_ ?_ hxv
  · intro α hα c hm
    have hαr : IsRoot τ α := hα.1
    have hconj : b * pinnedX τ GGL α c * b⁻¹ =
        pinnedX τ GGL α ((rootChar (rckTorusCoord b) α : GGL) * c) := by
      have h0 := rootDiagUnit_conj_pinnedX (rckTorusCoord b) hαr c
      rwa [hb'] at h0
    have hmem : pinnedX τ GGL α ((rootChar (rckTorusCoord b) α : GGL) * c) ∈ RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ) α hα
        le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
    have hmem' : b * pinnedX τ GGL α c * b⁻¹ ∈ RetH τ β := by rw [hconj]; exact hmem
    refine ⟨hmem', ?_⟩
    have e1 : (⟨b * pinnedX τ GGL α c * b⁻¹, hmem'⟩ : ↥(RetH τ β)) =
        ⟨pinnedX τ GGL α ((rootChar (rckTorusCoord b) α : GGL) * c), hmem⟩ := Subtype.ext hconj
    rw [e1, hgen α hα _ hmem, hgen α hα c hm]
    have hιr : IsRoot Tag.E6 (ι α) := hι.1.mapsTo hα
    rw [rootDiagUnit_conj_pinnedX c' hιr, hval α hα]
  · have h1 : b * (1 : ModGL τ GGL) * b⁻¹ = 1 := by group
    have hmem1 : b * (1 : ModGL τ GGL) * b⁻¹ ∈ RetH τ β := by rw [h1]; exact one_mem _
    refine ⟨hmem1, ?_⟩
    have e : (⟨b * (1 : ModGL τ GGL) * b⁻¹, hmem1⟩ : ↥(RetH τ β)) = 1 := Subtype.ext h1
    have e' : (⟨(1 : ModGL τ GGL), one_mem _⟩ : ↥(RetH τ β)) = 1 := rfl
    rw [e, e', map_one]
    group
  · intro y z hy hz ⟨hyb, hθy⟩ ⟨hzb, hθz⟩
    have hyz : b * (y * z) * b⁻¹ ∈ RetH τ β := by
      have : b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹) := by group
      rw [this]
      exact mul_mem hyb hzb
    refine ⟨hyz, ?_⟩
    have e : (⟨b * (y * z) * b⁻¹, hyz⟩ : ↥(RetH τ β)) =
        ⟨b * y * b⁻¹, hyb⟩ * ⟨b * z * b⁻¹, hzb⟩ := Subtype.ext (by
          show b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹)
          group)
    have e' : (⟨y * z, mul_mem hy hz⟩ : ↥(RetH τ β)) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, hθy, hθz, e', map_mul]
    group

theorem rckRet_not_isRoot_add_of_orth
    {τ : Tag} (hτ : SimplyLacedTag τ) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h0 : iform γ δ = 0) : ¬ IsRoot τ (γ + δ) := by
  intro h
  have h1 := iform_self_eq_two_of_simplyLaced hτ hγ
  have h2 := iform_self_eq_two_of_simplyLaced hτ hδ
  have h3 := iform_self_eq_two_of_simplyLaced hτ h
  have h4 : iform (γ + δ) (γ + δ) = iform γ γ + iform γ δ + iform δ γ + iform δ δ := by
    rw [iform_add_left, iform_add_right, iform_add_right]
    ring
  have h5 : iform δ γ = 0 := by rw [iform_comm]; exact h0
  omega

theorem rckRet_frobGL_symm {τ : Tag} (σ : GGL ≃+* GGL) (y : ModGL τ GGL) :
    frobGL σ (frobGL σ.symm y) = y := by
  have h : σ * σ.symm = 1 := RingEquiv.ext fun c => σ.apply_symm_apply c
  have h1 := (CFSG.LieType.Chevalley.units_map_entrywiseHom_mul_ringEquiv σ σ.symm y).symm
  rw [h, CFSG.LieType.Chevalley.units_map_entrywiseHom_one_ringEquiv] at h1
  exact h1

theorem rckRet_theta_frob
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ) (σ : GGL ≃+* GGL)
    (x : ↥(RetH τ β)) :
    ∃ hx : frobGL σ (x : ModGL τ GGL) ∈ RetH τ β,
      θ ⟨frobGL σ (x : ModGL τ GGL), hx⟩ = frobGL σ (θ x) := by
  classical
  obtain ⟨hgen, -, -, -⟩ := hθ
  obtain ⟨xv, hxv⟩ := x
  refine rckRet_rootSpan_induction (S := rootsOfFam β Set.univ)
    (P := fun y hy => ∃ hyb : frobGL σ y ∈ RetH τ β,
      θ ⟨frobGL σ y, hyb⟩ = frobGL σ (θ ⟨y, hy⟩)) ?_ ?_ ?_ hxv
  · intro α hα c hm
    have hmem : pinnedX τ GGL α (σ c) ∈ RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ) α hα
        le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
    have hm' : frobGL σ (pinnedX τ GGL α c) ∈ RetH τ β := by
      rw [frobGL_pinnedX]
      exact hmem
    refine ⟨hm', ?_⟩
    have e1 : (⟨frobGL σ (pinnedX τ GGL α c), hm'⟩ : ↥(RetH τ β)) =
        ⟨pinnedX τ GGL α (σ c), hmem⟩ := Subtype.ext (frobGL_pinnedX σ α c)
    rw [e1, hgen α hα _ hmem, hgen α hα c hm, frobGL_pinnedX]
  · have h1 : frobGL σ (1 : ModGL τ GGL) = 1 := map_one _
    have hmem1 : frobGL σ (1 : ModGL τ GGL) ∈ RetH τ β := by rw [h1]; exact one_mem _
    refine ⟨hmem1, ?_⟩
    have e : (⟨frobGL σ (1 : ModGL τ GGL), hmem1⟩ : ↥(RetH τ β)) = 1 := Subtype.ext h1
    have e' : (⟨(1 : ModGL τ GGL), one_mem _⟩ : ↥(RetH τ β)) = 1 := rfl
    rw [e, e', map_one, map_one]
  · intro y z hy hz ⟨hyb, hθy⟩ ⟨hzb, hθz⟩
    have hyz : frobGL σ (y * z) ∈ RetH τ β := by
      rw [map_mul]
      exact mul_mem hyb hzb
    refine ⟨hyz, ?_⟩
    have e : (⟨frobGL σ (y * z), hyz⟩ : ↥(RetH τ β)) =
        ⟨frobGL σ y, hyb⟩ * ⟨frobGL σ z, hzb⟩ := Subtype.ext (map_mul _ _ _)
    have e' : (⟨y * z, mul_mem hy hz⟩ : ↥(RetH τ β)) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, hθy, hθz, e', map_mul, map_mul]

theorem rckRet_zhat_compat
    {τ : Tag} (hτ : SimplyLacedTag τ) {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)}
    {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hΨ : componentRoots (rootCharHom a) i = rootsOfFam β Set.univ)
    (hι : RetIotaSpec β ι) {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    {z : ModGL τ GGL}
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a))) :
    (∀ x : ModGL τ GGL, x ∈ RetH τ β ↔ z * x * z⁻¹ ∈ RetH τ β) ∧
    ∃ zh ∈ adjointGroup Tag.E6 GGL, ∀ (x : ↥(RetH τ β))
      (hx : z * (x : ModGL τ GGL) * z⁻¹ ∈ RetH τ β),
      θ ⟨z * (x : ModGL τ GGL) * z⁻¹, hx⟩ = zh * θ x * zh⁻¹ := by
  classical
  let N : Subgroup (ModGL τ GGL) :=
    { carrier := {g | (∀ x : ModGL τ GGL, x ∈ RetH τ β ↔ g * x * g⁻¹ ∈ RetH τ β) ∧
        ∃ zh ∈ adjointGroup Tag.E6 GGL, ∀ (x : ↥(RetH τ β))
          (hx : g * (x : ModGL τ GGL) * g⁻¹ ∈ RetH τ β),
          θ ⟨g * (x : ModGL τ GGL) * g⁻¹, hx⟩ = zh * θ x * zh⁻¹}
      mul_mem' := by
        rintro g₁ g₂ ⟨hn₁, zh₁, hzh₁, hc₁⟩ ⟨hn₂, zh₂, hzh₂, hc₂⟩
        refine ⟨fun x => ?_, zh₁ * zh₂, mul_mem hzh₁ hzh₂, fun x hx => ?_⟩
        · have e : g₁ * g₂ * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
          rw [e]
          exact (hn₂ x).trans (hn₁ _)
        · have hy : g₂ * (x : ModGL τ GGL) * g₂⁻¹ ∈ RetH τ β := (hn₂ _).1 x.2
          have e : g₁ * g₂ * (x : ModGL τ GGL) * (g₁ * g₂)⁻¹ =
              g₁ * (g₂ * (x : ModGL τ GGL) * g₂⁻¹) * g₁⁻¹ := by group
          have hx' : g₁ * (g₂ * (x : ModGL τ GGL) * g₂⁻¹) * g₁⁻¹ ∈ RetH τ β := by
            rw [← e]; exact hx
          have e2 : (⟨g₁ * g₂ * (x : ModGL τ GGL) * (g₁ * g₂)⁻¹, hx⟩ : ↥(RetH τ β)) =
              ⟨g₁ * (g₂ * (x : ModGL τ GGL) * g₂⁻¹) * g₁⁻¹, hx'⟩ := Subtype.ext e
          rw [e2, hc₁ ⟨g₂ * (x : ModGL τ GGL) * g₂⁻¹, hy⟩ hx', hc₂ x hy]
          group
      one_mem' := by
        refine ⟨fun x => by simp, 1, one_mem _, fun x hx => ?_⟩
        have e : (⟨1 * (x : ModGL τ GGL) * 1⁻¹, hx⟩ : ↥(RetH τ β)) = x :=
          Subtype.ext (by simp)
        rw [e]
        group
      inv_mem' := by
        rintro g ⟨hn, zh, hzh, hc⟩
        have hn' : ∀ x : ModGL τ GGL, x ∈ RetH τ β ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ RetH τ β := by
          intro x
          rw [inv_inv]
          have := hn (g⁻¹ * x * g)
          have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
          rw [e] at this
          exact this.symm
        refine ⟨hn', zh⁻¹, inv_mem hzh, fun x hx => ?_⟩
        have hmem : g * (g⁻¹ * (x : ModGL τ GGL) * g⁻¹⁻¹) * g⁻¹ ∈ RetH τ β := by
          have e : g * (g⁻¹ * (x : ModGL τ GGL) * g⁻¹⁻¹) * g⁻¹ = (x : ModGL τ GGL) := by group
          rw [e]; exact x.2
        have h1 := hc ⟨g⁻¹ * (x : ModGL τ GGL) * g⁻¹⁻¹, hx⟩ hmem
        have e2 : (⟨g * (g⁻¹ * (x : ModGL τ GGL) * g⁻¹⁻¹) * g⁻¹, hmem⟩ : ↥(RetH τ β)) = x :=
          Subtype.ext (by group)
        rw [e2] at h1
        rw [h1]
        group }
  suffices hle : torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) ≤ N by
    exact ⟨(hle hzZ).1, (hle hzZ).2⟩
  refine sup_le ?_ (iSup₂_le fun γ hγ => ?_)
  · intro b hb
    have hz : ∀ x : ↥(RetH τ β), ∃ hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ RetH τ β,
        θ ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ =
          rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) * θ x *
            (rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)))⁻¹ :=
      fun x => rckRet_theta_torus hι hθ hb x
    refine ⟨fun x => ⟨fun hx => (hz ⟨x, hx⟩).1, fun hx => ?_⟩,
      rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)), ?_,
      fun x hx => (hz x).2⟩
    · obtain ⟨hx', -⟩ := rckRet_theta_torus hι hθ (inv_mem hb) ⟨b * x * b⁻¹, hx⟩
      have hx2 : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ ∈ RetH τ β := hx'
      have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
      rw [e] at hx2
      exact hx2
    · exact CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
        (rootDiagUnit_mem_torusGroup _)
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    have hγr : IsRoot τ γ := hγ.1
    by_cases hj : (⟦⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a)) = i
    · have hγΨ : γ ∈ rootsOfFam β Set.univ := hΨ ▸ (⟨hγ, hj⟩ : γ ∈ componentRoots (rootCharHom a) i)
      have hu : pinnedX τ GGL γ c ∈ RetH τ β :=
        (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ) γ hγΨ
          le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
      refine ⟨fun x => ⟨fun hx => mul_mem (mul_mem hu hx) (inv_mem hu), fun hx => ?_⟩,
        θ ⟨pinnedX τ GGL γ c, hu⟩, ?_, fun x hx => ?_⟩
      · have e : (pinnedX τ GGL γ c)⁻¹ * (pinnedX τ GGL γ c * x * (pinnedX τ GGL γ c)⁻¹) *
            pinnedX τ GGL γ c = x := by group
        rw [← e]
        exact mul_mem (mul_mem (inv_mem hu) hx) hu
      · rw [← hθ.2.1]
        exact ⟨_, rfl⟩
      · have e : (⟨pinnedX τ GGL γ c * (x : ModGL τ GGL) * (pinnedX τ GGL γ c)⁻¹, hx⟩ :
            ↥(RetH τ β)) = ⟨pinnedX τ GGL γ c, hu⟩ * x * ⟨pinnedX τ GGL γ c, hu⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
    · have hcomm : ∀ x ∈ RetH τ β, pinnedX τ GGL γ c * x = x * pinnedX τ GGL γ c := by
        have hle : RetH τ β ≤ Subgroup.centralizer {pinnedX τ GGL γ c} := by
          refine iSup₂_le fun δ hδ => ?_
          rw [rootSubgroup, Subgroup.closure_le]
          rintro _ ⟨d, rfl⟩
          refine Subgroup.mem_centralizer_singleton_iff.2 ?_
          have hδj : δ ∈ componentRoots (rootCharHom a) i := hΨ ▸ hδ
          have h0 : iform γ δ = 0 :=
            iform_eq_zero_of_mem_componentRoots hj (⟨hγ, rfl⟩ : γ ∈ componentRoots (rootCharHom a)
              ⟦⟨γ, hγ⟩⟧) hδj
          have hδr : IsRoot τ δ := hδ.1
          exact (pinnedX_commute_of_iform_eq_zero GGL hγr hδr h0
            (rckRet_not_isRoot_add_of_orth hτ hγr hδr h0) c d).symm
        intro x hx
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
      have hcomm' : ∀ x ∈ RetH τ β, (pinnedX τ GGL γ c) * x * (pinnedX τ GGL γ c)⁻¹ = x := by
        intro x hx
        rw [hcomm x hx]
        group
      refine ⟨fun x => ⟨fun hx => by rw [hcomm' x hx]; exact hx, fun hx => ?_⟩, 1, one_mem _,
        fun x hx => ?_⟩
      · have h2 := hcomm' _ hx
        have h3 : x = pinnedX τ GGL γ c * x * (pinnedX τ GGL γ c)⁻¹ := by
          calc x = (pinnedX τ GGL γ c)⁻¹ * (pinnedX τ GGL γ c * x * (pinnedX τ GGL γ c)⁻¹) *
                pinnedX τ GGL γ c := by group
            _ = (pinnedX τ GGL γ c)⁻¹ * (pinnedX τ GGL γ c *
                  (pinnedX τ GGL γ c * x * (pinnedX τ GGL γ c)⁻¹) * (pinnedX τ GGL γ c)⁻¹) *
                pinnedX τ GGL γ c := by rw [h2]
            _ = pinnedX τ GGL γ c * x * (pinnedX τ GGL γ c)⁻¹ := by group
        rw [h3]
        exact hx
      · have hx' := hcomm' x x.2
        have e : (⟨pinnedX τ GGL γ c * (x : ModGL τ GGL) * (pinnedX τ GGL γ c)⁻¹, hx⟩ :
            ↥(RetH τ β)) = x := Subtype.ext hx'
        rw [e]
        group

theorem rckRet_zhat
    {τ : Tag} (hτ : SimplyLacedTag τ) {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)}
    {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hΨ : componentRoots (rootCharHom a) i = rootsOfFam β Set.univ)
    (hι : RetIotaSpec β ι) {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    {w' : WeylGroup Tag.E6} (hw' : ∀ γ ∈ rootsOfFam β Set.univ, w' • ι γ = ι (S.ρ γ))
    {σ : GGL ≃+* GGL} (hσ : ∀ c, σ c = c ^ S.D.q) {z : ModGL τ GGL}
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hzs : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    ∃ zh ∈ adjointGroup Tag.E6 GGL,
      (∀ x : ↥(RetH τ β), ∃ hx : z * (x : ModGL τ GGL) * z⁻¹ ∈ RetH τ β,
        θ ⟨z * (x : ModGL τ GGL) * z⁻¹, hx⟩ = zh * θ x * zh⁻¹) ∧
      Units.map (entrywiseHom σ.toRingHom) zh⁻¹ =
        zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w' := by
  classical
  obtain ⟨hnorm, zh, hzh, hcompat⟩ := rckRet_zhat_compat hτ hΨ hι hθ hzZ
  refine ⟨zh, hzh, fun x => ⟨(hnorm x).1 x.2, hcompat x _⟩, ?_⟩
  set n := canonicalRep (coxeterSystem Tag.E6) GGL w' with hn_def
  have hFr : ∀ c, σ.toRingHom c = c ^ S.D.q := hσ
  have hE : ∀ x : ↥(RetH τ β), zh * frobGL σ (θ x) * zh⁻¹ =
      (n * frobGL σ zh) * frobGL σ (θ x) * (n * frobGL σ zh)⁻¹ := by
    intro x
    have hxz : z * (x : ModGL τ GGL) * z⁻¹ ∈ RetH τ β := (hnorm _).1 x.2
    obtain ⟨hFx, hθF⟩ := rckRet_theta_frob hθ σ x
    have hFxz : z * frobGL σ (x : ModGL τ GGL) * z⁻¹ ∈ RetH τ β := (hnorm _).1 hFx
    have h1 : θ ⟨z * frobGL σ (x : ModGL τ GGL) * z⁻¹, hFxz⟩ = zh * frobGL σ (θ x) * zh⁻¹ := by
      rw [hcompat ⟨frobGL σ (x : ModGL τ GGL), hFx⟩ hFxz, hθF]
    obtain ⟨hst, hθst⟩ := rckRet_theta_step S hι hθ hρΨ hw' (Fr := σ.toRingHom) hFr
      ⟨z * (x : ModGL τ GGL) * z⁻¹, hxz⟩
    have hxs : (x : ModGL τ GGL) ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
      rw [hΨ]; exact x.2
    have e : (⟨S.D.step (z * (x : ModGL τ GGL) * z⁻¹), hst⟩ : ↥(RetH τ β)) =
        ⟨z * frobGL σ (x : ModGL τ GGL) * z⁻¹, hFxz⟩ := Subtype.ext (hzs _ hxs)
    rw [e, h1] at hθst
    have h2 : θ ⟨z * (x : ModGL τ GGL) * z⁻¹, hxz⟩ = zh * θ x * zh⁻¹ := hcompat x hxz
    change _ = n * frobGL σ (θ ⟨z * (x : ModGL τ GGL) * z⁻¹, hxz⟩) * n⁻¹ at hθst
    rw [h2, map_mul, map_mul, map_inv] at hθst
    rw [hθst]
    group
  have hsurj : ∀ y ∈ adjointGroup Tag.E6 GGL, ∃ x : ↥(RetH τ β), frobGL σ (θ x) = y := by
    intro y hy
    have hy' : frobGL σ.symm y ∈ adjointGroup Tag.E6 GGL :=
      CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup σ.symm.toRingHom hy
    rw [← hθ.2.1] at hy'
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, by rw [hx, rckRet_frobGL_symm]⟩
  have hE' : ∀ y ∈ adjointGroup Tag.E6 GGL,
      zh * y * zh⁻¹ = (n * frobGL σ zh) * y * (n * frobGL σ zh)⁻¹ := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y hy
    exact hE x
  have hn : n ∈ adjointGroup Tag.E6 GGL := canonicalRep_mem_adjointGroup _ GGL w'
  have hFzh : frobGL σ zh ∈ adjointGroup Tag.E6 GGL :=
    CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup σ.toRingHom hzh
  have hm : n * frobGL σ zh ∈ adjointGroup Tag.E6 GGL := mul_mem hn hFzh
  have hmem : (n * frobGL σ zh)⁻¹ * zh ∈ adjointGroup Tag.E6 GGL := mul_mem (inv_mem hm) hzh
  have hcen : (⟨(n * frobGL σ zh)⁻¹ * zh, hmem⟩ : ↥(adjointGroup Tag.E6 GGL)) ∈
      Subgroup.center ↥(adjointGroup Tag.E6 GGL) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := hE' g g.2
    calc (g : ModGL Tag.E6 GGL) * ((n * frobGL σ zh)⁻¹ * zh) =
        (n * frobGL σ zh)⁻¹ * ((n * frobGL σ zh) * g * (n * frobGL σ zh)⁻¹) * zh := by group
      _ = (n * frobGL σ zh)⁻¹ * (zh * g * zh⁻¹) * zh := by rw [h]
      _ = ((n * frobGL σ zh)⁻¹ * zh) * g := by group
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E6 GGL, Subgroup.mem_bot] at hcen
  have h1 : (n * frobGL σ zh)⁻¹ * zh = 1 := congrArg Subtype.val hcen
  have h2 : n * frobGL σ zh = zh := inv_mul_eq_one.1 h1
  have h3 : frobGL σ zh = n⁻¹ * zh := eq_inv_mul_of_mul_eq h2
  change frobGL σ zh⁻¹ = zh⁻¹ * n
  rw [map_inv, h3]
  group

theorem rckRet_SK
    {σ : GGL ≃+* GGL} (hfin : Finite ↥(fixSubfield σ)) {Q : ℕ}
    (hQ : Nat.card ↥(fixSubfield σ) = Q) (hσ : ∀ c, σ c = c ^ Q) (hQ2 : ∃ g, 0 < g ∧ Q = 2 ^ g)
    {w' : WeylGroup Tag.E6} {zh : ModGL Tag.E6 GGL} (hzh : zh ∈ adjointGroup Tag.E6 GGL)
    (hlang : Units.map (entrywiseHom σ.toRingHom) zh⁻¹ =
      zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w') :
    ∃ SK : LangSetup Tag.E6 GGL 5, SK.D.q = Q ∧ SK.D.g0 = zh⁻¹ ∧
      SK.D.n = canonicalRep (coxeterSystem Tag.E6) GGL w' ∧
      SK.D.Φ = Units.map (entrywiseHom σ.toRingHom) ∧
      (∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' → SK.ρ γ' = w' • γ') ∧
      SK.Γ = ((adjointGroup Tag.E6 ↥(fixSubfield σ)).map
        (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj zh).toMonoidHom := by
  classical
  haveI : Finite ↥(fixSubfield σ) := hfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) ↥(fixSubfield σ) := ZMod.algebra _ 2
  haveI : @IsScalarTower (ZMod 2) ↥(fixSubfield σ) GGL Algebra.toSMul Algebra.toSMul
      Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure ↥(fixSubfield σ) GGL :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := ↥(fixSubfield σ))⟩
  obtain ⟨g, hg0, hQg⟩ := hQ2
  have hFr : ∀ c, σ.toRingHom c = c ^ Nat.card ↥(fixSubfield σ) := fun c => by
    rw [hQ]; exact hσ c
  have hpq : ¬ 5 ∣ Nat.card ↥(fixSubfield σ) := by
    rw [hQ, hQg]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
    omega
  have hperf : Group.IsPerfect ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) := by
    have hperfM : commutator ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        ↥(fixSubfield σ)) = ⊤ :=
      (CFSG.GroupTheory.GomiLeviExc.MinusculeModel.isCharTwoModel_e6
        ↥(fixSubfield σ)).isQuasisimple.1.commutator_eq_top
    have hsurj := CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective ↥(fixSubfield σ)
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map (CFSG.LieType.Steinberg.Isogeny.e6Isogeny
      ↥(fixSubfield σ))) hperfM
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj] at h1
    rw [commutator_def]
    exact h1
  obtain ⟨S, hSD, hdesc⟩ := exists_langSetup_untw_of_datum (K := ↥(fixSubfield σ)) (L := GGL)
    frobeniusOnRoots_proved 3 (Or.inl ⟨rfl, rfl⟩) (p := 5) (by norm_num) (by norm_num) hpq hperf
    hFr w' (inv_mem hzh) hlang
  have hq : S.D.q = Q := by rw [hSD]; exact hQ
  have hg0' : S.D.g0 = zh⁻¹ := by rw [hSD]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) GGL w' := by rw [hSD]; rfl
  have hΦ : S.D.Φ = Units.map (entrywiseHom σ.toRingHom) := by rw [hSD]; rfl
  refine ⟨S, hq, hg0', hn, hΦ, ?_, ?_⟩
  · intro γ' hγ'
    have h1 := rckRet_step_pinnedX S hγ' 1
    have h2 : S.D.step (pinnedX Tag.E6 GGL γ' 1) = pinnedX Tag.E6 GGL (w' • γ') 1 := by
      have hs : S.D.step (pinnedX Tag.E6 GGL γ' 1) =
          S.D.n * S.D.Φ (pinnedX Tag.E6 GGL γ' 1) * S.D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      rw [hs, hΦ, hn, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, map_one,
        canonicalRep_conj_pinnedX_two w' hγ']
    have h3 : pinnedX Tag.E6 GGL (w' • γ') 1 ∈ rootSubgroup Tag.E6 GGL (S.ρ γ') := by
      rw [← h2, h1, one_pow]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    have h4 : IsRoot Tag.E6 (w' • γ') := by rw [isRoot_smul_iff]; exact hγ'
    exact (eq_of_pinnedX_one_mem_rootSubgroup h4 ((S.frob.isRoot_iff γ').2 hγ') h3).symm
  · change S.D.Γ = _
    rw [hdesc.Γ_eq, hg0', inv_inv, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl

end CFSG.StandardType.RCKRP

end
