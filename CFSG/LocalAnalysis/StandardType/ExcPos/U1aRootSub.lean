module

public import CFSG.LocalAnalysis.StandardType.ExcPos.LangFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompat
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart1
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleLang
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.Canonical
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.Adapters.TauCetiExceptional.EvenLang

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints commutatorElement

open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.AmbientPairDescent
open CFSG.StandardType.F4ExplicitPos.PairStabilizer

private theorem u1aE2_langTag {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) :
    langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
  rcases ht with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem u1aE2_ht4 {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) :
    t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 := by
  rcases ht with rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem u1aE2_ht5 {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) :
    langTag t = .F4 ∨ langTag t = .D4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨
      langTag t = .E8 := by
  rcases ht with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private noncomputable def u1aE2_beta (t : StatedLieTag)
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) : Fin (ggU t n f).D.rank → ℤ :=
  ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f).symm (highRoot (langTag t))

private theorem u1aE2_beta_mem {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) : u1aE2_beta t ht n f ∈ (ggU t n f).D.roots := by
  rcases ht with rfl | rfl | rfl
  · exact (mem_roots_E6 n f _).2 (mem_rootFinset.2 (isRoot_highRoot _))
  · exact (mem_roots_E7 n f _).2 (mem_rootFinset.2 (isRoot_highRoot _))
  · exact (mem_roots_E8 n f _).2 (mem_rootFinset.2 (isRoot_highRoot _))

private theorem u1aE2_beta_long {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) : GGLongRoot (ggU t n f).D (u1aE2_beta t ht n f) := by
  refine ⟨1, u1aE2_beta t ht n f, u1aE2_beta_mem ht n f, ?_, ?_⟩
  · intro δ hδ
    rcases ht with rfl | rfl | rfl
    · exact height_le_height_highRoot (mem_rootFinset.1 ((mem_roots_E6 n f δ).1 hδ))
    · exact height_le_height_highRoot (mem_rootFinset.1 ((mem_roots_E7 n f δ).1 hδ))
    · exact height_le_height_highRoot (mem_rootFinset.1 ((mem_roots_E8 n f δ).1 hδ))
  · simp

private theorem u1aE2_reidx_beta {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) :
    ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) (u1aE2_beta t ht n f) =
      highRoot (langTag t) := by
  rcases ht with rfl | rfl | rfl <;> rfl

private theorem u1aE2_reidx_beta_neg {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) :
    ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) (-(u1aE2_beta t ht n f)) =
      -highRoot (langTag t) := by
  rw [show (-(u1aE2_beta t ht n f)) = -(u1aE2_beta t ht n f) from rfl,
    show ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) (-(u1aE2_beta t ht n f)) =
      -(ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) (u1aE2_beta t ht n f)) from rfl,
    u1aE2_reidx_beta ht n f]

private theorem u1aE2_Phi_eq_entrywise {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) :
    ggPhi t f = Units.map (entrywiseHom (ggFrobT f)) := by
  rcases ht with rfl | rfl | rfl <;> rfl

private theorem u1aE2_Phi_eq_frob {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) :
    ggPhi t f = frobTwistGL (langTag t) GGL 2 f 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  rcases ht with rfl | rfl | rfl <;> rfl

private theorem u1aE2_Phi_rootSubgroup {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) (γ : Fin (langTag t).rank → ℤ) :
    (rootSubgroup (langTag t) GGL γ).map (ggPhi t f) =
      rootSubgroup (langTag t) GGL γ := by
  rw [u1aE2_Phi_eq_entrywise ht f]
  have hbij : Function.Bijective (ggFrobT f) := bijective_iterateFrobenius GGL 2 f
  let σ : GGL ≃+* GGL := RingEquiv.ofBijective (ggFrobT f) hbij
  have hσ : σ.toRingHom = ggFrobT f := rfl
  rw [← hσ]
  exact map_entrywise_rootSubgroup (τ := langTag t) (K := GGL) σ γ

private theorem u1aE2_Phi_mem_adjoint {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) {x : ModGL (langTag t) GGL}
    (hx : x ∈ adjointGroup (langTag t) GGL) :
    ggPhi t f x ∈ adjointGroup (langTag t) GGL := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  rw [u1aE2_Phi_eq_entrywise ht f]
  rcases ht with rfl | rfl | rfl
  · exact entrywiseFrobGL_mem (τ := Tag.E6) (p := 2) (e := f) hx
  · exact entrywiseFrobGL_mem (τ := Tag.E7) (p := 2) (e := f) hx
  · exact entrywiseFrobGL_mem (τ := Tag.E8) (p := 2) (e := f) hx

private theorem u1aE2_step_mem_adjoint {t : StatedLieTag} {X : Type} [Group X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (F : ExcLangFrame t n f p ψ G₀ B₁ D x)
    {y : ModGL (langTag t) GGL} (hy : y ∈ adjointGroup (langTag t) GGL) :
    F.Δ.step y ∈ adjointGroup (langTag t) GGL := by
  obtain ⟨v, hv⟩ := F.Δ.n_weyl
  have hn : F.Δ.n ∈ adjointGroup (langTag t) GGL := by
    rw [hv]
    exact canonicalRep_mem_adjointGroup _ _ _
  change F.Δ.n * F.Δ.Φ y * F.Δ.n⁻¹ ∈ adjointGroup (langTag t) GGL
  rw [F.Φ_eq]
  exact (adjointGroup (langTag t) GGL).mul_mem
    ((adjointGroup (langTag t) GGL).mul_mem hn (u1aE2_Phi_mem_adjoint ht f hy))
    ((adjointGroup (langTag t) GGL).inv_mem hn)

private theorem u1aE2_V0_stable {t : StatedLieTag} {X : Type} [Group X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (F : ExcLangFrame t n f p ψ G₀ B₁ D x)
    {γ : Fin (langTag t).rank → ℤ} :
    (excCurve γ F.Δ.g0⁻¹).map F.Δ.step = excCurve γ F.Δ.g0⁻¹ := by
  have hcomp : F.Δ.step.comp (MulAut.conj (F.Δ.g0⁻¹)).toMonoidHom =
      (MulAut.conj (F.Δ.g0⁻¹)).toMonoidHom.comp (ggPhi t f) := by
    simpa only [F.Φ_eq] using F.Δ.step_comp_conj_g0_inv
  change ((rootSubgroup (langTag t) GGL γ).map
      (MulAut.conj (F.Δ.g0⁻¹)).toMonoidHom).map F.Δ.step =
    (rootSubgroup (langTag t) GGL γ).map (MulAut.conj (F.Δ.g0⁻¹)).toMonoidHom
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, u1aE2_Phi_rootSubgroup ht f γ]

private theorem u1aE2_mem_normalizer_conj {G : Type*} [Group G] {L : Subgroup G} {g h : G} :
    h ∈ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      g⁻¹ * h * g ∈ Subgroup.normalizer (L : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq L (MulAut.conj g), Subgroup.mem_map_equiv]
  have hsymm : (MulAut.conj g).symm h = g⁻¹ * h * g := by
    rw [MulEquiv.symm_apply_eq]
    simp only [MulAut.conj_apply]
    group
  rw [hsymm]

private theorem u1aE2_map_conj_inf_eq {G : Type*} [Group G] {H M : Subgroup G} {γ : G}
    (hγ : γ ∈ M) :
    H.map (MulAut.conj γ).toMonoidHom ⊓ M = (H ⊓ M).map (MulAut.conj γ).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨hxH, hxM⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hxH
    refine Subgroup.mem_map.2 ⟨y, ⟨hy, ?_⟩, rfl⟩
    change γ * y * γ⁻¹ ∈ M at hxM
    have h := M.mul_mem (M.mul_mem (M.inv_mem hγ) hxM) hγ
    rwa [show γ⁻¹ * (γ * y * γ⁻¹) * γ = y by group] at h
  · rintro ⟨y, ⟨hyH, hyM⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hyH, ?_⟩
    change γ * y * γ⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hγ hyM) (M.inv_mem hγ)

private theorem u1aE2_beta_neg_mem {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) : -(u1aE2_beta t ht n f) ∈ (ggU t n f).D.roots := by
  rcases ht with rfl | rfl | rfl
  · have h : IsRoot Tag.E6 (u1aE2_beta .E6 (Or.inl rfl) n f) :=
      mem_rootFinset.1 ((mem_roots_E6 n f _).1 (u1aE2_beta_mem (Or.inl rfl) n f))
    exact (mem_roots_E6 n f _).2 (mem_rootFinset.2 (IsRoot.neg h))
  · have h : IsRoot Tag.E7 (u1aE2_beta .E7 (Or.inr (Or.inl rfl)) n f) :=
      mem_rootFinset.1 ((mem_roots_E7 n f _).1 (u1aE2_beta_mem (Or.inr (Or.inl rfl)) n f))
    exact (mem_roots_E7 n f _).2 (mem_rootFinset.2 (IsRoot.neg h))
  · have h : IsRoot Tag.E8 (u1aE2_beta .E8 (Or.inr (Or.inr rfl)) n f) :=
      mem_rootFinset.1 ((mem_roots_E8 n f _).1 (u1aE2_beta_mem (Or.inr (Or.inr rfl)) n f))
    exact (mem_roots_E8 n f _).2 (mem_rootFinset.2 (IsRoot.neg h))

theorem exists_rootSub {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {X : Type}
    [Group X] {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (F : ExcLangFrame t n f p ψ G₀ B₁ D x) {α : Fin (langTag t).rank → ℤ}
    {w : ModGL (langTag t) GGL} (hα : IsRoot (langTag t) α) (hw : w ∈ adjointGroup (langTag t) GGL)
    (hV : (excCurve α w).map F.Δ.step = excCurve α w)
    (hVm : (excCurve (-α) w).map F.Δ.step = excCurve (-α) w) :
    ∃ (β : Fin (ggU t n f).D.rank → ℤ) (k : (ggU t n f).K), β ∈ (ggU t n f).D.roots ∧
      GGLongRoot (ggU t n f).D β ∧
      ((ggRootSub (ggU t n f).D ψ β k).subgroupOf G₀).map F.η = excCurve α w ⊓ F.Δ.model ∧
      ((ggRootSub (ggU t n f).D ψ (-β) k).subgroupOf G₀).map F.η =
        excCurve (-α) w ⊓ F.Δ.model ∧
      Nat.card ↥(excCurve α w ⊓ F.Δ.model) = Nat.card (GaloisField 2 f) ∧
      Nat.card ↥(excCurve (-α) w ⊓ F.Δ.model) = Nat.card (GaloisField 2 f) := by
  classical
  let K := GaloisField 2 f
  letI : Algebra K GGL := (ggRatEmb f).toAlgebra
  haveI : IsScalarTower (ZMod 2) K GGL := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic K GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) (A := GGL)
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hf : 1 ≤ f := F.one_le_f
  have hcardK : Nat.card K = 2 ^ f := GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp hf)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card K := fun c => by
    rw [ggFrobT_apply, hcardK]
  have hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := u1aE2_langTag ht
  let β : Fin (ggU t n f).D.rank → ℤ := u1aE2_beta t ht n f
  let θ : Fin (langTag t).rank → ℤ := highRoot (langTag t)
  let g0 : ModGL (langTag t) GGL := F.Δ.g0
  let nn : ModGL (langTag t) GGL := F.Δ.n
  let A : Subgroup (ModGL (langTag t) GGL) := adjointGroup (langTag t) GGL
  let Gg : Subgroup (ModGL (langTag t) GGL) := ggFixGp t f
  let M : Subgroup (ModGL (langTag t) GGL) := F.Δ.model
  let P : Subgroup (ModGL (langTag t) GGL) := rootSubgroup (langTag t) GGL θ
  let Pm : Subgroup (ModGL (langTag t) GGL) := rootSubgroup (langTag t) GGL (-θ)
  let V : Subgroup (ModGL (langTag t) GGL) := excCurve α w
  let Vm : Subgroup (ModGL (langTag t) GGL) := excCurve (-α) w
  let V0 : Subgroup (ModGL (langTag t) GGL) := excCurve θ g0⁻¹
  let Vm0 : Subgroup (ModGL (langTag t) GGL) := excCurve (-θ) g0⁻¹
  let ψ0 : (ggU t n f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun y => hψ ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
  let ηψ : (ggU t n f).K →* ModGL (langTag t) GGL := F.η.comp ψ0
  have hβmem : β ∈ (ggU t n f).D.roots := u1aE2_beta_mem ht n f
  have hβlong : GGLongRoot (ggU t n f).D β := u1aE2_beta_long ht n f
  have hβneg : -β ∈ (ggU t n f).D.roots := u1aE2_beta_neg_mem ht n f
  have hreidx : ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) β = θ := u1aE2_reidx_beta ht n f
  have hθroot : IsRoot (langTag t) θ := isRoot_highRoot _
  have hg0A : g0 ∈ A := F.Δ.g0_mem
  have hΦe : F.Δ.Φ = Units.map (entrywiseHom (ggFrobT f)) :=
    F.Φ_eq.trans (u1aE2_Phi_eq_entrywise ht f)
  have hΦfrob : F.Δ.Φ = frobTwistGL (langTag t) GGL 2 f 1 :=
    F.Φ_eq.trans (u1aE2_Phi_eq_frob ht f)
  have hηψ_apply : ∀ y : (ggU t n f).K,
      ηψ y = g0⁻¹ * ggIotaK t n f hf y * g0 := by
    intro y
    show F.η (ψ0 y) = g0⁻¹ * ggIotaK t n f hf y * g0
    rw [F.η_eq]
    change g0⁻¹ * F.θ ⟨ψ y, _⟩ * g0 = g0⁻¹ * ggIotaK t n f hf y * g0
    rw [F.θ_iota]
  have hM : M = Gg.map (MulAut.conj g0⁻¹).toMonoidHom := by
    have h1 := F.Δ.map_conj_model
    rw [show F.Δ.fix = Gg from ggFixGp_eq_fix F.Δ F.Φ_eq] at h1
    calc M = (M.map (MulAut.conj g0).toMonoidHom).map
          (MulAut.conj g0⁻¹).toMonoidHom := by
          rw [Subgroup.map_map]
          have e : (MulAut.conj g0⁻¹).toMonoidHom.comp (MulAut.conj g0).toMonoidHom =
              MonoidHom.id (ModGL (langTag t) GGL) := by
            refine MonoidHom.ext fun y => ?_
            simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
              MulAut.conj_apply]
            group
          rw [e, Subgroup.map_id]
      _ = Gg.map (MulAut.conj g0⁻¹).toMonoidHom := by rw [h1]
  have hV0map : V0 = P.map (MulAut.conj g0⁻¹).toMonoidHom := rfl
  have hVm0map : Vm0 = Pm.map (MulAut.conj g0⁻¹).toMonoidHom := rfl
  have hV0Mmap : V0 ⊓ M = (P ⊓ Gg).map (MulAut.conj g0⁻¹).toMonoidHom := by
    rw [hV0map, hM]
    exact (Subgroup.map_inf P Gg (MulAut.conj g0⁻¹).toMonoidHom
      (MulAut.conj g0⁻¹).injective).symm
  have hVm0Mmap : Vm0 ⊓ M = (Pm ⊓ Gg).map (MulAut.conj g0⁻¹).toMonoidHom := by
    rw [hVm0map, hM]
    exact (Subgroup.map_inf Pm Gg (MulAut.conj g0⁻¹).toMonoidHom
      (MulAut.conj g0⁻¹).injective).symm
  have hgg : ((ggU t n f).D.rootGroup β).map (ggIotaK t n f hf) = Gg ⊓ P := by
    have h := ggBC_untw (u1aE2_ht4 ht) n f hf β hβmem
    rw [hreidx] at h
    exact h
  have hggm : ((ggU t n f).D.rootGroup (-β)).map (ggIotaK t n f hf) = Gg ⊓ Pm := by
    have h := ggBC_untw (u1aE2_ht4 ht) n f hf (-β) hβneg
    rw [show ggLangReidx (ggRank_untw (u1aE2_ht4 ht) n f) (-β) = -θ by
      rw [show (-β) = -(u1aE2_beta t ht n f) from rfl, u1aE2_reidx_beta_neg ht n f]] at h
    exact h
  have hV0M : V0 ⊓ M = ((ggU t n f).D.rootGroup β).map ηψ := by
    rw [hV0Mmap, inf_comm, ← hgg,
      show ηψ = (MulAut.conj g0⁻¹).toMonoidHom.comp (ggIotaK t n f hf) from
        MonoidHom.ext hηψ_apply,
      Subgroup.map_map]
  have hVm0M : Vm0 ⊓ M = ((ggU t n f).D.rootGroup (-β)).map ηψ := by
    rw [hVm0Mmap, inf_comm, ← hggm,
      show ηψ = (MulAut.conj g0⁻¹).toMonoidHom.comp (ggIotaK t n f hf) from
        MonoidHom.ext hηψ_apply,
      Subgroup.map_map]
  have hV0stab : V0.map F.Δ.step = V0 := u1aE2_V0_stable ht F
  have hVm0stab : Vm0.map F.Δ.step = Vm0 := by
    have h := u1aE2_V0_stable ht F (γ := -θ)
    simpa only [Vm0, g0] using h
  obtain ⟨v, hv⟩ := CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq hτ hα
  let nv : ModGL (langTag t) GGL := canonicalRep (coxeterSystem (langTag t)) GGL v
  let h : ModGL (langTag t) GGL := w * nv * g0
  have hnvA : nv ∈ A := canonicalRep_mem_adjointGroup _ _ _
  have hhA : h ∈ A := A.mul_mem (A.mul_mem hw hnvA) hg0A
  have hnvU : P.map (MulAut.conj nv).toMonoidHom = rootSubgroup (langTag t) GGL α := by
    have h := (canonical_weyl_root_transport (langTag t) GGL).2.1 v θ hθroot
    rw [hv] at h
    exact h
  have hnvUm : Pm.map (MulAut.conj nv).toMonoidHom = rootSubgroup (langTag t) GGL (-α) := by
    have h := (canonical_weyl_root_transport (langTag t) GGL).2.1 v (-θ) (IsRoot.neg hθroot)
    rw [smul_neg, hv] at h
    exact h
  have hVeq : V = V0.map (MulAut.conj h).toMonoidHom := by
    calc V = (rootSubgroup (langTag t) GGL α).map (MulAut.conj w).toMonoidHom := rfl
      _ = (P.map (MulAut.conj nv).toMonoidHom).map (MulAut.conj w).toMonoidHom := by rw [hnvU]
      _ = P.map (((MulAut.conj w).toMonoidHom).comp
            ((MulAut.conj nv).toMonoidHom)) := Subgroup.map_map _ _ _
      _ = P.map (((MulAut.conj h).toMonoidHom).comp
            ((MulAut.conj g0⁻¹).toMonoidHom)) := by
            rw [show ((MulAut.conj w).toMonoidHom.comp (MulAut.conj nv).toMonoidHom) =
                ((MulAut.conj h).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom) from by
              refine MonoidHom.ext fun y => ?_
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
              show w * (nv * y * nv⁻¹) * w⁻¹ =
                w * nv * g0 * (g0⁻¹ * y * g0) * (w * nv * g0)⁻¹
              group]
      _ = (P.map (MulAut.conj g0⁻¹).toMonoidHom).map
            (MulAut.conj h).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = V0.map (MulAut.conj h).toMonoidHom := rfl
  have hVmeq : Vm = Vm0.map (MulAut.conj h).toMonoidHom := by
    calc Vm = (rootSubgroup (langTag t) GGL (-α)).map (MulAut.conj w).toMonoidHom := rfl
      _ = (Pm.map (MulAut.conj nv).toMonoidHom).map (MulAut.conj w).toMonoidHom := by
            rw [hnvUm]
      _ = Pm.map (((MulAut.conj w).toMonoidHom).comp
            ((MulAut.conj nv).toMonoidHom)) := Subgroup.map_map _ _ _
      _ = Pm.map (((MulAut.conj h).toMonoidHom).comp
            ((MulAut.conj g0⁻¹).toMonoidHom)) := by
            rw [show ((MulAut.conj w).toMonoidHom.comp (MulAut.conj nv).toMonoidHom) =
                ((MulAut.conj h).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom) from by
              refine MonoidHom.ext fun y => ?_
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
              show w * (nv * y * nv⁻¹) * w⁻¹ =
                w * nv * g0 * (g0⁻¹ * y * g0) * (w * nv * g0)⁻¹
              group]
      _ = (Pm.map (MulAut.conj g0⁻¹).toMonoidHom).map
            (MulAut.conj h).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = Vm0.map (MulAut.conj h).toMonoidHom := rfl
  have hstepcomp : (MulAut.conj (F.Δ.step h)).toMonoidHom.comp F.Δ.step =
      F.Δ.step.comp (MulAut.conj h).toMonoidHom := by
    rw [show h = w * nv * g0 from rfl]
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : F.Δ.step ((w * nv * g0) * y * (w * nv * g0)⁻¹) =
        F.Δ.step (w * nv * g0) * F.Δ.step y * (F.Δ.step (w * nv * g0))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    exact e.symm
  have hstabplus : V0.map (MulAut.conj (F.Δ.step h)).toMonoidHom =
      V0.map (MulAut.conj h).toMonoidHom := by
    have hL : V0.map (MulAut.conj (F.Δ.step h)).toMonoidHom = V := by
      calc V0.map (MulAut.conj (F.Δ.step h)).toMonoidHom
          = (V0.map F.Δ.step).map (MulAut.conj (F.Δ.step h)).toMonoidHom := by
              rw [hV0stab]
        _ = V0.map ((MulAut.conj (F.Δ.step h)).toMonoidHom.comp F.Δ.step) :=
              Subgroup.map_map _ _ _
        _ = V0.map (F.Δ.step.comp (MulAut.conj h).toMonoidHom) := by rw [hstepcomp]
        _ = (V0.map (MulAut.conj h).toMonoidHom).map F.Δ.step :=
              (Subgroup.map_map _ _ _).symm
        _ = V.map F.Δ.step := by rw [← hVeq]
        _ = V := hV
    rw [hL, ← hVeq]
  have hstabminus : Vm0.map (MulAut.conj (F.Δ.step h)).toMonoidHom =
      Vm0.map (MulAut.conj h).toMonoidHom := by
    have hL : Vm0.map (MulAut.conj (F.Δ.step h)).toMonoidHom = Vm := by
      calc Vm0.map (MulAut.conj (F.Δ.step h)).toMonoidHom
          = (Vm0.map F.Δ.step).map (MulAut.conj (F.Δ.step h)).toMonoidHom := by
              rw [hVm0stab]
        _ = Vm0.map ((MulAut.conj (F.Δ.step h)).toMonoidHom.comp F.Δ.step) :=
              Subgroup.map_map _ _ _
        _ = Vm0.map (F.Δ.step.comp (MulAut.conj h).toMonoidHom) := by rw [hstepcomp]
        _ = (Vm0.map (MulAut.conj h).toMonoidHom).map F.Δ.step :=
              (Subgroup.map_map _ _ _).symm
        _ = Vm.map F.Δ.step := by rw [← hVmeq]
        _ = Vm := hVm
    rw [hL, ← hVmeq]
  have hFA : ∀ y ∈ A, F.Δ.step y ∈ A := fun y hy => u1aE2_step_mem_adjoint ht F hy
  have hLang : ∀ c ∈ A ⊓ Subgroup.normalizer (V0 : Set (ModGL (langTag t) GGL)) ⊓
        Subgroup.normalizer (Vm0 : Set (ModGL (langTag t) GGL)),
      ∃ z ∈ A ⊓ Subgroup.normalizer (V0 : Set (ModGL (langTag t) GGL)) ⊓
        Subgroup.normalizer (Vm0 : Set (ModGL (langTag t) GGL)),
        z⁻¹ * F.Δ.step z = c := by
    intro c hc
    obtain ⟨⟨hcA, hcN0⟩, hcNm0⟩ := Subgroup.mem_inf.1 hc
    have hcP : g0 * c * g0⁻¹ ∈ Subgroup.normalizer (P : Set (ModGL (langTag t) GGL)) :=
      (u1aE2_mem_normalizer_conj (g := g0⁻¹)).1 hcN0
    have hcPm : g0 * c * g0⁻¹ ∈ Subgroup.normalizer (Pm : Set (ModGL (langTag t) GGL)) :=
      (u1aE2_mem_normalizer_conj (g := g0⁻¹)).1 hcNm0
    have hcA' : g0 * c * g0⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem hg0A hcA) (A.inv_mem hg0A)
    have hcZ : g0 * c * g0⁻¹ ∈ A ⊓
        Subgroup.normalizer (P : Set (ModGL (langTag t) GGL)) ⊓
        Subgroup.normalizer (Pm : Set (ModGL (langTag t) GGL)) :=
      Subgroup.mem_inf.2 ⟨⟨hcA', hcP⟩, hcPm⟩
    have hconn : IsConnectedAlgebraicSubgroup GGL
        ((A ⊓ Subgroup.normalizer (P : Set (ModGL (langTag t) GGL)) ⊓
          Subgroup.normalizer (Pm : Set (ModGL (langTag t) GGL))).map
            (modGLPoint (langTag t) GGL).toMonoidHom) :=
      isConnectedAlgebraicSubgroup_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
        (τ := langTag t) (K := GGL)
    obtain ⟨hsm, -, -⟩ := hconn.smooth
    have hΦZ : ∀ y ∈ A ⊓ Subgroup.normalizer (P : Set (ModGL (langTag t) GGL)) ⊓
          Subgroup.normalizer (Pm : Set (ModGL (langTag t) GGL)),
        F.Δ.Φ y ∈ A ⊓ Subgroup.normalizer (P : Set (ModGL (langTag t) GGL)) ⊓
          Subgroup.normalizer (Pm : Set (ModGL (langTag t) GGL)) := by
      intro y hy
      rw [hΦfrob]
      exact frobTwistGL_one_mem_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
        (τ := langTag t) (K := GGL) 2 f hy
    obtain ⟨z', hz', hz'eq⟩ :=
      exists_eq_inv_mul_frobTwistGL (τ := langTag t) (k := GGL) (p := 2) (e := f) hf
        (1 : ModGL (langTag t) GGL) hconn hsm (by
          intro y hy
          rw [← hΦfrob]
          exact hΦZ y hy) hcZ
    rw [← hΦfrob] at hz'eq
    obtain ⟨⟨hz'A, hz'P⟩, hz'Pm⟩ := Subgroup.mem_inf.1 hz'
    refine ⟨g0⁻¹ * z' * g0, ?_, ?_⟩
    · have hzA : g0⁻¹ * z' * g0 ∈ A :=
        A.mul_mem (A.mul_mem (A.inv_mem hg0A) hz'A) hg0A
      have hzN0 : g0⁻¹ * z' * g0 ∈
          Subgroup.normalizer (V0 : Set (ModGL (langTag t) GGL)) :=
        (u1aE2_mem_normalizer_conj (g := g0⁻¹)).2 (by
          have h : g0⁻¹⁻¹ * (g0⁻¹ * z' * g0) * g0⁻¹ = z' := by group
          rw [h]
          exact hz'P)
      have hzNm0 : g0⁻¹ * z' * g0 ∈
          Subgroup.normalizer (Vm0 : Set (ModGL (langTag t) GGL)) :=
        (u1aE2_mem_normalizer_conj (g := g0⁻¹)).2 (by
          have h : g0⁻¹⁻¹ * (g0⁻¹ * z' * g0) * g0⁻¹ = z' := by group
          rw [h]
          exact hz'Pm)
      exact Subgroup.mem_inf.2 ⟨⟨hzA, hzN0⟩, hzNm0⟩
    · have hstep := congrArg (fun φ : ModGL (langTag t) GGL →* ModGL (langTag t) GGL => φ z')
        F.Δ.step_comp_conj_g0_inv
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv, F.Φ_eq] at hstep
      calc (g0⁻¹ * z' * g0)⁻¹ * F.Δ.step (g0⁻¹ * z' * g0)
          = g0⁻¹ * z'⁻¹ * g0 * (g0⁻¹ * F.Δ.Φ z' * g0) := by
            change (F.Δ.g0⁻¹ * z' * F.Δ.g0)⁻¹ *
              F.Δ.step (F.Δ.g0⁻¹ * z' * F.Δ.g0) =
              F.Δ.g0⁻¹ * z'⁻¹ * F.Δ.g0 * (F.Δ.g0⁻¹ * F.Δ.Φ z' * F.Δ.g0)
            rw [hstep, ← F.Φ_eq]
            group
        _ = g0⁻¹ * (z'⁻¹ * F.Δ.Φ z') * g0 := by group
        _ = g0⁻¹ * (g0 * c * g0⁻¹) * g0 := by rw [hz'eq]
        _ = c := by group
  obtain ⟨u, huA, hustep, huV0, huVm0⟩ :=
    exists_fixed_conj_eq_of_lang_pair
      F.Δ.step A V0 Vm0 hFA hLang hhA hstabplus hstabminus
  have huM : u ∈ M := Subgroup.mem_inf.2 ⟨huA, MonoidHom.mem_eqLocusM.2 hustep⟩
  have huV : V0.map (MulAut.conj u).toMonoidHom = V := by
    rw [huV0, ← hVeq]
  have huVm : Vm0.map (MulAut.conj u).toMonoidHom = Vm := by
    rw [huVm0, ← hVmeq]
  have hrA : g0 * u * g0⁻¹ ∈ A := A.mul_mem (A.mul_mem hg0A huA) (A.inv_mem hg0A)
  have huΦ : F.Δ.Φ u = F.Δ.n⁻¹ * u * F.Δ.n := by
    have h : F.Δ.n * F.Δ.Φ u * F.Δ.n⁻¹ = u := hustep
    calc F.Δ.Φ u = F.Δ.n⁻¹ * (F.Δ.n * F.Δ.Φ u * F.Δ.n⁻¹) * F.Δ.n := by group
      _ = F.Δ.n⁻¹ * u * F.Δ.n := by rw [h]
  have hrFix : Units.map (entrywiseHom (ggFrobT f)) (g0 * u * g0⁻¹) =
      g0 * u * g0⁻¹ := by
    rw [← hΦe]
    change F.Δ.Φ (F.Δ.g0 * u * F.Δ.g0⁻¹) = F.Δ.g0 * u * F.Δ.g0⁻¹
    rw [map_mul, map_mul, map_inv, F.Δ.lang]
    change F.Δ.g0 * F.Δ.n * F.Δ.Φ u * (F.Δ.g0 * F.Δ.n)⁻¹ = F.Δ.g0 * u * F.Δ.g0⁻¹
    rw [huΦ]
    group
  obtain ⟨a, u0, hu0, hr⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed (τ := langTag t) (K := K) (L := GGL)
      (Fr := ggFrobT f) hFr hrA hrFix
  let D : ModGL (langTag t) GGL :=
    baseChangeGL (algebraMap K GGL) (rootDiagUnit (langTag t) a)
  let s : ModGL (langTag t) GGL := g0⁻¹ * D * g0
  let γ : ModGL (langTag t) GGL := u * s⁻¹
  have hDfix : F.Δ.Φ D = D := by
    rw [hΦe]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap (k := K) (L := GGL)
      (Fr := ggFrobT f) hFr (rootDiagUnit (langTag t) a)
  have hrG : g0 * u * g0⁻¹ ∈ Gg := by
    change g0 * u * g0⁻¹ ∈ ggFixGp t f
    rw [ggFixGp, u1aE2_Phi_eq_entrywise ht f]
    exact Subgroup.mem_inf.2 ⟨hrA, MonoidHom.mem_eqLocusM.2 hrFix⟩
  have hbc_le : (adjointGroup (langTag t) K).map
      (baseChangeGL (algebraMap K GGL)) ≤ F.θ.range := by
    rw [F.range_θ]
    have hperf : ⁅adjointGroup (langTag t) K, adjointGroup (langTag t) K⁆ =
        adjointGroup (langTag t) K :=
      CFSG.TauCetiBridge.Even.commutator_adjointGroup_eq_of_singleEdge
        (langTag t) K (u1aE2_ht5 ht)
    have hle : (adjointGroup (langTag t) K).map (baseChangeGL (algebraMap K GGL)) ≤ Gg := by
      rintro x ⟨y, hy, rfl⟩
      change baseChangeGL (algebraMap K GGL) y ∈ ggFixGp t f
      rw [ggFixGp, u1aE2_Phi_eq_entrywise ht f]
      exact Subgroup.mem_inf.2 ⟨baseChangeGL_mem_adjointGroup _ hy, MonoidHom.mem_eqLocusM.2
        (units_map_entrywiseHom_baseChangeGL_algebraMap (k := K) (L := GGL)
          (Fr := ggFrobT f) hFr y)⟩
    calc (adjointGroup (langTag t) K).map (baseChangeGL (algebraMap K GGL))
        = (⁅adjointGroup (langTag t) K,
            adjointGroup (langTag t) K⁆).map (baseChangeGL (algebraMap K GGL)) := by
            rw [hperf]
      _ = ⁅(adjointGroup (langTag t) K).map (baseChangeGL (algebraMap K GGL)),
            (adjointGroup (langTag t) K).map (baseChangeGL (algebraMap K GGL))⁆ :=
            Subgroup.map_commutator (adjointGroup (langTag t) K)
              (adjointGroup (langTag t) K) (baseChangeGL (algebraMap K GGL))
      _ ≤ ⁅Gg, Gg⁆ := Subgroup.commutator_mono hle hle
  have hu0θ : u0 ∈ F.θ.range := hbc_le hu0
  have hu0G : u0 ∈ Gg := Subgroup.commutator_le_self (H := Gg) (F.range_θ ▸ hu0θ)
  have hDmemG : D ∈ Gg := by
    have hD : D = (g0 * u * g0⁻¹) * u0⁻¹ := by
      calc D = (D * u0) * u0⁻¹ := by group
        _ = (g0 * u * g0⁻¹) * u0⁻¹ := by rw [← hr]
    rw [hD]
    exact Gg.mul_mem hrG (Gg.inv_mem hu0G)
  have hDA : D ∈ A := by
    have h := hDmemG
    change D ∈ ggFixGp t f at h
    rw [ggFixGp] at h
    exact h.1
  have hsA : s ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hg0A) hDA) hg0A
  have hsstep : F.Δ.step s = s := by
    change F.Δ.step (g0⁻¹ * D * g0) = g0⁻¹ * D * g0
    have hstep := congrArg (fun φ : ModGL (langTag t) GGL →* ModGL (langTag t) GGL => φ D)
      F.Δ.step_comp_conj_g0_inv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, F.Φ_eq] at hstep
    rw [hstep, ← F.Φ_eq, hDfix]
  have hsM : s ∈ M := Subgroup.mem_inf.2 ⟨hsA, MonoidHom.mem_eqLocusM.2 hsstep⟩
  have hDU : P.map (MulAut.conj D).toMonoidHom = P := by
    rw [show D = rootDiagUnit (langTag t) (fun i => Units.map
        (algebraMap K GGL).toMonoidHom (a i)) from
      baseChangeGL_rootDiagUnit (algebraMap K GGL) a]
    exact map_conj_rootDiagUnit_rootSubgroup _ hθroot
  have hDUm : Pm.map (MulAut.conj D).toMonoidHom = Pm := by
    rw [show D = rootDiagUnit (langTag t) (fun i => Units.map
        (algebraMap K GGL).toMonoidHom (a i)) from
      baseChangeGL_rootDiagUnit (algebraMap K GGL) a]
    exact map_conj_rootDiagUnit_rootSubgroup _ (IsRoot.neg hθroot)
  have hsz : (MulAut.conj s).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
      (MulAut.conj g0⁻¹).toMonoidHom.comp (MulAut.conj D).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show g0⁻¹ * D * g0 * (g0⁻¹ * y * g0) * (g0⁻¹ * D * g0)⁻¹ =
      g0⁻¹ * (D * y * D⁻¹) * g0
    group
  have hsV0 : V0.map (MulAut.conj s).toMonoidHom = V0 := by
    calc V0.map (MulAut.conj s).toMonoidHom
        = (P.map (MulAut.conj g0⁻¹).toMonoidHom).map
            (MulAut.conj s).toMonoidHom := by rw [hV0map]
      _ = P.map ((MulAut.conj s).toMonoidHom.comp
            (MulAut.conj g0⁻¹).toMonoidHom) := Subgroup.map_map _ _ _
      _ = P.map ((MulAut.conj g0⁻¹).toMonoidHom.comp
            (MulAut.conj D).toMonoidHom) := by rw [hsz]
      _ = (P.map (MulAut.conj D).toMonoidHom).map
            (MulAut.conj g0⁻¹).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = P.map (MulAut.conj g0⁻¹).toMonoidHom := by rw [hDU]
      _ = V0 := hV0map.symm
  have hsVm0 : Vm0.map (MulAut.conj s).toMonoidHom = Vm0 := by
    calc Vm0.map (MulAut.conj s).toMonoidHom
        = (Pm.map (MulAut.conj g0⁻¹).toMonoidHom).map
            (MulAut.conj s).toMonoidHom := by rw [hVm0map]
      _ = Pm.map ((MulAut.conj s).toMonoidHom.comp
            (MulAut.conj g0⁻¹).toMonoidHom) := Subgroup.map_map _ _ _
      _ = Pm.map ((MulAut.conj g0⁻¹).toMonoidHom.comp
            (MulAut.conj D).toMonoidHom) := by rw [hsz]
      _ = (Pm.map (MulAut.conj D).toMonoidHom).map
            (MulAut.conj g0⁻¹).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ = Pm.map (MulAut.conj g0⁻¹).toMonoidHom := by rw [hDUm]
      _ = Vm0 := hVm0map.symm
  have hsV0inv : V0.map (MulAut.conj s⁻¹).toMonoidHom = V0 := by
    calc V0.map (MulAut.conj s⁻¹).toMonoidHom
        = (V0.map (MulAut.conj s).toMonoidHom).map
            (MulAut.conj s⁻¹).toMonoidHom := by rw [hsV0]
      _ = V0.map ((MulAut.conj s⁻¹).toMonoidHom.comp
            (MulAut.conj s).toMonoidHom) := Subgroup.map_map _ _ _
      _ = V0.map (MonoidHom.id (ModGL (langTag t) GGL)) := by
            have e : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
                MonoidHom.id (ModGL (langTag t) GGL) := by
              refine MonoidHom.ext fun y => ?_
              simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
                MulAut.conj_apply]
              group
            rw [e]
      _ = V0 := Subgroup.map_id _
  have hsVm0inv : Vm0.map (MulAut.conj s⁻¹).toMonoidHom = Vm0 := by
    calc Vm0.map (MulAut.conj s⁻¹).toMonoidHom
        = (Vm0.map (MulAut.conj s).toMonoidHom).map
            (MulAut.conj s⁻¹).toMonoidHom := by rw [hsVm0]
      _ = Vm0.map ((MulAut.conj s⁻¹).toMonoidHom.comp
            (MulAut.conj s).toMonoidHom) := Subgroup.map_map _ _ _
      _ = Vm0.map (MonoidHom.id (ModGL (langTag t) GGL)) := by
            have e : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
                MonoidHom.id (ModGL (langTag t) GGL) := by
              refine MonoidHom.ext fun y => ?_
              simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
                MulAut.conj_apply]
              group
            rw [e]
      _ = Vm0 := Subgroup.map_id _
  have hγA : γ ∈ A := A.mul_mem huA (A.inv_mem hsA)
  have hγM : γ ∈ M := M.mul_mem huM (M.inv_mem hsM)
  have hγcomp : (MulAut.conj γ).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show u * s⁻¹ * y * (u * s⁻¹)⁻¹ = u * (s⁻¹ * y * (s⁻¹)⁻¹) * u⁻¹
    group
  have hγV : V0.map (MulAut.conj γ).toMonoidHom = V := by
    rw [hγcomp, ← Subgroup.map_map, hsV0inv, huV]
  have hγVm : Vm0.map (MulAut.conj γ).toMonoidHom = Vm := by
    rw [hγcomp, ← Subgroup.map_map, hsVm0inv, huVm]
  have hγθrange : g0 * γ * g0⁻¹ ∈ F.θ.range := by
    have hsr : g0 * s * g0⁻¹ = D := by
      change g0 * (g0⁻¹ * D * g0) * g0⁻¹ = D
      group
    have h1 : g0 * γ * g0⁻¹ = D * u0 * D⁻¹ := by
      have e : g0 * γ * g0⁻¹ = (g0 * u * g0⁻¹) * (g0 * s * g0⁻¹)⁻¹ := by
        show g0 * (u * s⁻¹) * g0⁻¹ = (g0 * u * g0⁻¹) * (g0 * s * g0⁻¹)⁻¹
        group
      rw [e, hr, hsr]
    have hu0c : u0 ∈ ⁅Gg, Gg⁆ := F.range_θ ▸ hu0θ
    have hDc : D ∈ Gg := hDmemG
    rw [h1, F.range_θ]
    have hcomm : ⁅D, u0⁆ ∈ ⁅Gg, Gg⁆ :=
      Subgroup.commutator_mem_commutator hDmemG hu0G
    have hDu : D * u0 * D⁻¹ = ⁅D, u0⁆ * u0 := by
      rw [commutatorElement_def]
      group
    rw [hDu]
    exact (⁅Gg, Gg⁆).mul_mem hcomm hu0c
  have hηrange : F.η.range = F.θ.range.map (MulAut.conj g0⁻¹).toMonoidHom := by
    have hη : F.η = (MulAut.conj g0⁻¹).toMonoidHom.comp F.θ :=
      MonoidHom.ext fun y => F.η_eq y
    rw [hη, MonoidHom.range_comp]
  have hγrange : γ ∈ F.η.range := by
    rw [hηrange]
    exact Subgroup.mem_map.2 ⟨g0 * γ * g0⁻¹, hγθrange, by
      show g0⁻¹ * (g0 * γ * g0⁻¹) * g0 = γ
      group⟩
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hγrange
  have hyG : (y : X) ∈ ψ.range := hψ.symm ▸ y.2
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hyG
  have hηψk : ηψ k = γ := by
    show F.η (ψ0 k) = γ
    rw [show ψ0 k = y from Subtype.ext hk]
    exact hy
  have hLHS : ((ggRootSub (ggU t n f).D ψ β k).subgroupOf G₀).map F.η =
      (((ggU t n f).D.rootGroup β).map (MulAut.conj k).toMonoidHom).map ηψ :=
    F.map_rootSub_eq_map_codRestrict hψ β k
  have hLHSm : ((ggRootSub (ggU t n f).D ψ (-β) k).subgroupOf G₀).map F.η =
      (((ggU t n f).D.rootGroup (-β)).map (MulAut.conj k).toMonoidHom).map ηψ :=
    F.map_rootSub_eq_map_codRestrict hψ (-β) k
  have hcomp_k : (MulAut.conj γ).toMonoidHom.comp ηψ =
      ηψ.comp (MulAut.conj k).toMonoidHom := by
    refine MonoidHom.ext fun y' => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, hηψk]
  have hVM : V ⊓ M = (V0 ⊓ M).map (MulAut.conj γ).toMonoidHom := by
    calc V ⊓ M = (V0.map (MulAut.conj γ).toMonoidHom) ⊓ M := by rw [hγV]
      _ = (V0 ⊓ M).map (MulAut.conj γ).toMonoidHom := u1aE2_map_conj_inf_eq hγM
  have hVMm : Vm ⊓ M = (Vm0 ⊓ M).map (MulAut.conj γ).toMonoidHom := by
    calc Vm ⊓ M = (Vm0.map (MulAut.conj γ).toMonoidHom) ⊓ M := by rw [hγVm]
      _ = (Vm0 ⊓ M).map (MulAut.conj γ).toMonoidHom := u1aE2_map_conj_inf_eq hγM
  have hPGeq : P ⊓ Gg = (rootSubgroup (langTag t) K θ).map
      (bcGL (algebraMap K GGL)) := by
    have hPleA : P ≤ A := rootSubgroup_le_adjointGroup θ
    have hfix : P ⊓ Gg = P ⊓ (Units.map (entrywiseHom (ggFrobT f))).eqLocus
        (MonoidHom.id (ModGL (langTag t) GGL)) := by
      change P ⊓ ggFixGp t f = _
      rw [ggFixGp, u1aE2_Phi_eq_entrywise ht f, ← inf_assoc, inf_eq_left.2 hPleA]
    rw [hfix, ← rootSubgroup_map_bcGL_eq_fixed
      (τ := langTag t) (K := K) (Ω := GGL) (Fr := ggFrobT f) hFr θ]
  have hcardV0M : Nat.card ↥(V0 ⊓ M) = Nat.card K := by
    rw [hV0Mmap, Subgroup.card_map_of_injective (MulAut.conj g0⁻¹).injective,
      hPGeq, card_map_bcGL_rootSubgroup (τ := langTag t) (K := K) (Ω := GGL)
        (Fr := ggFrobT f) hFr θ]
  have hcardVm0M : Nat.card ↥(Vm0 ⊓ M) = Nat.card K := by
    rw [hVm0Mmap, Subgroup.card_map_of_injective (MulAut.conj g0⁻¹).injective]
    have hPmeq : Pm ⊓ Gg = (rootSubgroup (langTag t) K (-θ)).map
        (bcGL (algebraMap K GGL)) := by
      have hPleA : Pm ≤ A := rootSubgroup_le_adjointGroup (-θ)
      have hfix : Pm ⊓ Gg = Pm ⊓ (Units.map (entrywiseHom (ggFrobT f))).eqLocus
          (MonoidHom.id (ModGL (langTag t) GGL)) := by
        change Pm ⊓ ggFixGp t f = _
        rw [ggFixGp, u1aE2_Phi_eq_entrywise ht f, ← inf_assoc, inf_eq_left.2 hPleA]
      rw [hfix, ← rootSubgroup_map_bcGL_eq_fixed
        (τ := langTag t) (K := K) (Ω := GGL) (Fr := ggFrobT f) hFr (-θ)]
    rw [hPmeq, card_map_bcGL_rootSubgroup (τ := langTag t) (K := K) (Ω := GGL)
      (Fr := ggFrobT f) hFr (-θ)]
  have hfinal : ((ggRootSub (ggU t n f).D ψ β k).subgroupOf G₀).map F.η = V ⊓ M := by
    rw [hLHS]
    calc (((ggU t n f).D.rootGroup β).map (MulAut.conj k).toMonoidHom).map ηψ
        = ((ggU t n f).D.rootGroup β).map
            (ηψ.comp (MulAut.conj k).toMonoidHom) :=
            Subgroup.map_map ((ggU t n f).D.rootGroup β) ηψ
              (MulAut.conj k).toMonoidHom
      _ = ((ggU t n f).D.rootGroup β).map
            ((MulAut.conj γ).toMonoidHom.comp ηψ) := by rw [hcomp_k]
      _ = (((ggU t n f).D.rootGroup β).map ηψ).map
            (MulAut.conj γ).toMonoidHom :=
            (Subgroup.map_map ((ggU t n f).D.rootGroup β)
              (MulAut.conj γ).toMonoidHom ηψ).symm
      _ = (V0 ⊓ M).map (MulAut.conj γ).toMonoidHom := by rw [← hV0M]
      _ = V ⊓ M := hVM.symm
  have hfinalm : ((ggRootSub (ggU t n f).D ψ (-β) k).subgroupOf G₀).map F.η = Vm ⊓ M := by
    rw [hLHSm]
    calc (((ggU t n f).D.rootGroup (-β)).map (MulAut.conj k).toMonoidHom).map ηψ
        = ((ggU t n f).D.rootGroup (-β)).map
            (ηψ.comp (MulAut.conj k).toMonoidHom) :=
            Subgroup.map_map ((ggU t n f).D.rootGroup (-β)) ηψ
              (MulAut.conj k).toMonoidHom
      _ = ((ggU t n f).D.rootGroup (-β)).map
            ((MulAut.conj γ).toMonoidHom.comp ηψ) := by rw [hcomp_k]
      _ = (((ggU t n f).D.rootGroup (-β)).map ηψ).map
            (MulAut.conj γ).toMonoidHom :=
            (Subgroup.map_map ((ggU t n f).D.rootGroup (-β))
              (MulAut.conj γ).toMonoidHom ηψ).symm
      _ = (Vm0 ⊓ M).map (MulAut.conj γ).toMonoidHom := by rw [← hVm0M]
      _ = Vm ⊓ M := hVMm.symm
  have hcard : Nat.card ↥(V ⊓ M) = Nat.card K := by
    rw [hVM, Subgroup.card_map_of_injective (MulAut.conj γ).injective, hcardV0M]
  have hcardm : Nat.card ↥(Vm ⊓ M) = Nat.card K := by
    rw [hVMm, Subgroup.card_map_of_injective (MulAut.conj γ).injective, hcardVm0M]
  exact ⟨β, k, hβmem, hβlong, hfinal, hfinalm, hcard, hcardm⟩

end CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame
