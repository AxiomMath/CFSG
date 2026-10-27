module

public import CFSG.LocalAnalysis.StandardType.ExcPos.LangFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeComp
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGFamComponent

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.ClassicalPosition


theorem attach_J {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map F.η)
      (F.Δ.Γ ⊓ Subgroup.centralizer ({rootDiagUnit (langTag t) (F.coord x),
        rootDiagUnit (langTag t) (F.coord F.d)} : Set (ModGL (langTag t) GGL))) := by
  obtain ⟨-, -, -, -, -, -, hB1N, -, -, -, hDB1, -, -, -, hJcomp, -, hx, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -⟩ := h
  have hker : F.η.ker = Subgroup.center ↥G₀ := by
    rw [← F.ker_θ]
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hy
      have h := F.η_eq y
      rw [hy] at h
      have h' := congrArg (fun t => F.Δ.g0 * t * F.Δ.g0⁻¹) h
      have h'' : F.θ y = 1 := by simpa [mul_assoc] using h'.symm
      exact h''
    · intro hy
      rw [F.η_eq, hy]
      simp
  let φ : ↥D →* ModGL (langTag t) GGL := F.Θ.comp (Subgroup.inclusion hDB1)
  let A : Subgroup (ModGL (langTag t) GGL) :=
    Subgroup.closure ({rootDiagUnit (langTag t) (F.coord x),
      rootDiagUnit (langTag t) (F.coord F.d)} : Set (ModGL (langTag t) GGL))
  have hφx : φ ⟨x, hx⟩ = rootDiagUnit (langTag t) (F.coord x) :=
    F.Θ_eq_coord ⟨x, hDB1 hx⟩ hx
  have hφd : φ ⟨F.d, F.d_mem⟩ = rootDiagUnit (langTag t) (F.coord F.d) :=
    F.Θ_eq_coord ⟨F.d, hDB1 F.d_mem⟩ F.d_mem
  have htop : (⊤ : Subgroup ↥D) =
      Subgroup.closure ({⟨x, hx⟩, ⟨F.d, F.d_mem⟩} : Set ↥D) := by
    apply Subgroup.map_injective (f := D.subtype) D.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure]
    simp only [Set.image_pair, Subgroup.coe_subtype]
    exact F.closure_eq.symm
  have hA : A = (⊤ : Subgroup ↥D).map φ := by
    rw [htop, MonoidHom.map_closure]
    simp only [Set.image_pair, Subgroup.coe_subtype, hφx, hφd]
    rfl
  have h₁ : ∀ d ∈ D, ∃ a ∈ A, LieCore.GGLiePartner G₀ F.η d a := by
    intro d hd
    refine ⟨rootDiagUnit (langTag t) (F.coord d), ?_, ?_⟩
    · rw [hA]
      exact Subgroup.mem_map.mpr ⟨⟨d, hd⟩, Subgroup.mem_top _,
        F.Θ_eq_coord ⟨d, hDB1 hd⟩ hd⟩
    · intro y hy
      have h := F.η_conj ⟨d, hDB1 hd⟩ y ⟨d * (y : X) * d⁻¹, hy⟩ rfl
      rw [F.Θ_eq_coord ⟨d, hDB1 hd⟩ hd] at h
      exact h
  have h₂ : ∀ a ∈ A, ∃ d ∈ D, LieCore.GGLiePartner G₀ F.η d a := by
    intro a ha
    rw [hA] at ha
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨d, d.2, ?_⟩
    intro y hy
    have h := F.η_conj ⟨d, hDB1 d.2⟩ y ⟨d * (y : X) * d⁻¹, hy⟩ rfl
    change F.η ⟨↑d * ↑y * (↑d)⁻¹, hy⟩ =
      F.Θ ⟨d, hDB1 d.2⟩ * F.η y * (F.Θ ⟨d, hDB1 d.2⟩)⁻¹
    rw [F.Θ_eq_coord ⟨d, hDB1 d.2⟩ d.2] at h ⊢
    exact h
  have hcomp := LieCore.ggLieBridge_component G₀ D J F.Δ.Γ A F.η hker F.range_η
    (fun d hd => hB1N (hDB1 hd)) h₁ h₂ hJcomp
  simpa only [A, Subgroup.centralizer_closure] using hcomp


theorem attach_nbr_of {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (hB1N : B₁ ≤ Subgroup.normalizer (G₀ : Set X)) (hDB1 : D ≤ B₁)
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    ∀ e ∈ D, ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) →
      CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map F.η)
        (F.Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit (langTag t) (F.coord e)}) := by
  have hker : F.η.ker = Subgroup.center ↥G₀ := by
    rw [← F.ker_θ]
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hy
      have h := F.η_eq y
      rw [hy] at h
      have h' := congrArg (fun t => F.Δ.g0 * t * F.Δ.g0⁻¹) h
      have h'' : F.θ y = 1 := by simpa [mul_assoc] using h'.symm
      exact h''
    · intro hy
      rw [F.η_eq, hy]
      simp
  intro e he K hKG0 hK
  have hK' : CFSG.Assembly.IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hK (fun x hx => ⟨hKG0 hx, hK.1 hx⟩) inf_le_right
  have hdN : e ∈ Subgroup.normalizer (G₀ : Set X) := hB1N (hDB1 he)
  have hpart : LieCore.GGLiePartner G₀ F.η e (rootDiagUnit (langTag t) (F.coord e)) := by
    intro y hy
    have h := F.η_conj ⟨e, hDB1 he⟩ y ⟨e * (y : X) * e⁻¹, hy⟩ rfl
    rw [F.Θ_eq_coord ⟨e, hDB1 he⟩ he] at h
    exact h
  exact LieCore.ggLieBridge_component_of_partner G₀ K F.Δ.Γ F.η hker F.range_η hdN hpart hK'

theorem attach_nbr {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    ∀ e ∈ D, ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) →
      CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map F.η)
        (F.Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit (langTag t) (F.coord e)}) := by
  obtain ⟨-, -, -, -, -, -, hB1N, -, -, -, hDB1, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -⟩ := h
  exact attach_nbr_of hB1N hDB1 F

section

theorem exists_ratComp_eq {t : StatedLieTag}
    (hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8) {X : Type}
    [Group X] [Finite X] {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    ∃ iJ : KernelComponent F.chiD,
      (J.subgroupOf G₀).map F.η = LieCore.ratComp F.ρ F.Δ.Γ (componentRoots F.chiD iJ) := by
  have hh : GGSixPosHyp t n f ψ p G₀ B₁ D J L x := h
  obtain ⟨-, -, -, -, hp, hp2, -, -, -, -, -, -, -, -, -, -, hx, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -⟩ := h
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum F.Δ F.ρ F.frob F.finite
    F.one_le_f F.q_eq
  let a : Fin 2 → Fin (langTag t).rank → GGLˣ := ![F.coord x, F.coord F.d]
  have hT : ∀ u : Fin 2, rootDiagUnit (langTag t) (a u) ∈ S.D.torus := by
    intro u
    rw [hSD]
    fin_cases u
    · simpa [a] using F.coord_torus x hx
    · simpa [a] using F.coord_torus F.d F.d_mem
  have hap : ∀ u j, a u j ^ p = 1 := by
    intro u
    fin_cases u
    · simpa [a] using F.coord_pow x hx
    · simpa [a] using F.coord_pow F.d F.d_mem
  have h1 : ∃ u : Fin 2, rootDiagUnit (langTag t) (a u) ≠ 1 := by
    rcases F.coord_ne_one hh with hne | hne
    · exact ⟨0, by simpa [a] using hne⟩
    · exact ⟨1, by simpa [a] using hne⟩
  have hTame : ∀ i : KernelComponent (TableCRes.famCharHom a),
      CFSG.IsQuasisimple (TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i) ∨
        Group.IsSolvable (TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i) :=
    fun i => TableCRes.langFamTame_of_prime hτ S hp hp2 hT hap h1 i
  have hJ' : CFSG.Open.IsComponentOf ((J.subgroupOf G₀).map F.η)
      (S.Γ ⊓ Subgroup.centralizer
        (Set.range fun u : Fin 2 => rootDiagUnit (langTag t) (a u))) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open]
    have hJ := attach_J hh F
    change CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map F.η)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : Fin 2 =>
        rootDiagUnit (langTag t) (![F.coord x, F.coord F.d] u)))
    rw [LangSetup.Γ, hSD]
    rw [← LieCore.centralizer_closure_pair_eq_range (τ := langTag t)
      (F.coord x) (F.coord F.d)]
    rw [Subgroup.centralizer_closure]
    exact hJ
  obtain ⟨i', hi', -⟩ := TableCRes.exists_eq_rationalComponentM_of_isComponentOf
    S hp hτ hp2 hT hap h1 hTame hJ'
  obtain ⟨i, hi⟩ := LieCore.exists_jointComponent_of_famCharHom (F.coord x) (F.coord F.d) i'
  change ∃ iJ : KernelComponent (LieCore.jointChar (F.coord x) (F.coord F.d)),
    (J.subgroupOf G₀).map F.η = LieCore.ratComp F.ρ F.Δ.Γ
      (componentRoots (LieCore.jointChar (F.coord x) (F.coord F.d)) iJ)
  refine ⟨i, ?_⟩
  rw [hi']
  rw [LieCore.ratComp_eq_rationalComponentM]
  have hcomp : TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) i' =
      TableCRes.rationalComponentM F.ρ F.Δ.Γ
        (LieCore.jointChar (F.coord x) (F.coord F.d)) i := by
    rw [hSρ, LangSetup.Γ, hSD]
    unfold TableCRes.rationalComponentM TableCRes.rationalSpanM TableCRes.rationalRootsM
    rw [hi]
  exact hcomp


end

end CFSG.StandardType.LieKnownR2.ExcPos.ExcLangFrame
