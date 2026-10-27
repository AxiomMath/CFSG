module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Conjugation

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel

structure ExcLangFrame
    (t : StatedLieTag) {X : Type} [Group X] (n f p : ℕ) (ψ : (ggU t n f).K →* X)
    (G₀ B₁ D : Subgroup X) (x : X) : Type where
  one_le_f : 1 ≤ f
  θ : ↥G₀ →* ModGL (langTag t) GGL
  ker_θ : θ.ker = Subgroup.center ↥G₀
  range_θ : θ.range = ⁅ggFixGp t f, ggFixGp t f⁆
  θ_iota : ∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f one_le_f k
  Δ : LangDatum (langTag t) GGL
  Φ_eq : Δ.Φ = ggPhi t f
  q_eq : Δ.q = 2 ^ f
  ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)
  frob : FrobRootMap Δ ρ
  finite : Finite Δ.model
  η : ↥G₀ →* ModGL (langTag t) GGL
  η_eq : ∀ y, η y = Δ.g0⁻¹ * θ y * Δ.g0
  range_η : η.range = Δ.Γ
  Θ : ↥B₁ →* ModGL (langTag t) GGL
  Θ_mem : ∀ b, Θ b ∈ Δ.model
  Θ_eq_one : ∀ b : ↥B₁, Θ b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X)
  η_conj : ∀ (b : ↥B₁) (g g' : ↥G₀), (g' : X) = b * g * (b : X)⁻¹ →
    η g' = Θ b * η g * (Θ b)⁻¹
  coord : X → Fin (langTag t).rank → GGLˣ
  Θ_eq_coord : ∀ b : ↥B₁, (b : X) ∈ D → Θ b = rootDiagUnit (langTag t) (coord b)
  coord_pow : ∀ e ∈ D, ∀ i, coord e i ^ p = 1
  coord_torus : ∀ e ∈ D, rootDiagUnit (langTag t) (coord e) ∈ Δ.torus
  d : X
  d_mem : d ∈ D
  closure_eq : Subgroup.closure ({x, d} : Set X) = D

namespace ExcLangFrame

variable
  {t : StatedLieTag} {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU t n f).K →* X}
  {G₀ B₁ D : Subgroup X} {x : X}

@[expose] def chiD (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    Multiplicative (Fin (langTag t).rank → ℤ) →* GGLˣ × GGLˣ :=
  LieCore.jointChar (F.coord x) (F.coord F.d)

theorem ker_η (F : ExcLangFrame t n f p ψ G₀ B₁ D x) : F.η.ker = Subgroup.center ↥G₀ := by
  rw [← F.ker_θ]
  ext g
  simp only [MonoidHom.mem_ker]
  rw [F.η_eq]
  constructor
  · intro h
    have := congrArg (fun z => F.Δ.g0 * z * F.Δ.g0⁻¹) h
    simpa [mul_assoc] using this
  · intro h
    rw [h]
    simp

theorem map_rootSub_eq_map_codRestrict (F : ExcLangFrame t n f p ψ G₀ B₁ D x)
    (hψ : ψ.range = G₀) (γ : Fin (ggU t n f).D.rank → ℤ) (k : (ggU t n f).K) :
    ((ggRootSub (ggU t n f).D ψ γ k).subgroupOf G₀).map F.η =
      (((ggU t n f).D.rootGroup γ).map (MulAut.conj k).toMonoidHom).map
        (F.η.comp (ψ.codRestrict G₀ (fun y => hψ ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩))) := by
  let ψ₀ : (ggU t n f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun y => hψ ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
  change _ = (((ggU t n f).D.rootGroup γ).map (MulAut.conj k).toMonoidHom).map (F.η.comp ψ₀)
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : X) ∈ ggRootSub (ggU t n f).D ψ γ k :=
      Subgroup.mem_subgroupOf.1 hg
    rw [ggRootSub] at hg'
    obtain ⟨y, hy, hψy⟩ := Subgroup.mem_map.1 hg'
    exact ⟨y, hy, congrArg F.η (Subtype.ext hψy)⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨ψ₀ ((MulAut.conj k) u), Subgroup.mem_subgroupOf.2 (by
      rw [ggRootSub]
      exact Subgroup.mem_map_of_mem ψ
        (Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hu)), rfl⟩

theorem coord_ne_one [Finite X] {J L : Subgroup X}
    (h : ClassicalPosition.GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    (F : ExcLangFrame t n f p ψ G₀ B₁ D x) :
    rootDiagUnit (langTag t) (F.coord x) ≠ 1 ∨ rootDiagUnit (langTag t) (F.coord F.d) ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hDB1, -, -, -, -, -, hx, -, hLG0, -, -,
    hDnotc, -, -, -, -, -, -, -, -, -⟩ := h
  by_contra hcon
  push Not at hcon
  obtain ⟨htx, htd⟩ := hcon
  apply hDnotc
  rw [← F.closure_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (hy | hy)
  · rw [hy]
    have hxG0 : x ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [← F.Θ_eq_one ⟨x, hDB1 hx⟩, F.Θ_eq_coord ⟨x, hDB1 hx⟩ hx]
      exact htx
    exact Subgroup.centralizer_le hLG0 hxG0
  · rw [hy]
    have hdG0 : F.d ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [← F.Θ_eq_one ⟨F.d, hDB1 F.d_mem⟩, F.Θ_eq_coord ⟨F.d, hDB1 F.d_mem⟩ F.d_mem]
      exact htd
    exact Subgroup.centralizer_le hLG0 hdG0

end ExcLangFrame

end CFSG.StandardType.LieKnownR2.ExcPos

end
