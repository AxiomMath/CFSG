module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairOneAssembly
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootLangTransitive
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def TwE6LongRootStmt : Prop :=
  ∀ n f : ℕ, ∃ β : Fin (ggU .twistedE6 n f).D.rank → ℤ, β ∈ (ggU .twistedE6 n f).D.roots ∧
    (-β) ∈ (ggU .twistedE6 n f).D.roots ∧ GGLongRoot (ggU .twistedE6 n f).D β

@[expose] def TwE6StdPairStmt : Prop :=
  ∀ {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (_hB : TwE6BaseCompat n f p ψ B) (_hψr : ψ.range = G₀)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (_hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (_hβn : (-β) ∈ (ggU .twistedE6 n f).D.roots) (_hlong : GGLongRoot (ggU .twistedE6 n f).D β),
    ∃ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a ∧
      (excCurve a B.Δ.g0⁻¹).map B.Δ.step = excCurve a B.Δ.g0⁻¹ ∧
      (excCurve (-a) B.Δ.g0⁻¹).map B.Δ.step = excCurve (-a) B.Δ.g0⁻¹ ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ β 1).subgroupOf G₀).map B.η =
        excCurve a B.Δ.g0⁻¹ ⊓ B.Δ.model ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ (-β) 1).subgroupOf G₀).map B.η =
        excCurve (-a) B.Δ.g0⁻¹ ⊓ B.Δ.model ∧
      Nat.card ↥(excCurve a B.Δ.g0⁻¹ ⊓ B.Δ.model) = Nat.card (GaloisField 2 f) ∧
      Nat.card ↥(excCurve (-a) B.Δ.g0⁻¹ ⊓ B.Δ.model) = Nat.card (GaloisField 2 f)

@[expose] def TwE6ModelDecompStmt : Prop :=
  ∀ {X : Type} [Group X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (_hB : TwE6BaseCompat n f p ψ B) (_hψr : ψ.range = G₀)
    (a : Fin Tag.E6.rank → ℤ) (_ha : IsRoot Tag.E6 a),
    ∀ h ∈ B.Δ.model, ∃ t ∈ B.Δ.model, ∃ γ ∈ B.Δ.Γ, h = t * γ ∧
      (excCurve a B.Δ.g0⁻¹).map (MulAut.conj t).toMonoidHom = excCurve a B.Δ.g0⁻¹ ∧
      (excCurve (-a) B.Δ.g0⁻¹).map (MulAut.conj t).toMonoidHom = excCurve (-a) B.Δ.g0⁻¹

theorem map_eta_conj {X : Type} [Group X] {G₀ : Subgroup X} {H : Type} [Group H] (η : ↥G₀ →* H)
    (R : Subgroup X) (g : ↥G₀) :
    ((R.map (MulAut.conj (g : X)).toMonoidHom).subgroupOf G₀).map η =
      ((R.subgroupOf G₀).map η).map (MulAut.conj (η g)).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulAut.conj_apply,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨r, hr, hry⟩, rfl⟩
    refine ⟨η ⟨(g : X)⁻¹ * (y : X) * (g : X), ?_⟩, ⟨⟨(g : X)⁻¹ * (y : X) * (g : X), ?_⟩, ?_, rfl⟩, ?_⟩
    · exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem g.2) y.2) g.2
    · exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem g.2) y.2) g.2
    · show (g : X)⁻¹ * (y : X) * (g : X) ∈ R
      have : (g : X)⁻¹ * (y : X) * (g : X) = r := by
        rw [← hry]
        group
      rw [this]
      exact hr
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp
      group
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, ⟨(y : X), hy, ?_⟩, ?_⟩
    · simp
    · simp

theorem ggRootSub_eq_conj_map {U X : Type} [Group U] [Group X] (Δ : UniversalRootDatum U)
    (ψ : U →* X) (γ : Fin Δ.rank → ℤ) (u : U) :
    ggRootSub Δ ψ γ u = (ggRootSub Δ ψ γ 1).map (MulAut.conj (ψ u)).toMonoidHom := by
  unfold ggRootSub
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem map_conj_inv_inf_eq {M : Type*} [Group M] {model : Subgroup M} {Vs V : Subgroup M}
    {h t γ : M} (hht : h = t * γ) (ht : t ∈ model) (hγ : γ ∈ model)
    (hconj : V.map (MulAut.conj h).toMonoidHom = Vs)
    (htn : Vs.map (MulAut.conj t).toMonoidHom = Vs) :
    (Vs ⊓ model).map (MulAut.conj γ⁻¹).toMonoidHom = V ⊓ model := by
  have hV1 : ∀ x ∈ V, h * x * h⁻¹ ∈ Vs := fun x hx => by
    rw [← hconj]
    exact ⟨x, hx, rfl⟩
  have hV2 : ∀ x, h * x * h⁻¹ ∈ Vs → x ∈ V := by
    intro x hx
    rw [← hconj] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    have h2 : h * x' * h⁻¹ = h * x * h⁻¹ := hxx
    have : x' = x := by simpa using h2
    exact this ▸ hx'
  have hT1 : ∀ y ∈ Vs, t * y * t⁻¹ ∈ Vs := fun y hy => by
    rw [← htn]
    exact ⟨y, hy, rfl⟩
  have hT2 : ∀ y, t * y * t⁻¹ ∈ Vs → y ∈ Vs := by
    intro y hy
    rw [← htn] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have h2 : t * y' * t⁻¹ = t * y * t⁻¹ := hyy
    have : y' = y := by simpa using h2
    exact this ▸ hy'
  ext x
  constructor
  · rintro ⟨y, ⟨hyV, hym⟩, rfl⟩
    have e : (MulAut.conj γ⁻¹).toMonoidHom y = γ⁻¹ * y * γ := by simp
    have hyV' : y ∈ Vs := hyV
    refine ⟨?_, ?_⟩
    · apply hV2
      have : h * ((MulAut.conj γ⁻¹).toMonoidHom y) * h⁻¹ = t * y * t⁻¹ := by
        rw [e, hht]
        group
      rw [this]
      exact hT1 y hyV'
    · rw [e]
      exact model.mul_mem (model.mul_mem (model.inv_mem hγ) hym) hγ
  · rintro ⟨hxV, hxm⟩
    have hxV' : x ∈ V := hxV
    refine ⟨γ * x * γ⁻¹, ⟨?_, ?_⟩, ?_⟩
    · apply hT2
      have e : t * (γ * x * γ⁻¹) * t⁻¹ = h * x * h⁻¹ := by
        rw [hht]
        group
      rw [e]
      exact hV1 x hxV'
    · exact model.mul_mem (model.mul_mem hγ hxm) (model.inv_mem hγ)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem twE6RootTransport_of_pieces (hlongR : TwE6LongRootStmt) (hstdP : TwE6StdPairStmt)
    (hdec : TwE6ModelDecompStmt) : TwE6RootTransport := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos B hB hb α w hα hw hV hVm
  have hψr : ψ.range = G₀ := hpos.1
  obtain ⟨β, hβ, hβn, hlong⟩ := hlongR n f
  obtain ⟨a, ha, hVs, hVms, hstd, hstdm, hcard, hcardm⟩ :=
    hstdP B hB hψr hβ hβn hlong
  have hαroot : IsRoot Tag.E6 α := by
    obtain ⟨hk, -⟩ := hα
    exact hk.1
  have hwA : w ∈ adjointGroup Tag.E6 GGL :=
    sup_le (CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup)
      (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL _) hw
  have hg0 : B.Δ.g0⁻¹ ∈ adjointGroup Tag.E6 GGL := inv_mem B.Δ.g0_mem
  have hq : B.Δ.q = 2 ^ f := by
    rw [B.hq]
    exact GaloisField.card 2 f (by have := B.one_le_f; omega)
  obtain ⟨h, hh, hc1, hc2⟩ :=
    exists_conj_stableOppositePair B.one_le_f B.Δ hq hαroot ha hwA hg0 hV hVm hVs hVms
  obtain ⟨t, ht, γ, hγ, hhtγ, htn, htnm⟩ := hdec B hB hψr a ha h hh
  have hΓmodel : B.Δ.Γ ≤ B.Δ.model :=
    Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
        (Subgroup.inv_mem _ h₂)
  obtain ⟨g, hg⟩ : γ ∈ B.η.range := B.range_η ▸ hγ
  obtain ⟨u₀, hu₀⟩ : (g : X) ∈ ψ.range := hψr ▸ g.2
  have hψu : ψ u₀⁻¹ ∈ G₀ := hψr ▸ ⟨u₀⁻¹, rfl⟩
  have hgu : (⟨ψ u₀⁻¹, hψu⟩ : ↥G₀) = g⁻¹ := by
    apply Subtype.ext
    simp [hu₀]
  have hψe : ψ u₀⁻¹ = ((g⁻¹ : ↥G₀) : X) := congrArg Subtype.val hgu
  have key : ∀ (γ' : Fin (ggU .twistedE6 n f).D.rank → ℤ) (a' : Fin Tag.E6.rank → ℤ)
      (Vc : Subgroup (ModGL Tag.E6 GGL)),
      ((ggRootSub (ggU .twistedE6 n f).D ψ γ' 1).subgroupOf G₀).map B.η =
        excCurve a' B.Δ.g0⁻¹ ⊓ B.Δ.model →
      Vc.map (MulAut.conj h).toMonoidHom = excCurve a' B.Δ.g0⁻¹ →
      (excCurve a' B.Δ.g0⁻¹).map (MulAut.conj t).toMonoidHom = excCurve a' B.Δ.g0⁻¹ →
      ((ggRootSub (ggU .twistedE6 n f).D ψ γ' u₀⁻¹).subgroupOf G₀).map B.η =
        Vc ⊓ B.Δ.model ∧
      Nat.card ↥(((ggRootSub (ggU .twistedE6 n f).D ψ γ' u₀⁻¹).subgroupOf G₀).map B.η) =
        Nat.card ↥(excCurve a' B.Δ.g0⁻¹ ⊓ B.Δ.model) := by
    intro γ' a' Vc hs hc hn
    rw [ggRootSub_eq_conj_map (ggU .twistedE6 n f).D ψ γ' u₀⁻¹, hψe]
    have h1 := map_eta_conj B.η (ggRootSub (ggU .twistedE6 n f).D ψ γ' 1) g⁻¹
    rw [map_inv, hg] at h1
    rw [h1, hs]
    exact ⟨map_conj_inv_inf_eq hhtγ ht (hΓmodel hγ) hc hn,
      Subgroup.card_map_of_injective (MulAut.conj γ⁻¹).injective⟩
  obtain ⟨hR, hRc⟩ := key β a (excCurve α w) hstd hc1 htn
  obtain ⟨hRm, hRmc⟩ := key (-β) (-a) (excCurve (-α) w) hstdm hc2 htnm
  refine ⟨β, u₀⁻¹, hβ, hβn, hlong, ?_, ?_, ?_, ?_⟩
  · rw [hRc]
    exact hcard
  · exact hR
  · rw [hRmc]
    exact hcardm
  · exact hRm

end CFSG.StandardType.LieKnownR2.ExcPos
