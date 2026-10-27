module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGQTwoDStdModel
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsDefs

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

section Defs

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}

@[expose] def OrthFrameCore.img (Φ : OrthFrameCore p Bs X) (S : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
    Subgroup G :=
  (S.subgroupOf (orthDerived Φ.Q)).map Φ.ψ

@[expose] def OrthFrameCore.fixTorus (Φ : OrthFrameCore p Bs X) (x : OmPlusIdx Φ.r) :
    Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  (MonoidHom.eqLocus (omPlusRefl p x).toMonoidHom (MonoidHom.id _)).map Φ.Δ.τ

@[expose] noncomputable def OrthFrameCore.rank1 (Φ : OrthFrameCore p Bs X)
    (x : OmPlusIdx Φ.r) : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  ggOTwoPrime (orthDerived Φ.Q ⊓
    Subgroup.centralizer (Φ.fixTorus x : Set (Φ.V ≃ₗ[Φ.F] Φ.V)))

@[expose] noncomputable def OrthFrameCore.rank2 (Φ : OrthFrameCore p Bs X)
    (x y : OmPlusIdx Φ.r) : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  ggOTwoPrime (orthDerived Φ.Q ⊓
    Subgroup.centralizer ((Φ.fixTorus x ⊓ Φ.fixTorus y : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
      Set (Φ.V ≃ₗ[Φ.F] Φ.V)))

@[expose] def OrthFrameCore.Acts (Φ : OrthFrameCore p Bs X) (ρ : MulAut ↥Bs)
    (x : OmPlusIdx Φ.r) : Prop :=
  ∀ (b : ↥Bs) (f : Fin Φ.r → Multiplicative (ZMod p)),
    (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f →
      (Φ.β (ρ b) : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ (omPlusRefl p x f)

theorem OrthFrameCore.img_sup (Φ : OrthFrameCore p Bs X) {S S' : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)}
    (hS : S ≤ orthDerived Φ.Q) (hS' : S' ≤ orthDerived Φ.Q) :
    Φ.img (S ⊔ S') = Φ.img S ⊔ Φ.img S' := by
  rw [OrthFrameCore.img, OrthFrameCore.img, OrthFrameCore.img,
    Subgroup.subgroupOf_sup hS hS', Subgroup.map_sup]

end Defs

end OrthTorus

end CFSG.StandardType

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.RankThree.Classical2 (orthDerived)

section Ident

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

private theorem pmoi_map_orthDerived_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q) :
    (orthDerived Φ.Q).map (MulAut.conj μ).toMonoidHom = orthDerived Φ.Q := by
  have hH : (TauCeti.QuadraticMap.orthogonalGroup Φ.Q).map (MulAut.conj μ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      exact mul_mem (mul_mem hμ hh) (inv_mem hμ)
    · intro h hh
      refine Subgroup.mem_map.mpr ⟨μ⁻¹ * h * μ, mul_mem (mul_mem (inv_mem hμ) hh) hμ, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [show orthDerived Φ.Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
      TauCeti.QuadraticMap.orthogonalGroup Φ.Q⁆ from rfl]
  rw [Subgroup.map_commutator, hH]

private theorem pmoi_fixTorus_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x x' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹) :
    Φ.fixTorus x' = (Φ.fixTorus x).map (MulAut.conj μ).toMonoidHom := by
  ext t
  constructor
  · intro ht
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at ht
    obtain ⟨g, hg, rfl⟩ := ht
    change omPlusRefl p x' g = g at hg
    refine Subgroup.mem_map.mpr ⟨Φ.Δ.τ (w⁻¹ g), ?_, ?_⟩
    · rw [OrthFrameCore.fixTorus, Subgroup.mem_map]
      refine ⟨w⁻¹ g, ?_, rfl⟩
      change omPlusRefl p x (w⁻¹ g) = w⁻¹ g
      have h2 : omPlusRefl p x' g = w (omPlusRefl p x (w⁻¹ g)) := by
        rw [hx]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      have h3 : w (omPlusRefl p x (w⁻¹ g)) = g := h2 ▸ hg
      apply w.injective
      rw [h3, MulAut.apply_inv_self]
    · show (MulAut.conj μ) (Φ.Δ.τ (w⁻¹ g)) = Φ.Δ.τ g
      rw [MulAut.conj_apply, hw (w⁻¹ g), MulAut.apply_inv_self]
  · intro ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    change omPlusRefl p x f = f at hf
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map]
    refine ⟨w f, ?_, ?_⟩
    · change omPlusRefl p x' (w f) = w f
      have h2 : omPlusRefl p x' (w f) = w (omPlusRefl p x f) := by
        rw [hx]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      rw [h2, hf]
    · show Φ.Δ.τ (w f) = (MulAut.conj μ) (Φ.Δ.τ f)
      rw [MulAut.conj_apply, hw f]

theorem qtwoOrth_rank1_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x x' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹) :
    Φ.rank1 x' = (Φ.rank1 x).map (MulAut.conj μ).toMonoidHom := by
  have hfix := pmoi_fixTorus_conj Φ hw hx
  have hder := pmoi_map_orthDerived_conj Φ hμ
  unfold OrthFrameCore.rank1
  rw [ggOTwoPrime_map_conj μ (orthDerived Φ.Q ⊓
      Subgroup.centralizer (Φ.fixTorus x : Set (Φ.V ≃ₗ[Φ.F] Φ.V))),
    Subgroup.map_inf _ _ _ (MulAut.conj μ).injective,
    ggMap_conj_centralizer μ (Φ.fixTorus x), hder, ← hfix]

theorem qtwoOrth_rank2_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x y x' y' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹)
    (hy : omPlusRefl p y' = w * omPlusRefl p y * w⁻¹) :
    Φ.rank2 x' y' = (Φ.rank2 x y).map (MulAut.conj μ).toMonoidHom := by
  have hfixx := pmoi_fixTorus_conj Φ hw hx
  have hfixy := pmoi_fixTorus_conj Φ hw hy
  have hder := pmoi_map_orthDerived_conj Φ hμ
  have hfixxy : Φ.fixTorus x' ⊓ Φ.fixTorus y' =
      (Φ.fixTorus x ⊓ Φ.fixTorus y).map (MulAut.conj μ).toMonoidHom := by
    rw [hfixx, hfixy, Subgroup.map_inf _ _ _ (MulAut.conj μ).injective]
  unfold OrthFrameCore.rank2
  rw [ggOTwoPrime_map_conj μ (orthDerived Φ.Q ⊓ Subgroup.centralizer
      ((Φ.fixTorus x ⊓ Φ.fixTorus y : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
        Set (Φ.V ≃ₗ[Φ.F] Φ.V))),
    Subgroup.map_inf _ _ _ (MulAut.conj μ).injective,
    ggMap_conj_centralizer μ (Φ.fixTorus x ⊓ Φ.fixTorus y), hder, ← hfixxy]

end Ident

end CFSG.StandardType.QTwo

end
