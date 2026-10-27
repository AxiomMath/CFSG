module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdent
public import CFSG.ClassicalInvolution.Phan.StandardPair
import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
import CFSG.GH74.L5U5.ModelsPairsUnitary

public section

namespace CFSG.StandardType.OrthTorus

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.Classical2 (orthDerived)

section Img

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

theorem OrthFrameCore.rank1_le_orthDerived [Fact p.Prime] (x : OmPlusIdx Φ.r) :
    Φ.rank1 x ≤ orthDerived Φ.Q := by
  rw [OrthFrameCore.rank1]
  exact (ggOTwoPrime_le _).trans inf_le_left

theorem OrthFrameCore.rank2_le_orthDerived [Fact p.Prime] (x y : OmPlusIdx Φ.r) :
    Φ.rank2 x y ≤ orthDerived Φ.Q := by
  rw [OrthFrameCore.rank2]
  exact (ggOTwoPrime_le _).trans inf_le_left

theorem OrthFrameCore.img_standardPair {K : Type} [Field K] [Finite K] [CharP K 2] {Y' : Type}
    [Group Y'] (Θ : (Φ.V ≃ₗ[Φ.F] Φ.V) ≃* Y') {S S₁ S₂ : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)}
    {S' S₁' S₂' : Subgroup Y'} (hS : S ≤ orthDerived Φ.Q) (hS₁ : S₁ ≤ orthDerived Φ.Q)
    (hS₂ : S₂ ≤ orthDerived Φ.Q) (h : S.map Θ.toMonoidHom = S')
    (h₁ : S₁.map Θ.toMonoidHom = S₁') (h₂ : S₂.map Θ.toMonoidHom = S₂')
    (hpair : UnitaryBlockStandardPair K 2 1 S' S₁' S₂') :
    UnitaryBlockStandardPair K 2 1 (Φ.img S) (Φ.img S₁) (Φ.img S₂) := by
  have e : ∀ T : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V),
      (T.map Θ.toMonoidHom).map Θ.symm.toMonoidHom = T := by
    intro T
    rw [Subgroup.map_map]
    rw [show Θ.symm.toMonoidHom.comp Θ.toMonoidHom =
        MonoidHom.id (Φ.V ≃ₗ[Φ.F] Φ.V) from by
      ext x; simp]
    exact Subgroup.map_id (G := Φ.V ≃ₗ[Φ.F] Φ.V) T
  have hpair' : UnitaryBlockStandardPair K 2 1
      (S'.map Θ.symm.toMonoidHom) (S₁'.map Θ.symm.toMonoidHom)
      (S₂'.map Θ.symm.toMonoidHom) :=
    CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hpair Θ.symm.toMonoidHom Θ.symm.injective
  rw [← h, ← h₁, ← h₂, e S, e S₁, e S₂] at hpair'
  have hres := unitaryBlockStandardPair_restrict hpair' (orthDerived Φ.Q) hS
  simpa only [OrthFrameCore.img] using
    CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hres Φ.ψ Φ.hinj

theorem OrthFrameCore.exists_hom_range_img {S₀ Y' : Type} [Group S₀] [Group Y']
    (Θ : (Φ.V ≃ₗ[Φ.F] Φ.V) ≃* Y') {A B : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)}
    {A' B' : Subgroup Y'} (hA : A ≤ orthDerived Φ.Q) (hB : B ≤ orthDerived Φ.Q)
    (h : A.map Θ.toMonoidHom = A') (h' : B.map Θ.toMonoidHom = B') (θ' : S₀ →* Y')
    (hθ : θ'.range = A' ⊔ B') : ∃ θ : S₀ →* G, θ.range = Φ.img A ⊔ Φ.img B := by
  have e : ∀ T : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V),
      (T.map Θ.toMonoidHom).map Θ.symm.toMonoidHom = T := by
    intro T
    rw [Subgroup.map_map]
    rw [show Θ.symm.toMonoidHom.comp Θ.toMonoidHom =
        MonoidHom.id (Φ.V ≃ₗ[Φ.F] Φ.V) from by
      ext x; simp]
    exact Subgroup.map_id (G := Φ.V ≃ₗ[Φ.F] Φ.V) T
  have hθ₁ : (Θ.symm.toMonoidHom.comp θ').range = A ⊔ B := by
    rw [MonoidHom.range_comp, hθ, Subgroup.map_sup, ← h, ← h', e A, e B]
  have hle : ∀ g, (Θ.symm.toMonoidHom.comp θ') g ∈ orthDerived Φ.Q := by
    intro g
    have hg : (Θ.symm.toMonoidHom.comp θ') g ∈ A ⊔ B := by
      rw [← hθ₁]; exact ⟨g, rfl⟩
    exact sup_le hA hB hg
  refine ⟨Φ.ψ.comp ((Θ.symm.toMonoidHom.comp θ').codRestrict (orthDerived Φ.Q) hle), ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_map,
    CFSG.map_codRestrict_eq_subgroupOf (Θ.symm.toMonoidHom.comp θ') hle ⊤,
    ← MonoidHom.range_eq_map, hθ₁]
  simpa only [OrthFrameCore.img] using OrthFrameCore.img_sup Φ hA hB

theorem OrthFrameCore.img_commute {Y' : Type} [Group Y'] (Θ : (Φ.V ≃ₗ[Φ.F] Φ.V) ≃* Y')
    {A B : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)} {A' B' : Subgroup Y'} (hA : A ≤ orthDerived Φ.Q)
    (hB : B ≤ orthDerived Φ.Q) (h : A.map Θ.toMonoidHom = A') (h' : B.map Θ.toMonoidHom = B')
    (hc : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) : ∀ a ∈ Φ.img A, ∀ b ∈ Φ.img B, a * b = b * a := by
  intro a ha b hb
  rw [OrthFrameCore.img, Subgroup.mem_map] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  rw [OrthFrameCore.img, Subgroup.mem_map] at hb
  obtain ⟨v, hv, rfl⟩ := hb
  rw [Subgroup.mem_subgroupOf] at hu hv
  have hΘu : Θ u ∈ A' := by rw [← h]; exact ⟨u, hu, rfl⟩
  have hΘv : Θ v ∈ B' := by rw [← h']; exact ⟨v, hv, rfl⟩
  have hΘ : Θ ((u : Φ.V ≃ₗ[Φ.F] Φ.V) * (v : Φ.V ≃ₗ[Φ.F] Φ.V)) =
      Θ ((v : Φ.V ≃ₗ[Φ.F] Φ.V) * (u : Φ.V ≃ₗ[Φ.F] Φ.V)) := by
    rw [map_mul, map_mul]
    exact hc (Θ u) hΘu (Θ v) hΘv
  have huv : u * v = v * u := by
    apply Subtype.ext
    exact MulEquiv.injective Θ hΘ
  rw [← map_mul, ← map_mul, huv]

end Img

section Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y) {K : Type} [Field K] [Algebra Φ.F K] {n : ℕ}

@[expose] def orthModelEquiv (χ : Φ.V ≃ₗ[Φ.F] (Fin n → K)) (μ : Φ.V ≃ₗ[Φ.F] Φ.V) :
    (Φ.V ≃ₗ[Φ.F] Φ.V) ≃* ((Fin n → K) ≃ₗ[Φ.F] (Fin n → K)) :=
  (MulAut.conj μ).trans (LinearEquiv.autCongr χ)

theorem orthModelEquiv_map (χ : Φ.V ≃ₗ[Φ.F] (Fin n → K)) (μ : Φ.V ≃ₗ[Φ.F] Φ.V)
    (S : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
    S.map (orthModelEquiv Φ χ μ).toMonoidHom =
      (S.map (MulAut.conj μ).toMonoidHom).map (LinearEquiv.autCongr χ).toMonoidHom := by
  have hcomp : (orthModelEquiv Φ χ μ).toMonoidHom =
      (LinearEquiv.autCongr χ).toMonoidHom.comp (MulAut.conj μ).toMonoidHom := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map]

theorem OrthFrameCore.rank1_map_model (χ : Φ.V ≃ₗ[Φ.F] (Fin n → K)) {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x x' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹)
    {U' : Subgroup ((Fin n → K) ≃ₗ[Φ.F] (Fin n → K))}
    (hU : (Φ.rank1 x').map (LinearEquiv.autCongr χ).toMonoidHom = U') :
    (Φ.rank1 x).map (orthModelEquiv Φ χ μ).toMonoidHom = U' := by
  rw [orthModelEquiv_map, ← CFSG.StandardType.QTwo.qtwoOrth_rank1_conj Φ hμ hw hx]
  exact hU

theorem OrthFrameCore.rank2_map_model (χ : Φ.V ≃ₗ[Φ.F] (Fin n → K)) {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x y x' y' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹)
    (hy : omPlusRefl p y' = w * omPlusRefl p y * w⁻¹)
    {W' : Subgroup ((Fin n → K) ≃ₗ[Φ.F] (Fin n → K))}
    (hW : (Φ.rank2 x' y').map (LinearEquiv.autCongr χ).toMonoidHom = W') :
    (Φ.rank2 x y).map (orthModelEquiv Φ χ μ).toMonoidHom = W' := by
  rw [orthModelEquiv_map, ← CFSG.StandardType.QTwo.qtwoOrth_rank2_conj Φ hμ hw hx hy]
  exact hW

end Model

end CFSG.StandardType.OrthTorus

end
