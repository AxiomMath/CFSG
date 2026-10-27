module

public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] {Γ V : Type} [Group Γ] [Group V] {act : Γ →* MulAut V}
  {L F : Subgroup G}

@[expose] noncomputable def weylConjAut (S : WCtx act L F) {y : G}
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) : MulAut V :=
  (MulAut.congr S.tor).symm (F.normalizerMonoidHom ⟨y, hyF⟩)

theorem coe_tor_weylConjAut (S : WCtx act L F) {y : G}
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) (v : V) :
    ((S.tor (weylConjAut S hyF v) : F) : G) = y * ((S.tor v : F) : G) * y⁻¹ := by
  have h1 : MulAut.congr S.tor (weylConjAut S hyF) (S.tor v) =
      S.tor (weylConjAut S hyF v) := by
    show S.tor (weylConjAut S hyF (S.tor.symm (S.tor v))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : MulAut.congr S.tor (weylConjAut S hyF) = F.normalizerMonoidHom ⟨y, hyF⟩ :=
    MulEquiv.apply_symm_apply _ _
  rw [← h1, h2]
  rfl

theorem exists_scalar_of_weylConjAut (S : WCtx act L F) {y : G}
    (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (H : ∃ (γ : Γ) (k : ℤ), ∀ v, weylConjAut S hyF v = act γ (v ^ k)) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h * f ^ k * h⁻¹ := by
  obtain ⟨γ, k, hk⟩ := H
  obtain ⟨g, hgF, hgL, hgγ⟩ := S.exists_elt γ
  refine ⟨g, hgL, hgF, k, fun f hf => ?_⟩
  obtain ⟨v, hv⟩ := S.tor.surjective ⟨f, hf⟩
  have hfv : f = ((S.tor v : F) : G) := by rw [hv]
  have h2 : ((S.tor (act γ (v ^ k)) : F) : G) = g * ((S.tor v : F) : G) ^ k * g⁻¹ := by
    rw [← S.actF_apply, S.actF_eq, ← hgγ, WCtx.coe_normalizerMonoidHom_apply hgF, map_zpow,
      Subgroup.coe_zpow]
  calc y * f * y⁻¹ = ((S.tor (weylConjAut S hyF v) : F) : G) := by
        rw [coe_tor_weylConjAut, hfv]
    _ = ((S.tor (act γ (v ^ k)) : F) : G) := by rw [hk v]
    _ = g * ((S.tor v : F) : G) ^ k * g⁻¹ := h2
    _ = g * f ^ k * g⁻¹ := by rw [hfv]

end CFSG.RankThree.PartOne.KEXC
