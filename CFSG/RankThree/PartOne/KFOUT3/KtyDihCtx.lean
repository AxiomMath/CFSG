module

public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

section Pull

variable {G : Type} [Group G] {Γ Γ₁ V : Type} [Group Γ] [Group Γ₁] [Group V]
  {act₁ : Γ₁ →* MulAut V} {act : Γ →* MulAut V} {L F : Subgroup G}

@[expose] def wctxPull (f : Γ →* Γ₁) (hf : Function.Surjective f)
    (hact : ∀ γ, act₁ (f γ) = act γ) (S : WCtx act₁ L F) : WCtx act L F where
  tor := S.tor
  exists_elt γ := by
    obtain ⟨g, hg, hgL, hgγ⟩ := S.exists_elt (f γ)
    exact ⟨g, hg, hgL, by rw [hgγ, hact]⟩
  induced g hg hgL := by
    obtain ⟨γ₁, hγ₁⟩ := S.induced g hg hgL
    obtain ⟨γ, rfl⟩ := hf γ₁
    exact ⟨γ, by rw [hγ₁, hact]⟩

end Pull

section Conj

variable {M Q V Γ : Type} [Group M] [Group Q] [Group V] [Group Γ] {act : Γ →* MulAut V}
  {T : Subgroup M}

theorem conj_of_wctx (SM : WCtx act (⊤ : Subgroup M) T) (ι : V →* M)
    (hι : ∀ d, (SM.tor d : M) = ι d) (q : M →* Q) (γ : Γ) :
    ∃ m : Q, ∀ v : V, m * q (ι v) * m⁻¹ = q (ι (act γ v)) := by
  obtain ⟨g, hg, -, hgγ⟩ := SM.exists_elt γ
  refine ⟨q g, fun v => ?_⟩
  have h1 : ((T.normalizerMonoidHom ⟨g, hg⟩ (SM.tor v) : T) : M) = g * (SM.tor v : M) * g⁻¹ := rfl
  have h2 : T.normalizerMonoidHom ⟨g, hg⟩ (SM.tor v) = SM.tor (act γ v) := by
    rw [hgγ]
    exact SM.actF_apply γ v
  have h3 : g * (SM.tor v : M) * g⁻¹ = (SM.tor (act γ v) : M) := by rw [← h1, h2]
  rw [hι, hι] at h3
  rw [← h3, map_mul, map_mul, map_inv]

end Conj

end CFSG.RankThree.PartOne.KFOUT3
