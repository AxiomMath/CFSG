module

public import CFSG.Quasithin.EmptyFaithful.S146F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Tv

variable {G : Type} [Group G] {T M H : Subgroup G}

structure TvData (T M H : Subgroup G) (g : G) : Prop where
  g_not : g ∉ mcOf T
  le_H : conjSub g⁻¹ (conjClosure (VZ T M) H) ≤ H
  U_le : conjClosure (VZ T M) H ≤ conjSub g⁻¹ H
  comm : ⁅conjSub g⁻¹ (conjClosure (VZ T M) H), conjClosure (VZ T M) H⁆ =
    conjSub g⁻¹ (quasithinOmegaOneCenter T)
  card : Nat.card (conjSub g⁻¹ (quasithinOmegaOneCenter T)) = 2
  inf : conjSub g⁻¹ (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T = ⊥

end Tv

section Build

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.tvData (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g)
    (hD : F8.Uγ (VZ T M) H (g : G) = F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G)) :
    TvData T M H (g : G) := by
  classical
  obtain ⟨hF81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have htg := h98.lemma_14_5_18_one hs hD
  have hUγH : F8.Uγ (VZ T M) H (g : G) ≤ H := h98.Uγ_le_H hs
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← hs.edge₁, stab_smul, stab_γ₁ h98.amalgamHypV.le₂]
  have hUstab : conjClosure (VZ T M) H ≤ conjSub (g : G) H := by
    have h1 := (h98.F913_2 hs).1
    rw [← hstab]
    exact h1.trans ((pCoreOf_le 2 _).trans inf_le_right)
  have hUγ : F8.Uγ (VZ T M) H (g : G) = conjSub (g : G) (conjClosure (VZ T M) H) := rfl
  refine ⟨?_, ?_, ?_, ?_, (card_conjSub _ _).trans S.card_Z, ?_⟩
  · intro hg
    obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
    apply S.conj_not_mem_Z hH hs hz hz1
    have hgN : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
      rw [S.normalizer_Z]
      exact hg
    exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz
  · have h1 := conjSub_mono (g : G)⁻¹ hUstab
    rwa [conjSub_conjSub_inv] at h1
  · exact (conjSub_le_iff _).mp hUγH
  · have h1 := congrArg (conjSub (g : G)⁻¹) htg.2.2
    rw [← conjSub_commutator, hUγ, conjSub_conjSub_inv] at h1
    exact h1
  · have h5b := F8.F87_5b hF81 hs
    have hA : F8.A₁ (quasithinOmegaOneCenter T) (g : G) = conjSub (g : G) (quasithinOmegaOneCenter T) :=
      rfl
    rw [hA] at h5b
    have h1 := congrArg (conjSub (g : G)⁻¹) h5b
    rw [conjSub_inf, conjSub_conjSub_inv, conjSub_bot] at h1
    exact h1

end Build

end CFSG.Quasithin
