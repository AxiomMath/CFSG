module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTwelveC
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem lemma_12_8_12_three (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    G111Hyp D.B (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a)
      (D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) (D.img (rconj (wOfU T M) g))
      (D.img (rconj (centerOf (uOfL22 T M)) g)) where
  toG101Hyp := h.lemma_12_8_12_one hU hg D haV haZ
  three := by
    classical
    obtain ⟨hπa, hπaV, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
    by_cases hlt : D.hat (VZ T M) < D.fixSpace (rconj (wOfU T M) g)
    · right
      obtain ⟨γ, hγ, -, hrk, hrange⟩ := h.lemma_12_8_11_six hU hg D hlt
      exact ⟨γ, hγ, hrk, hrange hπaV⟩
    · left
      intro v hv
      have hle : D.hat (VZ T M) ≤ D.fixSpace (rconj (wOfU T M) g) := by
        intro w hw
        rw [D.mem_fixSpace]
        intro γ hγ
        rcases hhatV w hw with h0 | h0
        · rw [h0, map_zero]
        · rw [h0]
          exact h.X_fixes_img hU hg D haV γ hγ
      have hge : D.fixSpace (rconj (wOfU T M) g) ≤ D.hat (VZ T M) := by
        by_contra hnot
        exact hlt (lt_of_le_not_ge hle hnot)
      exact hhatV v (hge (D.mem_fixSpace.mpr hv))
  four := by
    classical
    have hTH : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      h.almostSpecialHyp_g1.T_le_H
    have hXT : rconj (wOfU T M) g ≤ T := h.rconj_wOfU_le_T hU hg
    have hstab := h.img_T_le_stabilizer hU D haV haZ
    have hle : D.img T ≤ D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊓
        MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
      le_inf (HatModel.img_mono hTH) hstab
    refine ⟨D.img T, ⟨hle, ?_, ?_⟩, HatModel.img_mono hXT, ?_⟩
    · intro γ
      obtain ⟨t, htT, htN, hγ⟩ := HatModel.mem_img.mp γ.2
      obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, htT⟩
      have ht1 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hN1 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (uOfL22 T M : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using ht1)
      refine ⟨k, Subtype.ext ?_⟩
      show (γ : D.V ≃ₗ[ZMod 2] D.V) ^ 2 ^ k = 1
      rw [← hγ, ← map_pow, hN1, map_one]
    · intro hdvd
      have h1 : (D.img T).relIndex
            (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)) *
          (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)).relIndex
            (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) =
          (D.img T).relIndex (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) :=
        Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
      have h2 : (D.img T).relIndex
            (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)) ∣ T.index :=
        (Dvd.intro _ h1).trans (h.relIndex_img_T_dvd D)
      exact h.sylow.2 (hdvd.trans h2)
    · have hTn := (h.lemma_12_8_12_two hU hg).2.2
      have hXN := h.rconj_wOfU_le_normalizer_uOfL22 hU hg
      have hCN : centralizerHat T M ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx =>
        h.g1_le_normalizer_uOfL22 hx.1
      have hCρ : ∀ x (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)),
          x ∈ centralizerHat T M → D.rho ⟨x, hxN⟩ = 1 := fun x hxN hx =>
        (D.rho_eq_one_iff ⟨x, hxN⟩).mpr hx.2.2
      have himg : D.img (rconj (wOfU T M) g ⊔ centralizerHat T M) = D.img (rconj (wOfU T M) g) :=
        HatModel.img_sup_eq_of_forall_rho_eq_one hXN hCN hCρ
      intro γ hγ
      obtain ⟨t, htT, htN, rfl⟩ := HatModel.mem_img.mp hγ
      apply mem_normalizer_of_conj_mem_of_finite
      intro δ hδ
      obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hδ
      have hxC : t * x * t⁻¹ ∈ rconj (wOfU T M) g ⊔ centralizerHat T M :=
        (Subgroup.mem_normalizer_iff.mp (hTn htT) x).mp (Subgroup.mem_sup_left hxX)
      have htxN : t * x * t⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hxN) (Subgroup.inv_mem _ htN)
      have e : D.rho ⟨t, htN⟩ * D.rho ⟨x, hxN⟩ * (D.rho ⟨t, htN⟩)⁻¹ =
          D.rho ⟨t * x * t⁻¹, htxN⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e, ← himg]
      exact HatModel.rho_mem_img hxC htxN

end Hyp1281Two

end CFSG.Quasithin
