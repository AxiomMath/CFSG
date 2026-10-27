module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveC
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSix
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHatSix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace HatU

variable {G : Type} [Group G] {U : Subgroup G} {D : HatModelU U}

theorem img_sup_eq_of_forall_rho_eq_one {K E : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (U : Set G)) (hEN : E ≤ Subgroup.normalizer (U : Set G))
    (hE : ∀ x (hxN : x ∈ Subgroup.normalizer (U : Set G)), x ∈ E → D.ρ ⟨x, hxN⟩ = 1) :
    D.img (K ⊔ E) = D.img K := by
  unfold HatModelU.img
  rw [Subgroup.subgroupOf_sup hK hEN, Subgroup.map_sup]
  have : (E.subgroupOf (Subgroup.normalizer (U : Set G))).map D.ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hE (x : G) x.2 hx
  rw [this, sup_bot_eq]

end HatU

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem twelve_three (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁))
    (hU4 : 4 < (centerOf (uA V V₁)).relIndex (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) (D.img (rconj (wA V V₁) g))
      (D.img (rconj (centerOf (uA V V₁)) g)) where
  toG101Hyp := S.twelve_one hg D haV haZ
  three := by
    classical
    obtain ⟨hπa, hπaV, hhatV⟩ := S.hat_V_cases D haV haZ
    by_cases hlt : D.hat (V) < HatU.fixSpace D (rconj (wA V V₁) g)
    · right
      obtain ⟨γ, hγ, -, hrk, hrange⟩ := S.eleven_six hg D hU4 hlt
      exact ⟨γ, hγ, hrk, hrange hπaV⟩
    · left
      intro v hv
      have hle : D.hat (V) ≤ HatU.fixSpace D (rconj (wA V V₁) g) := by
        intro w hw
        rw [(HatU.mem_fixSpace D)]
        intro γ hγ
        rcases hhatV w hw with h0 | h0
        · rw [h0, map_zero]
        · rw [h0]
          exact S.X_fixes_img hg D haV γ hγ
      have hge : HatU.fixSpace D (rconj (wA V V₁) g) ≤ D.hat (V) := by
        by_contra hnot
        exact hlt (lt_of_le_not_ge hle hnot)
      exact hhatV v (hge ((HatU.mem_fixSpace D).mpr hv))
  four := by
    classical
    have hTH : T ≤ Subgroup.normalizer (V₁ : Set G) :=
      S.base.T_le_H
    have hXT : rconj (wA V V₁) g ≤ T := S.rconj_wA_le_T hg
    have hstab := S.img_T_le_stabilizer D haV haZ
    have hle : D.img T ≤ D.img (Subgroup.normalizer (V₁ : Set G)) ⊓
        MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
      le_inf (L1294.img_mono D hTH) hstab
    refine ⟨D.img T, ⟨hle, ?_, ?_⟩, L1294.img_mono D hXT, ?_⟩
    · intro γ
      obtain ⟨t, htT, htN, hγ⟩ := (HatU.mem_img D).mp γ.2
      obtain ⟨k, hk⟩ := S.base.isPGroup_T ⟨t, htT⟩
      have ht1 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hN1 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (uA V V₁ : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using ht1)
      refine ⟨k, Subtype.ext ?_⟩
      show (γ : D.V ≃ₗ[ZMod 2] D.V) ^ 2 ^ k = 1
      rw [← hγ, ← map_pow, hN1, map_one]
    · intro hdvd
      have h1 : (D.img T).relIndex
            (D.img (Subgroup.normalizer (V₁ : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)) *
          (D.img (Subgroup.normalizer (V₁ : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)).relIndex
            (D.img (Subgroup.normalizer (V₁ : Set G))) =
          (D.img T).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) :=
        Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_left
      have h2 : (D.img T).relIndex
            (D.img (Subgroup.normalizer (V₁ : Set G)) ⊓
              MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)) ∣
            T.relIndex (Subgroup.normalizer (V₁ : Set G)) :=
        (Dvd.intro _ h1).trans (relIndex_img_T_dvd D)
      exact S.base.sylow_H.2.2 (hdvd.trans h2)
    · have hTn := (S.twelve_two hg).2.2
      have hXN := S.rconj_wA_le_normalizer_uA hg
      have hCN : centralizerHat V V₁ ≤ Subgroup.normalizer (uA V V₁ : Set G) := fun x hx =>
        normalizer_le_normalizer_uA V V₁ hx.1
      have hCρ : ∀ x (hxN : x ∈ Subgroup.normalizer (uA V V₁ : Set G)),
          x ∈ centralizerHat V V₁ → D.ρ ⟨x, hxN⟩ = 1 := fun x hxN hx =>
        (HatU.rho_eq_one_iff D ⟨x, hxN⟩).mpr hx.2.2
      have himg : D.img (rconj (wA V V₁) g ⊔ centralizerHat V V₁) = D.img (rconj (wA V V₁) g) :=
        HatU.img_sup_eq_of_forall_rho_eq_one hXN hCN hCρ
      intro γ hγ
      obtain ⟨t, htT, htN, rfl⟩ := (HatU.mem_img D).mp hγ
      apply mem_normalizer_of_conj_mem_of_finite
      intro δ hδ
      obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hδ
      have hxC : t * x * t⁻¹ ∈ rconj (wA V V₁) g ⊔ centralizerHat V V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hTn htT) x).mp (Subgroup.mem_sup_left hxX)
      have htxN : t * x * t⁻¹ ∈ Subgroup.normalizer (uA V V₁ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hxN) (Subgroup.inv_mem _ htN)
      have e : D.ρ ⟨t, htN⟩ * D.ρ ⟨x, hxN⟩ * (D.ρ ⟨t, htN⟩)⁻¹ =
          D.ρ ⟨t * x * t⁻¹, htxN⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e, ← himg]
      exact HatU.rho_mem_img D hxC htxN

end Setting

end L128A

end CFSG.Quasithin.H13
