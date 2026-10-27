module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection1
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.B15P4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Offender

section Dictionary

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem exists_le_map_eq {A : Subgroup (MulAut V)} {B' : Subgroup (W ≃ₗ[ZMod 2] W)}
    (h : B' ≤ A.map (binPsi θ).toMonoidHom) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ B.map (binPsi θ).toMonoidHom = B' := by
  refine ⟨B'.comap (binPsi θ).toMonoidHom, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hax⟩ := h hx
    have : a = x := (binPsi θ).injective hax
    rw [← this]
    exact ha
  · exact Subgroup.map_comap_eq_self_of_surjective (binPsi θ).surjective B'

theorem weight_le_of_isFFStarOffender {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (B' : Subgroup (W ≃ₗ[ZMod 2] W)) (hB' : B' ≤ A.map (binPsi θ).toMonoidHom) :
    weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) B' ≤
      weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (A.map (binPsi θ).toMonoidHom) := by
  obtain ⟨B, hBA, rfl⟩ := exists_le_map_eq θ hB'
  rw [weight_map θ B, weight_map θ A]
  exact hA.card_le hBA

end Dictionary

theorem normalizes_of_isQuadratic {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G A K : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (hq : IsQuadratic A) (hK : CFSG.Open.IsComponentOf K G) :
    A ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (V := V) fun v => by
    rw [← pow_two]
    exact hV v
  have hAG : A.map (binPsi θ).toMonoidHom ≤
      Subgroup.normalizer ((G.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)) :=
    (Subgroup.map_mono hA.1).trans Subgroup.le_normalizer
  have hel : CFSG.IsElementaryAbelian 2 ↥(A.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ A).1 hA.2.2.1
  have hquad := (isQuadratic_iff_map θ A).1 hq
  have hcomp : IsComponentIn (K.map (binPsi θ).toMonoidHom) (G.map (binPsi θ).toMonoidHom) :=
    (isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff K G).1 hK)
  have key := quadBestOffendersNormalize (k := ZMod 2) (V := W)
    (G.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) hAG hel hquad
    (fun B' hB' => weight_le_of_isFFStarOffender θ hA B' hB')
    (K.map (binPsi θ).toMonoidHom) hcomp
  refine (map_le_normalizer_iff (binPsi θ)).1 fun a ha => ?_
  exact CFSG.Quasithin.B6.mem_normalizer_of_conjSub_le (le_of_eq (key a ha))
    (le_of_eq (key a⁻¹ (Subgroup.inv_mem _ ha)))

theorem normalizes_of_isFFStarMin {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G A K : Subgroup (MulAut V)} (hA : IsFFStarMin G A)
    (hK : CFSG.Open.IsComponentOf K G) : A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
  normalizes_of_isQuadratic hV hA.1 (B1_4_3 hV hA) hK

theorem asB15Part4Quad :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A → IsQuadratic A →
        ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G →
          A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
  fun _ _ _ hV _ _ hA hq _ hK => normalizes_of_isQuadratic hV hA hq hK

theorem asB15Part4Star :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ G A : Subgroup (MulAut V), IsFFStarMin G A →
        ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G →
          A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
  fun _ _ _ hV _ _ hA _ hK => normalizes_of_isFFStarMin hV hA hK

end CFSG.Quasithin.B15P4
