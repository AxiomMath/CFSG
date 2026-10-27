module

public import CFSG.Quasithin.EmptyFaithful.SBc14C
public import CFSG.Quasithin.EmptyFaithful.SBc13G2
public import CFSG.Quasithin.EmptyFaithful.SBc13AMain
public import CFSG.Quasithin.EmptyFaithful.SBc13B2Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc14

@[expose] def Input14615Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H →
          Gap3Theta T (oTwoUpper H₁) (oTwoUpper H₂)

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem gap3Theta_of_ctx (h : Input14615Theta) (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hctx : Ctx15 T M H p H₁) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    Gap3Theta T K₁ K₂ := by
  rcases hset.shape with ⟨-, -, hG, -⟩ | ⟨hK₁, hK₂⟩
  · exact SBc13.gap3Theta_of_shapeOne S hset hG
  · have hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H := by
      rw [hset.kz, hK₁, hK₂]
      exact (hdec.oTwoUpper_eq S hred).symm
    rw [hK₁, hK₂]
    exact h G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx hCz

theorem input14615GP_of_theta (h : Input14615Theta) : Input14615GP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset γ γ' g hF8 hA hZ hcent
  have hp5 : p = 5 := hctx.1
  rcases hset.shape with ⟨hc₁, hc₂, hG, hQ⟩ | ⟨hK₁, hK₂⟩
  · exact SBc13.g_mem_g2_of_theta_shapeOne S hp5 hred hdec hset hc₁ hc₂ hG hQ
      (SBc13.gap3Theta_of_shapeOne S hset hG) hF8 hZ hcent
  · exact SBc13.g_mem_g2_of_theta_shapeTwo S hp5 hred hdec hK₁ hK₂ hset
      (gap3Theta_of_ctx h S hred hmax hdec hctx hset) hF8 hZ hcent

theorem input14615HypP_proved (h5 : Stage1461Five) : Input14615HypP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
  obtain ⟨hHyp, hnot⟩ := hypC23_of_ctx S h5 hred hdec hset hG₂
  exact ⟨hHyp, charTwo_g2 S h5 hred hdec hset, hnot⟩

end SBc14

end CFSG.Quasithin
