module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem Setting146.facts1469_f (h5 : Stage1461Five) {T M H : Subgroup G} {u : G}
    {I K₁ K₂ : Subgroup G} {ρ : G} (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (he : omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) ≤ omegaOneCenterOf (pCoreOf 2 (mcOf T))) :
    oTwoUpper (oTwoFstarIn (mcOf T)) ≤ Subgroup.centralizer
      ((omegaOneCenterOf (pCoreOf 2 (mcOf T)) ⊔ omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) :
        Subgroup G) : Set G) := by
  have S := c.ctx.setting
  have h := h5 G T M S (mcOf T) S.isHTM_mcOf
  rw [sup_eq_left.mpr he]
  exact (oTwoUpper_le _).trans h

theorem Setting146.facts1469_g (i5 : Input1469A5C567) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (hd : T ⊓ I = tZero T u) :
    IsElemAbelian 2 (dOf1469 T I K₁ K₂) ∧
      pCoreOf 2 I = dOf1469 T I K₁ K₂ ⊔ pCoreOf 2 (K₁ ⊔ K₂) ∧
      omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) =
        dOf1469 T I K₁ K₂ ⊔ z0Of1469 (I ⊓ mcOf T) K₁ K₂ := by
  have S := c.ctx.setting
  have hu := c.ctx.hu
  have hidx := (h1 G T M S H c.ctx.hH u hu).2.1
  have hN0 := h2 G T M S H c.ctx.hH u hu
  have hNu := (h4 G T M S H c.ctx.hH u hu).1
  have hsyl : IsSylowTwoOf (T ⊓ I) I := (isIStar_sylow_cases S hu hidx hN0 hNu c.ctx.hI.1).1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hSQ : IsSQTKTC I := S.isSQTKTC_of_pCoreOf_ne_bot c.ctx.hI.1.1.1.2
  have hTbot : pCoreOf 2 T ≠ ⊥ := by
    intro h
    have hle : T ≤ pCoreOf 2 T :=
      CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer le_rfl Subgroup.le_normalizer hT2
    have hT1 : T = ⊥ := le_bot_iff.mp (hle.trans h.le)
    have hcard := c.ctx.hT
    rw [hT1, Subgroup.card_bot] at hcard
    omega
  have hSQT : IsSQTKTC T := S.isSQTKTC_of_pCoreOf_ne_bot hTbot
  have hsylR : IsSylowTwoOf (T ⊓ I) (oTwoUpper I ⊔ (T ⊓ I)) := by
    refine ⟨le_sup_right, hsyl.2.1, fun hdvd => hsyl.2.2 ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ I) (oTwoUpper I ⊔ (T ⊓ I)) I le_sup_right
      (sup_le (oTwoUpper_le I) inf_le_right)
    have h2' : 2 ∣ (T ⊓ I).relIndex I := by
      rw [← hmul]
      exact Dvd.dvd.mul_right hdvd _
    exact h2'
  have hnorm : T ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
    rw [hd]
    exact hN0.ge
  have hrel : (T ⊓ I).relIndex T = 2 := by
    rw [hd]
    exact hu.index_two
  have hnormal : ∀ R₀ : Subgroup G, R₀ ≤ T ⊓ I → R₀ ≠ ⊥ →
      ¬ (T ⊔ I ≤ Subgroup.normalizer (R₀ : Set G)) := by
    intro R₀ hR₀ hR₀1 hle
    obtain ⟨_, hTN, _⟩ := c.obs_a R₀ hR₀ hR₀1 (le_sup_right.trans hle)
    have hTI : T ⊓ I = T := by
      rw [← hTN]
      exact inf_eq_left.mpr (le_sup_left.trans hle)
    exact (S.tI_lt c.ctx.hI.1.1).ne hTI
  have key := i5 G I (T ⊓ I) (I ⊓ mcOf T) K₁ K₂ T hSQ c.charTwo c.ctx.minPar c.blocks c.a5.1
    c.a5.2 c.not_le
    ⟨hSQ, hSQT, c.charTwo, hsyl, ⟨_, c.ctx.minPar.uniqueMax⟩, le_rfl, inf_le_left, hsylR, hnorm⟩
    hrel hnormal
  exact ⟨key.1, key.2.2.1, key.2.2.2⟩

end CFSG.Quasithin
