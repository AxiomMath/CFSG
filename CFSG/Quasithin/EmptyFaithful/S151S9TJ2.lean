module

public import CFSG.Quasithin.EmptyFaithful.S151S9TKInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.Quasithin.Background.E2TwoProofSporJ2

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat
open CFSG.Sporadic.J2 (a b)

theorem j2_S_sylow :
    IsSylowTwoOf j2Ctx.S ⊤ := by
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j2Ctx.S
  rw [j2Ctx.S_card, j2Ctx.hΓ, hN] at h1
  have h2 : j2Ctx.S.index = 4725 := by
    have : j2Ctx.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem j2_centre :
    ∃ z₀ : ↥CFSG.Sporadic.J2.J, orderOf z₀ = 2 ∧ centerOf j2Ctx.S = Subgroup.zpowers z₀ ∧
      (tab 315 z₀).toArray = j2SLP[143]! := by
  have hc : BaseCertS 315 (List.range 315)
      (slpTabsA (tab 315 a).toArray (tab 315 b).toArray j2Prog) j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
    rw [j2_ta', j2_tb']
    exact j2_cert
  have hk : 0 < j2Ctx.k := by
    have : j2Ctx.k = 7 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS j2Ctx hk a b j2Prog j2_valid j2Qp
    143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 hc rfl
  exact ⟨z₀, hz2, hZ, by rw [hzT, j2_ta', j2_tb']; rfl⟩

section K


@[expose] noncomputable def j2CtxF (h : j2FactsK) : LatCtx ↥CFSG.Sporadic.J2.J 315 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful j2_delta_valid j2_ta' j2_tb' CFSG.Sporadic.J2.closure_ab
    j2_sGens.1 j2_sGens.2 4725 (by rw [CFSG.Sporadic.J2.card_J]; norm_num) h.choose_spec.1

theorem j2F_S_sylow (h : j2FactsK) : IsSylowTwoOf (j2CtxF h).S ⊤ := by
  have hN : (j2CtxF h).D.O.lbl.size = 4725 := LatFactsK.ctx_O_size ..
  refine K1.isSylowTwoOf_top_iff.mpr ⟨(j2CtxF h).S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index (j2CtxF h).S
  rw [(j2CtxF h).S_card, (j2CtxF h).hΓ, hN] at h1
  have h2 : (j2CtxF h).S.index = 4725 := by
    have : (j2CtxF h).k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem j2F_centre (h : j2FactsK) :
    ∃ z₀ : ↥CFSG.Sporadic.J2.J, orderOf z₀ = 2 ∧ centerOf (j2CtxF h).S = Subgroup.zpowers z₀ ∧
      (tab 315 z₀).toArray = j2SLP[143]! := by
  have hc : BaseCertS 315 (List.range 315)
      (slpTabsA (tab 315 a).toArray (tab 315 b).toArray j2Prog) j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
    rw [j2_ta', j2_tb']
    exact j2_cert
  have hk : 0 < (j2CtxF h).k := by
    have : (j2CtxF h).k = 7 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS (j2CtxF h) hk a b j2Prog j2_valid j2Qp
    143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 hc rfl
  exact ⟨z₀, hz2, hZ, by rw [hzT, j2_ta', j2_tb']; rfl⟩

theorem j2_idx3Model (h : j2FactsK) :
    Idx3Model ↥CFSG.Sporadic.J2.J (j2CtxF h).S ((j2CtxF h).Y 4) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := j2F_centre h
  have hok : j2Wit.Ok 315 (j2CtxF h).A.act (j2CtxF h).Δ (j2CtxF h).D (tab 315 z₀).toArray := by
    rw [hzT]
    exact h.choose_spec.2.2
  have hN : (j2CtxF h).D.O.lbl.size = 4725 := LatFactsK.ctx_O_size ..
  exact idx3Model_of_lat (j2CtxF h) (j2F_S_sylow h) hz2 hZ j2Wit hok h.choose_spec.2.1
    (by decide) (by decide) (by rw [hN]; decide) (by decide)

theorem j2_threeD (h : j2FactsK) :
    ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsSporadic .J2 ↥L → IsPGroup 2 ↥S →
      S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      ∀ z ∈ centerOf (S ⊓ L), ¬ L ≤ Subgroup.centralizer ({z} : Set G) →
        ∃ P : Subgroup G, P ≤ L ∧ S ⊓ L ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
          ¬ P ≤ Subgroup.centralizer ({z} : Set G) ∧ CharTwo P ∧
          IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
          oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  obtain ⟨e⟩ := hL
  have e₀ : ↥L ≃* ↥CFSG.Sporadic.J2.J := e.trans CFSG.Sporadic.J2.nativeEquiv
  exact @threeD_of_idx3Model G _ _ L S z hS2 hSN hSyl hz hnc ↥CFSG.Sporadic.J2.J
    (Subgroup.toGroup _) _ e₀ _ _ (j2_idx3Model h)

end K

end CFSG.Quasithin.S151S9T
