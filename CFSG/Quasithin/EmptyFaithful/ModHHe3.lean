module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.EmptyFaithful.ModHHe2
public import CFSG.Quasithin.EmptyFaithful.ModHInn4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.ModH.He3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.Open CFSG.Quasithin CFSG.Blueprint

section


noncomputable def heLat : HeLat ↥CFSG.Sporadic.He.J where
  S := heCtx.S
  Y := heCtx.Y
  S_pgroup := heCtx.S_isPGroup
  S_sylow := he_S_sylow
  S_le_Y := heCtx.S_le_Y
  complete := by
    intro Z hZ
    obtain ⟨j, hj, hZeq⟩ := he_complete Z hZ
    by_cases h : j < 11
    · left
      exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
    · right
      rw [hZeq]
      simp [memberOrTop, h]
  card_Y := he_member_card
  card_J := he_card
  le_iff := he_Y_le_iff
  o2_ne_bot := by
    intro j hj
    obtain ⟨m, hm, hms⟩ := he_row j (by omega)
    have key : ∀ m ∈ heMems, m.order = 138240 → m.o2 = 64 := by decide
    have h1 : Nat.card ↥(heCtx.Y j) = 138240 := by
      rcases hj with rfl | rfl <;> rw [he_member_card _ (by norm_num)] <;> rfl
    have h2 := key m hm (hms.1.symm.trans h1)
    intro hb
    have h3 : Nat.card ↥(pCoreOf 2 (heCtx.Y j)) = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hms.2.1, h2] at h3
    omega
  simple :=
    @MulEquiv.isSimpleGroup ↥CFSG.Sporadic.He.J _ CFSG.Blueprint.NativeSporadic.He _
      CFSG.Sporadic.He.isSimpleGroup_He CFSG.Sporadic.He.heEquivJ.symm

end

theorem false_of_he_abstract {Γ : Type} [Group Γ] [Finite Γ] (hl : HeLat Γ)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (qe : (↥L ⧸ Subgroup.center ↥L) ≃* Γ) : False := by
  have hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := center_quot_eq_bot c
  have hcfg := config2_of_ctx c hmin hN hcen hIeq hYL
  have hcfgΓ := hcfg.of_equiv qe
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hcfgΓ.sylow hl.S_sylow
  have hcfgΓ' := hcfgΓ.of_equiv (MulAut.conj g)
  rw [hg] at hcfgΓ'
  exact He2.not_config2_he hl hcfgΓ'

section


theorem false_of_he {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .He) : False := by
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  exact false_of_he_abstract heLat c hmin hN hIeq hYL
    (((QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e).trans CFSG.Sporadic.He.heEquivJ)

end

end CFSG.Quasithin.ModH.He3
