module

public import CFSG.Quasithin.EmptyFaithful.ModHM24e

public section

namespace CFSG.Quasithin.ModH.M24f

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms


theorem false_of_m24 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M24) : False := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  let qe : (↥L ⧸ Subgroup.center ↥L) ≃* M24a.G24 :=
    (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
  have hin : inner M24a.G24 = ⊤ :=
    CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
      CFSG.Sporadic.Schreier.m24_mulAut_card
  have hinn : ∀ α : MulAut M24a.G24, ∃ g : M24a.G24, MulAut.conj g = α := by
    intro α
    have : α ∈ inner M24a.G24 := by rw [hin]; exact Subgroup.mem_top α
    exact this
  obtain ⟨hinnQ, hcenQ⟩ := inner_of_equiv_of_inner qe hinn CFSG.Sporadic.Schreier.m24_center_eq_bot'
  obtain ⟨ρ, -, hρ⟩ := exists_rho hLI hN hinnQ hcenQ
  have hcfg : Config M24a.G24 := (config_of_ctx c hmin hN hIeq hYL ρ hρ).of_equiv qe
  obtain ⟨hns, Sb, Yb, hd⟩ := hcfg
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hd.sylow M24b.Sg_sylow
  have hd' := hd.of_equiv (MulAut.conj g)
  rw [hg] at hd'
  exact M24e.not_configData_m24 hns hd'

end CFSG.Quasithin.ModH.M24f
