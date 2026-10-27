module

public import CFSG.Quasithin.EmptyFaithful.S146zWK
public import CFSG.Quasithin.EmptyFaithful.S146zWI
public import CFSG.Quasithin.EmptyFaithful.S146zWH

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.C2Push CFSG.Quasithin.S146zV CFSG.Quasithin.SBc17
open scoped commutatorElement

theorem input14615OuterSylowOut_proved
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h56 : AsB56)
    (hA21 : AsA21SQTKSection) : Input14615OuterSylowOut := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hR hex
  have hcfg : WreathCfg (g2_14615 K₂) (pCoreOf 2 (mcOf T)) J :=
    ⟨hHyp.sqtk, hchar, hHyp.radical,
      hHyp.cgs.trans (le_of_eq (normalizer_inf_eq_g12 hHyp).symm), hJc, hJq, hR⟩
  obtain ⟨J', ρ, d⟩ := hcfg.exists_data (hOrb G)
  by_cases hsmall : Nat.card ((↥J ⧸ CFSG.pCore 2 ↥J) ⧸
      Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) < 504
  · exfalso
    obtain ⟨k, hkK, hk5, hkn⟩ := hout
    have hkJ : k ∈ Subgroup.normalizer (J : Set G) := sup_le hK₁N hK₂N hkK
    have hk5' : k ^ 5 = 1 := by
      rw [← hk5]
      exact pow_orderOf_eq_one k
    exact hkn (mem_innerSub_of_out5_quot (d.out5Inner_of_small h56 hA21 hsmall) hkJ hk5')
  · exact d.isSylowTwoOf_inf_of_large h56 hA21
      ((not_lt.mp hsmall).trans d.card_center_quot_le_wAut)

theorem input14615ContraOuterE_proved
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h56 : AsB56)
    (hA21 : AsA21SQTKSection) : Input14615ContraOuterE :=
  input14615ContraOuterE_of_sylowOut hC129 (input14615OuterSylowOut_proved hOrb h56 hA21)

end CFSG.Quasithin.S146zW
