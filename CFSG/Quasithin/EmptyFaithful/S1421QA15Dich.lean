module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421

theorem isQuasisimple_of_isComponent {G : Type} [Group G] [Finite G] {G0 L : Subgroup G}
    (hL : L ∈ cComp G0) (hLn : (L.subgroupOf G0).Normal)
    (hsolv : Group.IsSolvable (↥G0 ⧸ L.subgroupOf G0)) {K : Subgroup ↥G0}
    (hK : CFSG.IsComponent K) : CFSG.IsQuasisimple ↥L := by
  have hKc : K ∈ cComp (⊤ : Subgroup ↥G0) := mem_cComp_top_of_isComponent hK
  have hL' : L.subgroupOf G0 ∈ cComp (⊤ : Subgroup ↥G0) := subgroupOf_mem_cComp hL
  have hKL : K ≤ L.subgroupOf G0 := by
    intro k hk
    have : Group.IsPerfect ↥K := hK.1.1
    have h1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
      ((QuotientGroup.mk' (L.subgroupOf G0)).comp K.subtype)
    have h2 := DFunLike.congr_fun h1 ⟨k, hk⟩
    simpa [QuotientGroup.eq_one_iff] using h2
  have hKeq : K = L.subgroupOf G0 := by
    by_contra hne
    exact not_subnormal_of_mem_cComp hL' (lt_of_le_of_ne hKL hne) (ne_bot_of_mem_cComp hKc)
      (perfect_of_mem_cComp hKc) (subnormal_of_mem_cComp hKc)
  have hq : CFSG.IsQuasisimple ↥(L.subgroupOf G0) := by
    rw [← hKeq]
    exact hK.1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hL)) hq

theorem pPrimeCore_eq_bot_of_oddCoreIn_eq_bot {G : Type} [Group G] {H : Subgroup G}
    (hO : oddCoreIn H = ⊥) : CFSG.pPrimeCore 2 ↥H = ⊥ := by
  have h1 : CFSG.Open.fusionOddCore ↥H = ⊥ := by
    have h0 : (CFSG.Open.fusionOddCore ↥H).map H.subtype = ⊥ := hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h0
  rw [← h1]
  unfold CFSG.pPrimeCore CFSG.Open.fusionOddCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem isQuasisimple_or_charTwo {G : Type} [Group G] [Finite G] {G0 L : Subgroup G}
    (hL : L ∈ cComp G0) (hLn : (L.subgroupOf G0).Normal)
    (hsolv : Group.IsSolvable (↥G0 ⧸ L.subgroupOf G0)) (hodd : oddCoreIn G0 = ⊥) :
    CFSG.IsQuasisimple ↥L ∨ CharTwo G0 := by
  by_cases hLq : CFSG.IsQuasisimple ↥L
  · exact Or.inl hLq
  · refine Or.inr ?_
    have hno : ∀ K : Subgroup ↥G0, ¬ CFSG.IsComponent K := fun K hK =>
      hLq (isQuasisimple_of_isComponent hL hLn hsolv hK)
    have hlayer : CFSG.layer ↥G0 = ⊥ := sSup_eq_bot.mpr fun K hK => absurd hK (hno K)
    have hcore : CFSG.pPrimeCore 2 ↥G0 = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn_eq_bot hodd
    have hc := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥G0 2 hcore hlayer
    rw [CFSG.QuasithinUnique.charTwo_iff_internal]
    exact hc

end S1421

end CFSG.Quasithin
