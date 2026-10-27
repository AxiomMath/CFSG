module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Component

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open CFSG.Quasithin

theorem ffConclusion_of_mulAut_of_commutator_ne_bot
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A L : Subgroup (MulAut V)} (hK : CFSG.Open.IsKGroup ↥G)
    (hO2 : pCoreOf 2 G = ⊥) (hA : IsFFStarOffender G A)
    (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ ≠ ⊥) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (↥L ⧸ Subgroup.center ↥L) := by
  letI : Module (ZMod 2) (Additive V) := CFSG.RankThree.FFModules.moduleOfSq hV
  haveI : Finite (MulAut V) := inferInstanceAs (Finite (V ≃* V))
  obtain ⟨hAG, -, hAel0, hAmax⟩ := hA
  obtain ⟨hLG, hsn, hq⟩ := hL
  obtain ⟨hcomm, hsq⟩ := hAel0
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Representation (ZMod 2) ↥G (Additive V),
      ρ = (CFSG.RankThree.FFModules.autRep V).comp G.subtype := ⟨_, rfl⟩
  have hρinj : Function.Injective ρ := by
    rw [hρdef]
    exact CFSG.RankThree.FFModules.autRep_injective.comp G.subtype_injective
  have hfix : ∀ B : Subgroup ↥G,
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ B) = Nat.card (fixV (B.map G.subtype)) := by
    intro B
    rw [hρdef]
    exact CFSG.RankThree.FFModules.card_fixSub_autRep_comp G.subtype B
  have hmapA : (A.subgroupOf G).map G.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAG]
  have hmapL : (L.subgroupOf G).map G.subtype = L := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLG]
  have hx : ∀ x : ↥(A.subgroupOf G), ((x : ↥G) : MulAut V) ∈ A :=
    fun x => Subgroup.mem_subgroupOf.mp x.2
  have hAel : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf G) := by
    refine { is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hcomm _ (hx x) _ (hx y)
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simpa using hsq _ (hx x)
  have hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ (A.subgroupOf G) := by
    intro B hB
    have hBA : B.map G.subtype ≤ A := (Subgroup.map_mono hB).trans hmapA.le
    have hk := hAmax (B.map G.subtype) hBA
    have hcB : Nat.card (B.map G.subtype) = Nat.card B :=
      Subgroup.card_map_of_injective G.subtype_injective
    have hcA : Nat.card (A.subgroupOf G) = Nat.card A := by
      have h : Nat.card ((A.subgroupOf G).map G.subtype) = Nat.card (A.subgroupOf G) :=
        Subgroup.card_map_of_injective G.subtype_injective
      rw [hmapA] at h
      exact h.symm
    rw [hfix B, hfix (A.subgroupOf G), hmapA, hcA, ← hcB]
    exact hk
  have hO2' : CFSG.pCore 2 ↥G = ⊥ := by
    have h : (CFSG.pCore 2 ↥G).map G.subtype = ⊥ := hO2
    exact Subgroup.map_injective G.subtype_injective (h.trans (Subgroup.map_bot _).symm)
  have htop : G.comap G.subtype = ⊤ := by
    ext x
    simp
  have hL' : CFSG.Open.IsComponentOf (L.subgroupOf G) ⊤ := by
    refine ⟨le_top, ?_, hq.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG)⟩
    have h1 := hsn.comap G.subtype
    rw [htop] at h1
    exact h1
  have hLA' : ⁅L.subgroupOf G, A.subgroupOf G⁆ ≠ ⊥ := by
    intro h
    have h1 := congrArg (Subgroup.map G.subtype) h
    rw [Subgroup.map_commutator, hmapL, hmapA, Subgroup.map_bot] at h1
    exact hLA h1
  have hres := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_component hFF
    ↥G (Additive V) ρ hρinj hK hO2' (A.subgroupOf G) hAel hAbest (L.subgroupOf G) hL' hLA'
  have hcen : (Subgroup.center ↥(L.subgroupOf G)).map (Subgroup.subgroupOfEquivOfLe hLG) =
      Subgroup.center ↥L := Subgroup.map_center_eq _
  exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥(L.subgroupOf G)) (Subgroup.center ↥L)
      (Subgroup.subgroupOfEquivOfLe hLG) hcen) hres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg
