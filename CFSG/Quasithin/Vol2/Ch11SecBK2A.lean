module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch11G2Q8LeviG2
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace BK2

variable {G : Type} [Group G] [Finite G]

theorem inf_le_centralizer_of {L V T U : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (hlev : autOn (T ⊓ L) V ≤ perfectCore (autOn L V ⊓ SecA.stabW (U.subgroupOf V)))
    (hpt : ∀ h ∈ perfectCore (autOn L V ⊓ SecA.stabW (U.subgroupOf V)), ∀ u ∈ U.subgroupOf V,
      h u * u⁻¹ ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V) :
    T ⊓ L ≤ Subgroup.centralizer (U : Set G) := by
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hfix := KGNat.fix_of_perfect (perfectCore_perfect _)
    (fun h hh z hz => SecA.autOn_fixes_cV h
      (Subgroup.mem_inf.mp (perfectCore_le (autOn L V ⊓ SecA.stabW (U.subgroupOf V)) hh)).1
      z hz) hpt
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hLV ht.2
  have h1 := hfix _ (hlev (SecA.conjV_mem_autOn ht htV)) ⟨u, hUV hu⟩ hu
  have h2 := congrArg Subtype.val h1
  rw [SecA.conjV_apply_coe] at h2
  calc u * t = t * u * t⁻¹ * t := by rw [h2]
    _ = t * u := by group

end BK2

theorem factFlagOneCentral_holds : FactFlagOneCentral := by
  intro G _ _ L V T U n hV hn hLV _ hnat hTS _ hTL hCU hUV hst hidx hTU
  obtain ⟨_, hnat⟩ := hnat
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  have hP := SecA.isSylowTwoOf_autOn hLV hTL'
  have hFW : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (2 ^ n) 1 (U.subgroupOf V) := by
    refine ⟨fun z hz => hCU ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
    · have := (SecA.isEndStable_iff hLV _ U).mp hst
      rwa [SecA.inf_centralizer_subgroupOf] at this
    · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, pow_one]
    · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact (SecA.conjV_mem_stabW_iff hUV hyV).mpr (hTU hy.1)
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · exact BK2.inf_le_centralizer_of hLV hUV
      (KGNat.factSylowLeviSL3_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)
      (KGNat.factPointSL3_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)
  · exact BK2.inf_le_centralizer_of hLV hUV
      (KGNat.factSylowLeviSp4_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)
      (KGNat.factPointSp4_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)
  · exact BK2.inf_le_centralizer_of hLV hUV
      (G2Q8.factSylowLeviG2_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)
      (G2Q8.factPointG2A_holds K n hn hK _ hsq _ _ π hπ _ hP _ hFW)

end CFSG.Quasithin.Vol2.Ch11.SecB
