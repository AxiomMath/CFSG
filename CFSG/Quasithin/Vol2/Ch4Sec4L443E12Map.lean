module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E11Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E8Cent

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem exists_component (hF : A38Facts) (hS : Vol2Native.SchreierFactCat) (h4411 : Fact4411)
    (s : Setting443 G T M L B Tp VB)
    (hU : IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M)
    (h448 : oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G))
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hVL : VB = ⁅VB, perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆) :
    ∃ K : Subgroup G, K ≤ Subgroup.normalizer (B : Set G) ∧
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      CFSG.IsQuasisimple ↥K ∧ ¬ K ≤ M ∧ VB ≤ K ∧
      perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ K ∧
      Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer (K : Set G) =
        oddCoreIn (Subgroup.normalizer (B : Set G)) := by
  set GB := Subgroup.normalizer (B : Set G) with hGB
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  have hVGB : VB ≤ GB := VB_le_normalizer s
  have hLBGB : LB ≤ GB :=
    (perfectCore_le _).trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨K, hK, hKn, hKM, hVK, hLK, hC⟩ :=
    exists_normal_component hF hS h4411 (locConf_of s hU h448 h37 h38 h39 hVL)
  have hKK : (K.map GB.subtype).subgroupOf GB = K :=
    Subgroup.comap_map_eq_self_of_injective GB.subtype_injective K
  refine ⟨K.map GB.subtype, Subgroup.map_subtype_le _, fun x hx => ?_, ?_, fun h => ?_, ?_, ?_,
    ?_⟩
  · refine coe_mem_normalizer_map (x := ⟨x, hx⟩) ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    trivial
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective _ GB.subtype_injective) hK.1
  · exact hKM fun k hk => h (Subgroup.mem_map_of_mem _ hk)
  · rw [← Subgroup.map_subgroupOf_eq_of_le hVGB]
    exact Subgroup.map_mono hVK
  · rw [← Subgroup.map_subgroupOf_eq_of_le hLBGB]
    exact Subgroup.map_mono hLK
  · ext x
    constructor
    · rintro ⟨hx, hxc⟩
      have h1 : (⟨x, hx⟩ : ↥GB) ∈ Subgroup.centralizer (K : Set ↥GB) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc _ (Subgroup.mem_map_of_mem _ hk))
      rw [hC] at h1
      exact (mem_oddCoreIn_iff GB ⟨x, hx⟩).mpr h1
    · intro hx
      have hxGB : x ∈ GB := oddCoreIn_le GB hx
      have h1 := (mem_oddCoreIn_iff GB ⟨x, hxGB⟩).mp hx
      rw [← hC] at h1
      refine ⟨hxGB, coe_mem_centralizer (Subgroup.map_subtype_le K) (x := ⟨x, hxGB⟩) ?_⟩
      rw [hKK]
      exact h1

end CFSG.Quasithin.H13.Ch4.E443
