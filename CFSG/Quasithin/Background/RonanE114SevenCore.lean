module

public import CFSG.Quasithin.Background.RonanE114SevenWr
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IG

public section

namespace CFSG.Quasithin.RonanE114.Seven

open CFSG.Wreathed CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Quasithin CFSG.Quasithin.A1b
  CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_one_of_wreathed {L : Subgroup G} (hAS : SecE3.AlmostSimple L) {T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (h2 : 2 ∣ Nat.card L)
    (hwr : ∀ S : Sylow 2 ↥L, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup ↥L) ≃* CFSG.Open.WreathedTwoGroup m))
    (hmax : ∀ x ∈ L, orderOf x = 2 → IsCoatom (Subgroup.centralizer ({x} : Set G)))
    (hn1 : ∀ x ∈ L, orderOf x = 2 → E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := hAS.normal
  obtain ⟨z, hzL, hz2, hzT, hzc⟩ := SecU1.L3I.exists_central_involution_of_normal hLn h2 hT
  have hSyl : IsSylowIn 2 (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  set S : Sylow 2 ↥L := hSyl.toSylow with hS
  have hScoe : (S : Subgroup ↥L) = (T ⊓ L).subgroupOf L := rfl
  obtain ⟨m, hm, ⟨e⟩⟩ := hwr S
  have e' : ↥(S : Subgroup ↥L) ≃* Wreath (2 ^ m) := e
  set BL : Subgroup ↥L := modelBase S e' with hBL
  set B : Subgroup G := BL.map L.subtype with hB
  set N : Subgroup G := Subgroup.normalizer (B : Set G) with hN
  set ι : Wreath (2 ^ m) →* G := L.subtype.comp (wreathModelHom S e') with hι
  have hιinj : Function.Injective ι := L.subtype_injective.comp (wreathModelHom_injective S e')
  have hBι : B = (baseSubgroup (2 ^ m)).map ι := by
    rw [hB, hBL, modelBase, Subgroup.map_map]
  have hrange : ι.range = T ⊓ L := by
    rw [hι, MonoidHom.range_comp, wreathModelHom_range S e', hScoe]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hTN : T ≤ N := by
    intro t ht
    have htn : t ∈ Subgroup.normalizer (ι.range : Set G) := by
      rw [hrange, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyT, hyL⟩
        exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht), hLn.conj_mem y hyL t⟩
      · rintro ⟨hyT, hyL⟩
        refine ⟨?_, ?_⟩
        · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
          simpa [mul_assoc] using this
        · have := hLn.conj_mem _ hyL t⁻¹
          simpa [mul_assoc] using this
    rw [hN, hBι]
    exact mem_normalizer_map_of_characteristic ι hιinj
      (base_characteristic (2 ^ m) (by
        have : 4 ≤ 2 ^ m := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega)) htn
  haveI : Group.IsSolvable ↥(Subgroup.normalizer (BL : Set ↥L)) :=
    isSolvable_normalizer_modelBase m hm S e'
  haveI : Group.IsNilpotent (G ⧸ L) := hAS.isPGroup_quotient.isNilpotent
  have hmemN : ∀ g : ↥L, g ∈ Subgroup.normalizer (BL : Set ↥L) → (g : G) ∈ N := fun g hg => by
    have := Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem _ hg)
    exact this
  have hNsolv : Group.IsSolvable ↥N := by
    let f : ↥(Subgroup.normalizer (BL : Set ↥L)) →* ↥N :=
      (L.subtype.comp (Subgroup.normalizer (BL : Set ↥L)).subtype).codRestrict N
        (fun g => hmemN g.1 g.2)
    refine Group.isSolvable_of_ker_le_range f (QuotientGroup.mk' L |>.comp N.subtype) ?_
    intro n hn
    have hnL : (n : G) ∈ L := (QuotientGroup.eq_one_iff _).mp hn
    have hnN : (n : G) ∈ N := n.2
    refine ⟨⟨⟨n, hnL⟩, ?_⟩, Subtype.ext rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy := Subgroup.mem_normalizer_iff.mp hnN (y : G)
    have hmap : ∀ u : ↥L, u ∈ BL ↔ (u : G) ∈ B := fun u =>
      (Subgroup.mem_map_iff_mem L.subtype_injective).symm
    rw [hmap, hmap]
    exact hy
  have hzS : (⟨z, hzL⟩ : ↥L) ∈ (S : Subgroup ↥L) := by
    rw [hScoe, Subgroup.mem_subgroupOf]
    exact ⟨hzT, hzL⟩
  have hzBL : (⟨z, hzL⟩ : ↥L) ∈ BL := by
    refine mem_modelBase_of_central m hm S e' hzS fun s hs => ?_
    rw [hScoe, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (hzc _ hs.1)
  have hz2L : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by
    rw [← hz2, Subgroup.orderOf_mk]
  haveI : IsSimpleGroup ↥L := hAS.simple
  obtain ⟨g, hgN, hgz⟩ := exists_normalizer_moves hAS.nonabelian m hm S e' hzBL hz2L
  have hnotC : ¬ N ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hle
    have hg := hle (hmemN g hgN)
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    apply hgz
    apply Subtype.ext
    have : (g : G) * z * (g : G)⁻¹ = z := by
      rw [hg]
      group
    exact this
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hCmax : IsCoatom C := hmax z hzL hz2
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hCN : C ⊔ N = ⊤ :=
    hCmax.2 _ (lt_of_le_of_ne le_sup_left fun h => hnotC (h ▸ le_sup_right))
  refine E1.nParam_le_of_generated (Δ := {C, N}) hT ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    exact hCN
  · intro D hD
    rcases hD with rfl | rfl
    · exact hTC
    · exact hTN
  · intro D hD
    rcases hD with rfl | rfl
    · exact hn1 z hzL hz2
    · exact E1.solvable_nParam_le_one hNsolv

end CFSG.Quasithin.RonanE114.Seven
