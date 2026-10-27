module

public import CFSG.Quasithin.Background.RonanE114SevenWr
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IG

public section

namespace CFSG.Quasithin.RonanE114.Seven

open CFSG.Wreathed CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Quasithin CFSG.Quasithin.A1b
  CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_one_of_wreathed_of_sup_centralizer_eq {L : Subgroup G}
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (h2 : 2 ∣ Nat.card L)
    (hwr : ∀ S : Sylow 2 ↥L, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup ↥L) ≃* CFSG.Open.WreathedTwoGroup m))
    (hgen : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
      (L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        (L ⊓ Subgroup.centralizer ({y} : Set G)) = L)
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
  set zL : ↥L := ⟨z, hzL⟩ with hzLdef
  have hzS : zL ∈ (S : Subgroup ↥L) := by
    rw [hScoe, Subgroup.mem_subgroupOf]
    exact ⟨hzT, hzL⟩
  have hzBL : zL ∈ BL := by
    refine mem_modelBase_of_central m hm S e' hzS fun s hs => ?_
    rw [hScoe, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (hzc _ hs.1)
  have hz2L : orderOf zL = 2 := by
    rw [hzLdef, ← hz2, Subgroup.orderOf_mk]
  haveI : IsSimpleGroup ↥L := hAS.simple
  obtain ⟨g, hgN, hgz⟩ := exists_normalizer_moves hAS.nonabelian m hm S e' hzBL hz2L
  set sL : ↥L := g * zL * g⁻¹ with hsLdef
  have hsBL : sL ∈ BL := by
    rw [hsLdef]
    exact (Subgroup.mem_normalizer_iff.mp hgN zL).mp hzBL
  have hsne : sL ≠ zL := by
    rw [hsLdef]
    exact hgz
  have hs2L : orderOf sL = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) zL
    rw [MulAut.conj_apply] at h
    rw [hsLdef, h, hz2L]
  have hcommL : zL * sL = sL * zL := modelBase_comm S e' hzBL hsBL
  have hcomm : z * (sL : G) = (sL : G) * z := by
    simpa [hzLdef] using congrArg (Subtype.val) hcommL
  have hne : z ≠ (sL : G) := by
    intro h
    apply hsne
    exact Subtype.ext (by simpa [hzLdef] using h.symm)
  have hs2 : orderOf (sL : G) = 2 := by
    rw [Subgroup.orderOf_coe, hs2L]
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hpair := hgen z hzL (sL : G) sL.2 hz2 hs2 hne hcomm
  have hLle : L ≤ C ⊔ N := by
    rw [← hpair]
    refine sup_le ?_ ?_
    · exact inf_le_right.trans le_sup_left
    · intro x hx
      have hxL : x ∈ L := hx.1
      have hxs : x * (sL : G) = (sL : G) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hyL : (g : G)⁻¹ * x * (g : G) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem g.2) hxL) g.2
      have hscoe : ((sL : ↥L) : G) = (g : G) * z * (g : G)⁻¹ := by
        simp [hsLdef, hzLdef]
      have hyc : (g : G)⁻¹ * x * (g : G) ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g : G)⁻¹ * x * (g : G) * z
            = (g : G)⁻¹ * (x * ((g : G) * z * (g : G)⁻¹)) * (g : G) := by group
          _ = (g : G)⁻¹ * (((g : G) * z * (g : G)⁻¹) * x) * (g : G) := by
                rw [← hscoe, hxs]
          _ = z * ((g : G)⁻¹ * x * (g : G)) := by group
      have hyX : (g : G)⁻¹ * x * (g : G) ∈ C ⊔ N :=
        (show L ⊓ Subgroup.centralizer ({z} : Set G) ≤ C ⊔ N from
          inf_le_right.trans le_sup_left) ⟨hyL, hyc⟩
      have hgX : (g : G) ∈ C ⊔ N := (show N ≤ C ⊔ N from le_sup_right) (hmemN g hgN)
      have hxeq : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
      rw [hxeq]
      exact (C ⊔ N).mul_mem ((C ⊔ N).mul_mem hgX hyX) ((C ⊔ N).inv_mem hgX)
  have hCN : C ⊔ N = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← SecU1.L3I.sup_eq_top_of_almostSimple hAS hT]
    exact sup_le hLle (hTN.trans le_sup_right)
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
