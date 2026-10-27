module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSetup
public import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem center_Halpha_eq_zpowers {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (h5 : Subgroup.centralizer ((S : Set G) ∩ D) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hΔH : (S : Set G) ∩ D ⊆ Halpha D hC.alpha := by
      rw [hU.sylow_inter]
      rintro _ ⟨v, hv, rfl⟩
      exact (Halpha D hC.alpha).mul_mem (d_mem_Halpha hC h3)
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hv))
    have hxC : (x : G) ∈ Subgroup.centralizer ((S : Set G) ∩ D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hΔH hy⟩)
    rw [h5] at hxC
    obtain ⟨x', hx'T, hx'x⟩ := Subgroup.mem_map.mp hxC
    have hxx' : x' = x := Subtype.ext hx'x
    subst hxx'
    have hxP : x' ∈ CFSG.pCore 2 (Halpha D hC.alpha) :=
      mem_pCore_of_mem_center hx ((T.isPGroup').to_le ((Subgroup.zpowers_le).mpr hx'T))
    rw [← h3.2.1]
    exact Subgroup.mem_map_of_mem _ hxP
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨hC.d, d_mem_Halpha hC h3⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun h => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC h.2))

theorem nonempty_pResidualOf_mulEquiv {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (h5 : Subgroup.centralizer ((S : Set G) ∩ D) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    Nonempty (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≃*
      Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) := by
  obtain ⟨C, hCn, hCZ, -, ⟨e⟩⟩ := exists_quotient_mulEquiv_pResidualOf hC h3
  have hZ := center_Halpha_eq_zpowers h3 hU h5
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ := hCZ hx
    have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
      Subgroup.map_subtype_le _
    have hxH : ((x : _) : G) ∈ Halpha D hC.alpha := hLH x.2
    have hxcomm : ∀ h ∈ Halpha D hC.alpha, Commute ((x : _) : G) h := by
      intro h hh
      rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hh with hl | hl
      · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨h, hl⟩).symm
      · have hc1 : Commute ((x : _) : G) (hC.d * h) :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨_, hl⟩).symm
        have hc2 : Commute ((x : _) : G) hC.d :=
          (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hxH))
        have : h = hC.d * (hC.d * h) := by
          rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul]
        rw [this]
        exact hc2.mul_right hc1
    have hxZH : ((x : _) : G) ∈ (Subgroup.center (Halpha D hC.alpha)).map
        (Halpha D hC.alpha).subtype := by
      refine ⟨⟨_, hxH⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
      exact (hxcomm h h.2).eq.symm
    rw [hZ] at hxZH
    have h1 := Subgroup.disjoint_def.mp h3.2.2.2 hxZH x.2
    exact Subtype.ext h1
  subst hCbot
  exact ⟨(QuotientGroup.quotientBot.symm).trans e⟩

theorem pResidualOf_le_commutator {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (h5 : Subgroup.centralizer ((S : Set G) ∩ D) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ commutator G := by
  obtain ⟨e⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5
  have hB : CFSG.BenderSuzuki.IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
    isBenderGroup_of_mulEquiv e hH.bender
  have hc := IsBenderGroup.commutator_eq_top hB
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  have hperf : ⁅L, L⁆ = L := by
    have h := congrArg (Subgroup.map L.subtype) hc
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  rw [← hperf]
  exact Subgroup.commutator_mono le_top le_top

end CFSG.OddTranspositions.PartThree.Nine
