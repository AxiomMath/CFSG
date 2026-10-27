module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NF
public import CFSG.Quasithin.Vol2.KGFactAutSylowL2pOuter
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312H

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3312

open CFSG.Open CFSG.QuasithinUnique

namespace NQ

theorem subgroupOf_sup_eq_top {X : Type} [Group X] (H K : Subgroup X) :
    H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
  apply Subgroup.map_injective (H ⊔ K).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left le_sup_left, inf_of_le_left le_sup_right, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end NQ

theorem fact3312Nonquasi_of (hNorm : FactL2pSylowNorm)
    (hFour : FactL2pSylowFour) (hOut : FactAutL2pOuter) : Fact3312Nonquasi := by
  intro X _ _ B L hBL hNQ hA36 htype
  obtain ⟨hcomm, hcase, hext⟩ := NQ.a36case_of_nonquasi hNQ hA36
  have htype₀ : Type3312R (ModO2 (B.subgroupOf L)) := by
    obtain ⟨e⟩ := modO2_equiv_of_surjective (Subgroup.subgroupOfEquivOfLe hBL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBL).surjective (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subgroupOfEquivOfLe hBL).injective]
        exact IsPGroup.of_bot)
    exact Type3312R.of_equiv e.symm htype
  have hBO₀ := NQ.inf_oddCore_eq_bot htype₀
  have hO1 : ∀ hOL : ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥, CFSG.oddCore ↥L ≠ ⊥ := by
    intro hOL h
    apply hOL
    rw [h, Subgroup.map_bot, Subgroup.commutator_bot_left]
  rcases hNQ with ⟨hOL, hL, p, hp, hp2, hSL⟩ | ⟨hOL, ⟨p, hp, hp5, hp8, hSL⟩, N, hN, hNdef, hB5⟩
  ·
    have hBsup : B.subgroupOf L ⊔ CFSG.oddCore ↥L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBL, ← hL,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact NQ.oddNorm_case21 hcomm hcase hext htype₀ (hO1 hOL) hBsup hp hp2 hSL
  ·
    obtain ⟨e5⟩ := hB5
    subst hNdef
    have hBOL : B ⊓ (CFSG.oddCore ↥L).map L.subtype = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxB, l, hl, rfl⟩
      have : l ∈ B.subgroupOf L ⊓ CFSG.oddCore ↥L := ⟨Subgroup.mem_subgroupOf.mpr hxB, hl⟩
      rw [hBO₀, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    have hinf : B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⊓
        ((CFSG.oddCore ↥L).map L.subtype).subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) =
          ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxB, hxO⟩
      have : (x : X) ∈ B ⊓ (CFSG.oddCore ↥L).map L.subtype := ⟨hxB, hxO⟩
      rw [hBOL, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    have eB : ↥(B.subgroupOf L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      (Subgroup.subgroupOfEquivOfLe hBL).trans
        ((Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans
          ((NQ.equivQuotOfCompl hinf (NQ.subgroupOf_sup_eq_top _ _)).trans e5))
    exact NQ.oddNorm_case22 hNorm hFour hOut hcomm hcase hext htype₀ (hO1 hOL) hp hp5 hp8 hSL
      ⟨eB⟩

theorem fact3312Nonquasi_holds :
    Fact3312Nonquasi :=
  fact3312Nonquasi_of factL2pSylowNorm_holds KGAutSyl.factL2pSylowFour_holds
    KGAutSyl.factAutL2pOuter_holds

end CFSG.Quasithin.H13.L3312
