module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE9
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch
public import CFSG.Quasithin.Vol2.KGFactC31KG443Sec
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem barImage_m22_center_card_and_exists_e9
    {G : Type} [Group G] [Finite G] {M K : Subgroup G} (hK : K ∈ calC M)
    {Y : Type} [Group Y] {ψ : Bar2 M →* Y} {H : Subgroup Y}
    (himage : (barImage M K).map ψ = H) (hM22 : IsSpor H .M22) :
    (Nat.card (Subgroup.center (barImage M K)) = 1 ∨
      Nat.card (Subgroup.center (barImage M K)) = 3) ∧
    ∃ E : Subgroup (Bar2 M), E ≤ barImage M K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  let C : Subgroup (Bar2 M) := barImage M K
  have hcomp : CFSG.IsComponent C := uc22p22l_barImage_isComponent hK
  have hCq : CFSG.IsQuasisimple ↥C := hcomp.1
  have hodd : Odd (Nat.card (Subgroup.center ↥C)) := by
    obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv hK
    have hoddK : Odd (Nat.card (Subgroup.center (Bar2 K))) :=
      uc22p22l_odd_center_quotient (Λ := K)
    have hcard : Nat.card (Subgroup.center (Bar2 K)) =
        Nat.card (Subgroup.center ↥C) :=
      Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    rw [← hcard]
    exact hoddK
  obtain ⟨eH⟩ := hM22
  have hnabH : ∃ a b : ↥H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.Quasithin.KGC31.KG443.not_comm_m22
    exact ⟨eH.symm a, eH.symm b, fun h =>
      hab (by simpa using congrArg eH h)⟩
  have hHcenter : Subgroup.center ↥H = ⊥ := by
    have hmap : Subgroup.map (eH : ↥H →* CFSG.Blueprint.NativeSporadic.Carrier .M22)
        (Subgroup.center ↥H) = ⊥ := by
      rw [Subgroup.map_center_eq eH, CFSG.Quasithin.KGC31.KG443.center_m22]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥H) eH.injective).mp hmap
  let φ : ↥C →* ↥H :=
    (ψ.comp C.subtype).codRestrict H (fun c => by
      have hc : ψ (c : Bar2 M) ∈ C.map ψ := Subgroup.mem_map_of_mem ψ c.2
      rwa [show C.map ψ = H from himage] at hc)
  have hφsurj : Function.Surjective φ := by
    intro h
    have hh : (h : Y) ∈ C.map ψ := by
      rw [show C.map ψ = H from himage]
      exact h.2
    obtain ⟨c, hc, hψc⟩ := Subgroup.mem_map.1 hh
    exact ⟨⟨c, hc⟩, Subtype.ext (by
      change ψ (c : Bar2 M) = (h : Y)
      exact hψc)⟩
  have hφne : ∃ c : ↥C, φ c ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hnabH
    have ha : a ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
    obtain ⟨c, hc⟩ := hφsurj a
    exact ⟨c, by rw [hc]; exact ha⟩
  have hker_le : φ.ker ≤ Subgroup.center ↥C :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hCq hφne
  let eZ : (↥C ⧸ Subgroup.center ↥C) ≃* (↥H ⧸ Subgroup.center ↥H) :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple (φ := φ) hCq hφsurj hker_le
  let eHq : (↥H ⧸ Subgroup.center ↥H) ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hHcenter).trans QuotientGroup.quotientBot
  let eC : (↥C ⧸ Subgroup.center ↥C) ≃* ↥H := eZ.trans eHq
  have hcenter_cases : Nat.card (Subgroup.center ↥C) = 1 ∨
      Nat.card (Subgroup.center ↥C) = 3 :=
    @CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.m22_center_card_odd_cases
      ↥C inferInstance inferInstance hCq.1 hodd (eC.trans eH)
  obtain ⟨EH, hEH_ea, hEH_card⟩ :=
    CFSG.Quasithin.H13.Ch4.J4KX.exists_e9_of_isSporadic_M22 (X := ↥H) ⟨eH⟩
  let E0 : Subgroup (↥C ⧸ Subgroup.center ↥C) := EH.map eC.symm.toMonoidHom
  have hE0_ea : IsElemAbelian 3 E0 := hEH_ea.map eC.symm.toMonoidHom
  have hE0_card : Nat.card E0 = 9 := by
    rw [Subgroup.card_map_of_injective eC.symm.injective, hEH_card]
  obtain ⟨E, hE_ea, hE_card⟩ :=
    CFSG.Quasithin.H13.Ch4.J4KX.exists_e9_of_quotient
      (Subgroup.center ↥C) E0 hE0_ea hE0_card
  refine ⟨?_, ?_⟩
  · change Nat.card (Subgroup.center C) = 1 ∨ Nat.card (Subgroup.center C) = 3
    exact hcenter_cases
  · change ∃ E : Subgroup (Bar2 M), E ≤ C ∧ IsElemAbelian 3 E ∧ Nat.card E = 9
    exact ⟨E.map C.subtype, Subgroup.map_subtype_le E, hE_ea.map C.subtype,
      by rw [Subgroup.card_subtype C E, hE_card]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
