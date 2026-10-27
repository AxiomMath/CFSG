module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section ModuleTheory

variable {W : Type} [CommGroup W] [Finite W]

private theorem s15_Three_semisimple_of_sSup_irr {A : Subgroup (MulAut W)}
    (hgen : sSup {I : Subgroup W | IsIrrOn A I ⊥} = ⊤) : s15Semisimple A := by
  intro S hS
  let F : Set (Subgroup W) := {S' : Subgroup W | StableUnder A S' ∧ S ⊓ S' = ⊥}
  have hbot : (⊥ : Subgroup W) ∈ F := by
    refine ⟨?_, by simp⟩
    intro a _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  obtain ⟨S', hS'mem, hmax⟩ := Set.exists_max_image F (fun S' => Nat.card S')
    (Set.toFinite F) ⟨⊥, hbot⟩
  refine ⟨S', hS'mem.1, hS'mem.2, ?_⟩
  by_contra hne
  have hnot : ¬ (⊤ : Subgroup W) ≤ S ⊔ S' := fun h => hne (le_antisymm le_top h)
  obtain ⟨I, hIirr, hInle⟩ : ∃ I : Subgroup W, IsIrrOn A I ⊥ ∧ ¬ I ≤ S ⊔ S' := by
    by_contra h
    have h' : ∀ I : Subgroup W, IsIrrOn A I ⊥ → I ≤ S ⊔ S' := by
      intro I hI
      by_contra hle
      exact h ⟨I, hI, hle⟩
    have hle : (⊤ : Subgroup W) ≤ S ⊔ S' := by
      rw [← hgen]
      exact sSup_le h'
    exact hnot hle
  have hSsup : StableUnder A (S ⊔ S') := s15_Three_stableUnder_sup hS hS'mem.1
  have hdisjI : I ⊓ (S ⊔ S') = ⊥ := by
    rcases s15_Three_irr_inf_or_le hIirr hSsup with h | h
    · exact h
    · exact absurd h hInle
  have hTmem : S' ⊔ I ∈ F := by
    refine ⟨s15_Three_stableUnder_sup hS'mem.1 hIirr.2.1, ?_⟩
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_sup] at hx
    obtain ⟨hxS, s', hs', i, hi, hx_eq⟩ := hx
    have hiS : i ∈ S ⊔ S' := by
      have hsi : i = s'⁻¹ * x := by rw [← hx_eq]; group
      rw [hsi]
      exact (S ⊔ S').mul_mem ((S ⊔ S').inv_mem (Subgroup.mem_sup_right hs'))
        (Subgroup.mem_sup_left hxS)
    have hi1 : i = 1 := by
      have hIbot : i ∈ I ⊓ (S ⊔ S') := ⟨hi, hiS⟩
      rw [hdisjI, Subgroup.mem_bot] at hIbot
      exact hIbot
    have hxS' : x ∈ S ⊓ S' := by
      refine ⟨hxS, ?_⟩
      rw [← hx_eq, hi1, mul_one]
      exact hs'
    rw [hS'mem.2] at hxS'
    exact hxS'
  have hneT : S' ≠ S' ⊔ I := by
    intro hEq
    refine hInle ?_
    calc I ≤ S' := le_sup_right.trans_eq hEq.symm
      _ ≤ S ⊔ S' := le_sup_right
  have hlt : S' < S' ⊔ I := lt_of_le_of_ne le_sup_left hneT
  exact absurd (hmax (S' ⊔ I) hTmem) (not_le.2 (Subgroup.card_lt_of_lt hlt))

end ModuleTheory

section Restrict

variable {W : Type} [CommGroup W] [Finite W]

private theorem s15_Three_semisimple_restrict {A : Subgroup (MulAut W)}
    (hsemi : s15Semisimple A) {Y : Subgroup W} (hY : StableUnder A Y) :
    s15Semisimple (autSub A Y) := by
  have hA : A ≤ stabSub Y := by
    intro a ha
    refine mem_stabSub.2 fun u => ⟨fun hu => ?_, fun hu => hY a ha u hu⟩
    have hmem : a.symm (a u) ∈ Y := hY a.symm (A.inv_mem ha) (a u) hu
    simpa using hmem
  intro S hS
  have hS'stab : StableUnder A (S.map Y.subtype) := by
    intro a ha u hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hu
    have hayY : a (y : W) ∈ Y := (mem_stabSub.1 (hA ha) (y : W)).2 y.2
    refine Subgroup.mem_map.2 ⟨⟨a (y : W), hayY⟩, ?_, rfl⟩
    have hres : resHom Y ⟨a, hA ha⟩ ∈ autSub A Y :=
      mem_autSub.2 ⟨⟨a, hA ha⟩, ha, rfl⟩
    have hmem := hS (resHom Y ⟨a, hA ha⟩) hres y hy
    have hEq : (⟨a (y : W), hayY⟩ : ↥Y) = resHom Y ⟨a, hA ha⟩ y := Subtype.ext rfl
    rw [hEq]
    exact hmem
  obtain ⟨C, hCstab, hCdisj, hCsup⟩ := hsemi (S.map Y.subtype) hS'stab
  refine ⟨C.comap Y.subtype, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_autSub.1 hx
    have hyC : (y : W) ∈ C := Subgroup.mem_comap.mp hy
    have hayC : (a : MulAut W) (y : W) ∈ C := hCstab (a : MulAut W) ha (y : W) hyC
    exact Subgroup.mem_comap.mpr (by simpa [resHom_apply] using hayC)
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyS, hyC⟩ := hy
    have hyC' : (y : W) ∈ C := Subgroup.mem_comap.mp hyC
    have hmem : (y : W) ∈ S.map Y.subtype ⊓ C :=
      ⟨Subgroup.mem_map.2 ⟨y, hyS, rfl⟩, hyC'⟩
    rw [hCdisj, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  · rw [eq_top_iff]
    intro y _
    have hyW : (y : W) ∈ S.map Y.subtype ⊔ C := by
      rw [hCsup]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup] at hyW
    obtain ⟨s, hsS', c, hcC, hsc⟩ := hyW
    obtain ⟨sy, hsy, hsy_eq⟩ := Subgroup.mem_map.1 hsS'
    have hcY : c ∈ Y := by
      have hsY : s ∈ Y := by rw [← hsy_eq]; exact sy.2
      have hc : c = s⁻¹ * (y : W) := by rw [← hsc]; group
      rw [hc]
      exact Y.mul_mem (Y.inv_mem hsY) y.2
    refine Subgroup.mem_sup.2 ⟨sy, hsy, ⟨⟨c, hcY⟩, ?_, ?_⟩⟩
    · exact Subgroup.mem_comap.mpr hcC
    · apply Subtype.ext
      show ((sy : W) * c) = (y : W)
      rw [← hsc]
      exact congrArg (fun z : W => z * c) hsy_eq

end Restrict

section Semisimple

variable {D : Data G} {V₀ V L : Subgroup G}

theorem s15_Three_semisimple_AW_of_sSup_irr (h : Hyp151 D V₀ V L)
    (hgen : sSup {I : Subgroup (vStar D.M V₀ V h.isElemAbelian L) |
      IsIrrOn (lStar D.M V₀ V h.isElemAbelian L) I ⊥} = ⊤) :
    s15Semisimple (s15AW h) := by
  have hY : StableUnder (lStar D.M V₀ V h.isElemAbelian L)
      (wStar D.M V₀ V h.isElemAbelian L) := by
    intro a ha u hu
    exact (mem_stabSub.1 (s15_Three_lStar_le_stabSub h ha) u).2 hu
  exact s15_Three_semisimple_restrict (s15_Three_semisimple_of_sSup_irr hgen) hY

end Semisimple

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
