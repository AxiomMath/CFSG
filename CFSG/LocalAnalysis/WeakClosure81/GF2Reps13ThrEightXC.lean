module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX.isPGroup
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem w16g_map_map_conj (U : Subgroup W) (g h : MulAut W) :
    (U.map h.toMonoidHom).map g.toMonoidHom = U.map (g * h).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_map_map_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map g⁻¹.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have hcomp : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem w16g_stableUnder_iSup_map_orbit {U₀ : Subgroup W}
    {Y : Subgroup (MulAut W)} : StableUnder Y (⨆ g ∈ Y, U₀.map g.toMonoidHom) := by
  intro a ha u hu
  refine Subgroup.iSup_induction (fun g : MulAut W => ⨆ (_ : g ∈ Y), U₀.map g.toMonoidHom)
    (C := fun u => a u ∈ ⨆ g ∈ Y, U₀.map g.toMonoidHom) hu ?_ ?_ ?_
  · intro g u hu'
    refine Subgroup.iSup_induction (fun _ : g ∈ Y => U₀.map g.toMonoidHom)
      (C := fun u => a u ∈ ⨆ g ∈ Y, U₀.map g.toMonoidHom) hu' ?_ ?_ ?_
    · intro hg v hv
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
      exact le_iSup₂ (f := fun g (_ : g ∈ Y) => U₀.map g.toMonoidHom)
        (a * g) (Y.mul_mem ha hg)
        (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro x y hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy

theorem s13_eight_comps_rk (h : Cfg133 A t 3) (hI : IsIndivisible A) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N) :
    commSub ⊤ (conjClosure A (Subgroup.zpowers z)) = ⊤ ∧
      ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)), rk ↥U = 6 := by
  classical
  let X : Subgroup (MulAut W) := conjClosure A (Subgroup.zpowers z)
  let W6 : Subgroup W := commSub ⊤ (Subgroup.zpowers z)
  let C : Set (Subgroup W) := s13IsoComps X
  let O6 : Set (Subgroup W) := {U | ∃ g ∈ A, U = W6.map g.toMonoidHom}
  let S1 : Subgroup W := ⨆ g ∈ A, W6.map g.toMonoidHom
  let S2 : Subgroup W := ⨆ U ∈ C \ O6, U
  obtain ⟨hXe, hXA, hXO, hcent⟩ := w16g_s13_eight_X_facts h hD
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have hodd : Odd (Nat.card X) :=
    w16g_odd_card_of_isElemAbelian Nat.prime_three (by norm_num) hXe
  have hzpX : Subgroup.zpowers z ≤ X :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure
      ⟨1, A.one_mem, z, Subgroup.mem_zpowers z, by group⟩)
  have hW6mem : W6 ∈ C := s13_eight_W6_comp h hD
  have hW6ne : W6 ≠ ⊥ := (s13IsoComps_le_commSub h.hW hodd hW6mem).1
  have hIndep : sSupIndep C := s13IsoComps_sSupIndep h.hW hodd
  have hfix_stab : StableUnder A (fixV X) := stableUnder_fixV hXA
  have hcomm_stab : StableUnder A (commSub ⊤ X) :=
    stableUnder_commSub hXA (fun _ _ _ _ => Subgroup.mem_top _)
  have hsup : fixV X ⊔ commSub ⊤ X = ⊤ :=
    CFSG.Quasithin.Asc81c.fixV_sup_commSub_eq_top' hW2 hodd
  have hcommX_top : commSub ⊤ X = ⊤ := by
    rcases hI (fixV X) (commSub ⊤ X) hfix_stab hcomm_stab hsup with hfix | hcomm
    · exfalso
      have hbot : W6 = ⊥ := by
        change commSub ⊤ (Subgroup.zpowers z) = ⊥
        rw [commSub_eq_bot_iff]
        intro w _
        rw [mem_fixV]
        intro y hy
        exact (mem_fixV.mp (by rw [hfix]; exact Subgroup.mem_top w)) y (hzpX hy)
      exact hW6ne hbot
    · exact hcomm
  have hO6sub : O6 ⊆ C := by
    rintro U ⟨g, hg, rfl⟩
    exact map_mem_s13IsoComps (hXA g hg)
      (fun x hx => by simpa only [inv_inv] using hXA g⁻¹ (A.inv_mem hg) x hx) hW6mem
  have hS1stab : StableUnder A S1 := w16g_stableUnder_iSup_map_orbit
  have hS2stab : StableUnder A S2 := by
    intro g hg u hu
    refine Subgroup.iSup_induction (fun U : Subgroup W => ⨆ (_ : U ∈ C \ O6), U)
      (C := fun u => g u ∈ S2) hu ?_ ?_ ?_
    · intro U u hu'
      refine Subgroup.iSup_induction (fun _ : U ∈ C \ O6 => U)
        (C := fun u => g u ∈ S2) hu' ?_ ?_ ?_
      · intro hU v hv
        have hmapC : U.map g.toMonoidHom ∈ C :=
          map_mem_s13IsoComps (hXA g hg)
            (fun x hx => by simpa only [inv_inv] using hXA g⁻¹ (A.inv_mem hg) x hx) hU.1
        have hmapnot : U.map g.toMonoidHom ∉ O6 := by
          intro hmem
          obtain ⟨k, hk, hkU⟩ := hmem
          apply hU.2
          refine ⟨g⁻¹ * k, A.mul_mem (A.inv_mem hg) hk, ?_⟩
          have h1 : (U.map g.toMonoidHom).map g⁻¹.toMonoidHom =
              W6.map (g⁻¹ * k).toMonoidHom := by
            rw [hkU]
            exact w16g_map_map_conj W6 g⁻¹ k
          rwa [w16g_map_map_inv U g] at h1
        exact le_iSup₂ (f := fun U (_ : U ∈ C \ O6) => U)
          (U.map g.toMonoidHom) ⟨hmapC, hmapnot⟩
          (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro x y hx hy
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro x y hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  have hW6memO6 : W6 ∈ O6 := ⟨1, A.one_mem, by ext w; simp⟩
  have hcover : ∀ U ∈ C, U ≤ S1 ⊔ S2 := by
    intro U hU
    by_cases hmem : U ∈ O6
    · obtain ⟨g, hg, rfl⟩ := hmem
      exact le_sup_of_le_left
        (le_iSup₂ (f := fun g (_ : g ∈ A) => W6.map g.toMonoidHom) g hg)
    · exact le_sup_of_le_right
        (le_iSup₂ (f := fun U (_ : U ∈ C \ O6) => U) U ⟨hU, hmem⟩)
  have hUnion_le : (⨆ U ∈ C, U) ≤ S1 ⊔ S2 :=
    iSup_le fun U => iSup_le fun hU => hcover U hU
  have hUnion_top : (⨆ U ∈ C, U) = ⊤ := by
    change (⨆ U ∈ s13IsoComps X, U) = ⊤
    rw [iSup_s13IsoComps h.hW hodd, hcommX_top]
  have hS1S2top : S1 ⊔ S2 = ⊤ := by
    apply le_antisymm le_top
    rw [← hUnion_top]
    exact hUnion_le
  have hS2le : S2 ≤ sSup (C \ {W6}) := by
    change (⨆ U ∈ C \ O6, U) ≤ sSup (C \ {W6})
    refine iSup_le fun U => iSup_le fun hU => le_sSup ?_
    exact ⟨hU.1, fun h => hU.2 ((Set.mem_singleton_iff.mp h).symm ▸ hW6memO6)⟩
  have hdisjW6 : Disjoint W6 (sSup (C \ {W6})) :=
    hIndep.disjoint_sSup hW6mem (fun _ hV => hV.1) (by simp)
  have hS2ne : S2 ≠ ⊤ := by
    intro htop
    have hleS2 : W6 ≤ S2 := by rw [htop]; exact le_top
    have hle : W6 ≤ sSup (C \ {W6}) := hleS2.trans hS2le
    exact hW6ne (hdisjW6.eq_bot_of_le hle)
  have hS1top : S1 = ⊤ := by
    rcases hI S1 S2 hS1stab hS2stab hS1S2top with h | h
    · exact h
    · exact absurd h hS2ne
  have hallO6 : C ⊆ O6 := by
    intro U hU
    by_contra hUnot
    have hsub : O6 ⊆ C \ {U} := by
      intro V hV
      exact ⟨hO6sub hV, fun hVU => hUnot (Set.mem_singleton_iff.mp hVU ▸ hV)⟩
    have hS1le : S1 ≤ sSup (C \ {U}) := by
      change (⨆ g ∈ A, W6.map g.toMonoidHom) ≤ sSup (C \ {U})
      refine iSup_le fun g => iSup_le fun hg => le_sSup (hsub ⟨g, hg, rfl⟩)
    have hdisjU : Disjoint U (sSup (C \ {U})) :=
      hIndep.disjoint_sSup hU (fun _ hV => hV.1) (by simp)
    have hUle : U ≤ sSup (C \ {U}) :=
      (show U ≤ S1 from by rw [hS1top]; exact le_top).trans hS1le
    have hbot : U = ⊥ := hdisjU.eq_bot_of_le hUle
    exact (s13IsoComps_le_commSub h.hW hodd hU).1 hbot
  refine ⟨hcommX_top, ?_⟩
  intro U hU
  obtain ⟨g, hg, rfl⟩ := hallO6 hU
  have hrk : rk ↥(W6.map g.toMonoidHom) = rk ↥W6 := by
    unfold rk
    rw [Subgroup.card_map_of_injective g.injective]
  exact hrk.trans hD.hrkz

end CFSG.LocalAnalysis.WeakClosure81
