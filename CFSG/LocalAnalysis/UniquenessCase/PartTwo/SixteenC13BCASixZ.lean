module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_six_z (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 2)
    {Z : Subgroup (MulAut (Vtil ⊥ V hV))} (hZM : Z ≤ Mbar D.M ⊥ V hV) (hZc : Nat.card Z = 3)
    (hZn : ∀ m ∈ Mbar D.M ⊥ V hV, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z)
    (hLp : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤) {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (hsup : J₀ ⊔ J₁ = wTil ⊥ V hV L) :
    ∃ z : MulAut (Vtil ⊥ V hV), z ^ 3 = 1 ∧ (∀ l ∈ lBar ⊥ V hV L, z * l = l * z) ∧
      (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁ ∧ ∃ u ∈ J₀ ⊔ J₁, z u ≠ u := by
  classical
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZc])
  have hzo : orderOf (z : MulAut (Vtil ⊥ V hV)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hz3 : (z : MulAut (Vtil ⊥ V hV)) ^ 3 = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one _
  have hzL' := s16c13bc_commute_of_perfect Nat.prime_three hLp hZc
    (fun m hm x hx => hZn m (hLM hm) x hx)
  have hzL : ∀ l ∈ lBar ⊥ V hV L, (z : MulAut (Vtil ⊥ V hV)) * l =
      l * (z : MulAut (Vtil ⊥ V hV)) := fun l hl => (hzL' l hl z z.2).symm
  have hzW : (J₀ ⊔ J₁).map (z : MulAut (Vtil ⊥ V hV)).toMonoidHom = J₀ ⊔ J₁ := by
    rw [hsup]
    exact s16c13bcA_wTil_map_eq ⊥ V hV L (s16c13bcA_map_conj_eq_of_commute hzL)
  refine ⟨z, hz3, hzL, hzW, ?_⟩
  by_contra hcon
  have hfixW : ∀ u ∈ wTil ⊥ V hV L, (z : MulAut (Vtil ⊥ V hV)) u = u := by
    intro u hu
    by_contra hne
    exact hcon ⟨u, hsup ▸ hu, hne⟩
  have hM2 : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ φ ∈ Mbar D.M ⊥ V hV,
      Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs
    exact hs
  obtain ⟨g, hgM, hgne, -, -⟩ := s16c13bcA_exists_other_conj D hV hH hs
  have hpair := s16c13bc_conj_mem_pair hgM hgne hM2
  have hVsup : wTil ⊥ V hV L ⊔ (wTil ⊥ V hV L).map g.toMonoidHom = ⊤ := by
    obtain ⟨-, -, -, -, -, hW1, -⟩ := hc.conc
    refine top_le_iff.1 ?_
    rw [← hW1]
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g', hg'M, rfl⟩ := hX
    change (wTil ⊥ V hV L).map g'.toMonoidHom ≤ _
    rw [s16c13bcA_wTil_map_conj ⊥ V hV L g']
    rcases hpair g' hg'M with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1, ← s16c13bcA_wTil_map_conj ⊥ V hV L g]
      exact le_sup_right
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  have hZz : Subgroup.zpowers (z : MulAut (Vtil ⊥ V hV)) = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 z.2) ?_
    rw [Nat.card_zpowers, hzo, hZc]
  have hconj : g⁻¹ * (z : MulAut (Vtil ⊥ V hV)) * g ∈ Z := by
    have h1 := hZn g⁻¹ ((Mbar D.M ⊥ V hV).inv_mem hgM) z z.2
    rwa [inv_inv] at h1
  have hconj' : g⁻¹ * (z : MulAut (Vtil ⊥ V hV)) * g ∈
      Subgroup.zpowers (z : MulAut (Vtil ⊥ V hV)) := by
    rw [hZz]
    exact hconj
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hconj'
  have hzj : ∀ u ∈ wTil ⊥ V hV L, ((z : MulAut (Vtil ⊥ V hV)) ^ j) u = u := by
    intro u hu
    have hmem : (z : MulAut (Vtil ⊥ V hV)) ∈
        MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) u := hfixW u hu
    exact MulAction.mem_stabilizer_iff.1 (Subgroup.zpow_mem _ hmem j)
  have hfixWg : ∀ u ∈ (wTil ⊥ V hV L).map g.toMonoidHom,
      (z : MulAut (Vtil ⊥ V hV)) u = u := by
    rintro _ ⟨x, hx, rfl⟩
    have e : (z : MulAut (Vtil ⊥ V hV)) * g = g * (g⁻¹ * (z : MulAut (Vtil ⊥ V hV)) * g) := by
      group
    calc (z : MulAut (Vtil ⊥ V hV)) (g x) = ((z : MulAut (Vtil ⊥ V hV)) * g) x := rfl
      _ = (g * (g⁻¹ * (z : MulAut (Vtil ⊥ V hV)) * g)) x := by rw [e]
      _ = g ((g⁻¹ * (z : MulAut (Vtil ⊥ V hV)) * g) x) := rfl
      _ = g x := by rw [← hj, hzj x hx]
  have hall : ∀ u : Vtil ⊥ V hV, (z : MulAut (Vtil ⊥ V hV)) u = u := by
    intro u
    have hu : u ∈ wTil ⊥ V hV L ⊔ (wTil ⊥ V hV L).map g.toMonoidHom := by
      rw [hVsup]
      exact Subgroup.mem_top u
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul, hfixW a ha, hfixWg b hb]
  have hz1 : (z : MulAut (Vtil ⊥ V hV)) = 1 := MulEquiv.ext hall
  rw [hz1, orderOf_one] at hzo
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
