module

public import CFSG.LocalAnalysis.StandardType.GGResJLineA3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_coroot_subgroup_of_B2 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .B2) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  let _ : AddCommGroup V := instA
  let _ : Module (ZMod 3) V := instM
  have hpairB : ∀ i j : Fin 2, α i (h j) = (CartanMatrix.B 2 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  have hα2 : ∀ j : Fin 2, α j (h j) = 2 := by
    intro j
    rw [hpairB j j]
    fin_cases j <;> norm_num [CartanMatrix.B]
  have hC := ker_zero_of_det_two (C := CartanMatrix.B 2) (CartanMatrix.B_det (by norm_num))
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 2) hN ι r h α
    (CartanMatrix.B 2) hform hα2 hpairB hind hC hgen W rfl
  refine ⟨ggSpanSub ι W, hprops.1, hprops.2.1, ?_, hprops.2.2.2⟩
  rw [hprops.2.2.1]
  norm_num

theorem exists_coroot_subgroup_of_B3C3 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {T : GGResLineJType}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  classical
  rcases hT with rfl | rfl
  · obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
    let _ : AddCommGroup V := instA
    let _ : Module (ZMod 3) V := instM
    have hpairB : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.B 3 i j : ZMod 3) := by
      intro i j
      simpa only [GGResLineJType.cartan] using hpair i j
    have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
      intro j
      rw [hpairB j j]
      fin_cases j <;> norm_num [CartanMatrix.B]
    have hC := ker_zero_of_det_two (C := CartanMatrix.B 3) (CartanMatrix.B_det (by norm_num))
    let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
    have hprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3) hN ι r h α
      (CartanMatrix.B 3) hform hα2 hpairB hind hC hgen W rfl
    refine ⟨ggSpanSub ι W, hprops.1, hprops.2.1, ?_, hprops.2.2.2⟩
    rw [hprops.2.2.1]
    norm_num
  · obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
    let _ : AddCommGroup V := instA
    let _ : Module (ZMod 3) V := instM
    have hpairC : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.C 3 i j : ZMod 3) := by
      intro i j
      simpa only [GGResLineJType.cartan] using hpair i j
    have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
      intro j
      rw [hpairC j j]
      fin_cases j <;> norm_num [CartanMatrix.C]
    have hC := ker_zero_of_det_two (C := CartanMatrix.C 3) (CartanMatrix.C_det (by norm_num))
    let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
    have hprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3) hN ι r h α
      (CartanMatrix.C 3) hform hα2 hpairC hind hC hgen W rfl
    refine ⟨ggSpanSub ι W, hprops.1, hprops.2.1, ?_, hprops.2.2.2⟩
    rw [hprops.2.2.1]
    norm_num

theorem cube_le_card_gamma_of_B3C3 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {T : GGResLineJType}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3) :
    3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
  obtain ⟨E, hE, _hEelem, hEcard, hEbot⟩ := exists_coroot_subgroup_of_B3C3 hN hD hT
  have hEBs : E ≤ Bs := hE.trans inf_le_left
  calc 3 ^ 3 = Nat.card E := hEcard.symm
    _ ≤ Nat.card (ggGamma J hN).range :=
        GGResLineJDatum.card_le_card_range_ggGamma_of_le_of_inf_eq_bot hN hEBs hEbot

end CFSG.StandardType
