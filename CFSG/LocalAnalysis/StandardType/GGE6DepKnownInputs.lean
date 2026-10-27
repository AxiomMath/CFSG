module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly
public import CFSG.LocalAnalysis.StandardType.GGE6DepXNotInL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem conjSetting_mem_L {p : ℕ} {Bs : Subgroup G} {x y : G} {L : Subgroup G}
    (h : GGE6DepConjSetting p Bs x y L) : y ∈ L := by
  obtain ⟨-, -, g, x₁, y₁, w, hx₁, hy₁, hy, hw, -, -, -, -, -, -, hyL, -⟩ := h
  exact hyL

private theorem zpowers_eq_of_mem_inf {D L : Subgroup G} {x y y' : G} (hDab : IsElemAbelian 3 D)
    (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D) (hxL : x ∉ L) (hyD : y ∈ D) (hyL : y ∈ L)
    (hy1 : y ≠ 1) (hy'D : y' ∈ D) (hy'L : y' ∈ L) (hy'1 : y' ≠ 1) :
    Subgroup.zpowers y' = Subgroup.zpowers y := by
  have hy3 : y ^ 3 = 1 := hDab.2 y hyD
  have hy'3 : y' ^ 3 = 1 := hDab.2 y' hy'D
  have hordy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hordy' : orderOf y' = 3 := orderOf_eq_prime hy'3 hy'1
  have hzy : Subgroup.zpowers y ≤ D ⊓ L :=
    Subgroup.zpowers_le.mpr ⟨hyD, hyL⟩
  have hzy' : Subgroup.zpowers y' ≤ D ⊓ L :=
    Subgroup.zpowers_le.mpr ⟨hy'D, hy'L⟩
  have hD9 : Nat.card D = 9 := by rw [hDcard]; norm_num
  have hdvd9 : Nat.card ↥(D ⊓ L) ∣ 9 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ L ≤ D)
    rwa [hD9] at h
  have hdvd3 : 3 ∣ Nat.card ↥(D ⊓ L) := by
    have h := Subgroup.card_dvd_of_le hzy
    rw [Nat.card_zpowers, hordy] at h
    exact h
  have hne : Nat.card ↥(D ⊓ L) ≠ 9 := by
    intro h9
    have hDL : D ⊓ L = D :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : D ⊓ L ≤ D) (le_of_eq (by rw [hD9, h9]))
    exact hxL ((inf_eq_left.mp hDL) hxD)
  have hcard3 : Nat.card ↥(D ⊓ L) = 3 := by
    have hle : Nat.card ↥(D ⊓ L) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
    generalize Nat.card ↥(D ⊓ L) = n at hdvd9 hdvd3 hne hle
    interval_cases n <;> omega
  have h1 : Subgroup.zpowers y = D ⊓ L :=
    Subgroup.eq_of_le_of_card_ge hzy (le_of_eq (by rw [hcard3, Nat.card_zpowers, hordy]))
  have h2 : Subgroup.zpowers y' = D ⊓ L :=
    Subgroup.eq_of_le_of_card_ge hzy' (le_of_eq (by rw [hcard3, Nat.card_zpowers, hordy']))
  rw [h1, h2]

theorem ggE6DepConj_of_known (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hX : GGE6DepPerpXNotInL) (hI : GGE6DepNonIsoPt) : GGE6DepConj := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hnbr hE
  obtain rfl : p = 3 := hE.1
  exact ggE6Dep_conjSetting hRig hM hI hcfg hinn hnt hnbr hE
    (hX G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE)

theorem ggE6DepNbrPin_of_known (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hX : GGE6DepPerpXNotInL) (hI : GGE6DepNonIsoPt) (hTP : GGE6DepPerpTablePInput) :
    GGE6DepNbrPin := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr'
  obtain rfl : p = 3 := hE.1
  have hE' : GGE6DepPerpCfg 3 Bs L K' :=
    hTP G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr'
  have hxL : x ∉ L := hX G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE
  have hyL : y ∈ L :=
    conjSetting_mem_L
      (ggE6DepConj_of_known hRig hM hX hI G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE)
  have hy'L : y' ∈ L :=
    conjSetting_mem_L
      (ggE6DepConj_of_known hRig hM hX hI G 3 B Bs x L D J hcfg hop hinn hnt y' K' hnbr' hE')
  obtain ⟨-, hxy, -, -⟩ := ggE6Dep_nbr_facts hcfg hnbr
  obtain ⟨-, hxy', -, -⟩ := ggE6Dep_nbr_facts hcfg hnbr'
  have hyD : y ∈ D := by
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton y))
  have hy'D : y' ∈ D := by
    rw [hnbr'.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton y'))
  exact zpowers_eq_of_mem_inf hcfg.2.2.1.2.1 hcfg.2.2.1.2.2.1 hcfg.2.2.1.2.2.2.1 hxL hyD hyL
    (fun h => hxy (h ▸ Subgroup.one_mem _)) hy'D hy'L (fun h => hxy' (h ▸ Subgroup.one_mem _))

end CFSG.StandardType

end
