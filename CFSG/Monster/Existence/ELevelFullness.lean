module

public import CFSG.Monster.Existence.AnchoredFullness
public import CFSG.Monster.Existence.ELevelR
public import CFSG.Monster.Existence.ELevelRank
public import CFSG.Monster.Existence.ELevelOrder4
public import CFSG.Monster.Existence.ELevelCore
public import CFSG.Monster.Existence.ELevelNative

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

theorem no_sq_in_FE_all
    {k : MGriess} (hkF : k ∈ Subgroup.centralizer (FE : Set MGriess))
    (hkx : k ∈ Subgroup.centralizer ({xGriess} : Set MGriess)) (hk2 : k * k ∈ FE)
    (hk2' : k * k ≠ 1) : False :=
  no_sq_in_FE (fun _ hi => noConfig_of_checkSpec hi (checkSpec hi)) hkF hkx hk2 hk2'

theorem hanch_FE
    (hEb : ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f)) :
    ∀ k ∈ Subgroup.centralizer (FE : Set MGriess) ⊓ Subgroup.centralizer ({xGriess} : Set MGriess),
      k * k ∈ FE → k ∉ FE → ∃ f ∈ FE, IsConj xGriess (k * f) := by
  intro k hk hk2 hkF
  by_cases h1 : k * k = 1
  · exact hEb k hk h1 hkF
  · exact (no_sq_in_FE_all hk.1 hk.2 hk2 h1).elim

theorem centralizer_FE_le_GmatGriess
    (hcensus : ∀ y ∈ GmatGriess, IsConj xGriess y → ∃ g ∈ GmatGriess, g * xGriess * g⁻¹ = y)
    (hEb : ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f)) :
    Subgroup.centralizer (FE : Set MGriess) ≤ GmatGriess :=
  centralizer_le_of_anchored GmatGriess xGriess xGriess_mul_self centralizer_xGriess_le hcensus FE
    FE_le_GmatGriess FE_comm xGriess_mem_centralizer_FE xGriess_not_mem_FE
    (fun _ hf hc => not_isConj_x_mul hf hc) RE
    RE_le_centralizer_x RE_le_centralizer_FE isPGroup_RE RE_normalized (RE_hCR rankSpec)
    RE_hZR RE_hinv (hanch_FE hEb)

theorem normalizer_FE_le_GmatGriess
    (hcensus : ∀ y ∈ GmatGriess, IsConj xGriess y → ∃ g ∈ GmatGriess, g * xGriess * g⁻¹ = y)
    (hEb : ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f)) :
    Subgroup.normalizer (FE : Set MGriess) ≤ GmatGriess := by
  intro n hn
  have hxG : xGriess ∈ GmatGriess :=
    centralizer_FE_le_GmatGriess hcensus hEb xGriess_mem_centralizer_FE
  have hnx : n * xGriess * n⁻¹ ∈ Subgroup.centralizer (FE : Set MGriess) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : n⁻¹ * f * n ∈ FE := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) f).1 hf
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 xGriess_mem_centralizer_FE _ hf'
    calc f * (n * xGriess * n⁻¹) = n * ((n⁻¹ * f * n) * xGriess) * n⁻¹ := by group
      _ = n * (xGriess * (n⁻¹ * f * n)) * n⁻¹ := by rw [hc]
      _ = n * xGriess * n⁻¹ * f := by group
  exact mem_of_isConj_of_conj_mem centralizer_xGriess_le hcensus (IsConj.refl xGriess) hxG
    (centralizer_FE_le_GmatGriess hcensus hEb hnx)

end CFSG.Monster.Existence
