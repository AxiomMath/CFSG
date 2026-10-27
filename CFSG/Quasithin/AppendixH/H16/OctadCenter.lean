module

public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer
public import CFSG.Assembly.ComponentTypeDefs

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

theorem octFix_le_of_isSylowIn {O : Finset (Fin 24)} (hO : IsOctad O)
    {T₀ : Subgroup S24} (hT : CFSG.Quasithin.IsSylowIn 2 T₀ M24g)
    (hstab : ∀ g ∈ T₀, g • O = O) : octFix O ≤ T₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTle : T₀ ≤ octStab O := by
    intro g hg
    rw [mem_octStab_iff]
    exact ⟨hT.le hg, hstab g hg⟩
  have hOM : octStab O ≤ M24g := inf_le_left
  have hrel := Subgroup.relIndex_mul_relIndex T₀ (octStab O) M24g hTle hOM
  have hSyl : CFSG.Quasithin.IsSylowIn 2 T₀ (octStab O) := by
    refine ⟨hTle, hT.isPGroup, ?_⟩
    intro h2
    apply hT.not_dvd_relIndex
    rw [← hrel]
    exact dvd_mul_of_dvd_left h2 _
  exact hSyl.le_of_normal (octFix_le_octStab O) (normal_octFix O) (isPGroup_octFix hO)

theorem center_gen_mem_octFix {O : Finset (Fin 24)} (hO : IsOctad O)
    {T₀ : Subgroup S24} (hT : CFSG.Quasithin.IsSylowIn 2 T₀ M24g)
    (hstab : ∀ g ∈ T₀, g • O = O) {z : S24}
    (hz : z ∈ T₀ ∧ ∀ t ∈ T₀, (t ∈ Subgroup.zpowers z ↔ ∀ s ∈ T₀, s * t = t * s)) :
    z ∈ octFix O ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoctFix_le_T₀ : octFix O ≤ T₀ := octFix_le_of_isSylowIn hO hT hstab
  have hzstab : z ∈ octStab O := by
    rw [mem_octStab_iff]
    exact ⟨hT.le hz.1, hstab z hz.1⟩
  have hzcent : z ∈ Subgroup.centralizer (octFix O : Set S24) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hz.2 z hz.1).1 (Subgroup.mem_zpowers z) h (hoctFix_le_T₀ hh)
  refine ⟨?_, ?_⟩
  ·
    have hmem : z ∈ octStab O ⊓ Subgroup.centralizer (octFix O : Set S24) :=
      Subgroup.mem_inf.mpr ⟨hzstab, hzcent⟩
    rwa [octStab_inf_centralizer_octFix hO] at hmem
  ·
    intro hz1
    have hcent : ∀ t : ↥T₀, t ∈ Subgroup.center ↥T₀ → t = 1 := by
      intro t ht
      have hcommT : ∀ s : ↥T₀, s * t = t * s := Subgroup.mem_center_iff.mp ht
      have hcommS : ∀ s ∈ T₀, s * (t : S24) = (t : S24) * s := by
        intro s hs
        have h := congrArg Subtype.val (hcommT ⟨s, hs⟩)
        simpa using h
      have ht_z : (t : S24) ∈ Subgroup.zpowers z := (hz.2 (t : S24) t.2).mpr hcommS
      rw [hz1, Subgroup.zpowers_one_eq_bot] at ht_z
      exact Subtype.ext (by simpa using ht_z)
    haveI : Nontrivial ↥T₀ := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      calc 1 < Nat.card ↥(octFix O) := by rw [card_octFix hO]; norm_num
        _ ≤ Nat.card ↥T₀ := Nat.card_le_card_of_injective
            (fun x : ↥(octFix O) => (⟨x.1, hoctFix_le_T₀ x.2⟩ : ↥T₀))
            (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    obtain ⟨x, y, hxy⟩ := IsPGroup.center_nontrivial hT.isPGroup
    have hx1 : x = 1 := Subtype.ext (hcent x.1 x.2)
    have hy1 : y = 1 := Subtype.ext (hcent y.1 y.2)
    exact hxy (hx1.trans hy1.symm)

end CFSG.ASVolI.H16
