module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem false_of_charTwo_cover {G : Type*} [Group G] [Finite G] {N : Subgroup G} {D : Type*}
    [Group D] (hN : CharTwo N) (ψ : ↥N →* D) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥N, ψ x = 1 → x ∈ Subgroup.center ↥N) (hD : IsSimpleGroup D)
    (hD2 : ¬ IsPGroup 2 D) : False := by
  have hRn : (CFSG.pCore 2 ↥N).Normal := CFSG.pCore_normal
  have hRp : IsPGroup 2 ↥(CFSG.pCore 2 ↥N) := CFSG.pCore_isPGroup
  have hKn : ((CFSG.pCore 2 ↥N).map ψ).Normal := hRn.map ψ hψ
  have hfin : (∀ d : D, d ∈ (CFSG.pCore 2 ↥N).map ψ) → False := by
    intro hall
    apply hD2
    intro d
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp (hall d)
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    have hr1 : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [← map_pow, hr1, map_one]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥N).map ψ) with hbot | htop
  · have hcentral : ∀ r ∈ CFSG.pCore 2 ↥N, r ∈ Subgroup.center ↥N := by
      intro r hr
      apply hker r
      have hmem : ψ r ∈ (CFSG.pCore 2 ↥N).map ψ := Subgroup.mem_map_of_mem ψ hr
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hcent : (⊤ : Subgroup ↥N) ≤ Subgroup.centralizer (CFSG.pCore 2 ↥N : Set ↥N) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_center_iff.mp (hcentral h hh) x).symm
    have htopN : ∀ x : ↥N, x ∈ CFSG.pCore 2 ↥N := fun x =>
      charTwo_iff_internal.mp hN (hcent (Subgroup.mem_top x))
    apply hfin
    intro d
    obtain ⟨x, rfl⟩ := hψ d
    exact Subgroup.mem_map_of_mem ψ (htopN x)
  · apply hfin
    intro d
    rw [htop]
    exact Subgroup.mem_top d

end CFSG.Quasithin.H13
