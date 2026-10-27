module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis

open Subgroup

theorem characteristic_p_normal_p_extension {G : Type*} [Group G] {p : ℕ} {Y : Subgroup G}
    [hYn : Y.Normal] (hY : IsCharacteristicP p Y) (hGY : IsPGroup p (G ⧸ Y)) :
    IsCharacteristicP p G := by
  set A : Subgroup G := (pCore p Y).map Y.subtype with hA
  have hAn : A.Normal := ⟨fun a ha g => by
    obtain ⟨y, hy, rfl⟩ := ha
    have h := characteristic_iff_map_eq.mp (inferInstance : (pCore p Y).Characteristic)
      (MulAut.conjNormal g)
    have hmem : MulAut.conjNormal g y ∈ pCore p Y := by
      rw [← h]
      exact mem_map_of_mem _ hy
    exact ⟨_, hmem, rfl⟩⟩
  have hAp : IsPGroup p A := (pCore_isPGroup (p := p) (G := Y)).map Y.subtype
  have hAO : A ≤ pCore p G := le_sSup ⟨hAn, hAp⟩
  set C : Subgroup G := centralizer (pCore p G : Set G) with hC
  have hCY : ∀ c ∈ C, c ∈ Y → c ∈ A := by
    intro c hc hcY
    have h1 : (⟨c, hcY⟩ : Y) ∈ centralizer (pCore p Y : Set Y) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp hc (y : G) (hAO ⟨y, hy, rfl⟩))
    exact ⟨⟨c, hcY⟩, hY h1, rfl⟩
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨n, hn⟩ := hGY (c : G)
    have h1 : (c : G) ^ p ^ n ∈ Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hn]
    obtain ⟨m, hm⟩ := hAp ⟨_, hCY _ (pow_mem c.2 _) h1⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
    rw [pow_add, pow_mul]
    exact this
  exact le_sSup ⟨inferInstance, hCp⟩

end CFSG.LocalAnalysis
