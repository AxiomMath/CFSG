module

public import CFSG.RankThree.GF2n.Stroth80.Sec37CommStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section OddCentral

variable {K : Type*} [Group K] (Z : Subgroup K) [Z.Normal]

theorem le_of_map_le_of_central_odd (hZ : Z ≤ Subgroup.center K) (hodd : Odd (Nat.card Z))
    {T₁ T₂ : Subgroup K} (h₁ : IsPGroup 2 T₁)
    (h : T₁.map (QuotientGroup.mk' Z) ≤ T₂.map (QuotientGroup.mk' Z)) : T₁ ≤ T₂ := by
  intro x hx
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (h (Subgroup.mem_map_of_mem _ hx))
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ Z, x = t * z :=
    ⟨t⁻¹ * x, QuotientGroup.eq.1 hte, (mul_inv_cancel_left t x).symm⟩
  obtain ⟨a, ha⟩ := h₁ ⟨x, hx⟩
  have hxa : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hcomm : Commute t z := Subgroup.mem_center_iff.1 (hZ hz) t
  have hpow : t ^ 2 ^ a * z ^ 2 ^ a = 1 := by
    rw [← hcomm.mul_pow, ← hxz]
    exact hxa
  have hzmem : z ^ 2 ^ a ∈ T₂ := by
    rw [eq_inv_of_mul_eq_one_right hpow]
    exact T₂.inv_mem (T₂.pow_mem ht _)
  have hord : Odd (orderOf z) := by
    have h1 : orderOf z ∣ Nat.card Z := by
      simpa [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨z, hz⟩ : Z)
    exact hodd.of_dvd_nat h1
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    ((Nat.coprime_two_left.2 hord).pow_left a)
  have hzT : z ∈ T₂ := by
    rw [← hm]
    exact T₂.pow_mem hzmem m
  rw [hxz]
  exact T₂.mul_mem ht hzT

theorem conjSubgroup_eq_iff_map_of_central_odd (hZ : Z ≤ Subgroup.center K)
    (hodd : Odd (Nat.card Z)) {T : Subgroup K} (hT : IsPGroup 2 T) (k l : K) :
    conjSubgroup k T = conjSubgroup l T ↔
      conjSubgroup (QuotientGroup.mk' Z k) (T.map (QuotientGroup.mk' Z)) =
        conjSubgroup (QuotientGroup.mk' Z l) (T.map (QuotientGroup.mk' Z)) := by
  rw [← map_conjSubgroup, ← map_conjSubgroup]
  refine ⟨fun h => by rw [h], fun h => le_antisymm ?_ ?_⟩
  · exact le_of_map_le_of_central_odd Z hZ hodd (hT.map (MulAut.conj k).toMonoidHom) h.le
  · exact le_of_map_le_of_central_odd Z hZ hodd (hT.map (MulAut.conj l).toMonoidHom) h.ge

end OddCentral

theorem oddCentralLift : OddCentralLiftStatement := by
  intro K _ _ Z _ hZ hodd T hT
  refine ⟨fun h2 a b c d hab hcd => ?_, fun hbar k => ?_⟩
  · have hne : ∀ k l : K, conjSubgroup k T ≠ conjSubgroup l T →
        conjSubgroup (QuotientGroup.mk' Z k) (T.map (QuotientGroup.mk' Z)) ≠
          conjSubgroup (QuotientGroup.mk' Z l) (T.map (QuotientGroup.mk' Z)) :=
      fun k l hkl h => hkl ((conjSubgroup_eq_iff_map_of_central_odd Z hZ hodd hT k l).2 h)
    obtain ⟨gb, hg1, hg2⟩ := h2 _ _ _ _ (hne a b hab) (hne c d hcd)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z gb
    refine ⟨g, ?_, ?_⟩
    · rw [conjSubgroup_eq_iff_map_of_central_odd Z hZ hodd hT, map_mul]
      exact hg1
    · rw [conjSubgroup_eq_iff_map_of_central_odd Z hZ hodd hT, map_mul]
      exact hg2
  · obtain ⟨⟨yb, hyb⟩, hyb1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.1 (hbar (QuotientGroup.mk' Z k))
    obtain ⟨hybc, hybn⟩ := Subgroup.mem_inf.1 hyb
    have hmem : yb ∈ (conjSubgroup k T).map (QuotientGroup.mk' Z) := by
      rw [map_conjSubgroup]
      exact hybc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hmem
    have hyN : y ∈ Subgroup.normalizer (T : Set K) := by
      rw [mem_normalizer_iff_conjSubgroup_eq]
      have h1 := mem_normalizer_iff_conjSubgroup_eq.1 hybn
      rw [← map_conjSubgroup] at h1
      exact le_antisymm
        (le_of_map_le_of_central_odd Z hZ hodd (hT.map (MulAut.conj y).toMonoidHom) h1.le)
        (le_of_map_le_of_central_odd Z hZ hodd hT h1.ge)
    have hy1 : y ≠ 1 := fun h => hyb1 (Subtype.ext (by simp [h]))
    exact Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨y, Subgroup.mem_inf.2 ⟨hy, hyN⟩⟩, fun h => hy1 (congrArg Subtype.val h)⟩

end CFSG.RankThree.GF2n.Stroth80.Tim37
