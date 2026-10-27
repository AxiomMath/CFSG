module

public import CFSG.RankThree.GF2n.Stroth80.Sec37CommStmt
public import CFSG.LargeExtraspecial.S4TwoB

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section NormalLift

variable {X : Type} [Group X]

theorem conjSubgroup_mul_eq (g a : X) (T : Subgroup X) :
    conjSubgroup (g * a) T = conjSubgroup g (conjSubgroup a T) := by
  ext x
  simp only [mem_conjSubgroup, mul_inv_rev, mul_assoc]

theorem conjSubgroup_le_of_mem {K T : Subgroup X} (hTK : T ≤ K) {k : X} (hk : k ∈ K) :
    conjSubgroup k T ≤ K := by
  intro x hx
  have h1 : k⁻¹ * x * k ∈ K := hTK (mem_conjSubgroup.mp hx)
  have h2 : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  rw [h2]
  exact K.mul_mem (K.mul_mem hk h1) (K.inv_mem hk)

theorem conjSubgroup_subgroupOf_eq (K T : Subgroup X) (k : K) :
    conjSubgroup k (T.subgroupOf K) = (conjSubgroup (k : X) T).subgroupOf K := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  rfl

theorem conjSubgroup_eq_iff_subgroupOf_eq {K T : Subgroup X} (hTK : T ≤ K) (k l : K) :
    conjSubgroup (k : X) T = conjSubgroup (l : X) T ↔
      conjSubgroup k (T.subgroupOf K) = conjSubgroup l (T.subgroupOf K) := by
  rw [conjSubgroup_subgroupOf_eq, conjSubgroup_subgroupOf_eq, Subgroup.subgroupOf_inj,
    inf_eq_left.mpr (conjSubgroup_le_of_mem hTK k.2),
    inf_eq_left.mpr (conjSubgroup_le_of_mem hTK l.2)]

theorem mem_normalizer_of_mem_normalizer_subgroupOf_of_le {K T : Subgroup X} (hTK : T ≤ K) {y : K}
    (hy : y ∈ Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K)) :
    (y : X) ∈ Subgroup.normalizer (T : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro h
  constructor
  · intro hh
    exact (hy ⟨h, hTK hh⟩).mp hh
  · intro hh
    have hhK : h ∈ K := by
      have h1 : (y : X)⁻¹ * ((y : X) * h * (y : X)⁻¹) * (y : X) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem y.2) (hTK hh)) y.2
      simpa [mul_assoc] using h1
    exact (hy ⟨h, hhK⟩).mpr hh

theorem exists_conjSubgroup_eq_of_weaklyClosed [Finite X] {K T : Subgroup X} [K.Normal]
    (hTK : T ≤ K) (hT : IsPGroup 2 T)
    (hwc : ∀ g : X, conjSubgroup g T ≤ Subgroup.normalizer (T : Set X) → conjSubgroup g T = T)
    (x : X) : ∃ k : K, conjSubgroup x T = conjSubgroup (k : X) T := by
  obtain ⟨k, hk, e⟩ := CFSG.LargeExtraspecial.S4.exists_mem_conj_eq_of_weaklyClosed hTK hT hwc x
  exact ⟨⟨k, hk⟩, e⟩

end NormalLift

theorem normalLift : NormalLiftStatement := by
  intro X _ _ K _ T hTK hT hwc
  refine ⟨fun h2 a b c d hab hcd => ?_, fun h x => ?_⟩
  · obtain ⟨ka, ea⟩ := exists_conjSubgroup_eq_of_weaklyClosed hTK hT hwc a
    obtain ⟨kb, eb⟩ := exists_conjSubgroup_eq_of_weaklyClosed hTK hT hwc b
    obtain ⟨kc, ec⟩ := exists_conjSubgroup_eq_of_weaklyClosed hTK hT hwc c
    obtain ⟨kd, ed⟩ := exists_conjSubgroup_eq_of_weaklyClosed hTK hT hwc d
    rw [ea, eb] at hab
    rw [ec, ed] at hcd
    obtain ⟨g, hg1, hg2⟩ := h2 ka kb kc kd
      (fun h => hab ((conjSubgroup_eq_iff_subgroupOf_eq hTK ka kb).mpr h))
      (fun h => hcd ((conjSubgroup_eq_iff_subgroupOf_eq hTK kc kd).mpr h))
    refine ⟨(g : X), ?_, ?_⟩
    · rw [conjSubgroup_mul_eq, ea, ← conjSubgroup_mul_eq, ec]
      exact (conjSubgroup_eq_iff_subgroupOf_eq hTK (g * ka) kc).mpr hg1
    · rw [conjSubgroup_mul_eq, eb, ← conjSubgroup_mul_eq, ed]
      exact (conjSubgroup_eq_iff_subgroupOf_eq hTK (g * kb) kd).mpr hg2
  · obtain ⟨k, ek⟩ := exists_conjSubgroup_eq_of_weaklyClosed hTK hT hwc x
    obtain ⟨⟨y, hyc, hyn⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h k)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(y : X), ?_, mem_normalizer_of_mem_normalizer_subgroupOf_of_le hTK hyn⟩, ?_⟩
    · rw [ek]
      rwa [conjSubgroup_subgroupOf_eq] at hyc
    · intro h1
      have h2 := congrArg Subtype.val h1
      exact hy1 (Subtype.ext (Subtype.ext h2))

end CFSG.RankThree.GF2n.Stroth80.Tim37
