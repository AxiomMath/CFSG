module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open CFSG Equiv

theorem sp6_oTwoP_solvable (Y : Type) [Group Y] [Finite Y] :
    Group.IsSolvable ↥(Sec4.oTwoP 3 Y) := by
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 Y) := CFSG.pCore_isNilpotent
  haveI : Group.IsNilpotent ↥(CFSG.pCore 3 (Y ⧸ CFSG.pCore 2 Y)) := CFSG.pCore_isNilpotent
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (Sec4.pCore_two_le_oTwoP 3 Y))
    (((QuotientGroup.mk' (CFSG.pCore 2 Y)).comp (Sec4.oTwoP 3 Y).subtype).codRestrict
      (CFSG.pCore 3 (Y ⧸ CFSG.pCore 2 Y)) (fun x => Subgroup.mem_comap.1 x.2)) ?_
  intro x hx
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 Y) (x : Y) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact MonoidHom.mem_range.2 ⟨⟨x.1, (QuotientGroup.eq_one_iff (x : Y)).1 hx1⟩, Subtype.ext rfl⟩

theorem sp6_alt6_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  intro h
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 6))).2 h
  let g1 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let g2 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have hne : g1 * g2 ≠ g2 * g1 := by decide +kernel
  exact hne (hc g1 g2)

theorem sp6_units_eq_of_iff (u v : ℤˣ) (h : u = 1 ↔ v = 1) : u = v := by
  rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv
  · rw [hu, hv]
  · exact absurd (h.1 hu) (by rw [hv]; decide)
  · exact absurd (h.2 hv) (by rw [hu]; decide)
  · rw [hu, hv]

theorem sp6_card_le_two_of_normal_solvable_perm (N : Subgroup (Perm (Fin 6))) [N.Normal]
    [Group.IsSolvable N] : Nat.card N ≤ 2 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : ((N ⊓ alternatingGroup (Fin 6)).subgroupOf (alternatingGroup (Fin 6))).Normal :=
    Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N ⊓ alternatingGroup (Fin 6)).subgroupOf (alternatingGroup (Fin 6))) with hM | hM
  · have hinj : Function.Injective
        (fun x : N => decide (Equiv.Perm.sign (x : Perm (Fin 6)) = 1)) := by
      intro x y hxy
      have hsx : Equiv.Perm.sign (x : Perm (Fin 6)) = Equiv.Perm.sign (y : Perm (Fin 6)) :=
        sp6_units_eq_of_iff _ _ (by simpa using hxy)
      have hmem : (x : Perm (Fin 6)) * (y : Perm (Fin 6))⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsx, mul_inv_cancel]
      have hm : (⟨_, hmem⟩ : alternatingGroup (Fin 6)) ∈
          (N ⊓ alternatingGroup (Fin 6)).subgroupOf (alternatingGroup (Fin 6)) :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨N.mul_mem x.2 (N.inv_mem y.2), hmem⟩)
      rw [hM, Subgroup.mem_bot] at hm
      exact Subtype.ext (mul_inv_eq_one.1 (congrArg Subtype.val hm))
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  · have hAN : alternatingGroup (Fin 6) ≤ N := by
      intro a ha
      have hmem : (⟨a, ha⟩ : alternatingGroup (Fin 6)) ∈
          (N ⊓ alternatingGroup (Fin 6)).subgroupOf (alternatingGroup (Fin 6)) := by
        rw [hM]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAN)
      (Subgroup.inclusion_injective hAN)) sp6_alt6_not_solvable

theorem sp6_card_le_two_of_normal_solvable {G : Type} [Group G] (ψ : G ≃* Perm (Fin 6))
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] : Nat.card N ≤ 2 := by
  haveI hNn : (N.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance ψ.toMonoidHom ψ.surjective
  haveI hsol : Group.IsSolvable ↥(N.map ψ.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := (MulEquiv.subgroupMap ψ N).toMonoidHom)
      (MulEquiv.subgroupMap ψ N).surjective
  have hcard : Nat.card N = Nat.card ↥(N.map ψ.toMonoidHom) :=
    Nat.card_congr (MulEquiv.subgroupMap ψ N).toEquiv
  rw [hcard]
  exact sp6_card_le_two_of_normal_solvable_perm (N.map ψ.toMonoidHom)

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
