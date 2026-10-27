module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iGeneral
public import CFSG.RankThree.PartTwo.Sec21.Hering233iQ8D8

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree.PartTwo

theorem isPGroup_two_Q8D8 : IsPGroup 2 Sec4.Q8D8 := by
  have h64 : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 2 ^ 6 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
      DihedralGroup.nat_card]
    norm_num
  exact (IsPGroup.of_card h64).to_quotient _

theorem false_of_isExtOf_oTwoP {X : Type*} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X ≤ Subgroup.center X) (hO3 : CFSG.pCore 3 X ≤ Subgroup.center X)
    (h : Sec4.IsExtOf (X ⧸ Sec4.oTwoP 3 X) (alternatingGroup (Fin 5)) Sec4.Q8D8) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hK'n, ⟨eK⟩, -⟩ := h
  have hR : Sec4.oTwoP 3 X ≤ Subgroup.center X := oTwoP_le_center hO2 hO3
  set π := QuotientGroup.mk' (Sec4.oTwoP 3 X) with hπ
  set M : Subgroup X := K'.comap π with hM
  haveI : M.Normal := Subgroup.Normal.comap hK'n π
  let f : M →* K' := (π.comp M.subtype).codRestrict K' (fun x => x.2)
  have hK'2 : IsPGroup 2 K' := isPGroup_two_Q8D8.of_equiv eK.symm
  have hrange : IsPGroup 2 f.range := hK'2.to_subgroup _
  have hker : f.ker.map M.subtype ≤ Subgroup.center X := by
    rintro _ ⟨x, hx, rfl⟩
    apply hR
    have h1 : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hMc : M ≤ Subgroup.center X := le_center_of_central_ext (p := 2) hO2 f hrange hker
  obtain ⟨a, b, hab⟩ := exists_not_commute_Q8D8
  set a' : K' := eK.symm a with ha'
  set b' : K' := eK.symm b with hb'
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Sec4.oTwoP 3 X) (a' : X ⧸ Sec4.oTwoP 3 X)
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Sec4.oTwoP 3 X) (b' : X ⧸ Sec4.oTwoP 3 X)
  have hxM : x ∈ M := by
    rw [hM, Subgroup.mem_comap]
    change π x ∈ K'
    rw [hx]
    exact a'.2
  have hyM : y ∈ M := by
    rw [hM, Subgroup.mem_comap]
    change π y ∈ K'
    rw [hy]
    exact b'.2
  have hxy : x * y = y * x := Subgroup.mem_center_iff.mp (hMc hxM) y |>.symm
  have hcomm : a' * b' = b' * a' := by
    apply Subtype.ext
    change (a' : X ⧸ Sec4.oTwoP 3 X) * (b' : X ⧸ Sec4.oTwoP 3 X) =
      (b' : X ⧸ Sec4.oTwoP 3 X) * (a' : X ⧸ Sec4.oTwoP 3 X)
    rw [← hx, ← hy, ← map_mul, ← map_mul, hxy]
  apply hab
  have := congrArg eK hcomm
  simpa [ha', hb'] using this

end CFSG.RankThree.PartTwo.Sec21.Hering233i
