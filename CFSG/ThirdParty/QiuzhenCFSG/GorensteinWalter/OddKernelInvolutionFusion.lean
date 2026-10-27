module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Lifting involution fusion across odd kernels

Conjugacy of quotient involutions lifts across a finite odd normal kernel by
Schur--Zassenhaus conjugacy of the corresponding order-two complements.
-/

namespace CFSG.GorensteinWalter

/-- If two involutions are conjugate modulo an odd normal subgroup, then
they are conjugate in the ambient group. -/
public theorem involutions_conjugate_of_quotient_conjugate_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {x y : H} (hx : IsInvolution x) (hy : IsInvolution y)
    (hconj : ∃ gq : H ⧸ N,
      gq * QuotientGroup.mk' N x * gq⁻¹ = QuotientGroup.mk' N y) :
    ∃ g : H, g * x * g⁻¹ = y := by
  classical
  obtain ⟨gq, hgq⟩ := hconj
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N gq
  let z : H := g * x * g⁻¹
  have hz : IsInvolution z := by
    constructor
    · intro hzone
      apply hx.1
      have h := congrArg (fun w : H => g⁻¹ * w * g) hzone
      simpa [z, mul_assoc] using h
    · calc
        z ^ 2 = g * (x ^ 2) * g⁻¹ := by
          simp [z, pow_two, mul_assoc]
        _ = 1 := by rw [hx.2]; simp
  have hqzy : QuotientGroup.mk' N z = QuotientGroup.mk' N y := by
    dsimp [z]
    change (QuotientGroup.mk' N g) * (QuotientGroup.mk' N x) *
      (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N y
    rw [hg]
    exact hgq
  have heq : ∃ a : H, a * z * a⁻¹ = y := by
    let X : Subgroup H := Subgroup.zpowers z
    let Y : Subgroup H := Subgroup.zpowers y
    let S : Subgroup H := N ⊔ X
    let q : H →* H ⧸ N := QuotientGroup.mk' N
    have hzOrder : orderOf z = 2 := orderOf_eq_prime hz.2 hz.1
    have hyOrder : orderOf y = 2 := orderOf_eq_prime hy.2 hy.1
    have hXcard : Nat.card X = 2 := by
      simp [X, Nat.card_zpowers, hzOrder]
    have hYcard : Nat.card Y = 2 := by
      simp [Y, Nat.card_zpowers, hyOrder]
    have hyzN : y * z⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q (y * z⁻¹) = 1
      simp [q, map_mul, map_inv, hqzy]
    have hzyN : z * y⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q (z * y⁻¹) = 1
      simp [q, map_mul, map_inv, hqzy]
    have hyS : y ∈ S := by
      change y ∈ N ⊔ X
      have h1 : y * z⁻¹ ∈ N ⊔ X :=
        (show N ≤ N ⊔ X from le_sup_left) hyzN
      have h2 : z ∈ N ⊔ X :=
        (show X ≤ N ⊔ X from le_sup_right) (Subgroup.mem_zpowers z)
      have hmul := (N ⊔ X).mul_mem h1 h2
      simpa [mul_assoc] using hmul
    have hzNY : z ∈ N ⊔ Y := by
      have h1 : z * y⁻¹ ∈ N ⊔ Y :=
        (show N ≤ N ⊔ Y from le_sup_left) hzyN
      have h2 : y ∈ N ⊔ Y :=
        (show Y ≤ N ⊔ Y from le_sup_right) (Subgroup.mem_zpowers y)
      have hmul := (N ⊔ Y).mul_mem h1 h2
      simpa [mul_assoc] using hmul
    have hYleS : Y ≤ S := Subgroup.zpowers_le.mpr hyS
    have hXleNY : X ≤ N ⊔ Y := Subgroup.zpowers_le.mpr hzNY
    have hsup : N ⊔ Y = S := by
      apply le_antisymm
      · exact sup_le le_sup_left hYleS
      · change N ⊔ X ≤ N ⊔ Y
        exact sup_le le_sup_left hXleNY
    have hNXcop : Nat.Coprime (Nat.card N) (Nat.card X) := by
      rw [hXcard]
      exact (Nat.coprime_two_left.mpr hNodd).symm
    have hNYcop : Nat.Coprime (Nat.card N) (Nat.card Y) := by
      rw [hYcard]
      exact (Nat.coprime_two_left.mpr hNodd).symm
    have hNXdisj : Disjoint N X :=
      Subgroup.disjoint_of_coprime_natCard hNXcop
    have hNYdisj : Disjoint N Y :=
      Subgroup.disjoint_of_coprime_natCard hNYcop
    have hcompX :
        (N.subgroupOf S).IsComplement' (X.subgroupOf S) := by
      simpa [S] using
        (isComplement'_subgroupOf_sup_of_disjoint N X hNXdisj)
    have hcompY :
        (N.subgroupOf S).IsComplement' (Y.subgroupOf S) := by
      have h0 := isComplement'_subgroupOf_sup_of_disjoint N Y hNYdisj
      rw [hsup] at h0
      exact h0
    have hNnormalS : (N.subgroupOf S).Normal :=
      (inferInstance : N.Normal).subgroupOf S
    have hNcardS : Nat.card (N.subgroupOf S) = Nat.card N :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (show N ≤ S from le_sup_left))
    have hNoddS : Odd (Nat.card (N.subgroupOf S)) := by
      rw [hNcardS]
      exact hNodd
    have hXcardS : Nat.card (X.subgroupOf S) = 2 := by
      calc
        Nat.card (X.subgroupOf S) = Nat.card X :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (show X ≤ S from le_sup_right))
        _ = 2 := hXcard
    have hNindexS : (N.subgroupOf S).index = 2 := by
      rw [hcompX.symm.index_eq_card, hXcardS]
    have hcopS : Nat.Coprime (Nat.card (N.subgroupOf S))
        (N.subgroupOf S).index := by
      rw [hNindexS]
      exact (Nat.coprime_two_left.mpr hNoddS).symm
    obtain ⟨a, ha⟩ :=
      SchurZassenhaus.complements_conjugate_of_coprime
        (N.subgroupOf S) (X.subgroupOf S) (Y.subgroupOf S)
        hNnormalS hcompX hcompY hcopS
    let yS : S := ⟨y, hyS⟩
    have hyY : yS ∈ Y.subgroupOf S := Subgroup.mem_zpowers y
    rw [ha] at hyY
    obtain ⟨b, hbX, hab⟩ := Subgroup.mem_map.mp hyY
    have hb_ne : b ≠ 1 := by
      intro hb
      subst b
      simp at hab
      exact hy.1 (congrArg Subtype.val hab.symm)
    let bX : X.subgroupOf S := ⟨b, hbX⟩
    let zS : S := ⟨z,
      (show X ≤ S from le_sup_right) (Subgroup.mem_zpowers z)⟩
    let zX : X.subgroupOf S := ⟨zS, Subgroup.mem_zpowers z⟩
    have hbX_ne : bX ≠ 1 := by
      intro hb
      exact hb_ne (congrArg Subtype.val hb)
    have hzX_ne : zX ≠ 1 := by
      intro hzone
      exact hz.1 (congrArg Subtype.val (congrArg Subtype.val hzone))
    obtain ⟨w, _hwne, hwuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : X.subgroupOf S)).mp hXcardS
    have hbz : bX = zX :=
      (hwuniq bX hbX_ne).trans (hwuniq zX hzX_ne).symm
    have hbzS : b = zS := congrArg Subtype.val hbz
    have hconjS : (MulAut.conj a) zS = yS := by
      simpa [hbzS] using hab
    exact ⟨(a : H), congrArg Subtype.val hconjS⟩
  obtain ⟨a, ha⟩ := heq
  refine ⟨a * g, ?_⟩
  calc
    (a * g) * x * (a * g)⁻¹ = a * z * a⁻¹ := by
      simp [z, mul_assoc]
    _ = y := ha

end CFSG.GorensteinWalter
