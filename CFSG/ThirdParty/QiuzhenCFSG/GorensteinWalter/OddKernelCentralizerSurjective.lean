module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizers lift across odd normal kernels

The correction conjugator in the Schur--Zassenhaus lifting argument can be
chosen in the odd kernel.  Consequently a quotient element centralizing an
involution has a representative centralizing the involution itself.
-/

namespace CFSG.GorensteinWalter

/-- The quotient map from the centralizer of an involution is surjective
onto the centralizer of its image modulo an odd normal subgroup. -/
public theorem exists_centralizer_lift_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (O : Subgroup H) [O.Normal] (hOodd : Odd (Nat.card O))
    {t : H} (ht : IsInvolution t)
    (y : H ⧸ O)
    (hy : y ∈ Subgroup.centralizer
      ({QuotientGroup.mk' O t} : Set (H ⧸ O))) :
    ∃ x : H, x ∈ Subgroup.centralizer ({t} : Set H) ∧
      QuotientGroup.mk' O x = y := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
  let z : H := g * t * g⁻¹
  have hz : IsInvolution z := by
    constructor
    · intro hzone
      apply ht.1
      have h := congrArg (fun w : H => g⁻¹ * w * g) hzone
      simpa [z, mul_assoc] using h
    · calc
        z ^ 2 = g * (t ^ 2) * g⁻¹ := by simp [z, pow_two, mul_assoc]
        _ = 1 := by rw [ht.2]; simp
  have hqzt : QuotientGroup.mk' O z = QuotientGroup.mk' O t := by
    dsimp [z]
    have hc := Subgroup.mem_centralizer_iff.mp hy
      (QuotientGroup.mk' O t) (by simp)
    change QuotientGroup.mk' O g * QuotientGroup.mk' O t *
      (QuotientGroup.mk' O g)⁻¹ = QuotientGroup.mk' O t
    calc
      QuotientGroup.mk' O g * QuotientGroup.mk' O t *
          (QuotientGroup.mk' O g)⁻¹ =
        QuotientGroup.mk' O t * QuotientGroup.mk' O g *
          (QuotientGroup.mk' O g)⁻¹ := by rw [hc]
      _ = QuotientGroup.mk' O t := by group
  let X : Subgroup H := Subgroup.zpowers z
  let Y : Subgroup H := Subgroup.zpowers t
  let S : Subgroup H := O ⊔ X
  have htS : t ∈ S := by
    have htzO : t * z⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff (N := O)]
      calc
        QuotientGroup.mk' O (t * z⁻¹) =
            QuotientGroup.mk' O t * (QuotientGroup.mk' O z)⁻¹ := by
              rw [map_mul, map_inv]
        _ = 1 := by rw [hqzt]; simp
    have h1 : t * z⁻¹ ∈ O ⊔ X :=
      (show O ≤ O ⊔ X from le_sup_left) htzO
    have h2 : z ∈ O ⊔ X :=
      (show X ≤ O ⊔ X from le_sup_right) (Subgroup.mem_zpowers z)
    simpa [mul_assoc] using S.mul_mem h1 h2
  have hYleS : Y ≤ S := Subgroup.zpowers_le.mpr htS
  have hzOY : z ∈ O ⊔ Y := by
    have hztO : z * t⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff (N := O)]
      calc
        QuotientGroup.mk' O (z * t⁻¹) =
            QuotientGroup.mk' O z * (QuotientGroup.mk' O t)⁻¹ := by
              rw [map_mul, map_inv]
        _ = 1 := by rw [hqzt]; simp
    have h1 : z * t⁻¹ ∈ O ⊔ Y :=
      (show O ≤ O ⊔ Y from le_sup_left) hztO
    have h2 : t ∈ O ⊔ Y :=
      (show Y ≤ O ⊔ Y from le_sup_right) (Subgroup.mem_zpowers t)
    simpa [mul_assoc] using (O ⊔ Y).mul_mem h1 h2
  have hXleOY : X ≤ O ⊔ Y := Subgroup.zpowers_le.mpr hzOY
  have hsup : O ⊔ Y = S := by
    apply le_antisymm
    · exact sup_le le_sup_left hYleS
    · exact sup_le le_sup_left hXleOY
  have hzOrder : orderOf z = 2 := orderOf_eq_prime hz.2 hz.1
  have htOrder : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  have hXcard : Nat.card X = 2 := by simp [X, Nat.card_zpowers, hzOrder]
  have hYcard : Nat.card Y = 2 := by simp [Y, Nat.card_zpowers, htOrder]
  have hOXdisj : Disjoint O X :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hXcard]
      exact (Nat.coprime_two_left.mpr hOodd).symm)
  have hOYdisj : Disjoint O Y :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hYcard]
      exact (Nat.coprime_two_left.mpr hOodd).symm)
  have hcompX : (O.subgroupOf S).IsComplement' (X.subgroupOf S) := by
    simpa [S] using isComplement'_subgroupOf_sup_of_disjoint O X hOXdisj
  have hcompY : (O.subgroupOf S).IsComplement' (Y.subgroupOf S) := by
    have h := isComplement'_subgroupOf_sup_of_disjoint O Y hOYdisj
    rw [hsup] at h
    exact h
  have hOnormalS : (O.subgroupOf S).Normal :=
    (inferInstance : O.Normal).subgroupOf S
  have hOcardS : Nat.card (O.subgroupOf S) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show O ≤ S from le_sup_left)).toEquiv
  have hXcardS : Nat.card (X.subgroupOf S) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show X ≤ S from le_sup_right)).toEquiv]
    exact hXcard
  have hOindexS : (O.subgroupOf S).index = 2 := by
    rw [hcompX.symm.index_eq_card, hXcardS]
  have hcopS : Nat.Coprime (Nat.card (O.subgroupOf S))
      (O.subgroupOf S).index := by
    rw [hOcardS, hOindexS]
    exact (Nat.coprime_two_left.mpr hOodd).symm
  obtain ⟨a, ha⟩ := SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    (O.subgroupOf S) (X.subgroupOf S) (Y.subgroupOf S)
    hOnormalS hcompX hcompY hcopS
  let zS : S := ⟨z,
    (show X ≤ S from le_sup_right) (Subgroup.mem_zpowers z)⟩
  have hzY : (MulAut.conj (a : S)) zS ∈ Y.subgroupOf S := by
    rw [ha]
    exact Subgroup.mem_map.mpr
      ⟨zS, Subgroup.mem_zpowers z, rfl⟩
  have hconj : (a : H) * z * (a : H)⁻¹ = t := by
    have hmem : (a : H) * z * (a : H)⁻¹ ∈ Y :=
      Subgroup.mem_subgroupOf.mp hzY
    have hne : (a : H) * z * (a : H)⁻¹ ≠ 1 := by
      intro h1
      apply hz.1
      have h := congrArg (fun w : H => (a : H)⁻¹ * w * (a : H)) h1
      simpa [mul_assoc] using h
    let v : Y := ⟨(a : H) * z * (a : H)⁻¹, hmem⟩
    let tY : Y := ⟨t, Subgroup.mem_zpowers t⟩
    have hcardY : Nat.card Y = 2 := hYcard
    obtain ⟨w, _hw, hwuniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hcardY
    exact congrArg Subtype.val ((hwuniq v (fun hv => hne (congrArg Subtype.val hv))).trans
      (hwuniq tY (fun ht1 => ht.1 (congrArg Subtype.val ht1))).symm)
  refine ⟨(a : H) * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hxconj : ((a : H) * g) * t * ((a : H) * g)⁻¹ = t := by
      calc
        ((a : H) * g) * t * ((a : H) * g)⁻¹ =
            (a : H) * z * (a : H)⁻¹ := by simp [z, mul_assoc]
        _ = t := hconj
    exact mul_inv_eq_iff_eq_mul.mp hxconj
  · rw [map_mul]
    have haO : (a : H) ∈ O := by
      exact (a.2 : (a : S) ∈ O.subgroupOf S)
    have hqa : QuotientGroup.mk' O (a : H) = 1 :=
      (QuotientGroup.eq_one_iff (N := O) (a : H)).mpr haO
    rw [hqa]
    simp

end CFSG.GorensteinWalter
