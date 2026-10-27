module

public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique

variable {G : Type*} [Group G]

structure IsChiefFactor (X Y : Subgroup G) : Prop where
  normal_left : X.Normal
  normal_right : Y.Normal
  lt : Y < X
  minimal : ∀ N : Subgroup G, N.Normal → Y ≤ N → N ≤ X → N = Y ∨ N = X

@[expose] def IsCompositionFactor (G : Type*) [Group G] (L : Type*) [Group L] : Prop :=
  ∃ (N M : Subgroup G) (_ : (N.subgroupOf M).Normal), N ≤ M ∧ N.IsSubnormal ∧ M.IsSubnormal ∧
    IsSimpleGroup (M ⧸ N.subgroupOf M) ∧ Nonempty ((M ⧸ N.subgroupOf M) ≃* L)

theorem isSylowIn_two_iff {P H : Subgroup G} : IsSylowIn 2 P H ↔ IsSylowTwoOf P H := Iff.rfl

theorem ten_one {T X Y K : Subgroup G} [Y.Normal] (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hYX : Y ≤ X) (hK : K ∈ sFamily T X Y) :
    K = (K ⊓ X) ⊔ T ∧
      (K ⊓ X).map (QuotientGroup.mk' Y) = X.map (QuotientGroup.mk' Y) ∧
      Nonempty ((↥(K ⊓ X) ⧸ Y.subgroupOf (K ⊓ X)) ≃*
        ↥((K ⊓ X).map (QuotientGroup.mk' Y))) := by
  obtain ⟨hKle, hTK, hEq, -⟩ := hK
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm (fun k hk => ?_) (sup_le inf_le_left hTK)
    have hk' := hKle hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X T hTX] at hk'
    obtain ⟨x, hx, t, ht, hxt⟩ := hk'
    have hxK : x ∈ K := by
      have : x = k * t⁻¹ := by rw [← hxt]; group
      rw [this]
      exact K.mul_mem hk (K.inv_mem (hTK ht))
    rw [← hxt]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hxK, hx⟩) (Subgroup.mem_sup_right ht)
  · refine le_antisymm (Subgroup.map_mono inf_le_right) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ K ⊔ Y := hEq ▸ Subgroup.mem_sup_left hx
    obtain ⟨k, hk, y, hy, hky⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    have hkX : k ∈ X := by
      have : k = x * y⁻¹ := by rw [← hky]; group
      rw [this]
      exact X.mul_mem hx (X.inv_mem (hYX hy))
    refine ⟨k, ⟨hk, hkX⟩, ?_⟩
    rw [← hky]
    simp [(QuotientGroup.eq_one_iff y).mpr hy]
  · let f : ↥(K ⊓ X) →* G ⧸ Y := (QuotientGroup.mk' Y).comp (K ⊓ X).subtype
    have hker : f.ker = Y.subgroupOf (K ⊓ X) := by
      ext x
      simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    have hrange : f.range = (K ⊓ X).map (QuotientGroup.mk' Y) := by
      simp [f, MonoidHom.range_comp]
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)⟩

@[expose] def preO2 (K Y : Subgroup G) [Y.Normal] : Subgroup G :=
  K ⊓ (pCoreOf 2 (K.map (QuotientGroup.mk' Y))).comap (QuotientGroup.mk' Y)

theorem ten_two_core [Finite G] {T X Y K H : Subgroup G} [Y.Normal]
    (hT : IsSylowIn 2 T H) (hXH : X ≤ H) (hK : K ∈ sFamily T X Y) :
    IsSylowIn 2 (T ⊓ preO2 K Y) (preO2 K Y) ∧
      K ≤ Subgroup.normalizer ((T ⊓ preO2 K Y : Subgroup G) : Set G) ∧
      ∀ z ∈ preO2 K Y, ∃ s ∈ T ⊓ preO2 K Y, ∃ y ∈ K ⊓ Y, z = s * y := by
  obtain ⟨hKle, hTK, hEq, hmin⟩ := hK
  set π := QuotientGroup.mk' Y with hπ
  set Z := K ⊓ (pCoreOf 2 (K.map π)).comap π with hZ
  have hZK : Z ≤ K := inf_le_left
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hkb : π k ∈ K.map π := Subgroup.mem_map_of_mem _ hk
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K.map π) hkb) (π z)
    simp only [hZ, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨hz, hz2⟩
      exact ⟨K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), h1.mp hz2⟩
    · rintro ⟨hz, hz2⟩
      refine ⟨?_, h1.mpr hz2⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk
      simpa [mul_assoc] using this
  have hKYZ : K ⊓ Y ≤ Z := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy.2
    show π y ∈ pCoreOf 2 (K.map π)
    rw [h1]
    exact Subgroup.one_mem _
  have hnorm : ((K ⊓ Y).subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKYZ).mpr (fun z hz => by
      have hzK : z ∈ K := hZK hz
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have : w ∈ K ⊓ Y ↔ z * w * z⁻¹ ∈ K ⊓ Y := by
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨hw, hwY⟩
          exact ⟨K.mul_mem (K.mul_mem hzK hw) (K.inv_mem hzK),
            Subgroup.Normal.conj_mem inferInstance w hwY z⟩
        · rintro ⟨hw, hwY⟩
          refine ⟨?_, ?_⟩
          · have := K.mul_mem (K.mul_mem (K.inv_mem hzK) hw) hzK
            simpa [mul_assoc] using this
          · have := Subgroup.Normal.conj_mem inferInstance _ hwY z⁻¹
            simpa [mul_assoc] using this
      exact this)
  have hpow : ∀ z ∈ Z, ∃ k : ℕ, z ^ 2 ^ k ∈ K ⊓ Y := by
    intro z hz
    have hz2 : π z ∈ pCoreOf 2 (K.map π) := hz.2
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K.map π)) ⟨π z, hz2⟩
    refine ⟨k, Subgroup.mem_inf.mpr ⟨K.pow_mem (hZK hz) _, ?_⟩⟩
    show z ^ 2 ^ k ∈ Y
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have := congrArg Subtype.val hk
    exact (by simpa using this : π z ^ 2 ^ k = 1)
  have hTK' : IsSylowTwoOf T K :=
    B6.isSylowTwoOf_mono hT hTK (hKle.trans (sup_le hXH hT.le))
  have hP : IsSylowTwoOf (T ⊓ Z) Z := B6.isSylowTwoOf_inf_normal hTK' hZK hKZ
  have hfr : K ≤ Z ⊔ (K ⊓ Subgroup.normalizer ((T ⊓ Z : Subgroup G) : Set G)) :=
    B6.frattini_two hZK hKZ hP
  set N' := K ⊓ Subgroup.normalizer ((T ⊓ Z : Subgroup G) : Set G) with hN'
  have hTN' : T ≤ N' := by
    refine le_inf hTK ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer ht
    have h2 : t ∈ Subgroup.normalizer (Z : Set G) := hKZ (hTK ht)
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp h1 w, Subgroup.mem_normalizer_iff.mp h2 w]
  have hPN' : T ⊓ Z ≤ N' := fun x hx => ⟨hTK hx.1, Subgroup.le_normalizer hx⟩
  have hKN' : K ≤ N' ⊔ Y := by
    intro k hk
    have hk' := hfr hk
    have hN'norm : N' ≤ Subgroup.normalizer (Z : Set G) := inf_le_left.trans hKZ
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Z N' hN'norm] at hk'
    obtain ⟨z, hz, n, hn, rfl⟩ := hk'
    obtain ⟨s, hs, y, hy, rfl⟩ := exists_mul_eq_of_pow_mem (p := 2) hnorm hpow
      (isSylowIn_two_iff.mpr hP) z hz
    have hy' : (y : G) ∈ Y := hy.2
    have hs' : (s : G) ∈ N' := hPN' hs
    have e : (s : G) * y * n = (s * n) * (n⁻¹ * y * n) := by group
    have hc : n⁻¹ * y * n ∈ Y := by
      have := Subgroup.Normal.conj_mem inferInstance y hy' n⁻¹
      simpa using this
    show (s : G) * y * n ∈ N' ⊔ Y
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N'.mul_mem hs' hn)) (Subgroup.mem_sup_right hc)
  have hN'le : N' ≤ K := inf_le_left
  have hEq' : X ⊔ T = N' ⊔ Y := by
    refine le_antisymm ?_ (sup_le (hN'le.trans hKle) ?_)
    · rw [hEq]
      exact sup_le hKN' le_sup_right
    · exact (le_sup_right : Y ≤ K ⊔ Y).trans hEq.ge
  have hN'K : N' = K :=
    hmin N' (hN'le.trans hKle) hTN' hEq' hN'le
  have hKP : K ≤ Subgroup.normalizer ((T ⊓ Z : Subgroup G) : Set G) :=
    fun k hk => (hN'K ▸ hk : k ∈ N').2
  exact ⟨isSylowIn_two_iff.mpr hP, hKP, fun z hz =>
    exists_mul_eq_of_pow_mem (p := 2) hnorm hpow (isSylowIn_two_iff.mpr hP) z hz⟩

theorem ten_two [Finite G] {T X Y K H : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T H)
    (hXH : X ≤ H) (hK : K ∈ sFamily T X Y) : IsTwoClosed (preO2 K Y) := by
  obtain ⟨h1, h2, -⟩ := ten_two_core hT hXH hK
  refine ⟨T ⊓ preO2 K Y, h1, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    ((inf_le_left : preO2 K Y ≤ K).trans h2)

end E1

end CFSG.Quasithin
