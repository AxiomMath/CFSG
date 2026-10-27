module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derPerfAut
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpComm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48bK_centerL
    {G : Type} [Group G] {B L J : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {hJL : J ≤ L}
    {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hM : GGB2derModelProp B L hBL ψ β)
    {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hψJ : (J.subgroupOf L).map ψ = ⁅ggSpFixPerp W, ggSpFixPerp W⁆)
    (b : ↥B) (j : ↥J)
    (hcomm : ∀ s ∈ ggSpFixPerp W, β b * s = s * β b) :
    L.normalizerMonoidHom (Subgroup.inclusion hBL b) ⟨j, hJL j.2⟩ *
      (⟨j, hJL j.2⟩ : ↥L)⁻¹ ∈ Subgroup.center ↥L := by
  let jL : ↥L := ⟨j, hJL j.2⟩
  have hmem : ψ jL ∈ (J.subgroupOf L).map ψ := by
    rw [Subgroup.mem_map]
    exact ⟨jL, j.2, rfl⟩
  have hmemS : ψ jL ∈ ggSpFixPerp W := by
    rw [hψJ] at hmem
    exact Subgroup.commutator_le_self _ hmem
  have hc := hcomm _ hmemS
  have hconj : ψ (L.normalizerMonoidHom (Subgroup.inclusion hBL b) jL) = ψ jL := by
    rw [hM.conj b jL, hc]
    group
  rw [← hM.ker_eq, MonoidHom.mem_ker]
  show ψ (L.normalizerMonoidHom (Subgroup.inclusion hBL b) jL * jL⁻¹) = 1
  rw [map_mul, map_inv, hconj, mul_inv_cancel]

private lemma l48bK_central
    {G : Type} [Group G] {B L J : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)}
    {hBJ : B ≤ Subgroup.normalizer (J : Set G)}
    {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hM : GGB2derModelProp B L hBL ψ β)
    (hJL : J ≤ L)
    {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hψJ : (J.subgroupOf L).map ψ = ⁅ggSpFixPerp W, ggSpFixPerp W⁆)
    (b : ↥B) (j : ↥J)
    (hcomm : ∀ s ∈ ggSpFixPerp W, β b * s = s * β b) :
    J.normalizerMonoidHom (Subgroup.inclusion hBJ b) j * j⁻¹ ∈ Subgroup.center ↥J := by
  set zJ : ↥J := J.normalizerMonoidHom (Subgroup.inclusion hBJ b) j * j⁻¹ with hzJdef
  change zJ ∈ Subgroup.center ↥J
  have hzL := l48bK_centerL hM (hJL := hJL) hψJ b j hcomm
  have hcoe : Subgroup.inclusion hJL zJ =
      L.normalizerMonoidHom (Subgroup.inclusion hBL b) ⟨j, hJL j.2⟩ *
        (⟨j, hJL j.2⟩ : ↥L)⁻¹ := by
    rw [hzJdef]
    ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [Subgroup.mem_center_iff] at hzL ⊢
  intro k
  apply Subgroup.inclusion_injective hJL
  calc Subgroup.inclusion hJL (k * zJ)
      = Subgroup.inclusion hJL k * Subgroup.inclusion hJL zJ := map_mul _ _ _
    _ = Subgroup.inclusion hJL k *
          (L.normalizerMonoidHom (Subgroup.inclusion hBL b) ⟨j, hJL j.2⟩ *
            (⟨j, hJL j.2⟩ : ↥L)⁻¹) := by rw [hcoe]
    _ = (L.normalizerMonoidHom (Subgroup.inclusion hBL b) ⟨j, hJL j.2⟩ *
          (⟨j, hJL j.2⟩ : ↥L)⁻¹) * Subgroup.inclusion hJL k := hzL _
    _ = Subgroup.inclusion hJL zJ * Subgroup.inclusion hJL k := by rw [hcoe]
    _ = Subgroup.inclusion hJL (zJ * k) := (map_mul _ _ _).symm

theorem ggB2der_hker {G : Type} [Group G] [Finite G] {B L D J : Subgroup G} {x : G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)} (hM : GGB2derModelProp B L hBL ψ β)
    (hJL : J ≤ L) (hJperf : commutator ↥J = ⊤) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hDB : D ≤ B) (hDcent : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hβx : ∀ b : ↥B, (b : G) ∈ Subgroup.zpowers x → β b = 1) {y : ↥B}
    (hDxy : ∀ d ∈ D, ∃ i j : ℤ, d = x ^ i * (y : G) ^ j) (hyD : (y : G) ∈ D)
    (hcompl : IsCompl (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)))
      ((SmallRule.spBilin K r).orthogonal
        (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)))))
    (hψJ : (J.subgroupOf L).map ψ =
      ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))),
        ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)))⁆) :
    ∀ a ∈ β.range,
      (∀ v ∈ SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)),
        (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v = v) →
      a ∈ Subgroup.zpowers (β y) := by
  intro a ha hfix
  let W : Submodule K (Fin r ⊕ Fin r → K) :=
    SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
  have hfixb : ∀ v ∈ W, (SmallRule.spRep (β b) : Module.End K (Fin r ⊕ Fin r → K)) v = v := by
    simpa only [W, ← hb] using hfix
  have hcomm : ∀ s ∈ ggSpFixPerp W, β b * s = s * β b :=
    (ggB2der_centralizer_fixperp hK (W := W) hcompl (β b)).mpr hfixb
  have hψJW : (J.subgroupOf L).map ψ = ⁅ggSpFixPerp W, ggSpFixPerp W⁆ := hψJ
  have hcen : ∀ j : ↥J,
      J.normalizerMonoidHom (Subgroup.inclusion hBJ b) j * j⁻¹ ∈ Subgroup.center ↥J :=
    fun j => l48bK_central hM hJL hψJW b j hcomm
  let φ : ↥J →* ↥J := J.normalizerMonoidHom (Subgroup.inclusion hBJ b)
  have hφ : ∀ j : ↥J, φ j = j := fun j => ggB2der_eq_of_perfect hJperf φ hcen j
  have hbC : (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hφj : J.normalizerMonoidHom (Subgroup.inclusion hBJ b) ⟨j, hj⟩ = ⟨j, hj⟩ :=
      hφ ⟨j, hj⟩
    have hval : j = (b : G) * j * (b : G)⁻¹ := by
      have h := Subgroup.normalizerMonoidHom_apply_apply_coe J
        (Subgroup.inclusion hBJ b) ⟨j, hj⟩
      rw [hφj] at h
      simpa using h
    calc j * (b : G) = ((b : G) * j * (b : G)⁻¹) * (b : G) := by
          conv_lhs => rw [hval]
      _ = (b : G) * j := by group
  have hbD : (b : G) ∈ D := by
    rw [hDcent]
    exact ⟨b.2, hbC⟩
  obtain ⟨i, j, hbij⟩ := hDxy b hbD
  have hxB : x ^ i ∈ B := by
    have hxi : x ^ i = (b : G) * ((y : G) ^ j)⁻¹ := by rw [hbij]; group
    rw [hxi]
    exact B.mul_mem b.2 (B.inv_mem (Subgroup.zpow_mem B y.2 j))
  have hb_eq : b = ⟨x ^ i, hxB⟩ * y ^ j := by
    apply Subtype.ext
    show (b : G) = x ^ i * (y : G) ^ j
    rw [hbij]
  have hβx1 : β ⟨x ^ i, hxB⟩ = 1 :=
    hβx ⟨x ^ i, hxB⟩ (Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) i)
  have hfinal : β b = (β y) ^ j := by
    rw [hb_eq, map_mul, map_zpow, hβx1, one_mul]
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨j, hfinal.symm.trans hb⟩

end CFSG.StandardType
