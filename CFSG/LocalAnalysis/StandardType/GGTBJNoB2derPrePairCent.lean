module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpComm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48pC_normalizerMonoidHom_fix {G : Type} [Group G] {B L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} (c : ↥B) (j : ↥L)
    (hcj : (c : G) * (j : G) = (j : G) * (c : G)) :
    (L.normalizerMonoidHom (Subgroup.inclusion hBL c)) j = j := by
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  change (c : G) * (j : G) * (c : G)⁻¹ = (j : G)
  rw [hcj, mul_assoc, mul_inv_cancel, mul_one]

theorem ggB2der_centralizer_eq {G : Type} [Group G] {B L : Subgroup G} {x : G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K 4)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K 4)} (hM : GGB2derModelProp B L hBL ψ β)
    (hβx : β.ker.map B.subtype = Subgroup.zpowers x) {b : ↥B}
    {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hcompl : IsCompl W ((SmallRule.spBilin K 4).orthogonal W))
    (hkere : ∀ a ∈ β.range,
      (∀ v ∈ W, (SmallRule.spRep a : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v) →
      a ∈ Subgroup.zpowers (β b))
    {J₁ : Subgroup ↥L} (hψJ : J₁.map ψ = ggSpFixPerp W) :
    ∀ c : ↥B, (∀ j ∈ J₁, (c : G) * (j : G) = (j : G) * (c : G)) →
      (c : G) ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers (b : G) := by
  intro c hc
  have hcomm : ∀ s ∈ ggSpFixPerp W, β c * s = s * β c := by
    intro s hs
    rw [← hψJ, Subgroup.mem_map] at hs
    obtain ⟨j, hjJ, rfl⟩ := hs
    have hfix := l48pC_normalizerMonoidHom_fix (hBL := hBL) c j (hc j hjJ)
    have h := hM.conj c j
    rw [hfix] at h
    have h' : β c * ψ j * (β c)⁻¹ = ψ j := h.symm
    have : β c * ψ j = ψ j * β c := by
      calc β c * ψ j = (β c * ψ j * (β c)⁻¹) * (β c) := by group
        _ = ψ j * β c := by rw [h']
    exact this
  have hfixW : ∀ v ∈ W, (SmallRule.spRep (β c) : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v :=
    (ggB2der_centralizer_fixperp hK hcompl (β c)).mp hcomm
  have hmem : β c ∈ Subgroup.zpowers (β b) :=
    hkere (β c) (MonoidHom.mem_range.mpr ⟨c, rfl⟩) hfixW
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  let e : ↥B := c * (b ^ n)⁻¹
  have he : β e = 1 := by
    change β (c * (b ^ n)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hn]
    simp
  have heker : e ∈ β.ker := MonoidHom.mem_ker.mpr he
  have hez : (e : G) ∈ Subgroup.zpowers x := by
    rw [← hβx]
    exact Subgroup.mem_map.mpr ⟨e, heker, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hez
  have hce : (c : G) = (e : G) * ((b : G) ^ n) := by
    have h1 : c = e * b ^ n := by
      change c = (c * (b ^ n)⁻¹) * b ^ n
      group
    calc (c : G) = ((c : ↥B) : G) := rfl
      _ = ((e * b ^ n : ↥B) : G) := by rw [h1]
      _ = (e : G) * ((b : G) ^ n) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
  rw [hce, ← hm]
  exact (Subgroup.zpowers x ⊔ Subgroup.zpowers (b : G)).mul_mem
    (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x m))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers (b : G) n))

end CFSG.StandardType
