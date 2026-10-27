module

public import CFSG.Walter.W67.Section6.Util
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Lift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.StandardType

open scoped Pointwise

theorem exists_mul_mem_normalizer_of_isComplement
    {G : Type*} [Group G] [Finite G] {K H S S' : Subgroup G} {n0 : G}
    (hKH : K ≤ H) (hKHnorm : H ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (K.relIndex H))
    (hSH : S ≤ H) (hS'H : S' ≤ H)
    (hKS : K ⊓ S = ⊥) (hKsupS : K ⊔ S = H)
    (hKS' : K ⊓ S' = ⊥) (hKsupS' : K ⊔ S' = H)
    (hS' : S' = S.map (MulAut.conj n0).toMonoidHom) :
    ∃ z ∈ K, z⁻¹ * n0 ∈ Subgroup.normalizer (S : Set G) := by
  obtain ⟨z, hzK, hz⟩ := CFSG.Walter.W67.Sec6.exists_conj_complement_in
    hKH hKHnorm hcop hSH hS'H hKS hKsupS hKS' hKsupS'
  have hz' : S.map (MulAut.conj n0).toMonoidHom = S.map (MulAut.conj z).toMonoidHom := by
    rw [← hS']
    exact hz
  refine ⟨z, hzK, ?_⟩
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    have hy : n0 * x * n0⁻¹ ∈ S.map (MulAut.conj n0).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hz'] at hy
    rcases hy with ⟨w, hw, hw_eq⟩
    have hw_eq' : z * w * z⁻¹ = n0 * x * n0⁻¹ := by
      simpa [MulAut.conj_apply] using hw_eq
    have hcalc : z⁻¹ * n0 * x * (z⁻¹ * n0)⁻¹ = w := by
      calc
        z⁻¹ * n0 * x * (z⁻¹ * n0)⁻¹ = z⁻¹ * (n0 * x * n0⁻¹) * z := by group
        _ = w := by rw [← hw_eq']; group
    change z⁻¹ * n0 * x * (z⁻¹ * n0)⁻¹ ∈ S
    rw [hcalc]
    exact hw
  · rw [Subgroup.card_map_of_injective (MulAut.conj (z⁻¹ * n0)).injective]

theorem exists_normalizer_lift_of_isComplement
    {G R : Type} [Group G] [Finite G] [Group R]
    {Y B J K H S : Subgroup G} {n0 : G} (hn0Y : n0 ∈ Y)
    (ρ : Y →* MulAut R)
    (hBS : B ≤ S) (hBchar : (B.subgroupOf S).Characteristic)
    (hKH : K ≤ H) (hKHnorm : H ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (K.relIndex H))
    (hSH : S ≤ H)
    (hKS : K ⊓ S = ⊥) (hKsupS : K ⊔ S = H)
    (hKJ : K ≤ J) (hKY : K ≤ Y) (hn0J : n0 ∈ J)
    (hρK : ∀ (z : G) (hz : z ∈ K), ρ ⟨z, hKY hz⟩ = 1)
    (hn0H : n0 ∈ Subgroup.normalizer (H : Set G))
    (hn0K : n0 ∈ Subgroup.normalizer (K : Set G)) :
    ∃ n' ∈ J, n' ∈ Subgroup.normalizer (B : Set G) ∧
      ∃ hn'Y : n' ∈ Y, ρ ⟨n', hn'Y⟩ = ρ ⟨n0, hn0Y⟩ := by
  let S' : Subgroup G := S.map (MulAut.conj n0).toMonoidHom
  have hS'H : S' ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn0H s).mp (hSH hs)
  have hKmap : K.map (MulAut.conj n0).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn0K
  have hHmap : H.map (MulAut.conj n0).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn0H
  have hKS' : K ⊓ S' = ⊥ := by
    have h := congrArg (fun T : Subgroup G => T.map (MulAut.conj n0).toMonoidHom) hKS
    have hmap : (K ⊓ S).map (MulAut.conj n0).toMonoidHom = K ⊓ S' := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n0).injective, hKmap]
    rw [hmap, Subgroup.map_bot] at h
    exact h
  have hKsupS' : K ⊔ S' = H := by
    have h := congrArg (fun T : Subgroup G => T.map (MulAut.conj n0).toMonoidHom) hKsupS
    rw [Subgroup.map_sup, hKmap, hHmap] at h
    exact h
  obtain ⟨z, hzK, hn'S⟩ := exists_mul_mem_normalizer_of_isComplement
    hKH hKHnorm hcop hSH hS'H hKS hKsupS hKS' hKsupS' rfl
  have hnormB : z⁻¹ * n0 ∈ Subgroup.normalizer (B : Set G) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.l43_normalizer_le_of_characteristic
      (G := G) (Y := S) (Y₀ := B) hBS hBchar) hn'S
  have hzY : z ∈ Y := hKY hzK
  have hn'Y : z⁻¹ * n0 ∈ Y := Y.mul_mem (Y.inv_mem hzY) hn0Y
  refine ⟨z⁻¹ * n0, J.mul_mem (J.inv_mem (hKJ hzK)) hn0J, hnormB, hn'Y, ?_⟩
  have hsub : (⟨z⁻¹ * n0, hn'Y⟩ : Y) = (⟨z, hzY⟩ : Y)⁻¹ * ⟨n0, hn0Y⟩ := by
    apply Subtype.ext
    rfl
  rw [hsub, map_mul, map_inv, hρK z hzK]
  simp

end CFSG.StandardType
