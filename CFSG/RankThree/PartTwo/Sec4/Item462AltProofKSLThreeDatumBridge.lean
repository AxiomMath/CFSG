module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeLift
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFixed
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem noncyclicDatum_of_innThetaNoncyclic {S X : Type} [Group S] [Finite S] [Group X]
    [Finite X] (φ : S →* X) (hφ : Function.Surjective φ)
    (hker : (Subgroup.center X).comap φ = Subgroup.center S)
    (hZ : Nat.card (Subgroup.center S) = 3) {β' : MulAut S} (hβ' : β' ^ 3 = 1)
    {β : MulAut X} (hlift : ∀ s, φ (β' s) = β (φ s)) (h : InnThetaNoncyclic β) :
    NoncyclicDatum β' := by
  classical
  obtain ⟨W, V, hWs, hW3, hWle, hWcomm, hWnorm, hVW, hV2, hVnc⟩ := h
  have hconj1 : ∀ x : X, MulAut.conj x = 1 ↔ x ∈ Subgroup.center X := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun γ : MulAut X => γ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    · intro hx
      refine MulEquiv.ext fun g => ?_
      rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hx g,
        mul_inv_cancel_right]
  let ρ : S →* MulAut X := (MulAut.conj : X →* MulAut X).comp φ
  have hρk : ρ.ker = Subgroup.center S := by
    ext s
    rw [MonoidHom.mem_ker, ← hker, Subgroup.mem_comap]
    exact hconj1 (φ s)
  have hWρ : W ≤ ρ.range := by
    intro w hw
    obtain ⟨x, hx⟩ := hWle hw
    obtain ⟨s, rfl⟩ := hφ x
    exact ⟨s, hx⟩
  have hVρ : V ≤ ρ.range := hVW.trans hWρ
  set R₀ : Subgroup S := W.comap ρ with hR₀
  have hker_le : ρ.ker ≤ R₀ := by
    intro z hz
    rw [hR₀, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact W.one_mem
  have hZR₀ : Subgroup.center S ≤ R₀ := hρk ▸ hker_le
  let g : R₀ →* W := (ρ.domRestrict R₀).codRestrict W (fun t => t.2)
  have hg : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨s, hs⟩ := hWρ hw
    exact ⟨⟨s, by rw [hR₀, Subgroup.mem_comap, hs]; exact hw⟩, Subtype.ext hs⟩
  have hgker_eq : g.ker = ρ.ker.subgroupOf R₀ := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun ht => congrArg Subtype.val ht, fun ht => Subtype.ext ht⟩
  have hgker : Nat.card g.ker = 3 := by
    rw [hgker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv, hρk, hZ]
  have hcardR₀ : Nat.card R₀ = 3 * Nat.card W := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hg, hgker]
  haveI hWs' : Group.IsSolvable W := hWs
  haveI : Group.IsSolvable ρ.ker :=
    Group.isSolvable_of_isSolvable_injective (f := (MulEquiv.subgroupCongr hρk).toMonoidHom)
      (MulEquiv.subgroupCongr hρk).injective
  haveI : Group.IsSolvable g.ker := by
    rw [hgker_eq]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hker_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hker_le).injective
  haveI hR₀s : Group.IsSolvable R₀ :=
    Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  have hD : ∀ r ∈ R₀, (β' r)⁻¹ * r ∈ Subgroup.center S := by
    intro r hr
    have hρr : ρ r ∈ W := hr
    have hcomm := hWcomm _ hρr
    have e1 : β * MulAut.conj (φ r) * β⁻¹ = MulAut.conj (β (φ r)) := by
      refine MulEquiv.ext fun m => ?_
      simp [MulAut.mul_apply, map_mul, map_inv]
    have h1 : MulAut.conj (β (φ r)) = MulAut.conj (φ r) := by
      rw [← e1]
      have hρ' : ρ r = MulAut.conj (φ r) := rfl
      rw [hρ'] at hcomm
      rw [hcomm, mul_inv_cancel_right]
    have h2 : (β (φ r))⁻¹ * φ r ∈ Subgroup.center X := by
      rw [← hconj1, map_mul, map_inv, h1, inv_mul_cancel]
    rw [← hker, Subgroup.mem_comap]
    simp only [map_mul, map_inv, hlift]
    exact h2
  have hZfix : ∀ z ∈ Subgroup.center S, β' z = z := fixed_center_of_cube hZ hβ'
  have hnormR₀ : ∀ c : S, β' c = c → ∀ r ∈ R₀, c * r * c⁻¹ ∈ R₀ := by
    intro c hc r hr
    have hβc : β (φ c) = φ c := by rw [← hlift, hc]
    rw [hR₀, Subgroup.mem_comap]
    have hw := hWnorm (φ c) hβc (ρ r) hr
    have e : ρ (c * r * c⁻¹) = MulAut.conj (φ c) * ρ r * (MulAut.conj (φ c))⁻¹ := by
      simp only [ρ, MonoidHom.comp_apply, map_mul, map_inv]
    rw [e]
    exact hw
  have hZ3 : ∀ z ∈ Subgroup.center S, z ^ 3 = 1 := by
    intro z hz
    have h : (⟨z, hz⟩ : Subgroup.center S) ^ Nat.card (Subgroup.center S) = 1 := pow_card_eq_one'
    rw [hZ] at h
    exact congrArg Subtype.val h
  obtain ⟨P, hP2, hPnc, hPV⟩ := exists_lift_noncyclic_two ρ (by rw [hρk, hZ]) hVρ hV2 hVnc
  have hPR₀ : P ≤ R₀ := hPV.trans (Subgroup.comap_mono hVW)
  have hPfix : ∀ p ∈ P, β' p = p :=
    fixed_of_isPGroup_two hZ3 β' hP2 (fun p hp => hD p (hPR₀ hp))
  refine ⟨R₀ ⊓ fixedSub β', P, le_inf hPR₀ (fun p hp => hPfix p hp), hP2, hPnc, ?_,
    fun r hr => (Subgroup.mem_inf.mp hr).2, ?_, le_inf hZR₀ (fun z hz => hZfix z hz), ?_⟩
  · exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : R₀ ⊓ fixedSub β' ≤ R₀))
      (Subgroup.inclusion_injective _)
  · intro c hc r hr
    obtain ⟨hr1, hr2⟩ := Subgroup.mem_inf.mp hr
    refine Subgroup.mem_inf.mpr ⟨hnormR₀ c hc r hr1, ?_⟩
    rw [mem_fixedSub] at hr2 ⊢
    simp [map_mul, map_inv, hc, hr2]
  · intro h9
    have := h9.trans (Subgroup.card_dvd_of_le (inf_le_left : R₀ ⊓ fixedSub β' ≤ R₀))
    rw [hcardR₀] at this
    omega

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
