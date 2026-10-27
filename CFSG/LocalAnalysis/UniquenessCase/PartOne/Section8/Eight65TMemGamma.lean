module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65TMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

theorem t_mem_of_inverts_of_gamma
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {Q Z : Subgroup G} {t : G}
    (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hZt : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) :
    t ∈ D.M := by
  classical
  have hmap : Z.map (MulAut.conj t).toMonoidHom = Z := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      show t * z * t⁻¹ ∈ Z
      rw [hZt z hz]
      exact Z.inv_mem hz
    · intro hx
      refine ⟨x⁻¹, Z.inv_mem hx, ?_⟩
      show t * x⁻¹ * t⁻¹ = x
      simpa using hZt x⁻¹ (Z.inv_mem hx)
  have hnorm : t ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hZel : CFSG.Open.IsElemAbelian 3 Z := by
    haveI : IsCyclic ↥Z := isCyclic_of_prime_card hZcard
    refine ⟨inferInstance, ?_⟩
    intro x hx
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨x, hx⟩)
    rw [hZcard] at h
    simpa using congrArg Subtype.val h
  have hrank : 1 ≤ CFSG.Open.pRank 3 Z :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hZel
      (by rw [hZcard]; norm_num)
  have h1 : t ∈ CFSG.Open.rankThreeGamma 1 3 Q :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := 3) (k := 1) hZQ hrank hnorm
  exact hΓ h1

theorem t_mem_and_map_conj_of_inverts_of_gamma
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    {L Q Z : Subgroup G} {t : G}
    (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hLMle : L ≤ D.M) (hLM : (L.subgroupOf D.M).Normal)
    (hZt : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) :
    t ∈ D.M ∧ L.map (MulAut.conj t).toMonoidHom = L :=
  ⟨t_mem_of_inverts_of_gamma hZQ hZcard hΓ hZt,
    map_conj_eq_self_of_mem_of_normal hLMle hLM
      (t_mem_of_inverts_of_gamma hZQ hZcard hΓ hZt)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
