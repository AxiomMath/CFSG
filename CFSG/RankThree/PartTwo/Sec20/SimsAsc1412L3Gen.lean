module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem normalizer_zpowers_le_map {K : Subgroup X} [K.Normal] (hK2 : IsPGroup 2 K)
    {x : X} (hx3 : orderOf x = 3) :
    normalizer (zpowers (QuotientGroup.mk' K x) : Set (X ⧸ K)) ≤
      (normalizer (zpowers x : Set X)).map (QuotientGroup.mk' K) := by
  have hx3' : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  set π := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hπx3 : π x ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
  set V : Subgroup (X ⧸ K) := zpowers (π x) with hV
  have hV3 : IsPGroup 3 V := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [hV, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hπx3
  have hxV : x ∈ V.comap π := Subgroup.mem_zpowers (π x)
  set x' : ↥(V.comap π) := ⟨x, hxV⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'] using hx3')
  have hz3 : IsPGroup 3 (zpowers x') := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx'3
  obtain ⟨R, hR⟩ := hz3.exists_le_sylow
  have hxA : x ∈ CFSG.FiveTransitive.SylowPreimageNormalizer.ambient π V R :=
    ⟨x', hR (Subgroup.mem_zpowers x'), rfl⟩
  have hAeq : CFSG.FiveTransitive.SylowPreimageNormalizer.ambient π V R = zpowers x := by
    refine le_antisymm (fun a ha => ?_) (Subgroup.zpowers_le.2 hxA)
    have haV : π a ∈ V := by
      rw [← CFSG.FiveTransitive.SylowPreimageNormalizer.ambient_map π hπs V hV3 R]
      exact Subgroup.mem_map_of_mem _ ha
    obtain ⟨z, hz, hza⟩ : π a ∈ (zpowers x).map π := by
      rw [MonoidHom.map_zpowers]
      exact haV
    have hzA : z ∈ CFSG.FiveTransitive.SylowPreimageNormalizer.ambient π V R :=
      Subgroup.zpowers_le.2 hxA hz
    have hk : z⁻¹ * a ∈ (QuotientGroup.mk' K).ker := by
      rw [MonoidHom.mem_ker]
      change π (z⁻¹ * a) = 1
      rw [map_mul, map_inv, hza, inv_mul_cancel]
    rw [QuotientGroup.ker_mk'] at hk
    have hmem : z⁻¹ * a ∈ CFSG.FiveTransitive.SylowPreimageNormalizer.ambient π V R ⊓ K :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) ha, hk⟩
    have hdisj : Disjoint (CFSG.FiveTransitive.SylowPreimageNormalizer.ambient π V R) K :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ (R.isPGroup'.map _) hK2
    have h1 : z⁻¹ * a = 1 := Subgroup.mem_bot.1 (hdisj.le_bot hmem)
    have haz : a = z := by
      calc a = z * (z⁻¹ * a) := by group
        _ = z := by rw [h1, mul_one]
    rw [haz]
    exact hz
  have hN := CFSG.FiveTransitive.SylowPreimageNormalizer.normalizer_map π hπs V hV3 R
  rw [hAeq] at hN
  exact hN.ge

theorem sup_normalizer_eq_top_of_gen1412 (h : Hyp1411 X L S)
    (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {x : X} (hxL : x ∈ L) (hx3 : orderOf x = 3)
    {M : Subgroup X} (hSM : S ≤ M) {Ω : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)}
    (hΩM : Ω ≤ M.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (hgen : L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      normalizer (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) :
        Set (X ⧸ CFSG.pPrimeCore 3 X)) ⊔ Ω) :
    normalizer (zpowers x : Set X) ⊔ M = ⊤ := by
  obtain ⟨-, -, -, -, -, hQS, hSL, -⟩ := h
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hker : π.ker = CFSG.pCore 2 X := by rw [hπ, QuotientGroup.ker_mk', hK]
  have hK2 : IsPGroup 2 (CFSG.pPrimeCore 3 X) := hK ▸ CFSG.pCore_isPGroup
  have hFr := normalizer_zpowers_le_map hK2 hx3
  have himg : (normalizer (zpowers x : Set X) ⊔ M).map π = ⊤ := by
    rw [eq_top_iff]
    have h1 : L.map π ≤ (normalizer (zpowers x : Set X) ⊔ M).map π :=
      hgen.trans (sup_le (hFr.trans (Subgroup.map_mono le_sup_left))
        (hΩM.trans (Subgroup.map_mono le_sup_right)))
    have h2 : S.map π ≤ (normalizer (zpowers x : Set X) ⊔ M).map π :=
      Subgroup.map_mono (hSM.trans le_sup_right)
    have h3 : (S ⊔ L).map π = ⊤ := by
      rw [hSL, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← h3, Subgroup.map_sup]
    exact sup_le h2 h1
  rw [eq_top_iff]
  intro g _
  obtain ⟨t, ht, htg⟩ : π g ∈ (normalizer (zpowers x : Set X) ⊔ M).map π := by
    rw [himg]
    exact Subgroup.mem_top _
  have hkt : t⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, htg, inv_mul_cancel]
  rw [hker] at hkt
  have hg : g = t * (t⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem _ ht
    ((le_sup_right : M ≤ normalizer (zpowers x : Set X) ⊔ M) (hSM (hQS hkt)))

end CFSG.RankThree.PartTwo.Sec20
