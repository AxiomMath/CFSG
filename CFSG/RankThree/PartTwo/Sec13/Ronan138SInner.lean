module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_zpowers_of_inner {K P : Subgroup G} {e : G}
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hP3 : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hCT : ∀ T : Subgroup G, IsPGroup 3 T → P ≤ T → T ≤ Subgroup.normalizer (K : Set G) →
      ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e)
    {x : G} (hxP : x ∈ P) {k : G} (hk : k ∈ K)
    (hkx : k⁻¹ * x ∈ Sec4.thetaQuotCentralizer K) :
    x ∈ K ⊔ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (K : Set G) with hNdef
  have hxk : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hPN hxP⟩) =
      MulAut.conj ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := by
    obtain ⟨⟨w, hwN⟩, hker, hw⟩ := Subgroup.mem_map.mp hkx
    change w = k⁻¹ * x at hw
    have hkN : k ∈ N := Subgroup.le_normalizer hk
    have e1 : (⟨x, hPN hxP⟩ : N) = ⟨k, hkN⟩ * ⟨w, hwN⟩ := Subtype.ext (by
      change x = k * w
      rw [hw, mul_inv_cancel_left])
    have h1 : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨w, hwN⟩) = 1 := hker
    rw [e1, map_mul, map_mul, h1, mul_one]
    exact Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem ⟨k, hk⟩
  set ρ : N →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hρ
  set X := P ⊔ K with hX
  have hXN : X ≤ N := sup_le hPN Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := X)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup X).map X.subtype with hTdef
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T X := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun y hy =>
    ⟨⟨y, (le_sup_left : P ≤ X) hy⟩, hQ (show (⟨y, _⟩ : X) ∈ P.subgroupOf X from hy), rfl⟩
  have hT3 : IsPGroup 3 T := hTsyl.isPGroup
  have hTN : T ≤ N := hTsyl.le.trans hXN
  obtain ⟨SK, hSK⟩ := hTsyl.inf_of_le_normalizer (le_sup_right : K ≤ X) hXN
  have hSKmem : ∀ q : K, q ∈ (SK : Subgroup K) ↔ (q : G) ∈ T ⊓ K := by
    intro q
    constructor
    · intro hq
      rw [← hSK]
      exact ⟨q, hq, rfl⟩
    · intro hq
      rw [← hSK] at hq
      obtain ⟨q', hq', hqq'⟩ := hq
      rwa [← Subtype.ext hqq']
  set Qb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    SK.mapSurjective (QuotientGroup.mk'_surjective _) with hQbdef
  have hQb : (Qb : Subgroup _) =
      (SK : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
    Sylow.coe_mapSurjective _ _
  have hconj : Function.Injective
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _) :=
    KFacts.KS14.conj_injective_of_center_eq_bot hZ
  set Sh : Subgroup (K ⧸ aschbacherSolvableCore 3 K) :=
    ((T.subgroupOf N).map ρ).comap MulAut.conj with hShdef
  have hSh3 : IsPGroup 3 Sh :=
    ((hT3.comap_subtype (K := N)).map ρ).comap_of_injective _ hconj
  have hQbSh : (Qb : Subgroup _) ≤ Sh := by
    rw [hQb]
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, Subgroup.le_normalizer q.2⟩, ?_, ?_⟩
    · exact ((hSKmem q).mp hq).1
    · exact Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q
  have hShQb : Sh = Qb := Qb.3 hSh3 hQbSh
  have hkSh : ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈ Sh :=
    ⟨⟨x, hPN hxP⟩, hPT hxP, hxk⟩
  rw [hShQb, hQb] at hkSh
  obtain ⟨q, hqSK, hqk⟩ := hkSh
  have hqTK : (q : G) ∈ T ⊓ K := (hSKmem q).mp hqSK
  set r := (q : G)⁻¹ * x with hrdef
  have hqN : (q : G) ∈ N := Subgroup.le_normalizer q.2
  have hrN : r ∈ N := mul_mem (inv_mem hqN) (hPN hxP)
  have hrD : r ∈ Sec4.thetaQuotCentralizer K := by
    refine Subgroup.mem_map.mpr ⟨⟨r, hrN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have he : (⟨r, hrN⟩ : N) = (⟨q, hqN⟩ : N)⁻¹ * ⟨x, hPN hxP⟩ := rfl
    rw [he, map_mul, map_inv]
    change (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨q, hqN⟩))⁻¹ *
      Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hPN hxP⟩) = 1
    rw [Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q, hxk]
    have : (q : K ⧸ aschbacherSolvableCore 3 K) =
        ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := hqk
    rw [this, inv_mul_cancel]
  have hrT : r ∈ T := mul_mem (inv_mem hqTK.1) (hPT hxP)
  have hre : r ∈ Subgroup.zpowers e := hCT T hT3 hPT hTN r hrT hrD
  have hxqr : x = (q : G) * r := by rw [hrdef, mul_inv_cancel_left]
  rw [hxqr]
  exact mul_mem (Subgroup.mem_sup_left q.2) (Subgroup.mem_sup_right hre)

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
