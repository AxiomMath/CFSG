module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail22
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

namespace Proof1624KD

open CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotMulAut (H : Type*) [Group H] [Finite H] :
    MulAut H →* MulAut (H ⧸ CFSG.pPrimeCore 3 H) where
  toFun σ := QuotientGroup.congr _ _ σ
    (Subgroup.characteristic_iff_map_eq.mp CFSG.pPrimeCore_characteristic σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem quotMulAut_mk {H : Type*} [Group H] [Finite H] (σ : MulAut H) (h : H) :
    quotMulAut H σ (h : H ⧸ CFSG.pPrimeCore 3 H) = ((σ h : H) : H ⧸ CFSG.pPrimeCore 3 H) :=
  rfl

theorem exists_mem_zpowers_conj {X : Type*} [Group X] [Finite X]
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x y : X} (hx : orderOf x = 3)
    (hy : orderOf y = 3) : ∃ t : X, y ∈ Subgroup.zpowers (t * x * t⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨S, hS⟩ := hxP.exists_le_sylow
  obtain ⟨S', hS'⟩ := hyP.exists_le_sylow
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq X S S'
  refine ⟨t, ?_⟩
  have hcS' := hcyc S'
  have hxt : t * x * t⁻¹ ∈ (S' : Subgroup X) := by
    subst ht
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hS (Subgroup.mem_zpowers x) using 1
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    group
  have h1 : Subgroup.zpowers (t * x * t⁻¹) ≤ (S' : Subgroup X) := Subgroup.zpowers_le.mpr hxt
  have h2 : Subgroup.zpowers y ≤ (S' : Subgroup X) := hS'
  have hxt3 : orderOf (t * x * t⁻¹) = 3 := by
    rw [show t * x * t⁻¹ = (MulAut.conj t) x from rfl, MulEquiv.orderOf_eq, hx]
  have heq : (Subgroup.zpowers y).subgroupOf (S' : Subgroup X) =
      (Subgroup.zpowers (t * x * t⁻¹)).subgroupOf (S' : Subgroup X) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, hy, hxt3]
  rw [Subgroup.subgroupOf_inj, inf_of_le_left h2, inf_of_le_left h1] at heq
  rw [← heq]
  exact Subgroup.mem_zpowers y

theorem orderOf_mk_eq_three {D : Subgroup G} {d : D} (hd : orderOf d = 3) :
    orderOf (d : ↥D ⧸ CFSG.pPrimeCore 3 ↥D) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, ← hd, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hdvd : orderOf (⟨d, h1⟩ : CFSG.pPrimeCore 3 ↥D) ∣ Nat.card (CFSG.pPrimeCore 3 ↥D) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hd] at hdvd
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, dvd_rfl, hdvd⟩
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥D))

theorem isCyclic_sylow_quot {D : Subgroup G}
    (hcyc : ∀ S : Sylow 3 ↥D, IsCyclic ↥(S : Subgroup ↥D)) :
    ∀ S : Sylow 3 (↥D ⧸ CFSG.pPrimeCore 3 ↥D),
      IsCyclic ↥(S : Subgroup (↥D ⧸ CFSG.pPrimeCore 3 ↥D)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  obtain ⟨S₀, rfl⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥D)) 3 S
  rw [Sylow.coe_mapSurjective]
  have := hcyc S₀
  exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap (S₀ : Subgroup ↥D))
    (MonoidHom.subgroupMap_surjective _ _)

theorem normalClosure_eq_top {M : Subgroup G} {c : G} (hcM : c ∈ M) (hc3 : orderOf c = 3)
    (hcD : c ∈ normalClosureSub M (Subgroup.zpowers c))
    (hcyc : ∀ S : Sylow 3 (↥(normalClosureSub M (Subgroup.zpowers c)) ⧸
      CFSG.pPrimeCore 3 ↥(normalClosureSub M (Subgroup.zpowers c))),
      IsCyclic ↥(S : Subgroup (↥(normalClosureSub M (Subgroup.zpowers c)) ⧸
        CFSG.pPrimeCore 3 ↥(normalClosureSub M (Subgroup.zpowers c))))) :
    Subgroup.normalClosure ({((⟨c, hcD⟩ : normalClosureSub M (Subgroup.zpowers c)) :
      ↥(normalClosureSub M (Subgroup.zpowers c)) ⧸
        CFSG.pPrimeCore 3 ↥(normalClosureSub M (Subgroup.zpowers c)))} : Set _) = ⊤ := by
  set D := normalClosureSub M (Subgroup.zpowers c) with hDdef
  set O := CFSG.pPrimeCore 3 ↥D with hO
  set x : ↥D ⧸ O := ((⟨c, hcD⟩ : D) : ↥D ⧸ O) with hx
  set N := Subgroup.normalClosure ({x} : Set (↥D ⧸ O)) with hN
  obtain ⟨-, -, hMD⟩ := Proof169.normalClosureSub_spec (Subgroup.zpowers_le.mpr hcM)
  have hx3 : orderOf x = 3 := orderOf_mk_eq_three (d := ⟨c, hcD⟩) (by
    rw [Subgroup.orderOf_mk, hc3])
  set D' : Subgroup G := (N.comap (QuotientGroup.mk' O)).map D.subtype with hD'
  have hgen : Late.normalClosureIn M c ≤ D' := by
    rw [Late.normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    have hmD : m * c * m⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hMD hm) c).mp hcD
    refine ⟨⟨m * c * m⁻¹, hmD⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hy3 : orderOf ((⟨m * c * m⁻¹, hmD⟩ : D) : ↥D ⧸ O) = 3 := by
      refine orderOf_mk_eq_three ?_
      rw [Subgroup.orderOf_mk, show m * c * m⁻¹ = (MulAut.conj m) c from rfl,
        MulEquiv.orderOf_eq, hc3]
    obtain ⟨t, ht⟩ := exists_mem_zpowers_conj hcyc hx3 hy3
    have htx : t * x * t⁻¹ ∈ N :=
      (Subgroup.normalClosure_normal (s := ({x} : Set (↥D ⧸ O)))).conj_mem x
        (Subgroup.subset_normalClosure (Set.mem_singleton x)) t
    exact (Subgroup.zpowers_le.mpr htx) ht
  have hDD' : D ≤ D' := (Proof1622.normalClosureSub_le_normalClosureIn M c).trans hgen
  rw [eq_top_iff]
  intro q _
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective O q
  obtain ⟨d', hd', hdd'⟩ := hDD' d.2
  have : d' = d := Subtype.ext hdd'
  rw [this] at hd'
  exact hd'

end Proof1624KD

open Proof1624KD CFSG.RankThree.PartTwo.Sec15

end CFSG.RankThree.PartTwo.Sec16
