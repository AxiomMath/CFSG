module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Proof1520

variable {G : Type} [Group G] [Finite G]

theorem card_inf_dvd_card_quot {A Y : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    Nat.card ↥(A ⊓ Y) ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set ρ : ↥(A ⊓ Y) →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion inf_le_right) with hρ
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_two_iff] at ha
    exact Subtype.ext (eq_one_of_mem_pCoreOf_two ha (hA.2 _ a.2.1))
  rw [Nat.card_congr (MonoidHom.ofInjective hρi).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Proof1520

open Proof1520

theorem step1522HypMeet_of_hessSub (h1517 : Step1517R) (h1518 : Step1518R) (h138 : Item138N)
    (hHS : KS1522HessSub) : Step1522HypMeet := by
  intro G _ _ A c L h Y hctx p P hP
  obtain ⟨m, hm1, hisoL, h9, -, -, h9AL, -⟩ := config_of h1517 h138 h hctx hP
  have hD := h.toSec13Data
  have hY0 : Y ∈ scriptY0 A (lB A) := hctx.mem_y0Star.prop
  have hYA : A ≤ Subgroup.normalizer (Y : Set G) := hY0.1.1.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  obtain ⟨r, e, hr, -, -, -, hYeq, ⟨-, f, -, -, hYiso⟩, -⟩ := hctx.concl1515
  set E : Subgroup ↥L := A.subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_subgroupOf L hD.isElemAbelian
  have hE9 : Nat.card ↥E = 9 := by
    rw [hE, ← Subgroup.inf_subgroupOf_right, card_subgroupOf_inf, h9AL]
  set K : Subgroup ↥L := Y.subgroupOf L with hK
  have hEK : E ≤ Subgroup.normalizer (K : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hYA (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  have hKY : ∀ x : ↥K, ((x : ↥L) : G) ∈ Y := fun x => Subgroup.mem_subgroupOf.mp x.2
  let ι : ↥K →* ↥Y :=
    { toFun := fun x => ⟨((x : ↥L) : G), hKY x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (Subtype.ext (show ((a : ↥L) : G) = ((b : ↥L) : G) from
      congrArg (fun y : ↥Y => (y : G)) hab))
  set ψ : ↥K →* ↥Y ⧸ CFSG.pCore 2 ↥Y := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp ι with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ (((L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hYeq]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨k, hk, o, ho, hko⟩ := hy
    refine ⟨⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.mpr hk.2⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_two_iff]
    show (k : G)⁻¹ * (y : G) ∈ CFSG.Open.pCoreOf 2 Y
    rw [← hko]
    simpa using ho
  have hN2 : IsPGroup 2 ↥ψ.ker := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ hι
  have hKN : IsLThreeEpsAt (↥K ⧸ ψ.ker) r f :=
    IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm hYiso
  have hEleK := hHS ↥L m hm1 hisoL h9 E hEab hE9 K hEK ψ.ker hN2 r f hKN
  have hALY : A ⊓ L ≤ A ⊓ Y := fun x hx =>
    ⟨hx.1, Subgroup.mem_subgroupOf.mp
      (hEleK (Subgroup.mem_subgroupOf.mpr hx.1 : (⟨x, hx.2⟩ : ↥L) ∈ E))⟩
  have h9AY : 9 ∣ Nat.card ↥(A ⊓ Y) := h9AL ▸ Subgroup.card_dvd_of_le hALY
  have h9Y : 9 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    h9AY.trans (card_inf_dvd_card_quot hD.isElemAbelian)
  obtain ⟨-, -, -, -, -, -, hcY⟩ := quot_facts_of_nine_dvd h1518 h138 h hctx hYA h9Y
  have hdvd : Nat.card ↥(A ⊓ Y) ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← hD.card_eq]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(A ⊓ Y) ≠ 27 := by
    intro h27
    have hAY : A ⊓ Y = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hD.card_eq])
    have hcAY : c ∈ A ⊓ Y := by
      rw [hAY]
      exact hD.mem_A
    exact hcY hcAY.2
  obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hik] at h9AY hne ⊢
  interval_cases i
  · norm_num at h9AY
  · norm_num at h9AY
  · norm_num
  · norm_num at hne

end CFSG.RankThree.PartTwo.Sec15
