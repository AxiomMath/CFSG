module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open scoped Pointwise

namespace Proof1520

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff {Y : Subgroup G} {y : ↥Y} :
    y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Y := (CFSG.mem_openPCoreOf_iff y).symm

theorem not_dvd_card_of_isPGroup_two {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card H := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

theorem not_le_normalizer_of_ctx (h1517 : Step1517R) (hKT : KS1521TorusCent)
    {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) {p : ℕ} {P : Subgroup G} (hP : Data1519 A (lB A) L p P) :
    ¬ P ≤ Subgroup.normalizer (Y : Set G) := by
  intro hPN
  obtain ⟨m, hm1, -, hisoL, -⟩ := iso_of h1517 h hctx hP
  have hp : p.Prime := hP.1
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := hP.2.1
  have hPL : P ≤ L := hP.2.2.2.2.2.1.1.2
  have hY0 : Y ∈ scriptY0 A (lB A) := hctx.mem_y0Star.prop
  have hPQ : P ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf p) :=
    ⟨⟨hP.2.2.2.2.2.1.1.1, hPN⟩, hP.2.2.2.2.2.1.2⟩
  have hcent := hP.2.2.2.2.2.2 Y hY0 P hPQ
  obtain ⟨-, -, -, -, -, -, hYeq, -, -⟩ := hctx.concl1515
  set K : Subgroup G := L ⊓ Y with hK
  have hKY : K ≤ Y := inf_le_right
  set φ : ↥K →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [hK, ← hYeq]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨k, hk, o, ho, hko⟩ := hy
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_iff]
    simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hko]
    simpa using ho
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf (hPL.trans Subgroup.le_normalizer) hPN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hPp : IsPGroup p ↥P := fun g => ⟨1, Subtype.ext (by simpa using hP.2.2.2.1.2 g g.2)⟩
  have hker2 : IsPGroup 2 ↥φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hKY)
  have hker : ¬ p ∣ Nat.card ↥φ.ker := not_dvd_card_of_isPGroup_two hker2 hp (by omega)
  have hfix := exists_centralizer_with_same_image_of_trivial_quotient_action
    p hp P K hPp hPK φ hker (fun g k => by
      rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_iff]
      have h1 := (hcent g.2).2 ((k : G)⁻¹) (Y.inv_mem (hKY k.2))
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
        inv_inv] at h1 ⊢
      simpa [mul_assoc] using h1)
  have hCab := hKT ↥L m hm1 hisoL p hp hp3 (P.subgroupOf L)
    (isElemAbelian_subgroupOf L hP.2.2.2.1)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hP.2.2.2.2.1])
  have hcomm : ∀ a b : ↥K, (a : G) ∈ Subgroup.centralizer (P : Set G) →
      (b : G) ∈ Subgroup.centralizer (P : Set G) → (a : G) * b = b * a := by
    intro a b ha hb
    have hmem : ∀ z : ↥K, (z : G) ∈ Subgroup.centralizer (P : Set G) →
        (⟨(z : G), (z.2 : (z : G) ∈ K).1⟩ : ↥L) ∈
          Subgroup.centralizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz (y : G)
        (Subgroup.mem_subgroupOf.mp hy))
    have := hCab.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩
    exact congrArg (fun z => ((z : ↥L) : G)) (congrArg Subtype.val this)
  obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hY0.1.2.2.2
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨ku, rfl⟩ := hφs u
  obtain ⟨kv, rfl⟩ := hφs v
  obtain ⟨fu, hfuC, hfu⟩ := hfix ku
  obtain ⟨fv, hfvC, hfv⟩ := hfix kv
  apply huv
  rw [← hfu, ← hfv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← map_mul, ← map_mul,
    show fu * fv = fv * fu from Subtype.ext (hcomm fu fv hfuC hfvC)]

end Proof1520

open Proof1520

theorem step1521Gen_of (h1517 : Step1517R) (hKT : KS1521TorusCent) : Step1521Gen := by
  intro G _ _ A c L h Y hctx p P hP hPN
  exact (not_le_normalizer_of_ctx h1517 hKT h hctx hP hPN).elim

end CFSG.RankThree.PartTwo.Sec15
