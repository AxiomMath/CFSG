module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521Defs
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofHyp
import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof1521

theorem le_L_of_le_centralizer {A : Subgroup G} {c : G} {L Y : Subgroup G} (h : Sec15R G A c L)
    (hctx : Ctx1514 A (lB A) c L Y) (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) :
    Y ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := h.toSec14Std
  obtain ⟨-, h9, hAc⟩ := Proof1517.point_facts h hctx
  have hY4 := hctx.mem_y0Star.prop.1
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hΔ : delta A (lB A) Y ≤ L ⊔ O := by
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQq, hQY⟩ := hQ
    exact Item148Point.le_sup_of_eq_zpowers_sup142 hS hAc
      ⟨hQY.trans (hYc.trans (centralizer_singleton_le_normalizer_zpowers c)),
        hQq.1.2.1, hQq.1.2.2⟩
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hOL : O ≤ Subgroup.normalizer (L : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr h.mem_A))).trans
      (centralizer_le_normalizer_of_three_dvd hS h3)
  have hYres : oPrimeResidualOf 3 Y ≤ L := by
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hy, k, hk⟩
    exact mem_left_of_pow_prime_pow Nat.prime_three hOL (coprime_card_pPrimeCoreOf 3 _)
      (hY4.2.2.1.le.trans hΔ hy) hk
  calc Y = oPrimeResidualOf 3 Y := hY4.2.1
    _ ≤ L := hYres

theorem pCoreOf_two_eq_bot_of_le (h1517 : Step1517R) (hK : KS1521SubTwoCore) {A : Subgroup G}
    {c : G} {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) {p : ℕ}
    {P : Subgroup G} (hP : Data1519 A (lB A) L p P) (hYL : Y ≤ L) :
    CFSG.Open.pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm1, -, hisoL, -⟩ := Proof1520.iso_of h1517 h hctx hP
  obtain ⟨r, -, hr, -, -, -, -, ⟨-, f, -, -, hYiso⟩, -⟩ := hctx.concl1515
  set K : Subgroup ↥L := Y.subgroupOf L with hKdef
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
    exact ⟨⟨⟨y, hYL y.2⟩, y.2⟩, rfl⟩
  have hN2 : IsPGroup 2 ↥ψ.ker := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ hι
  have hKN : IsLThreeEpsAt (↥K ⧸ ψ.ker) r f :=
    IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm hYiso
  have hKS : ψ.ker = ⊥ := hK ↥L m hm1 hisoL K ψ.ker hN2 r f hKN
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyY : y ∈ Y := CFSG.openPCoreOf_le 2 Y hy
  let k : ↥K := ⟨⟨y, hYL hyY⟩, hyY⟩
  have hψk : ψ k = 1 := by
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Proof1520.mem_pCore_two_iff (Y := Y) (y := ⟨y, hyY⟩)).mpr hy
  have hk1 : k = 1 := by
    have hk : k ∈ ψ.ker := MonoidHom.mem_ker.mpr hψk
    rwa [hKS, Subgroup.mem_bot] at hk
  have h1 : ((k : ↥L) : G) = 1 := congrArg (fun k : ↥K => ((k : ↥L) : G)) hk1
  change ((k : ↥L) : G) = 1
  exact h1

end Proof1521

open Proof1521

theorem step1521CY_of (h1517 : Step1517R) (hK : KS1521SubTwoCore) : Step1521CY := by
  intro G _ _ A c L h Y hctx p P hP hOc
  obtain ⟨-, -, -, -, -, -, hYeq, -, -⟩ := hctx.concl1515
  have hYc : Y ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hYeq]
    exact sup_le (inf_le_left.trans h.le_centralizer) hOc
  have hYL : Y ≤ L := le_L_of_le_centralizer h hctx hYc
  have hO2 : CFSG.Open.pCoreOf 2 Y = ⊥ := pCoreOf_two_eq_bot_of_le h1517 hK h hctx hP hYL
  exact hctx.mem_y0Star.prop.2.2 hO2

end CFSG.RankThree.PartTwo.Sec15
