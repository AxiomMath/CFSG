module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3D
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3EightTorusE9Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem k_SU3EightBorelNine_holds :
    S17.K_SU3EightBorelNine := by
  intro X _ _ hX hZ S hS
  obtain ⟨-, -, -, -, hZ3, -⟩ := exists_mulEquiv_unitarySU_three_of_isSU3 hX hZ
  have hperf : Group.IsPerfect (↥(⊤ : Subgroup X)) := by
    rw [Group.IsPerfect.top_iff]
    exact Group.isPerfect_def.mpr hX.1.1
  let eTop : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  let eQ : (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ≃*
      (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr _ _ eTop (Subgroup.map_center_eq eTop)
  have hXPSU : CFSG.Quasithin.IsPSU 3 2 3 (X ⧸ Subgroup.center X) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hX.2
  have hPSU : CFSG.Quasithin.IsPSU 3 2 3
      (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv eQ.symm hXPSU
  obtain ⟨-, hcard, -, -, -⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds 3 (by norm_num) X (⊤ : Subgroup X) S
      hperf hPSU hS
  rw [top_inf_eq] at hcard
  have hcenTop : Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup X)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr eTop).toEquiv).trans hZ3
  have hcardN : Nat.card ↥(Subgroup.normalizer (S : Set X)) = 63 * Nat.card S := by
    have hmain : Nat.card ↥(Subgroup.normalizer (S : Set X)) * 3 =
        Nat.card S * 63 * 3 := by
      calc Nat.card ↥(Subgroup.normalizer (S : Set X)) * 3 =
            Nat.card ↥(Subgroup.normalizer (S : Set X)) * Nat.gcd 3 (2 ^ 3 + 1) := by
              norm_num
        _ = Nat.card S * (4 ^ 3 - 1) *
              Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup X)) := hcard
        _ = Nat.card S * 63 * 3 := by rw [hcenTop]; norm_num
    omega
  have hZN : Subgroup.center X ≤ Subgroup.normalizer (S : Set X) :=
    Subgroup.center_le_normalizer (S : Set X)
  let N : Subgroup X := Subgroup.normalizer (S : Set X)
  let ZN : Subgroup ↥N := (Subgroup.center X).subgroupOf N
  have hZNcard : Nat.card ↥ZN = 3 := by
    change Nat.card ↥((Subgroup.center X).subgroupOf N) = 3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv]
    exact hZ3
  have h9dvd : 9 ∣ Nat.card ↥N := by
    change 9 ∣ Nat.card ↥(Subgroup.normalizer (S : Set X))
    rw [hcardN]
    exact ⟨7 * Nat.card S, by ring⟩
  obtain ⟨P, hPcard, hZP, -⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    (p := 3) (n := 2) (H := ZN) (L := ⊤) Nat.prime_three
    (by rw [hZNcard]; norm_num) (by rw [Subgroup.card_top]; exact h9dvd) le_top
  have hPp : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) hPcard
  have hSN : S ≤ N := Subgroup.le_normalizer
  have hSsubp : IsPGroup 2 ↥(S.subgroupOf N) := by
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hk]
  have hdisjPS : Disjoint P (S.subgroupOf N) :=
    IsPGroup.disjoint_of_coprime hPp hSsubp
      ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have : (S.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hSylIn : CFSG.Quasithin.IsSylowIn 2 S ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_iff.mpr hS
  have hcycQ : IsCyclic (↥N ⧸ S.subgroupOf N) :=
    isCyclic_normalizer_quot_of_isSU3 hX hSylIn
  have : IsCyclic (↥N ⧸ S.subgroupOf N) := hcycQ
  let φ : ↥P →* (↥N ⧸ S.subgroupOf N) :=
    (QuotientGroup.mk' (S.subgroupOf N)).comp P.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyq : (QuotientGroup.mk (y : ↥N) : ↥N ⧸ S.subgroupOf N) = 1 := by
      simpa [φ] using hy
    have hyS : (y : ↥N) ∈ S.subgroupOf N := (QuotientGroup.eq_one_iff _).mp hyq
    have hmem : (y : ↥N) ∈ P ⊓ S.subgroupOf N := ⟨y.2, hyS⟩
    rw [disjoint_iff.mp hdisjPS] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hPcyc : IsCyclic ↥P := isCyclic_of_injective φ hinj
  have : IsCyclic ↥P := hPcyc
  obtain ⟨x, hxord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
  have hxord9 : orderOf x = 9 := by
    rw [hxord, hPcard]
    norm_num
  have : IsMulCommutative ↥P := IsCyclic.isMulCommutative
  have : (ZN.subgroupOf P).Normal := Subgroup.normal_of_isMulCommutative _
  have hZNsubcard : Nat.card ↥(ZN.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv]
    exact hZNcard
  have hquotcard : Nat.card (↥P ⧸ ZN.subgroupOf P) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZN.subgroupOf P)
    rw [hPcard, hZNsubcard] at h
    omega
  have hx3ZN : ((x : ↥P) : ↥N) ^ 3 ∈ ZN := by
    have hdvd : orderOf (QuotientGroup.mk x : ↥P ⧸ ZN.subgroupOf P) ∣
        Nat.card (↥P ⧸ ZN.subgroupOf P) := orderOf_dvd_natCard _
    rw [hquotcard] at hdvd
    have hmk : (QuotientGroup.mk (x ^ 3 : ↥P) : ↥P ⧸ ZN.subgroupOf P) = 1 := by
      have h3 : (QuotientGroup.mk x : ↥P ⧸ ZN.subgroupOf P) ^ 3 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hdvd
      simpa using h3
    have hmem : x ^ 3 ∈ ZN.subgroupOf P := (QuotientGroup.eq_one_iff _).mp hmk
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [SubgroupClass.coe_pow] using this
  let xN : ↥N := (x : ↥P)
  let xX : X := (xN : X)
  have hxNord : orderOf xN = 9 := by
    change orderOf ((x : ↥P) : ↥N) = 9
    rw [Subgroup.orderOf_coe, hxord9]
  have hxXord : orderOf xX = 9 := by
    change orderOf ((xN : ↥N) : X) = 9
    rw [Subgroup.orderOf_coe, hxNord]
  have hxX3ord : orderOf (xX ^ 3) = 3 := by
    have h := orderOf_pow_of_dvd (x := xX) (n := 3) (by norm_num)
      (by rw [hxXord]; norm_num)
    rw [hxXord] at h
    simpa using h
  have hxX3cen : xX ^ 3 ∈ Subgroup.center X := by
    have hmem : xN ^ 3 ∈ ZN := hx3ZN
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcoe : xX ^ 3 = ((xN ^ 3 : ↥N) : X) := by
      simp [xX, xN, SubgroupClass.coe_pow]
    rw [hcoe]
    exact hmem
  exact ⟨xX, xN.2, hxXord, hxX3ord, hxX3cen⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
