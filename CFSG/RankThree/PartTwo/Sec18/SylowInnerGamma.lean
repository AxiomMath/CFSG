module

public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS18L34GenProof
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

namespace SylowInner

open Sec19.Step1914TriProof in
theorem le_gamma_and_mem_zpowers_of_not_inner {E L : Subgroup G} (hE : IsE27 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hLp : ⁅L, L⁆ = L)
    (hLq : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2))) {c e : G}
    (hcE : c ∈ E) (hc3 : orderOf c = 3)
    (hcL : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L)
    (heE : e ∈ E) (heL : e ∈ L) (he1 : e ≠ 1)
    (hnot : ¬ ∀ a ∈ E, InducesInnerMod a L (CFSG.Open.pCoreOf 2 L)) :
    L ≤ gamma 2 E ∧ ∀ a ∈ E, (∀ x ∈ L, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      a ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hLq
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L := theta_eq_pCore_two_of_isSimpleGroup
  set θL := aschbacherSolvableCore 3 L with hθL
  have hθeq' : aschbacherSolvableCore 3 L = CFSG.pCore 2 L := hθeq
  set X := L ⧸ θL with hX
  set ι : L ⧸ CFSG.pCore 2 L ≃* X := QuotientGroup.quotientMulEquivOfEq hθeq.symm with hι
  have : IsSimpleGroup X := ι.symm.isSimpleGroup
  have : Group.IsPerfect X := inferInstance
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_isSimpleGroup_of_isPerfect
  have hconj := conj_injective_of_center_eq_bot' hZX
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut X := Sec12.thetaBarAct L with hρ
  set E' := E.subgroupOf N with hE'
  set Eb : Subgroup (MulAut X) := E'.map ρ with hEb
  have hE'E := isE27_subgroupOf hE hEN
  have hEbab : CFSG.Assembly.IsElemAbelian 3 Eb := Sec4.isElemAbelian_map ρ hE'E.1
  have hcount := card_map_mul_card_ker_subgroupOf ρ E'
  rw [hE'E.2] at hcount
  have hρ1 : ∀ x (hx : x ∈ N), (∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      ρ ⟨x, hx⟩ = 1 := by
    intro x hx hxL
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective θL q
    rw [MulAut.one_apply, hρ, Sec12.thetaBarAct_mk, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem, hθeq',
      mem_pCore_iff_mem_pCoreOf, Subgroup.coe_div, Sec4.normalizerMonoidHom_apply_coe,
      div_eq_mul_inv]
    exact hxL y y.2
  have hcN : c ∈ N := hEN hcE
  have hρc : ρ ⟨c, hcN⟩ = 1 := hρ1 c hcN hcL
  have heN : e ∈ N := hEN heE
  have he3 : e ^ 3 = 1 := hE.1.2 e heE
  have hρe : ρ ⟨e, heN⟩ = MulAut.conj (QuotientGroup.mk' θL ⟨e, heL⟩) := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective θL q
    rw [MulAut.conj_apply, hρ, Sec12.thetaBarAct_mk, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hρe1 : ρ ⟨e, heN⟩ ≠ 1 := by
    rw [hρe]
    intro h1
    have h2 : QuotientGroup.mk' θL ⟨e, heL⟩ = 1 := hconj (h1.trans (map_one _).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 := eq_one_of_mem_theta' h2 (k := 1) (Subtype.ext (by simpa using he3))
    exact he1 (by simpa using congrArg Subtype.val h3)
  have hρeEb : ρ ⟨e, heN⟩ ∈ Eb := ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr heE, rfl⟩
  have hρeinn : ρ ⟨e, heN⟩ ∈ (MulAut.conj : X →* MulAut X).range := ⟨_, hρe.symm⟩
  have hninn : ¬ Eb ≤ (MulAut.conj : X →* MulAut X).range := by
    intro hle
    apply hnot
    intro a ha
    have haN : a ∈ N := hEN ha
    obtain ⟨q, hq⟩ := hle ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective θL q
    refine ⟨haN, k, k.2, fun y hy => ?_⟩
    have h1 : ρ ⟨a, haN⟩ (QuotientGroup.mk' θL ⟨y, hy⟩) =
        QuotientGroup.mk' θL (k * ⟨y, hy⟩ * k⁻¹) := by
      rw [← hq, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [hρ, Sec12.thetaBarAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem, hθeq', mem_pCore_iff_mem_pCoreOf, Subgroup.coe_div,
      Sec4.normalizerMonoidHom_apply_coe] at h1
    simpa [div_eq_mul_inv] using h1
  obtain ⟨φ, hφEb, hφ⟩ : ∃ φ ∈ Eb, φ ∉ (MulAut.conj : X →* MulAut X).range := by
    by_contra hall
    exact hninn fun φ hφ => by_contra fun h => hall ⟨φ, hφ, h⟩
  have hEb9 : Nat.card Eb = 9 := by
    have hcmem : (⟨⟨c, hcN⟩, Subgroup.mem_subgroupOf.mpr hcE⟩ : E') ∈ ρ.ker.subgroupOf E' := by
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact hρc
    have h3k : 3 ∣ Nat.card (ρ.ker.subgroupOf E') := by
      have hord : orderOf (⟨_, hcmem⟩ : ρ.ker.subgroupOf E') = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact hc3
      have h1 := orderOf_dvd_natCard (⟨_, hcmem⟩ : ρ.ker.subgroupOf E')
      rwa [hord] at h1
    obtain ⟨m, hm⟩ := h3k
    rw [hm] at hcount
    have hEbdvd : Nat.card Eb ∣ 3 ^ 2 := ⟨m, by
      have h' : 3 * (Nat.card Eb * m) = 27 := by rw [← hcount]; ring
      omega⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hEbdvd
    interval_cases k
    · exfalso
      rw [pow_zero] at hk'
      have hbot : Eb = ⊥ := Subgroup.eq_bot_of_card_eq Eb hk'
      rw [hbot] at hρeEb
      exact hρe1 (Subgroup.mem_bot.mp hρeEb)
    · exfalso
      rw [pow_one] at hk'
      have hord : orderOf (ρ ⟨e, heN⟩) = 3 := orderOf_eq_prime (hEbab.2 _ hρeEb) hρe1
      have hzp : Subgroup.zpowers (ρ ⟨e, heN⟩) = Eb :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hρeEb)
          (by rw [hk', Nat.card_zpowers, hord])
      rw [← hzp] at hφEb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφEb
      exact hφ (zpow_mem hρeinn j)
    · rw [hk']
      norm_num
  obtain hgen | hinn := KFacts.ks18L34Gen X ⟨ι.symm.trans eL⟩ Eb hEbab hEb9
  swap
  · exact absurd hinn hninn
  have hLΓ : L ≤ gamma 2 E := by
    refine le_gamma_of_closure_eq_top hE hEN ?_
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono ?_
    rintro k ⟨ψ, hψ, hψ1, hψk⟩
    set B : Subgroup G := ((Subgroup.zpowers ψ).comap ρ).map N.subtype ⊓ E with hB
    refine ⟨B, inf_le_right, ?_, ?_⟩
    · obtain ⟨ê, hêE, hêψ⟩ := hψ
      have hcB : c ∈ B :=
        ⟨⟨⟨c, hcN⟩, (show ρ ⟨c, hcN⟩ ∈ Subgroup.zpowers ψ by rw [hρc]; exact Subgroup.one_mem _),
          rfl⟩, hcE⟩
      have hêB : (ê : G) ∈ B :=
        ⟨⟨ê, (show ρ ê ∈ Subgroup.zpowers ψ by rw [hêψ]; exact Subgroup.mem_zpowers ψ), rfl⟩,
          Subgroup.mem_subgroupOf.mp hêE⟩
      have hêc : (ê : G) ∉ Subgroup.zpowers c := by
        intro hmem
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hêeq : ê = (⟨c, hcN⟩ : N) ^ j :=
          Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj.symm)
        apply hψ1
        rw [← hêψ, hêeq, map_zpow, hρc, one_zpow]
      exact two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 inf_le_right)
        (nine_le_card_of_mem_of_not_mem hE inf_le_right hc3 hcB hêB hêc)
    · rintro b ⟨⟨n, hn, hnb⟩, -⟩ hb
      have : (⟨b, hb⟩ : N) = n := Subtype.ext hnb.symm
      rw [this]
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← hj]
      have hs : ψ ∈ MulAction.stabilizer (MulAut X) k := hψk
      exact MulAction.mem_stabilizer_iff.mp (zpow_mem hs j)
  refine ⟨hLΓ, fun a ha haL => ?_⟩
  set K₀ : Subgroup G := ((ρ.ker.subgroupOf E').map E'.subtype).map N.subtype with hK₀
  have hK₀3 : Nat.card K₀ = 3 := by
    rw [hK₀, Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.card_map_of_injective E'.subtype_injective]
    rw [hEb9] at hcount
    omega
  have hmem : ∀ x (hx : x ∈ E), ρ ⟨x, hEN hx⟩ = 1 → x ∈ K₀ := fun x hx h1 =>
    ⟨⟨x, hEN hx⟩, ⟨⟨⟨x, hEN hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩,
      Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_ker.mpr h1), rfl⟩, rfl⟩
  have hzp : Subgroup.zpowers c = K₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hmem c hcE hρc))
      (by rw [hK₀3, Nat.card_zpowers, hc3])
  rw [hzp]
  exact hmem a ha (hρ1 a (hEN ha) haL)

end SylowInner

end CFSG.RankThree.PartTwo.Sec18
