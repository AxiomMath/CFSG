module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
import CFSG.GH74.GLS.Balance.Bender.T59
import CFSG.Walter.W67.W1Basic
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.SteinbergCBFTHall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812
import CFSG.GroupTheory.ConjActionModPCore
import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.Quasithin.Background.F1Models
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem seven_dvd_card_of_threeCover_onan {Y : Type} [Group Y]
    [Finite Y] (hY : ThreeCover (fun Z _ => IsSpor Z .ONan) Y) : 7 ∣ Nat.card Y := by
  obtain ⟨-, -, ⟨e⟩⟩ := hY
  have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  have hdvd : Nat.card (Y ⧸ Subgroup.center Y) ∣ Nat.card Y :=
    Subgroup.card_quotient_dvd_card (Subgroup.center Y)
  rw [hcard] at hdvd
  exact (show 7 ∣ 460815505920 by norm_num).trans hdvd

namespace Ctx82E3

variable (c : Ctx82E3 D)

private theorem isHatON_lbar_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩

theorem pow_three_eq_one_of_mem_inf_L_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ P ⊓ c.L, x ^ 3 = 1 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  intro x hx
  have hxP : x ∈ P := hx.1
  let l : ↥c.L := ⟨x, hx.2⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers l) := by
    obtain ⟨n, hn⟩ := hP.isPGroup (⟨x, hxP⟩ : ↥P)
    have hlpow : l ^ 3 ^ n = 1 := by
      apply Subtype.ext
      simpa [l] using congrArg (fun y : ↥P => (y : G)) hn
    have hdvd : orderOf l ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hlpow
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.iff_card.mpr ⟨m, by rw [Nat.card_zpowers, hm]⟩
  have hπp : IsPGroup 3 (Subgroup.zpowers (π l)) := by
    rw [← MonoidHom.map_zpowers π l]
    exact IsPGroup.map hzp π
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hπp
  have hπl3 : (π l) ^ 3 = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds c.Lbar hON S (π l)
      (hS (Subgroup.mem_zpowers (π l)))
  have hl3N : l ^ 3 ∈ N := by
    have h1 : (QuotientGroup.mk' N) (l ^ 3) = 1 := by
      change π (l ^ 3) = 1
      rw [map_pow]
      exact hπl3
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff (l ^ 3)).mp h1
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hdisj : Disjoint N (Subgroup.zpowers l) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) N (Subgroup.zpowers l) hN2 hzp
  have hmem : l ^ 3 ∈ N ⊓ Subgroup.zpowers l :=
    ⟨hl3N, Subgroup.pow_mem (Subgroup.zpowers l) (Subgroup.mem_zpowers l) 3⟩
  rw [hdisj.eq_bot] at hmem
  have hl3 : l ^ 3 = 1 := by simpa using hmem
  have hx3 : x ^ 3 = 1 := congrArg (fun y : ↥c.L => (y : G)) hl3
  simpa [l] using hx3

private theorem inf_centralizer_map_le_center
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ≤ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = (Q.subgroupOf c.L).map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hHat := isHatON_lbar_of_onan c hON
  have hcen := (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).2.2.2
  rintro w ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hzQ : (z : G) ∈ Q := hzZ.1
  have hzcent := hzZ.2
  have hzY : z ∈ Q.subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]; exact hzQ
  have hzS : π z ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hzY
  refine hcen (π z) hzS ?_
  intro s hs
  rw [hScoe] at hs
  obtain ⟨q, hqY, rfl⟩ := Subgroup.mem_map.mp hs
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hqY
  exact Subgroup.mem_centralizer_iff.mp hzcent (q : G) hqQ

private theorem center_le_inf_centralizer_map
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Subgroup.center c.Lbar ≤
      (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  let Y : Subgroup ↥c.L := Q.subgroupOf c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = Y.map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hcenter3 : IsPGroup 3 (Subgroup.center c.Lbar) :=
    IsPGroup.of_card (n := 1) (by rw [hON.2.1]; norm_num)
  have hcenS : Subgroup.center c.Lbar ≤ (S : Subgroup c.Lbar) :=
    hcenter3.le_sylow_of_normal S
  have hQ3 : IsPGroup 3 Q := hP.isPGroup.to_le inf_le_left
  have hQsub3 : IsPGroup 3 Y := hQ3.comap_subtype
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hinjY : Function.Injective (π.comp Y.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y N hQsub3 hN2) y.2
      ((QuotientGroup.eq_one_iff (y : ↥c.L)).mp (MonoidHom.mem_ker.mp hy))))
  intro y hy
  have hyS : y ∈ (S : Subgroup c.Lbar) := hcenS hy
  rw [hScoe] at hyS
  obtain ⟨q, hqY, hqy⟩ := Subgroup.mem_map.mp hyS
  refine Subgroup.mem_map.mpr ⟨q, ?_, hqy⟩
  rw [Subgroup.mem_subgroupOf]
  refine ⟨Subgroup.mem_subgroupOf.mp hqY, ?_⟩
  change (q : G) ∈ Subgroup.centralizer (Q : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro q' hq'Q
  let q'L : ↥c.L := ⟨q', (Subgroup.mem_inf.mp hq'Q).2⟩
  let q'Y : ↥Y := ⟨q'L, by rw [Subgroup.mem_subgroupOf]; exact hq'Q⟩
  let qY : ↥Y := ⟨q, hqY⟩
  have hcomm : π q'L * y = y * π q'L := Subgroup.mem_center_iff.mp hy (π q'L)
  rw [← hqy] at hcomm
  have hprod : q'Y * qY = qY * q'Y := by
    apply hinjY
    show π (q'L * q) = π (q * q'L)
    rw [map_mul, map_mul]
    exact hcomm
  have hprod' : q'L * q = q * q'L :=
    congrArg (fun u : ↥Y => (u : ↥c.L)) hprod
  exact congrArg (fun u : ↥c.L => (u : G)) hprod'

private theorem map_inf_centralizer_eq_center
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = Subgroup.center c.Lbar :=
  le_antisymm (inf_centralizer_map_le_center c hON hP) (center_le_inf_centralizer_map c hON hP)

theorem card_inf_centralizer_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) = 3 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  have hZleL : Z ≤ c.L := (inf_le_left.trans inf_le_right)
  have hQ3 : IsPGroup 3 Q := hP.isPGroup.to_le inf_le_left
  have hZ3 : IsPGroup 3 Z := hQ3.to_le inf_le_left
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hZdisj : (Z.subgroupOf c.L) ⊓ N = ⊥ := by
    have hYdisj : (Q.subgroupOf c.L) ⊓ N = ⊥ := by
      have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) (Q.subgroupOf c.L) N
        (hQ3.comap_subtype) hN2
      exact hd.eq_bot
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ (Q.subgroupOf c.L) ⊓ N :=
      ⟨Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx.1).1, hx.2⟩
    rw [hYdisj] at hx'
    exact hx'
  have hZcard : Nat.card ↥(Z.subgroupOf c.L) = Nat.card ↥((Z.subgroupOf c.L).map π) := by
    have hker : (Z.subgroupOf c.L) ⊓ π.ker = ⊥ := by
      rw [QuotientGroup.ker_mk']
      exact hZdisj
    exact (CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot π (Z.subgroupOf c.L) hker).symm
  have hcardZ : Nat.card ↥Z = Nat.card ↥(Z.subgroupOf c.L) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleL).toEquiv).symm
  rw [hcardZ, hZcard, map_inf_centralizer_eq_center c hON hP]
  exact hON.2.1

private theorem preimage_center_eq_sup_pCore_inf_centralizer
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((Subgroup.center c.Lbar).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))).map
        c.L.subtype =
      (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype ⊔
        ((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G)) := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  let O : Subgroup G := N.map c.L.subtype
  let K : Subgroup G := ((Subgroup.center c.Lbar).comap π).map c.L.subtype
  have hZleM : Z ≤ D.M := (inf_le_left.trans inf_le_left).trans hP.le
  have hZnormO : Z ≤ Subgroup.normalizer (O : Set G) :=
    hZleM.trans (c.le_normalizer_L.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L))
  have hZmap := map_inf_centralizer_eq_center c hON hP
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    have hlcenter : π l ∈ Subgroup.center c.Lbar := Subgroup.mem_comap.mp hl
    have hlZ : π l ∈ (Z.subgroupOf c.L).map π := by rw [hZmap]; exact hlcenter
    obtain ⟨z, hzZ, hz⟩ := Subgroup.mem_map.mp hlZ
    have hoN : l * z⁻¹ ∈ N := by
      have h1 : π (l * z⁻¹) = 1 := by rw [map_mul, map_inv, hz, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (l * z⁻¹)).mp h1
    have hoO : ((l * z⁻¹ : ↥c.L) : G) ∈ O := Subgroup.mem_map_of_mem _ hoN
    have hzZ' : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hzZ
    refine (CFSG.Walter.W67.mem_sup_iff_of_le_normalizer (K := O) (E := Z) hZnormO).mpr
      ⟨((l * z⁻¹ : ↥c.L) : G), hoO, (z : G), hzZ', ?_⟩
    show ((l * z⁻¹ : ↥c.L) : G) * (z : G) = (l : G)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  · refine sup_le ?_ ?_
    · intro o ho
      obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.mp ho
      have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
      exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_comap.mpr (by rw [hn1]; exact Subgroup.one_mem _),
        rfl⟩
    · intro z hz
      have hzL : z ∈ c.L := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).1).2
      have hzcenter : π ⟨z, hzL⟩ ∈ Subgroup.center c.Lbar := by
        rw [← hZmap]
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, Subgroup.mem_comap.mpr hzcenter, rfl⟩

private theorem preimage_center_subgroupOf_normal
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((((Subgroup.center c.Lbar).comap
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))).map c.L.subtype).subgroupOf D.M).Normal := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let K : Subgroup G := ((Subgroup.center c.Lbar).comap π).map c.L.subtype
  have hKleM : K ≤ D.M := (Subgroup.map_subtype_le _).trans c.hyp81.1
  have hconj : ∀ m ∈ D.M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    have hlcenter : π l ∈ Subgroup.center c.Lbar := Subgroup.mem_comap.mp hl
    have hmlL : m * (l : G) * m⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hm) (l : G)).mp l.2
    refine Subgroup.mem_map.mpr ⟨⟨m * (l : G) * m⁻¹, hmlL⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    let f : MulAut c.Lbar := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L ⟨m, hm⟩
    have hπ : π ⟨m * (l : G) * m⁻¹, hmlL⟩ = f (π l) :=
      (CFSG.GroupTheory.conjModPCore_mk 2 c.L D.M c.le_normalizer_L ⟨m, hm⟩ l).symm
    rw [hπ]
    have hmap := Subgroup.map_center_eq f
    have hmem : f (π l) ∈ (Subgroup.center c.Lbar).map (f : c.Lbar →* c.Lbar) :=
      ⟨π l, hlcenter, rfl⟩
    rwa [hmap] at hmem
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleM]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact hconj m hm k
  · intro hk
    have hk' := hconj m⁻¹ (D.M.inv_mem hm) (m * k * m⁻¹) hk
    rwa [show m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k by group] at hk'

private theorem isSylowIn_inf_centralizer_preimage
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    CFSG.GH74.GLS.Balance.IsSylowIn 3
      ((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G))
      (((Subgroup.center c.Lbar).comap
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))).map c.L.subtype) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  let O : Subgroup G := N.map c.L.subtype
  let K : Subgroup G := ((Subgroup.center c.Lbar).comap (QuotientGroup.mk' N)).map c.L.subtype
  have hZleM : Z ≤ D.M := (inf_le_left.trans inf_le_left).trans hP.le
  have hZnormO : Z ≤ Subgroup.normalizer (O : Set G) :=
    hZleM.trans (c.le_normalizer_L.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L))
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup.map c.L.subtype
  have hZ3 : IsPGroup 3 Z := hP.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hZcard : Nat.card ↥Z = 3 := c.card_inf_centralizer_of_onan hON hP
  have hKcard : Nat.card K = Nat.card O * 3 := by
    have hKeq : K = O ⊔ Z := preimage_center_eq_sup_pCore_inf_centralizer c hON hP
    rw [hKeq, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O Z hZnormO
      (IsPGroup.disjoint_of_ne 2 3 (by norm_num) O Z hO2 hZ3), hZcard]
  have hKeq : K = O ⊔ Z := preimage_center_eq_sup_pCore_inf_centralizer c hON hP
  refine ⟨le_sup_right.trans hKeq.ge, hZ3, ?_⟩
  intro S hSK hS3
  have hSdvd : Nat.card S ∣ Nat.card O * 3 :=
    (Subgroup.card_dvd_of_le hSK).trans (dvd_of_eq hKcard)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS3
  have hcop : Nat.Coprime (Nat.card S) (Nat.card O) := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 Nat.prime_three (by norm_num)))
  exact (Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_left hSdvd)).trans hZcard.ge

theorem le_sup_normalizer_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    D.M ≤ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype ⊔ (D.M ⊓ Subgroup.normalizer
      (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
        Set G)) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  let O : Subgroup G := N.map c.L.subtype
  let K : Subgroup G := ((Subgroup.center c.Lbar).comap (QuotientGroup.mk' N)).map c.L.subtype
  have hKleM : K ≤ D.M := (Subgroup.map_subtype_le _).trans c.hyp81.1
  have hFr := CFSG.GH74.GLS.Balance.t59_frattini hKleM
    (preimage_center_subgroupOf_normal c hON hP)
    (isSylowIn_inf_centralizer_preimage c hON hP)
  have hKleOZ : K ≤ O ⊔ Z := (preimage_center_eq_sup_pCore_inf_centralizer c hON hP).le
  have hZleH : Z ≤ D.M ⊓ Subgroup.normalizer (Z : Set G) :=
    le_inf ((inf_le_left.trans inf_le_left).trans hP.le) Subgroup.le_normalizer
  exact hFr.trans (sup_le (hKleOZ.trans (sup_le le_sup_left (hZleH.trans le_sup_right)))
    le_sup_right)

theorem exists_mem_normalizer_mk_eq_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (ℓ : c.Lbar) :
    ∃ n : ↥c.L, (n : G) ∈ Subgroup.normalizer
        (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
          Set G) ∧
      (QuotientGroup.mk n : c.Lbar) = ℓ := by
  classical
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective ℓ
  have hHO : D.M ⊓ Subgroup.normalizer
      (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
        Set G) ≤ Subgroup.normalizer (((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype : Subgroup G) :
          Set G) :=
    inf_le_left.trans (c.le_normalizer_L.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L))
  obtain ⟨o, ho, h, hh, hoh⟩ := (CFSG.Walter.W67.mem_sup_iff_of_le_normalizer hHO).mp
    (c.le_sup_normalizer_of_onan hON hP (c.hyp81.1 l.2))
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp ho
  refine ⟨n⁻¹ * l, ?_, ?_⟩
  · have hnl : ((n⁻¹ * l : ↥c.L) : G) = h := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hoh, Subgroup.coe_subtype, inv_mul_cancel_left]
    exact hnl ▸ (Subgroup.mem_inf.mp hh).2
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).mpr hn, inv_one,
      one_mul]

theorem three_le_pRank_normalizer_inf_of_onan
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {p : ℕ} (hp : p ∈ D.sig) :
    3 ≤ CFSG.Open.pRank p (Subgroup.normalizer
      (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
        Set G) ⊓ D.M) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype with hO
  set H : Subgroup G := Subgroup.normalizer
    (((P ⊓ c.L) ⊓ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) : Subgroup G) :
      Set G) ⊓ D.M with hH
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_right.trans (c.le_normalizer_L.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L))
  have hOM : O ≤ D.M := (Subgroup.map_subtype_le _).trans c.hyp81.1
  have hM : H ⊔ O = D.M := le_antisymm (sup_le inf_le_right hOM)
    ((c.le_sup_normalizer_of_onan hON hP).trans
      (sup_le le_sup_right (le_sup_of_le_left (inf_comm _ _).le)))
  have hidx : H.relIndex D.M ∣ Nat.card O := by
    rw [← hM, ← CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hHO]
    exact (H.subgroupOf O).index_dvd_card
  have hnot : ¬ p ∣ (H.subgroupOf D.M).index := fun hpd =>
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup.map c.L.subtype)
      (D.sig_prime p hp).1 (D.sig_prime p hp).2 (hpd.trans hidx)
  exact (c.three_le p hp).trans
    (Theorem82.pRank_le_of_not_dvd_index (D.sig_prime p hp).1 inf_le_right hnot)

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
