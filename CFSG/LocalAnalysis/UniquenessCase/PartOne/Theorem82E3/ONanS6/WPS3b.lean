module

public import CFSG.GroupTheory.CommutatorLeSubgroupOf
public import CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open GroupTheory.CoprimeActionSupport.TwoModuloExtension (perfectResidual_le_of_isSolvable_quotient)
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem isHatON_lbar_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact ⟨hq.1, hZ, ⟨e.trans b⟩⟩

theorem zSub_map_le_center (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((zSub P c.L).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ≤ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = (Q.subgroupOf c.L).map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hHat := isHatON_lbar_of_onan c hON
  have hcen :=
    (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).2.2.2
  rintro w ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hz
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

theorem mem_perfectResidual_of_odd_order_of_map_mem
    {H C : Type*} [Group H] [Finite H] [Group C] [Finite C]
    (f : H →* C) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    {z : H} (hzodd : Odd (orderOf z))
    (hz : f z ∈ CFSG.perfectResidual C) :
    z ∈ CFSG.perfectResidual H := by
  classical
  have hmap := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf
  have hmap' : Subgroup.map f (CFSG.perfectResidual H) = CFSG.perfectResidual C := hmap
  have hzmap : f z ∈ (CFSG.perfectResidual H).map f := by
    rw [hmap']
    exact hz
  obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hzmap
  let P : Subgroup H := CFSG.perfectResidual H
  let q0 : H →* H ⧸ P := QuotientGroup.mk' P
  have hy1 : q0 y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  have hmemker : z * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have hfy' : f y = f z := hfy
    rw [map_mul, map_inv, hfy']
    group
  have hmemMap : q0 z ∈ f.ker.map q0 := by
    have h := Subgroup.mem_map_of_mem q0 hmemker
    simpa [map_mul, hy1] using h
  have hkerMap : IsPGroup 2 (f.ker.map q0) := hker.map q0
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hkerMap) ⟨q0 z, hmemMap⟩
  have hk' : orderOf (q0 z) = 2 ^ k := by simpa using hk
  have hdiv : orderOf (q0 z) ∣ orderOf z := orderOf_map_dvd q0 z
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ orderOf (q0 z) := by
      rw [hk']
      exact dvd_pow_self 2 hk0
    exact hzodd.not_two_dvd_nat (h2.trans hdiv)
  have hone : orderOf (q0 z) = 1 := by rw [hk', hk0, pow_zero]
  have hzP : q0 z = 1 := orderOf_eq_one_iff.mp hone
  exact (QuotientGroup.eq_one_iff z).mp hzP

theorem tripleCover_perfectCoreL
    (c : Ctx82E3 D) {A : Subgroup G} {a : G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (ha : a ∈ A) (haL : a ∈ c.L)
    (hx3 : orderOf (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨a, haL⟩) = 3)
    (hxZ : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨a, haL⟩ ∉ Subgroup.center c.Lbar)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
      (alternatingGroup (Fin 6)) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let aL : ↥c.L := ⟨a, haL⟩
  let x : c.Lbar := π aL
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer ({a} : Set G)
  let H : Subgroup ↥c.L := K.subgroupOf c.L
  let C : Subgroup c.Lbar := Subgroup.centralizer ({x} : Set c.Lbar)
  have hK2 := K2ONanCentralizer_holds (Y := c.Lbar) hON x hx3 hxZ
  dsimp only at hK2
  obtain ⟨hCcard, hZY, hJcard, hCeq, hAlt⟩ := hK2
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hCeq' : C = Subgroup.zpowers x ⊔ J := hCeq
  have hJleC : J ≤ C := Subgroup.commutator_le_self C
  have hxcentC : x ∈ Subgroup.centralizer (C : Set c.Lbar) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hxJ : x ∈ Subgroup.centralizer (J : Set c.Lbar) := by
    rw [Subgroup.mem_centralizer_iff] at hxcentC ⊢
    intro j hj
    exact hxcentC j (hJleC hj)
  have hBcentC : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set c.Lbar) :=
    Subgroup.zpowers_le.mpr hxcentC
  have hBcentJ : Subgroup.zpowers x ≤ Subgroup.centralizer (J : Set c.Lbar) :=
    Subgroup.zpowers_le.mpr hxJ
  have hBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set c.Lbar) :=
    hBcentJ.trans (Subgroup.centralizer_le_normalizer (J : Set c.Lbar))
  have hcomm1 : ⁅J ⊔ Subgroup.zpowers x, C⁆ = ⁅J, C⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := J) (B := Subgroup.zpowers x) (U := C)
      hBnorm hBcentC
  have hcomm2 : ⁅J, C⁆ = ⁅J ⊔ Subgroup.zpowers x, J⁆ := by
    rw [show C = J ⊔ Subgroup.zpowers x by rw [hCeq', sup_comm]]
    exact Subgroup.commutator_comm (H₁ := J) (H₂ := J ⊔ Subgroup.zpowers x)
  have hcomm3 : ⁅J ⊔ Subgroup.zpowers x, J⁆ = ⁅J, J⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := J) (B := Subgroup.zpowers x) (U := J)
      hBnorm hBcentJ
  have hJJ : J = ⁅J, J⁆ := by
    calc J = ⁅C, C⁆ := rfl
      _ = ⁅J ⊔ Subgroup.zpowers x, C⁆ := by rw [hCeq', sup_comm]
      _ = ⁅J, C⁆ := hcomm1
      _ = ⁅J ⊔ Subgroup.zpowers x, J⁆ := hcomm2
      _ = ⁅J, J⁆ := hcomm3
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJJ.symm
  have hNnormal : ((Subgroup.center c.Lbar).subgroupOf J).Normal := inferInstance
  have hNcard : Nat.card ((Subgroup.center c.Lbar).subgroupOf J) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv]
    exact hON.2.1
  have hcenterJ : Subgroup.center ↥J = (Subgroup.center c.Lbar).subgroupOf J := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [← QuotientGroup.eq_one_iff (N := (Subgroup.center c.Lbar).subgroupOf J)]
      have hzq : QuotientGroup.mk' ((Subgroup.center c.Lbar).subgroupOf J) z ∈
          Subgroup.center (↥J ⧸ (Subgroup.center c.Lbar).subgroupOf J) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
          ((Subgroup.center c.Lbar).subgroupOf J) w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
      obtain ⟨eA⟩ := hAlt
      have hzqA : eA (QuotientGroup.mk' ((Subgroup.center c.Lbar).subgroupOf J) z) ∈
          Subgroup.center (alternatingGroup (Fin 6)) := by
        rw [← Subgroup.map_center_eq eA]
        exact Subgroup.mem_map_of_mem eA.toMonoidHom hzq
      have hcenterA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
        alternatingGroup.center_eq_bot (by norm_num)
      rw [hcenterA, Subgroup.mem_bot] at hzqA
      exact eA.map_eq_one_iff.mp hzqA
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hz) (w : c.Lbar)
  have hcenterCard : Nat.card (Subgroup.center ↥J) = 3 := by
    rw [hcenterJ, hNcard]
  have hJtriple : IsTripleCover ↥J (alternatingGroup (Fin 6)) := by
    refine ⟨hcenterCard, ?_⟩
    obtain ⟨eA⟩ := hAlt
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenterJ).trans eA⟩
  have hJeq : (CFSG.perfectResidual ↥C).map C.subtype = J := by
    refine le_antisymm ?_ ?_
    · haveI : (J.subgroupOf C).Normal :=
        CFSG.GroupTheory.normal_subgroupOf_of_commutator_le (le_refl J)
      have hiscomm : IsMulCommutative (↥C ⧸ J.subgroupOf C) :=
        CFSG.GroupTheory.isMulCommutative_quotient_subgroupOf_of_commutator_le
          (V := J) (W := C) (le_refl J)
      letI : IsMulCommutative (↥C ⧸ J.subgroupOf C) := hiscomm
      have hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C) :=
        Group.isSolvable_of_comm (fun a b => (IsMulCommutative.is_comm).comm a b)
      have hle :=
        perfectResidual_le_of_isSolvable_quotient
          (N := J.subgroupOf C) hsolv
      calc (CFSG.perfectResidual ↥C).map C.subtype
          ≤ (J.subgroupOf C).map C.subtype := Subgroup.map_mono hle
        _ = J := Subgroup.map_subgroupOf_eq_of_le hJleC
    · have hperfJC : Group.IsPerfect ↥(J.subgroupOf C) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJleC).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hJleC).symm.surjective
      have hJC : J.subgroupOf C ≤ CFSG.perfectResidual ↥C :=
        CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
          (J.subgroupOf C) hperfJC
      have hmap := Subgroup.map_mono (f := C.subtype) hJC
      rwa [Subgroup.map_subgroupOf_eq_of_le hJleC] at hmap
  have haL3 : aL ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hA.2 a ha
  have ha1 : a ≠ 1 := by
    intro h1
    apply hxZ
    change π aL ∈ Subgroup.center c.Lbar
    rw [show aL = 1 from Subtype.ext h1]
    simp
  have ha1L : aL ≠ 1 := fun h => ha1 (Subtype.ext_iff.mp h)
  have ha_order : orderOf aL = 3 := orderOf_eq_prime haL3 ha1L
  have hzp3 : IsPGroup 3 ↥(Subgroup.zpowers aL) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha_order]
    norm_num
  letI : Fact (IsPGroup 3 ↥(Subgroup.zpowers aL)) := ⟨hzp3⟩
  have hcopO : Nat.Coprime 3 (Nat.card O) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
        CFSG.pCore_isPGroup Nat.prime_three (by norm_num))
  have hcentral :=
    CFSG.centralizer_map_quotient_eq_map_centralizer (p := 3)
      (T := Subgroup.zpowers aL) (M := O) (by infer_instance) hcopO
  have hzp_map : Subgroup.map (QuotientGroup.mk' O) (Subgroup.zpowers aL) =
      Subgroup.zpowers x := by
    simpa [x, π] using MonoidHom.map_zpowers (QuotientGroup.mk' O) aL
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers aL : Set ↥c.L) = H := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext x
    simp [H, K, aL, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcent_zpx : Subgroup.centralizer (Subgroup.zpowers x : Set c.Lbar) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHmapC : H.map π = C := by
    have h := hcentral
    dsimp only at h
    rw [hzp_map, hcent_zp, hcent_zpx] at h
    exact h.symm
  let φH : ↥H →* c.Lbar := π.comp H.subtype
  have hφH_range : φH.range = C := by
    rw [show φH = π.comp H.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hHmapC
  let φC : ↥H →* ↥C := φH.codRestrict C (fun h => by
    have hh : φH h ∈ φH.range := ⟨h, rfl⟩
    rwa [hφH_range] at hh)
  have hφC_surj : Function.Surjective φC := by
    intro y
    have hy : (y : c.Lbar) ∈ φH.range := by
      rw [hφH_range]
      exact y.2
    obtain ⟨h, hh⟩ := hy
    exact ⟨h, Subtype.ext hh⟩
  have hmapCsurj :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φC hφC_surj
  have hmapCsurj' : Subgroup.map φC (CFSG.perfectResidual H) =
      CFSG.perfectResidual ↥C := hmapCsurj
  let IP : Subgroup ↥H := CFSG.perfectResidual H
  have hmapJ : IP.map φH = J := by
    have hcomp : C.subtype.comp φC = φH := MonoidHom.ext (fun _ => rfl)
    calc IP.map φH = IP.map (C.subtype.comp φC) := by rw [hcomp]
      _ = (IP.map φC).map C.subtype := (Subgroup.map_map _ _ _).symm
      _ = (CFSG.perfectResidual ↥C).map C.subtype := by rw [hmapCsurj']
      _ = J := hJeq
  let fG : ↥H →* G := c.L.subtype.comp H.subtype
  have hfG_inj : Function.Injective fG :=
    c.L.subtype_injective.comp H.subtype_injective
  let f : ↥IP →* ↥J :=
    (φH.comp IP.subtype).codRestrict J (fun y => by
      have hy : φH (y : H) ∈ IP.map φH := Subgroup.mem_map_of_mem φH y.2
      rwa [hmapJ] at hy)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : c.Lbar) ∈ IP.map φH := by
      rw [hmapJ]
      exact y.2
    obtain ⟨z, hzIP, hzφ⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨z, hzIP⟩, ?_⟩
    apply Subtype.ext
    change φH z = (y : c.Lbar)
    exact hzφ
  have hpcoreJ : CFSG.pCore 2 ↥J = ⊥ := by
    have hJcomm : commutator ↥J = ⊤ := Group.isPerfect_def.mp hJperf
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := by
      obtain ⟨eA⟩ := hAlt
      haveI : IsSimpleGroup (↥J ⧸ (Subgroup.center c.Lbar).subgroupOf J) := eA.isSimpleGroup
      exact (QuotientGroup.quotientMulEquivOfEq hcenterJ).isSimpleGroup
    have hqJ : CFSG.Open.IsQuasisimple ↥J := ⟨hJcomm, inferInstance⟩
    have hpc_le_center : CFSG.pCore 2 ↥J ≤ Subgroup.center ↥J :=
      GL83.I243.pCore_le_center Nat.prime_two hqJ
    have hcenter3 : IsPGroup 3 (Subgroup.center ↥J) :=
      IsPGroup.of_card (n := 1) (by rw [hcenterCard]; norm_num)
    have hpc2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have hdisj : Disjoint (CFSG.pCore 2 ↥J) (Subgroup.center ↥J) :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hpc2 hcenter3
    have hbot : CFSG.pCore 2 ↥J ⊓ Subgroup.center ↥J = ⊥ := hdisj.eq_bot
    rw [eq_bot_iff]
    intro x hx
    have hxin : x ∈ CFSG.pCore 2 ↥J ⊓ Subgroup.center ↥J := ⟨hx, hpc_le_center hx⟩
    rw [hbot] at hxin
    exact hxin
  let NIP : Subgroup ↥IP := (O.subgroupOf H).subgroupOf IP
  have hNIPnormal : NIP.Normal := inferInstance
  have hNIP2 : IsPGroup 2 NIP := by
    exact ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).comap_subtype (K := H)).comap_subtype
      (K := IP)
  have hf_apply : ∀ y : ↥IP, ((f y : ↥J) : c.Lbar) = φH (y : H) := fun y => rfl
  have hker_eq : f.ker = NIP := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      have h := congrArg Subtype.val hy
      rw [hf_apply] at h
      exact (QuotientGroup.eq_one_iff (N := O) ((y : H) : ↥c.L)).mp h
    · intro hy
      have hy1 : φH (y : H) = 1 :=
        (QuotientGroup.eq_one_iff (N := O) ((y : H) : ↥c.L)).mpr (by simpa using hy)
      apply Subtype.ext
      rw [hf_apply]
      exact hy1
  have hNIP_le_pcore : NIP ≤ CFSG.pCore 2 ↥IP := by
    change NIP ≤ sSup {K : Subgroup ↥IP | K.Normal ∧ IsPGroup 2 K}
    exact le_sSup ⟨hNIPnormal, hNIP2⟩
  have hpcore_le_ker : CFSG.pCore 2 ↥IP ≤ f.ker := by
    have hmap_pcore : (CFSG.pCore 2 ↥IP).map f ≤ CFSG.pCore 2 ↥J := by
      change (CFSG.pCore 2 ↥IP).map f ≤
        sSup {K : Subgroup ↥J | K.Normal ∧ IsPGroup 2 K}
      exact le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal f hf_surj,
        IsPGroup.map CFSG.pCore_isPGroup f⟩
    rw [hpcoreJ] at hmap_pcore
    intro x hx
    have hx1 : f x = 1 := by
      have hxmap : f x ∈ (CFSG.pCore 2 ↥IP).map f := Subgroup.mem_map_of_mem f hx
      have hxbot : f x ∈ (⊥ : Subgroup ↥J) := hmap_pcore hxmap
      simpa using hxbot
    exact MonoidHom.mem_ker.mpr hx1
  have hker : f.ker = CFSG.pCore 2 ↥IP :=
    le_antisymm (hker_eq ▸ hNIP_le_pcore) hpcore_le_ker
  let eP : (↥IP ⧸ CFSG.pCore 2 ↥IP) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj)
  have hPtc : IsTripleCover (↥IP ⧸ CFSG.pCore 2 ↥IP) (alternatingGroup (Fin 6)) :=
    CFSG.RankThree.PartTwo.Sec4.Item426.isTripleCover_of_mulEquiv eP.symm hJtriple
  have hHmapK : H.map c.L.subtype = K := by
    change (K.subgroupOf c.L).map c.L.subtype = K
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact inf_le_left
  have hIPmap : IP.map fG = perfectCoreL c a := by
    change (CFSG.perfectResidual H).map (c.L.subtype.comp H.subtype) = perfectCoreL c a
    have h1 : (CFSG.perfectResidual H).map (c.L.subtype.comp H.subtype) =
        inSubgroup perfectResidual (H.map c.L.subtype) := by
      rw [← Subgroup.map_map, CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_map
        (f := c.L.subtype) (hf := c.L.subtype_injective)]
      rfl
    rw [h1, hHmapK]
  let eIP : ↥IP ≃* ↥(IP.map fG) :=
    IP.equivMapOfInjective fG hfG_inj
  let eQ : (↥IP ⧸ CFSG.Open.pCore 2 ↥IP) ≃*
      (↥(IP.map fG) ⧸ CFSG.Open.pCore 2 ↥(IP.map fG)) :=
    QuotientGroup.congr _ _ eIP (CFSG.pCore_map_iso 2 eIP)
  have eQ' : (↥IP ⧸ CFSG.Open.pCore 2 ↥IP) ≃*
      (↥(perfectCoreL c a) ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a)) := by
    rw [← hIPmap]
    exact eQ
  exact CFSG.RankThree.PartTwo.Sec4.Item426.isTripleCover_of_mulEquiv eQ' hPtc

theorem isPerfect_commutator_of_centralizer_decomp
    {Y : Type*} [Group Y] {x : Y} {C J : Subgroup Y}
    (hC : C = Subgroup.zpowers x ⊔ J) (hJdef : J = ⁅C, C⁆)
    (hxcentC : x ∈ Subgroup.centralizer (C : Set Y)) :
    Group.IsPerfect ↥J := by
  have hJleC : J ≤ C := hJdef ▸ Subgroup.commutator_le_self C
  have hxJ : x ∈ Subgroup.centralizer (J : Set Y) := by
    rw [Subgroup.mem_centralizer_iff] at hxcentC ⊢
    intro j hj
    exact hxcentC j (hJleC hj)
  have hBcentC : Subgroup.zpowers x ≤ Subgroup.centralizer (C : Set Y) :=
    Subgroup.zpowers_le.mpr hxcentC
  have hBcentJ : Subgroup.zpowers x ≤ Subgroup.centralizer (J : Set Y) :=
    Subgroup.zpowers_le.mpr hxJ
  have hBnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set Y) :=
    hBcentJ.trans (Subgroup.centralizer_le_normalizer (J : Set Y))
  have hcomm1 : ⁅J ⊔ Subgroup.zpowers x, C⁆ = ⁅J, C⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := J) (B := Subgroup.zpowers x) (U := C)
      hBnorm hBcentC
  have hcomm2 : ⁅J, C⁆ = ⁅J ⊔ Subgroup.zpowers x, J⁆ := by
    rw [show C = J ⊔ Subgroup.zpowers x by rw [hC, sup_comm]]
    exact Subgroup.commutator_comm (H₁ := J) (H₂ := J ⊔ Subgroup.zpowers x)
  have hcomm3 : ⁅J ⊔ Subgroup.zpowers x, J⁆ = ⁅J, J⁆ :=
    CFSG.commutator_sup_eq_commutator_left (A := J) (B := Subgroup.zpowers x) (U := J)
      hBnorm hBcentJ
  have hJJ : J = ⁅J, J⁆ := by
    calc J = ⁅C, C⁆ := hJdef
      _ = ⁅J ⊔ Subgroup.zpowers x, C⁆ := by rw [hC, sup_comm]
      _ = ⁅J, C⁆ := hcomm1
      _ = ⁅J ⊔ Subgroup.zpowers x, J⁆ := hcomm2
      _ = ⁅J, J⁆ := hcomm3
  exact Subgroup.isPerfect_iff.mpr hJJ.symm

theorem image_not_center_of_not_mem_zSub
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {a : G} (haP : a ∈ P) (haL : a ∈ c.L) (haZ : a ∉ zSub P c.L) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨a, haL⟩ ∉ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let aL : ↥c.L := ⟨a, haL⟩
  let Q : Subgroup G := P ⊓ c.L
  let Z : Subgroup G := zSub P c.L
  let ZL : Subgroup ↥c.L := Z.subgroupOf c.L
  let Zbar : Subgroup c.Lbar := ZL.map π
  have hZQ : ZL ≤ Q.subgroupOf c.L := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hQ3 : IsPGroup 3 (Q.subgroupOf c.L) := by
    change IsPGroup 3 ((P ⊓ c.L).subgroupOf c.L)
    exact (hP.isPGroup.to_le inf_le_left).comap_subtype
  have hZ3 : IsPGroup 3 ZL := hQ3.to_le hZQ
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hQO : Q.subgroupOf c.L ⊓ O = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (Q.subgroupOf c.L) O hQ3 hO2).eq_bot
  have hdisj : ZL ⊓ O = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxQ : x ∈ Q.subgroupOf c.L := hZQ hx.1
    have : x ∈ Q.subgroupOf c.L ⊓ O := ⟨hxQ, hx.2⟩
    rw [hQO] at this
    exact this
  have hZbar_card : Nat.card Zbar = 3 := by
    have hcardZ : Nat.card Z = 3 := c.card_inf_centralizer_of_onan hON hP
    have hcardZL : Nat.card ZL = 3 := by
      rw [← hcardZ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
        exact inf_le_left.trans inf_le_right)).toEquiv
    have hker : ZL ⊓ π.ker = ⊥ := by
      rw [QuotientGroup.ker_mk']
      exact hdisj
    have hmapcard : Nat.card (Subgroup.map π ZL) = Nat.card ZL :=
      CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot π ZL hker
    change Nat.card (Subgroup.map π ZL) = 3
    rw [hmapcard, hcardZL]
  have hZbar_le : Zbar ≤ Subgroup.center c.Lbar := zSub_map_le_center c hON hP
  have hZbar_eq : Zbar = Subgroup.center c.Lbar :=
    Subgroup.eq_of_le_of_card_ge hZbar_le (by rw [hZbar_card, hON.2.1])
  intro hxcent
  have hxcent' : π aL ∈ Subgroup.center c.Lbar := by
    simpa [π, aL] using hxcent
  have hxZbar : π aL ∈ Zbar := by
    rw [hZbar_eq]
    exact hxcent'
  obtain ⟨z, hzZL, hz⟩ := Subgroup.mem_map.mp hxZbar
  have hzQ : z ∈ Q.subgroupOf c.L := hZQ hzZL
  have haQ : aL ∈ Q.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr ⟨haP, haL⟩
  have hprodQ : z * aL⁻¹ ∈ Q.subgroupOf c.L :=
    (Q.subgroupOf c.L).mul_mem hzQ ((Q.subgroupOf c.L).inv_mem haQ)
  have hprodO : z * aL⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff (N := O)]
    change π z * (π aL)⁻¹ = 1
    rw [hz]
    group
  have hbot : z * aL⁻¹ ∈ (⊥ : Subgroup ↥c.L) := by
    rw [← hQO]
    exact ⟨hprodQ, hprodO⟩
  have hza : z = aL := by
    have h1 : z * aL⁻¹ = 1 := by simpa using hbot
    calc z = z * aL⁻¹ * aL := by group
      _ = 1 * aL := by rw [h1]
      _ = aL := one_mul aL
  have haz : a ∈ Z := by
    exact Subgroup.mem_subgroupOf.mp (by simpa [hza] using hzZL)
  exact haZ haz

theorem zSub_le_perfectCoreL
    (c : Ctx82E3 D) {P A : Subgroup G} {a : G}
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A)
    (haZ : a ∉ zSub P c.L) :
    zSub P c.L ≤ perfectCoreL c a := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let aL : ↥c.L := ⟨a, (Subgroup.mem_inf.mp (hAPL ha)).2⟩
  let x : c.Lbar := π aL
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer ({a} : Set G)
  let H : Subgroup ↥c.L := K.subgroupOf c.L
  let C : Subgroup c.Lbar := Subgroup.centralizer ({x} : Set c.Lbar)
  have hK2 := K2ONanCentralizer_holds (Y := c.Lbar) hON x
    (by
      have ha3 : a ^ 3 = 1 := hA.2 a ha
      have ha1 : a ≠ 1 := by
        intro h1
        exact haZ (by rw [h1]; exact Subgroup.one_mem _)
      have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
      have haLord : orderOf aL = 3 := by simpa [aL] using haord
      have hxne : x ≠ 1 := by
        intro hx1
        have hxO : aL ∈ O := (QuotientGroup.eq_one_iff (N := O) aL).mp (by simpa [x, π] using hx1)
        have h3dvd : 3 ∣ Nat.card O := by
          have h := Subgroup.orderOf_dvd_natCard O hxO
          rwa [haLord] at h
        exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
          CFSG.pCore_isPGroup Nat.prime_three (by norm_num) h3dvd
      have hxdvd : orderOf x ∣ 3 := by
        have h := orderOf_map_dvd π aL
        rwa [haLord] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hxdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h3)
    (image_not_center_of_not_mem_zSub c hON hP (Subgroup.mem_inf.mp (hAPL ha)).1
      (Subgroup.mem_inf.mp (hAPL ha)).2 haZ)
  dsimp only at hK2
  obtain ⟨-, hZY, -, hCeq, hAlt⟩ := hK2
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hCeq' : C = Subgroup.zpowers x ⊔ J := hCeq
  have hxcentC : x ∈ Subgroup.centralizer (C : Set c.Lbar) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hJperf : Group.IsPerfect ↥J :=
    isPerfect_commutator_of_centralizer_decomp hCeq' rfl hxcentC
  have hJleC : J ≤ C := Subgroup.commutator_le_self C
  have hperfJC : Group.IsPerfect ↥(J.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJleC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJleC).symm.surjective
  have hJ_le_perf : J ≤ (CFSG.perfectResidual ↥C).map C.subtype := by
    have hJC : J.subgroupOf C ≤ CFSG.perfectResidual ↥C :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
        (J.subgroupOf C) hperfJC
    have hmap := Subgroup.map_mono (f := C.subtype) hJC
    rwa [Subgroup.map_subgroupOf_eq_of_le hJleC] at hmap
  have haL3 : aL ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hA.2 a ha
  have ha1L : aL ≠ 1 := by
    intro h1
    apply haZ
    have ha1 : a = 1 := by
      simpa [aL] using (Subtype.ext_iff.mp h1)
    rw [ha1]
    exact Subgroup.one_mem _
  have haLord : orderOf aL = 3 := orderOf_eq_prime haL3 ha1L
  have hzp3 : IsPGroup 3 ↥(Subgroup.zpowers aL) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, haLord]
    norm_num
  letI : Fact (IsPGroup 3 ↥(Subgroup.zpowers aL)) := ⟨hzp3⟩
  have hcopO : Nat.Coprime 3 (Nat.card O) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
        CFSG.pCore_isPGroup Nat.prime_three (by norm_num))
  have hcentral :=
    CFSG.centralizer_map_quotient_eq_map_centralizer (p := 3)
      (T := Subgroup.zpowers aL) (M := O) (by infer_instance) hcopO
  have hzp_map : Subgroup.map π (Subgroup.zpowers aL) = Subgroup.zpowers x := by
    simpa [x, π] using MonoidHom.map_zpowers π aL
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers aL : Set ↥c.L) = H := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext y
    simp [H, K, aL, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcent_zpx : Subgroup.centralizer (Subgroup.zpowers x : Set c.Lbar) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHmapC : H.map π = C := by
    have h := hcentral
    dsimp only at h
    rw [hzp_map, hcent_zp, hcent_zpx] at h
    exact h.symm
  let φH : ↥H →* c.Lbar := π.comp H.subtype
  have hφH_range : φH.range = C := by
    rw [show φH = π.comp H.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hHmapC
  let φC : ↥H →* ↥C := φH.codRestrict C (fun y => by
    have hy : φH y ∈ φH.range := ⟨y, rfl⟩
    rwa [hφH_range] at hy)
  have hO2H : IsPGroup 2 (O.subgroupOf H) := CFSG.pCore_isPGroup.comap_subtype
  have hφC_ker_le : φC.ker ≤ O.subgroupOf H := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy1 : φH y = 1 := by
      have h := congrArg Subtype.val hy
      simpa [φC] using h
    exact (QuotientGroup.eq_one_iff (N := O) (H.subtype y)).mp hy1
  have hφC_ker2 : IsPGroup 2 φC.ker := hO2H.to_le hφC_ker_le
  intro z hz
  have hzQ : z ∈ P ⊓ c.L := hz.1
  have hzL : z ∈ c.L := hzQ.2
  let zL : ↥c.L := ⟨z, hzL⟩
  have hzodd : Odd (orderOf zL) := by
    have hzP : z ∈ P := hzQ.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) ⟨z, hzP⟩
    have hk' : orderOf z = 3 ^ k := by simpa using hk
    have hzord : orderOf zL = orderOf z := by simp [zL]
    rw [hzord, hk']
    exact (show Odd 3 by norm_num).pow
  have hzH : zL ∈ H := by
    change (zL : ↥c.L) ∈ K.subgroupOf c.L
    rw [Subgroup.mem_subgroupOf]
    change (zL : G) ∈ c.L ⊓ Subgroup.centralizer ({a} : Set G)
    refine ⟨hzL, ?_⟩
    have hcomm : a * (z : G) = (z : G) * a := Subgroup.mem_centralizer_iff.mp hz.2 a (hAPL ha)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  let zH : ↥H := ⟨zL, hzH⟩
  have hzoddH : Odd (orderOf zH) := by simpa [zH] using hzodd
  have hzCenter : (zL : c.Lbar) ∈ Subgroup.center c.Lbar := by
    have hzmem : zL ∈ (zSub P c.L).subgroupOf c.L := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    exact zSub_map_le_center c hON hP (Subgroup.mem_map_of_mem π hzmem)
  have hφC_surj : Function.Surjective φC := by
    intro y
    have hy : (y : c.Lbar) ∈ φH.range := by
      rw [hφH_range]
      exact y.2
    obtain ⟨h, hh⟩ := hy
    exact ⟨h, Subtype.ext hh⟩
  have hzPerfC : φC zH ∈ CFSG.perfectResidual ↥C := by
    have hzCenter' : π zL ∈ Subgroup.center c.Lbar := by simpa [π] using hzCenter
    have hzJ : (φC zH : c.Lbar) ∈ J := hZY (by simpa [φC, φH, zH, π] using hzCenter')
    have hzmap : (φC zH : c.Lbar) ∈ (CFSG.perfectResidual ↥C).map C.subtype :=
      hJ_le_perf hzJ
    obtain ⟨p, hp, hpv⟩ := Subgroup.mem_map.mp hzmap
    have hpeq : p = φC zH := Subtype.ext hpv
    simpa [hpeq] using hp
  have hzIP : zH ∈ CFSG.perfectResidual H :=
    mem_perfectResidual_of_odd_order_of_map_mem φC hφC_surj hφC_ker2 hzoddH hzPerfC
  let fG : ↥H →* G := c.L.subtype.comp H.subtype
  have hIPmap : (CFSG.perfectResidual H).map fG = perfectCoreL c a := by
    have hHmapK : H.map c.L.subtype = K := by
      change (K.subgroupOf c.L).map c.L.subtype = K
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
      exact inf_le_left
    have h1 : (CFSG.perfectResidual H).map (c.L.subtype.comp H.subtype) =
        inSubgroup perfectResidual (H.map c.L.subtype) := by
      rw [← Subgroup.map_map,
        CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_map
          (f := c.L.subtype) (hf := c.L.subtype_injective)]
      rfl
    rw [h1, hHmapK]
  have hzI : z ∈ (CFSG.perfectResidual H).map fG := by
    have h := Subgroup.mem_map_of_mem fG hzIP
    simpa [fG, zH, zL] using h
  rwa [hIPmap] at hzI

theorem f9PerfectCore_holds
    (c : Ctx82E3 D) {P A : Subgroup G} {a : G}
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hZA : zSub P c.L ≤ A) (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A)
    (haZ : a ∉ zSub P c.L) :
    F9PerfectCore c P a := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  have haPL : a ∈ P ⊓ c.L := hAPL ha
  have haP : a ∈ P := haPL.1
  have haL : a ∈ c.L := haPL.2
  let aL : ↥c.L := ⟨a, haL⟩
  let x : c.Lbar := π aL
  have ha3 : a ^ 3 = 1 := hA.2 a ha
  have ha1 : a ≠ 1 := by
    intro h1
    exact haZ (by rw [h1]; exact Subgroup.one_mem _)
  have ha_order : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have haL_order : orderOf aL = 3 := by simpa [aL] using ha_order
  have hx_ne : x ≠ 1 := by
    intro hx1
    have hxO : aL ∈ O := (QuotientGroup.eq_one_iff (N := O) aL).mp (by simpa [x, π] using hx1)
    have h3dvd : 3 ∣ Nat.card O := by
      have h := Subgroup.orderOf_dvd_natCard O hxO
      rwa [haL_order] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      CFSG.pCore_isPGroup Nat.prime_three (by norm_num) h3dvd
  have hx3 : orderOf x = 3 := by
    have hxdvd : orderOf x ∣ 3 := by
      have h := orderOf_map_dvd π aL
      rwa [haL_order] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hxdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hxZ : x ∉ Subgroup.center c.Lbar :=
    image_not_center_of_not_mem_zSub c hON hP haP haL haZ
  have hTC := tripleCover_perfectCoreL c hA ha haL hx3 hxZ hON
  have hZ := zSub_le_perfectCoreL c hON hP hA hAPL ha haZ
  refine ⟨hTC, hZ, ?_⟩
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have hvI : v ∈ perfectCoreL c a := hZ hv
  have huL : u ∈ c.L := (Subgroup.mem_inf.mp (perfectCoreL_le c a hu)).1
  have hvL : v ∈ c.L := (Subgroup.mem_inf.mp (perfectCoreL_le c a hvI)).1
  have hcommI : ⁅u, v⁆ ∈ perfectCoreL c a := by
    rw [commutatorElement_def]
    exact (perfectCoreL c a).mul_mem
      ((perfectCoreL c a).mul_mem ((perfectCoreL c a).mul_mem hu hvI)
        ((perfectCoreL c a).inv_mem hu)) ((perfectCoreL c a).inv_mem hvI)
  have hcommL : ⁅u, v⁆ ∈ c.L := (Subgroup.mem_inf.mp (perfectCoreL_le c a hcommI)).1
  have hvcent : π ⟨v, hvL⟩ ∈ Subgroup.center c.Lbar :=
    zSub_map_le_center c hON hP (Subgroup.mem_map_of_mem π (by
      rw [Subgroup.mem_subgroupOf]; exact hv))
  have hker : π ⟨⁅u, v⁆, hcommL⟩ = 1 := by
    change π (⁅(⟨u, huL⟩ : ↥c.L), (⟨v, hvL⟩ : ↥c.L)⁆) = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp hvcent (π (⟨u, huL⟩ : ↥c.L)))
  have hcommO' : (⟨⁅u, v⁆, hcommL⟩ : ↥c.L) ∈ O :=
    (QuotientGroup.eq_one_iff (N := O) _).mp hker
  have hcommO : ⁅u, v⁆ ∈ CFSG.Open.pCoreOf 2 c.L := ⟨_, hcommO', rfl⟩
  let I := perfectCoreL c a
  let N : Subgroup G := I ⊓ CFSG.Open.pCoreOf 2 c.L
  have hNI : N ≤ I := inf_le_left
  have hN2 : IsPGroup 2 N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le inf_le_right
  have hNnormal : (N.subgroupOf I).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hyL : ((y : ↥I) : G) ∈ c.L := (Subgroup.mem_inf.mp (perfectCoreL_le c a y.2)).1
    refine ⟨I.mul_mem (I.mul_mem y.2 hx.1) (I.inv_mem y.2), ?_⟩
    have hyn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L hyL
    exact (Subgroup.mem_normalizer_iff.mp hyn ((x : ↥I) : G)).mp hx.2
  have hNsub2 : IsPGroup 2 (N.subgroupOf I) := hN2.comap_subtype
  have hNsub_le : N.subgroupOf I ≤ CFSG.pCore 2 ↥I := by
    change N.subgroupOf I ≤ sSup {K : Subgroup ↥I | K.Normal ∧ IsPGroup 2 K}
    exact le_sSup ⟨hNnormal, hNsub2⟩
  have hN_le_pcore : N ≤ CFSG.Open.pCoreOf 2 I := by
    rw [CFSG.Open.pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hNI]
    exact Subgroup.map_mono hNsub_le
  exact hN_le_pcore ⟨hcommI, hcommO⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
