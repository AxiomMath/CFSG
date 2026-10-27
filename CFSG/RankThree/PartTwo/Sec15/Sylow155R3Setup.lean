module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofRead
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.KFacts.KS44Transport
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_res3Ctx
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : (omegaA A).ncard = 3) : ∃ (d : G) (K : Subgroup G), Res3Ctx A c L d K := by
  have h := hR.toSec14Std
  have hD := hR.toSec13Data
  have hA := h.isE27'
  obtain ⟨d, hdA, hd1, hdZ⟩ : ∃ d ∈ A, d ≠ 1 ∧ IsZCentral L d := by
    obtain ⟨d, hdA, hd1, hdL, S, hdS, hSd⟩ := exists_three_central_of_j2 hD hJ
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    obtain ⟨hS, hZ⟩ :=
      center_sylow_eq_zpowers_of_quot_j2 Sec4.Sporadic.rank3II_4_15 hθ3 hJ hdL hd1 S hdS hSd
    exact ⟨d, hdA, hd1, _, hS, hZ⟩
  have hcd : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Proof15Res11.isLBConfig_of hR hJ hdZ
  obtain ⟨hdL, -⟩ := hcd.2.2.2.2
  have hBcd : IsHyperplane A (Subgroup.closure {c, d}) :=
    Proof15Res11.isHyperplane_of hR hJ hdA hd1 hdL
  obtain ⟨-, -, -, -, -, -, -, -, -, hdc⟩ := Ronan152SL25.lbConfig_facts hA hBcd hcd
  have hdB' : d ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hLK⟩ := Desc143X.exists_mem_le_residual h48 h hBcd hcd hdB' hd1 hdc
  obtain ⟨hcL, hAL9, hAc⟩ := j2_point_facts hD hJ
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hLK with
    ⟨-, -, hΩ1⟩ | ⟨hKX, hT, hNA, hP, hP9, hPS, hΩ⟩ | ⟨-, -, -, h12⟩
  · rw [hΩ1, Set.ncard_singleton] at h3
    omega
  · rcases hΩ with ⟨hΩ, -⟩ | ⟨-, -, -, -, a, ha, had, hΩa, h6, La, hLa, hJa⟩
    · refine ⟨d, K, ?_⟩
      exact
        { R := hR, J2 := hJ, ncard := h3, d_mem := hdA, d_ne := hd1, d_Z := hdZ,
          d_L := hdL, c_notMem := hcL, AL_card := hAL9, A_eq := hAc,
          AL_le := Item148HJ.inf_le_residual h hBcd hcd, K_mem := hK, K_le := hLK,
          K_eq := hKX, K_cover := hT, NA := hNA, Pstar_elem := hP, Pstar_card := hP9,
          Pstar_syl := hPS, omega := hΩ }
    · omega
  · omega

section Quot

private abbrev mk3 (H : Type) [Group H] : H →* H ⧸ CFSG.pPrimeCore 3 H :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 H)

private theorem mk3_eq_one_iff {H : Type} [Group H] (x : H) :
    mk3 H x = 1 ↔ x ∈ CFSG.pPrimeCore 3 H :=
  QuotientGroup.eq_one_iff x

private theorem not_dvd_card_pPrimeCore (H : Type) [Group H] [Finite H] :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

private theorem eq_of_mk'_eq_of_pow_three {H : Type} [Group H] {N : Subgroup H} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {E : Subgroup H} (hE : ∀ e ∈ E, e ^ 3 = 1) {a b : H} (ha : a ∈ E)
    (hb : b ∈ E) (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  have hu : a⁻¹ * b ∈ N := (QuotientGroup.eq (s := N)).mp hab
  have hu3 : (a⁻¹ * b) ^ 3 = 1 := hE _ (E.mul_mem (E.inv_mem ha) hb)
  have hdvd1 : orderOf (a⁻¹ * b) ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hdvd2 : orderOf (a⁻¹ * b) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hu
  have hg : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  have h1 := Nat.dvd_gcd hdvd1 hdvd2
  rw [Nat.Coprime.gcd_eq_one hg] at h1
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

private theorem card_map_eq_of_injOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {E : Subgroup X} (hf : ∀ s ∈ E, ∀ t ∈ E, f s = f t → s = t) :
    Nat.card (E.map f) = Nat.card E := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hf]
  rfl

variable {H : Type} [Group H] [Finite H]

private theorem not_le_pPrimeCore_of_isTripleCover {K' : Subgroup H}
    (hT : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6))) :
    ¬ K' ≤ CFSG.pPrimeCore 3 H := by
  intro hle
  have h1 : Nat.card ↥K' ∣ Nat.card ↥(CFSG.pPrimeCore 3 H) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (Subgroup.center (↥K' ⧸ aschbacherSolvableCore 3 ↥K')) ∣
      Nat.card (↥K' ⧸ aschbacherSolvableCore 3 ↥K') := Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (↥K' ⧸ aschbacherSolvableCore 3 ↥K') ∣ Nat.card ↥K' :=
    Subgroup.card_quotient_dvd_card _
  rw [hT.1] at h2
  exact not_dvd_card_pPrimeCore H (h2.trans (h3.trans h1))

private theorem res3QComp_of_pPrimeCore {A' B' K' : Subgroup H} {c' d' : H}
    (hK' : K' ∈ thetaComponents 3 H)
    (hT : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)))
    (hA3 : ∀ a ∈ A', a ^ 3 = 1) (hAB : A' = Subgroup.zpowers c' ⊔ B') (hdB : d' ∈ B')
    (hd1 : d' ≠ 1) (hdZ : ∀ x : H, d' * x = x * d') (hB9 : Nat.card B' = 9) (hBK : B' ≤ K')
    (hcK : ∀ y ∈ K', mk3 H y * mk3 H c' = mk3 H c' * mk3 H y)
    (hcd : c' ∉ Subgroup.zpowers d') :
    Res3QComp (mk3 H c') (mk3 H d') (A'.map (mk3 H)) (B'.map (mk3 H)) (K'.map (mk3 H)) := by
  have hN3 := not_dvd_card_pPrimeCore H
  have hBA : B' ≤ A' := by rw [hAB]; exact le_sup_right
  have hcA : c' ∈ A' := by rw [hAB]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c')
  have hdA : d' ∈ A' := hBA hdB
  have hinj : ∀ a ∈ A', ∀ b ∈ A', mk3 H a = mk3 H b → a = b :=
    fun a ha b hb hab => eq_of_mk'_eq_of_pow_three hN3 hA3 ha hb hab
  have hKR : ¬ K' ≤ CFSG.pPrimeCore 3 H := not_le_pPrimeCore_of_isTripleCover hT
  have hcomp : IsComponent (K'.map (mk3 H)) := Y4Core.isComponent_map_mk' hK' hKR
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map (mk3 H) K' (aschbacherSolvableCore 3 ↥K')
    fun l => by
      rw [← Y4Core.subgroupOf_pPrimeCore_eq_theta hK' hKR, Subgroup.mem_subgroupOf]
      exact (mk3_eq_one_iff (l : H)).symm
  have hTbar : Sec4.IsTripleCover ↥(K'.map (mk3 H)) (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr η hT
  have hdbZ : ∀ q : H ⧸ CFSG.pPrimeCore 3 H, mk3 H d' * q = q * mk3 H d' := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 H) q
    have h1 := congrArg (mk3 H) (hdZ x)
    rwa [map_mul, map_mul] at h1
  have hdb3 : mk3 H d' ^ 3 = 1 := by rw [← map_pow, hA3 d' hdA, map_one]
  have hdb1 : mk3 H d' ≠ 1 := fun h1 =>
    hd1 (hinj d' hdA 1 A'.one_mem (by rw [h1, map_one]))
  have hdbord : orderOf (mk3 H d') = 3 := orderOf_eq_prime hdb3 hdb1
  have hdbK : mk3 H d' ∈ K'.map (mk3 H) := Subgroup.mem_map_of_mem _ (hBK hdB)
  have hcen : (Subgroup.center ↥(K'.map (mk3 H))).map (K'.map (mk3 H)).subtype =
      Subgroup.zpowers (mk3 H d') := by
    have hcard : Nat.card ((Subgroup.center ↥(K'.map (mk3 H))).map (K'.map (mk3 H)).subtype) =
        3 := by
      rw [Subgroup.card_map_of_injective (K'.map (mk3 H)).subtype_injective]
      exact hTbar.1
    have hle : Subgroup.zpowers (mk3 H d') ≤
        (Subgroup.center ↥(K'.map (mk3 H))).map (K'.map (mk3 H)).subtype := by
      rw [Subgroup.zpowers_le]
      exact ⟨⟨mk3 H d', hdbK⟩,
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hdbZ g).symm, rfl⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hdbord])).symm
  refine
    { K_quasi := hcomp.1, K_cover := hTbar, K_subnormal := hcomp.2, K_center := hcen
      d_center := Subgroup.mem_center_iff.mpr fun q => (hdbZ q).symm
      c_pow := by rw [← map_pow, hA3 c' hcA, map_one]
      c_cent := ?_, c_notMem := ?_, B₀_le := Subgroup.map_mono hBK
      B₀_card := ?_, B₀_pow := ?_, d_mem := Subgroup.mem_map_of_mem _ hdB, A_eq := ?_ }
  ·
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact hcK y hy
  ·
    intro hcK'
    have hcZ : mk3 H c' ∈
        (Subgroup.center ↥(K'.map (mk3 H))).map (K'.map (mk3 H)).subtype := by
      refine ⟨⟨mk3 H c', hcK'⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
      obtain ⟨y, hy, hyg⟩ := g.2
      have h1 := hcK y hy
      rw [hyg] at h1
      exact Subtype.ext h1
    rw [hcen] at hcZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcZ
    have hdk : d' ^ k ∈ A' := zpow_mem hdA k
    apply hcd
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, hinj _ hdk c' hcA (by rw [map_zpow]; exact hk)⟩
  · rw [card_map_eq_of_injOn (mk3 H) fun a ha b hb hab => hinj a (hBA ha) b (hBA hb) hab, hB9]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hA3 y (hBA hy), map_one]
  · rw [hAB, Subgroup.map_sup, MonoidHom.map_zpowers, sup_comm]

end Quot

namespace Res3Ctx

variable {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}

theorem res3QComp (h : Res3Ctx A c L d K) :
    Res3QComp (res3Pt d c h.c_mem_C) (res3Pt d d h.d_mem_C) (res3Img d A) (res3Img d (A ⊓ L))
      (res3Img d K) := by
  have hD := h.R.toSec13Data
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hD.isElemAbelian.2
  have hdC : d ∈ res3C d := h.d_mem_C
  have hcC : c ∈ res3C d := h.c_mem_C
  have hALC : A ⊓ L ≤ res3C d := inf_le_left.trans h.le_C
  obtain ⟨K', hK', hKeq⟩ := h.K_mem
  have hKeq' : K = K'.map (res3C d).subtype := hKeq.symm
  subst hKeq'
  have hT' : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr
      (KFacts.thetaQuotEquivOfMap (res3C d).subtype K'
        (KFacts.thetaQuotMap_iff_of_injective (res3C d).subtype Subtype.val_injective K')).symm
      h.K_cover
  have hKbar : res3Img d (K'.map (res3C d).subtype) = K'.map (res3Proj d) := by
    show ((K'.map (res3C d).subtype).subgroupOf (res3C d)).map (res3Proj d) = _
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (res3C d).subtype_injective]
  have hzp : (Subgroup.zpowers c).subgroupOf (res3C d) =
      Subgroup.zpowers (⟨c, hcC⟩ : ↥(res3C d)) := by
    apply Subgroup.map_injective (res3C d).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers,
      inf_eq_left.mpr (Subgroup.zpowers_le.mpr hcC)]
    rfl
  have hAB : A.subgroupOf (res3C d) = Subgroup.zpowers (⟨c, hcC⟩ : ↥(res3C d)) ⊔
      (A ⊓ L).subgroupOf (res3C d) := by
    rw [← hzp, ← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hcC) hALC, ← h.A_eq]
  have hALK : A ⊓ L ≤ K'.map (res3C d).subtype := h.AL_le.trans h.K_le
  have hBK : (A ⊓ L).subgroupOf (res3C d) ≤ K' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hALK (Subgroup.mem_subgroupOf.mp hx)
    obtain rfl : y = x := Subtype.ext hyx
    exact hy
  have hB9 : Nat.card ↥((A ⊓ L).subgroupOf (res3C d)) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALC).toEquiv]
    exact h.AL_card
  have hcd : (⟨c, hcC⟩ : ↥(res3C d)) ∉ Subgroup.zpowers (⟨d, hdC⟩ : ↥(res3C d)) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : d ^ k = c := by simpa using congrArg Subtype.val hk
    apply h.c_notMem
    rw [← hk']
    exact zpow_mem h.d_L k
  have hcK : ∀ y ∈ K', mk3 (res3C d) y * mk3 (res3C d) ⟨c, hcC⟩ =
      mk3 (res3C d) ⟨c, hcC⟩ * mk3 (res3C d) y := by
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup ↥(res3C d), ∀ y : ↥(res3C d), y ∈ S₀ ↔
        mk3 (res3C d) y * mk3 (res3C d) ⟨c, hcC⟩ = mk3 (res3C d) ⟨c, hcC⟩ * mk3 (res3C d) y :=
      ⟨(Subgroup.centralizer {mk3 (res3C d) ⟨c, hcC⟩}).comap (mk3 (res3C d)),
        fun y => Subgroup.mem_centralizer_singleton_iff⟩
    have hKS : K'.map (res3C d).subtype ≤ S₀.map (res3C d).subtype := by
      refine h.K_eq.le.trans (sup_le ?_ ?_)
      · intro r hr
        have hrL : r ∈ L := Item148HJ.residual_le L d hr
        have hrC : r ∈ res3C d := Item148HJ.residual_le_centralizer_singleton L d hr
        refine ⟨⟨r, hrC⟩, (hS₀ _).mpr ?_, rfl⟩
        have h1 : r * c = c * r :=
          Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hrL)
        have h2 := congrArg (mk3 (res3C d))
          (Subtype.ext h1 : (⟨r, hrC⟩ * ⟨c, hcC⟩ : ↥(res3C d)) = ⟨c, hcC⟩ * ⟨r, hrC⟩)
        rwa [map_mul, map_mul] at h2
      · rintro _ ⟨k, hk, rfl⟩
        obtain ⟨y, hy, hyk⟩ := k.2
        have hyk' : (res3C d).subtype.subgroupMap K' ⟨y, hy⟩ = k := Subtype.ext hyk
        have hθ : (⟨y, hy⟩ : ↥K') ∈ aschbacherSolvableCore 3 ↥K' :=
          (KFacts.thetaQuotMap_iff_of_injective (res3C d).subtype Subtype.val_injective K'
            ⟨y, hy⟩).mp (by rw [hyk']; exact hk)
        have hyN : y ∈ CFSG.pPrimeCore 3 ↥(res3C d) :=
          Subgroup.mem_subgroupOf.mp (Y4Core.theta_le_subgroupOf_pPrimeCore hK' hθ)
        refine ⟨y, (hS₀ y).mpr ?_, hyk⟩
        rw [(mk3_eq_one_iff y).mpr hyN, one_mul, mul_one]
    intro y hy
    obtain ⟨s, hs, hsy⟩ := hKS ⟨y, hy, rfl⟩
    obtain rfl : s = y := Subtype.ext hsy
    exact (hS₀ s).mp hs
  have key := res3QComp_of_pPrimeCore (A' := A.subgroupOf (res3C d))
    (B' := (A ⊓ L).subgroupOf (res3C d)) (c' := ⟨c, hcC⟩) (d' := ⟨d, hdC⟩) hK' hT'
    (fun a ha => Subtype.ext (hA3 a ha)) hAB (Subgroup.mem_subgroupOf.mpr ⟨h.d_mem, h.d_L⟩)
    (fun h1 => h.d_ne (congrArg Subtype.val h1))
    (fun x => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm) hB9 hBK hcK hcd
  rw [hKbar]
  exact key

end Res3Ctx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
