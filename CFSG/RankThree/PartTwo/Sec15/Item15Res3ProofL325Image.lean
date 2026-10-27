module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofL325
import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159W
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec19.Step1913

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KL325ThetaCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (_ : Fact (Nat.Prime 5)),
    Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) →
    ∀ x : X, orderOf x = 3 →
      IsPGroup 2 (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set X))) ∧
        Nat.card (inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({x} : Set X))) = 64

namespace Proof15Res3L325Image

variable {G : Type} [Group G] [Finite G]

theorem map_mk_map_conj_eq {L X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    (((X.map (MulAut.conj x).toMonoidHom) ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      (((X ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hx⟩)).toMonoidHom := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz
    obtain ⟨⟨y, hyX, hyz⟩, -⟩ := hz
    have hyz' : x * y * x⁻¹ = (z : G) := hyz
    have hyL : y ∈ L := by
      have hy : y = x⁻¹ * (z : G) * x⁻¹⁻¹ := by rw [← hyz']; group
      rw [hy]
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem hx) z).mp z.2
    refine ⟨QuotientGroup.mk' _ ⟨y, hyL⟩,
      ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr ⟨hyX, hyL⟩, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk,
      QuotientGroup.mk'_apply]
    congr 1
    exact Subtype.ext hyz'
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    refine ⟨L.normalizerMonoidHom ⟨x, hx⟩ y, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨⟨y, hy.1, rfl⟩, (L.normalizerMonoidHom ⟨x, hx⟩ y).2⟩
    · exact (Sec4.thetaQuotMulAut_mk _ y).symm

theorem le_normalizer_inSubgroup_theta {Γ : Type*} [Group Γ] [Finite Γ] (C : Subgroup Γ) :
    C ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) C : Set Γ) := by
  have : (aschbacherSolvableCore 3 ↥C).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (aschbacherSolvableCore 3 ↥C))

end Proof15Res3L325Image

open Proof15Res3L325Image

theorem step1515L325Image_of
    (h135 : Item135) (h142 : Item142R) (hloc : Claim1411LocalR)
    (hK : KL325ThetaCent) : Step1515L325Image := by
  intro G _ _ A c L h hf5 hL25 hprod T hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hiso : Sec4.IsoLThreePi (↥L ⧸ θ) 5 2 := Or.inl ⟨by norm_num, hL25⟩
  have hL3 : IsLThreePi (↥L ⧸ θ) := ⟨5, 2, hf5, by norm_num, hiso⟩
  have hsimp := Proof1514.isSimpleGroup_of_isoLThreePi h.mem_thetaComponentsAt (by norm_num) hiso
  obtain ⟨-, h9, hAeq⟩ := Proof1515Res.point_facts_of_prod h hsimp hprod
  have hθ : θ = CFSG.pCore 2 ↥L :=
    Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult (h135 G A c L hD h.hypS_or_hypT)
      (Or.inl hL3)
  have hθ2 : IsPGroup 2 θ := by
    rw [hθ]
    exact CFSG.pCore_isPGroup
  obtain ⟨a, haAL, ha1⟩ : ∃ a ∈ A ⊓ L, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : A ⊓ L = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [hbot, Subgroup.card_bot] at h9
    norm_num at h9
  set ab := π ⟨a, haAL.2⟩ with hab
  have ha3 : a ^ 3 = 1 := hD.isElemAbelian.2 a haAL.1
  have hab3 : orderOf ab = 3 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [hab, ← map_pow]
      have : (⟨a, haAL.2⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
      rw [this, map_one]
    ·
      have haθ : (⟨a, haAL.2⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨k, hk⟩ := hθ2 ⟨_, haθ⟩
      have hk' : a ^ 2 ^ k = 1 := by
        have := congrArg (fun t : θ => ((t : ↥L) : G)) hk
        simpa using this
      have hdvd : orderOf a ∣ Nat.gcd (2 ^ k) 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one ha3)
      rw [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at hdvd
      exact ha1 hdvd
  obtain ⟨hRb2, hRb64⟩ := hK _ hf5 hL25 ab hab3
  set Rb := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({ab} : Set (↥L ⧸ θ)))
    with hRbdef
  set R := (Rb.comap π).map L.subtype with hRdef
  have hR2 : IsPGroup 2 R := by
    refine (hRb2.comap_of_ker_isPGroup π ?_).map _
    rw [hπ, QuotientGroup.ker_mk']
    exact hθ2
  have hRL : R ≤ L := Subgroup.map_subtype_le _
  have hAbN : (A.subgroupOf L).map π ≤ Subgroup.normalizer (Rb : Set (↥L ⧸ θ)) := by
    refine le_trans ?_ (le_normalizer_inSubgroup_theta _)
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hab, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hb) haAL.1)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    Proof1515Res.le_normalizer_map_comap_of h hAeq hAbN
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := hRL.trans hD.le_centralizer
  have hRq := Proof15Res3W.mem_scriptQ_of_le_centralizer h142 h hR2 hAR hRc
  have hRH : R ≤ H := hRc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hRmem : R ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨hRq, hRH⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩
  obtain ⟨S₀, hRS₀, hS₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) hRmem
  have hcY : Subgroup.zpowers c ∈ scriptY A := by
    refine ⟨fun htop => ?_,
      hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)⟩
    obtain ⟨u, v, huv⟩ := h.nonabelian
    apply huv
    have hu : u ∈ Subgroup.zpowers c := htop ▸ Subgroup.mem_top u
    have hv : v ∈ Subgroup.zpowers c := htop ▸ Subgroup.mem_top v
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_add, ← zpow_add, add_comm]
  have hc1 : Subgroup.zpowers c ≠ ⊥ := by
    intro h0
    have h3 := hD.card_zpowers
    rw [h0, Subgroup.card_bot] at h3
    norm_num at h3
  have hHY : H ∈ scriptY A := normalizer_mem_scriptY h.isSimpleGroup hcY hc1
  obtain ⟨x, hx, rfl⟩ := (hloc G A c L h).1 H hHY S₀ hS₀ T hT
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L hx.2
  rw [map_mk_map_conj_eq hxL, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hRbS : Rb ≤ ((S₀ ⊓ L).subgroupOf L).map π := by
    have h1 : (R.subgroupOf L).map π = Rb := by
      rw [hRdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ)]
    rw [← h1]
    exact Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
      ⟨hRS₀ (Subgroup.mem_subgroupOf.mp hy), y.2⟩
  rw [← hRb64]
  exact Subgroup.card_dvd_of_le hRbS

theorem step1515LA7L325Gen_of_kfacts
    (h135 : Item135)
    (h142 : Item142R) (h1511 : Item1511R) (hloc : Claim1411LocalR) (hθ : KL325ThetaCent)
    (hK : KL325SubgroupOrder) : Step1515LA7L325Gen :=
  step1515LA7L325Gen_of h135 h142 h1511 (step1515L325Image_of h135 h142 hloc hθ) hK

end CFSG.RankThree.PartTwo.Sec15
