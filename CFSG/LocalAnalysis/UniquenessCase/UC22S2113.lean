module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UCFront10Alt
import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AltThreeRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.GroupTheory.PermutingProducts
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2113_inducedBarInfAutHom_of_mem {L : Subgroup G} {x : G} (hx : x ∈ L) :
    inducedBarInfAutHom L ⟨x, le_normalizer hx⟩ = MulAut.conj ((⟨x, hx⟩ : ↥L) : BarInf L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {b : G} (hb : b ∈ normalizer (L : Set G))
    (h1 : inducedBarInfAutHom L ⟨b, hb⟩ = 1) : CentralizesBar b L := by
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let c : ↥L →* ↥L := (L.normalizerMonoidHom ⟨b, hb⟩).toMonoidHom
  have hc : CFSG.pCore 2 ↥L ≤ (CFSG.pCore 2 ↥L).comap c :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance (L.normalizerMonoidHom ⟨b, hb⟩)
  let σ : Bar2 L →* Bar2 L := QuotientGroup.map _ _ c hc
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq.1
  have hR : ∀ l : ↥L, l⁻¹ * c l ∈ CFSG.solvableRadical ↥L := by
    intro l
    have h : ((c l : ↥L) : BarInf L) = (l : BarInf L) :=
      congrArg (fun φ : MulAut (BarInf L) => φ (l : BarInf L)) h1
    rw [QuotientGroup.eq] at h
    simpa using (CFSG.solvableRadical ↥L).inv_mem h
  have hcent : ∀ x : Bar2 L, x⁻¹ * σ x ∈ center (Bar2 L) := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← uc22p21k_map_solvableRadical_eq_center hq]
    exact ⟨l⁻¹ * c l, hR l, rfl⟩
  have hσ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ hcent
  refine ⟨hb, fun l hl => ?_⟩
  have h : ((c ⟨l, hl⟩ : ↥L) : Bar2 L) = ((⟨l, hl⟩ : ↥L) : Bar2 L) :=
    congrArg (fun f : Bar2 L →* Bar2 L => f ((⟨l, hl⟩ : ↥L) : Bar2 L)) hσ
  rw [QuotientGroup.eq] at h
  have hN : c ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L)⁻¹ ∈ CFSG.pCore 2 ↥L := by
    simpa using (CFSG.pCore 2 ↥L).inv_mem (Subgroup.Normal.mem_comm inferInstance h)
  exact ⟨_, hN, rfl⟩

theorem uc22s2113_five_le_of_isAlt {M L : Subgroup G} (hL : L ∈ calC M) {m : ℕ}
    (e : BarInf L ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra hm
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.2.1
  obtain ⟨e'⟩ := uc22p21k_barInf_equiv hL.2.2
  haveI : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hL.2.2.2
  haveI : Nontrivial (BarInf L) := e'.surjective.nontrivial
  haveI : Group.IsSolvable (alternatingGroup (Fin m)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact Group.IsPerfect.not_isSolvable (G := BarInf L)
    (solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem uc22s2113_not_thin8_of_isAlt {L : Subgroup G} {m : ℕ} (hm : 6 ≤ m)
    (e : BarInf L ≃* alternatingGroup (Fin m)) : ¬ F08.Thin8 L := by
  intro hthin
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_alternating hm
  have h3 := CFSG.GroupTheory.two_le_pRank_of_quotient (CFSG.solvableRadical ↥L)
    Nat.prime_three (by norm_num) h2
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
  have h1 := hthin 3 Nat.prime_three (by norm_num)
  omega

theorem uc22s2113_isPGroup_three_of_isAlt {L B T : Subgroup G} {m : ℕ} (hm : 5 ≤ m)
    (e : BarInf L ≃* alternatingGroup (Fin m))
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hT : IsPGroup 2 ↥T)
    (hBN : B ≤ normalizer (L : Set G)) (hBT : Permutes B T) (hBab : IsMulCommutative ↥B)
    (hBo : Odd (Nat.card ↥B))
    (hfaith : ∀ b (hb : b ∈ B), inducedBarInfAutHom L ⟨b, hBN hb⟩ = 1 → b = 1) :
    IsPGroup 3 ↥B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set φ := inducedBarInfAutHom L with hφdef
  set X : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hXdef
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : ∀ w : BarInf L, w * z = z * w := by
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    have hc : e z ∈ center (alternatingGroup (Fin m)) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hzc w']
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
      mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  let eX : BarInf L ≃* ↥X := MonoidHom.ofInjective hinj
  haveI : Finite ↥X := Finite.of_equiv _ eX.toEquiv
  set Bφ : Subgroup (MulAut (BarInf L)) := (B.subgroupOf N).map φ with hBφdef
  set Sφ : Subgroup (MulAut (BarInf L)) := ((T ⊓ N).subgroupOf N).map φ with hSφdef
  have hBX : Bφ ≤ X := by
    rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
    have hbB : b ∈ B := hb
    have hodd : Odd (orderOf (φ ⟨b, hbN⟩)) := by
      refine Odd.of_dvd_nat (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hbB)) ?_
      have h := orderOf_map_dvd φ ⟨b, hbN⟩
      rwa [Subgroup.orderOf_mk] at h
    obtain ⟨x, hx⟩ := F10.exists_conj_of_odd_orderOf_alt hm e _ hodd
    exact ⟨x, hx.symm⟩
  have hperm : (Bφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Bφ := by
    have h1 := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hBT.symm hBN
    exact CFSG.GroupTheory.map_permutes_map φ
      (CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBN inf_le_right h1.symm)
  have hpermX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hBX).symm
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf ((Sφ ⊓ X).subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hS2 : IsPGroup 2 ↥Sφ :=
        ((hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm).map φ
      exact (hS2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    · let f : ↥L →* ↥X := (MulAut.conj : BarInf L →* MulAut (BarInf L)).rangeRestrict.comp
        (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      have hf : Function.Surjective f :=
        (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)
      have hle : ((T ⊓ L).subgroupOf L).map f ≤ (Sφ ⊓ X).subgroupOf X := by
        rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
        have htT : t ∈ T := (mem_inf.mp (show t ∈ T ⊓ L from ht)).1
        rw [mem_subgroupOf]
        refine ⟨⟨⟨t, le_normalizer htL⟩, ?_, uc22s2113_inducedBarInfAutHom_of_mem htL⟩,
          (f ⟨t, htL⟩).2⟩
        show t ∈ T ⊓ N
        exact mem_inf.mpr ⟨htT, le_normalizer htL⟩
      have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
      change ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact fun h2 => hidx
        (h2.trans ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)))
  have eBX : ↥(Bφ.subgroupOf X) ≃* ↥Bφ := subgroupOfEquivOfLe hBX
  haveI : IsMulCommutative ↥(B.subgroupOf N) := inferInstance
  haveI : IsMulCommutative ↥Bφ := Subgroup.map_isMulCommutative _ _
  have hBn : Group.IsNilpotent ↥(Bφ.subgroupOf X) := Group.nilpotent_of_mulEquiv eBX.symm
  have hBo' : Odd (Nat.card ↥(Bφ.subgroupOf X)) := by
    rw [Nat.card_congr eBX.toEquiv]
    refine Odd.of_dvd_nat hBo ?_
    have h := Subgroup.card_map_dvd (B.subgroupOf N) φ
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv] at h
  have h3 : IsPGroup 3 ↥Bφ :=
    (F10.isPGroup_three_of_permutes_alt hm (eX.symm.trans e) hS hBn hBo' hpermX).of_equiv eBX
  rintro ⟨b, hb⟩
  obtain ⟨k, hk⟩ := h3 ⟨φ ⟨b, hBN hb⟩, ⟨b, hBN hb⟩, hb, rfl⟩
  refine ⟨k, Subtype.ext (hfaith _ (B.pow_mem hb _) ?_)⟩
  have hk' : (φ ⟨b, hBN hb⟩) ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  rw [← map_pow] at hk'
  exact hk'

theorem s21_13_of {D : Data G} {Ch : Choice2011 G} (h3 : S21_3 D Ch) (h5 : S21_5 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) : S21_13 D Ch := by
  intro hH c L hL m ⟨e⟩
  have hm5 := uc22s2113_five_le_of_isAlt hL e
  by_contra hm
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hBN : c.B0 ≤ normalizer (L : Set G) := h5 hH c₀ L hL
  have hthin := uc22s2113_not_thin8_of_isAlt (by omega) e
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBo : Odd (Nat.card ↥c.B0) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 2 h
    have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 b.2
    rw [Subgroup.orderOf_coe, hb] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hB3 := uc22s2113_isPGroup_three_of_isAlt hm5 e (uc22p2214_isSylowOf_inf D.sylowM hL.1)
    D.sylowM.isPGroup hBN hBT hBab hBo fun b hb h1 => by
      by_contra hb1
      exact hthin (h3 hH c₀ L hL ⟨b, hb, hb1,
        uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN hb) h1⟩)
  obtain ⟨p, hp, hpd, hp3⟩ := uc22p20o_prime_sub_one_ne_three (hn3 hH c)
  have hpB : p ∣ Nat.card ↥c.B0 := by
    have hpi : p ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨hp, hpd⟩
    exact hpi.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hB3.exists_card_eq
  rw [hk] at hpB
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hpB))

end CFSG.LocalAnalysis.UniquenessCase.UC22
