module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanE
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CLink
public import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_ne_zero_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSz X n) : n ≠ 0 := by
  have h3 := (CFSG.LocalAnalysis.WeakClosure81.SevenK.odd_and_three_le_of_isSz
    (uc22r3e5c_quasithin_isSz_of_isSz h)).2
  omega

private theorem uc22r3e5c_cartan_cap_pCore {D : Data G} {L C : Subgroup G}
    (hoddC : Odd (Nat.card C)) :
    C ⊓ pCoreOf 2 (conjClosure D.M L) = ⊥ := by
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (conjClosure D.M L)).exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [ha]
  exact ((Nat.coprime_two_left.mpr hoddC).pow_left a).symm

private theorem uc22r3e5c_card_barImage_cartan {D : Data G} {L : Subgroup G} {C : Subgroup G}
    (hCX : C ≤ conjClosure D.M L)
    (hcap : C ⊓ pCoreOf 2 (conjClosure D.M L) = ⊥) :
    Nat.card ↥(barImage (conjClosure D.M L) C) = Nat.card C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := uc22r3e5c_card_ker_mul_card_map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L)))
    (C.subgroupOf (conjClosure D.M L))
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L))).ker ⊓
      C.subgroupOf (conjClosure D.M L) = ⊥ := by
    rw [QuotientGroup.ker_mk']
    ext z
    constructor
    · intro hz
      obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
      have hzG : (z : G) ∈ C ⊓ pCoreOf 2 (conjClosure D.M L) :=
        ⟨hzC, (CFSG.mem_openPCoreOf_iff (p := 2) (H := conjClosure D.M L) z).mpr hzQ⟩
      rw [hcap] at hzG
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hzG))
    · intro hz
      rw [Subgroup.mem_bot.mp hz]
      exact Subgroup.mem_inf.mpr ⟨(CFSG.pCore 2 ↥(conjClosure D.M L)).one_mem,
        (C.subgroupOf (conjClosure D.M L)).one_mem⟩
  rw [hker, Subgroup.card_bot, one_mul] at h
  exact h.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv)

private theorem uc22r3e5c_cartan_E_le_prod {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) {C : Subgroup G}
    (hCβ : C ≤ conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) :
    (barImage (conjClosure D.M L) C).map e.toMonoidHom ≤
      (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) := by
  have hβbar : (barImage (conjClosure D.M L)
      (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))).map e.toMonoidHom =
      (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) :=
    uc22r3e5c_barImage_beta_eq_prod hL hKC hKne hset hSz heL heK
  exact (Subgroup.map_mono (barImage_mono hCβ)).trans (le_of_eq hβbar)

private theorem uc22r3e5c_cartan_proj_bounds {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n) {C : Subgroup G}
    (hCβ : C ≤ conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))
    (hCbar : Nat.card ↥(barImage (conjClosure D.M L) C) = Nat.card C)
    (hcardC : Nat.card C = (2 ^ n - 1) ^ 2)
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) :
    ∃ (E : Subgroup (Bar2 L × Bar2 K)) (DL : Subgroup (Bar2 L)) (DK : Subgroup (Bar2 K)),
      E = (barImage (conjClosure D.M L) C).map e.toMonoidHom ∧
      DL = E.map (MonoidHom.fst (Bar2 L) (Bar2 K)) ∧
      DK = E.map (MonoidHom.snd (Bar2 L) (Bar2 K)) ∧
      E ≤ (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
        (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) ∧
      DL ≤ Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)) ∧
      DK ≤ Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)) ∧
      E ≤ DL.prod DK ∧ Nat.card ↥E = (2 ^ n - 1) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup (Bar2 L × Bar2 K) := (barImage (conjClosure D.M L) C).map e.toMonoidHom
  let DL : Subgroup (Bar2 L) := E.map (MonoidHom.fst (Bar2 L) (Bar2 K))
  let DK : Subgroup (Bar2 K) := E.map (MonoidHom.snd (Bar2 L) (Bar2 K))
  have hEprod : E ≤ (Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))).prod
      (Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) :=
    uc22r3e5c_cartan_E_le_prod hL hKC hKne hset hSz hCβ heL heK
  have hDLle : DL ≤ Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)) :=
    (Subgroup.map_mono hEprod).trans (le_of_eq (uc22r3e5c_map_fst_prod _ _))
  have hDKle : DK ≤ Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)) :=
    (Subgroup.map_mono hEprod).trans (le_of_eq (uc22r3e5c_map_snd_prod _ _))
  have hEsub : E ≤ DL.prod DK := by
    intro z hz
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_map_of_mem _ hz, Subgroup.mem_map_of_mem _ hz⟩
  have hEcard : Nat.card ↥E = (2 ^ n - 1) ^ 2 := by
    rw [show E = (barImage (conjClosure D.M L) C).map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.injective, hCbar, hcardC]
  exact ⟨E, DL, DK, rfl, rfl, rfl, hEprod, hDLle, hDKle, hEsub, hEcard⟩


private theorem uc22r3e5c_card_normalizer_barImage {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card ↥(Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L))) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hULsyl : IsSylowTwoOf (barImage L (D.T ⊓ L)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  let QL : Sylow 2 (Bar2 L) := hULsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage L (D.T ⊓ L))]; exact hULsyl.2.2)
  have hQL : (QL : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := IsPGroup.toSylow_coe _ _
  have h := CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz
    (uc22r3e5c_quasithin_isSz_of_isSz hSz) QL
  rwa [hQL] at h

private theorem uc22r3e5c_cartan_proj_dvd {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {E : Subgroup (Bar2 L × Bar2 K)} {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hDLdef : DL = E.map (MonoidHom.fst (Bar2 L) (Bar2 K)))
    (hDKdef : DK = E.map (MonoidHom.snd (Bar2 L) (Bar2 K)))
    (hDLle : DL ≤ Subgroup.normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)))
    (hDKle : DK ≤ Subgroup.normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)))
    (hEcard : Nat.card ↥E = (2 ^ n - 1) ^ 2) :
    Odd (Nat.card DL) ∧ Odd (Nat.card DK) ∧
      Nat.card DL ∣ 2 ^ n - 1 ∧ Nat.card DK ∣ 2 ^ n - 1 := by
  have hn0 : n ≠ 0 := uc22r3e5c_ne_zero_of_isSz hSz
  have hm : Odd ((2 ^ n - 1) ^ 2) :=
    (Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Even.pow_of_ne_zero (by norm_num) hn0) odd_one).pow
  have hDLdvdE : Nat.card DL ∣ Nat.card ↥E := by
    have h := uc22r3e5c_card_ker_mul_card_map (MonoidHom.fst (Bar2 L) (Bar2 K)) E
    rw [hDLdef]
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  have hDKdvdE : Nat.card DK ∣ Nat.card ↥E := by
    have h := uc22r3e5c_card_ker_mul_card_map (MonoidHom.snd (Bar2 L) (Bar2 K)) E
    rw [hDKdef]
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  rw [hEcard] at hDLdvdE hDKdvdE
  have hDLodd : Odd (Nat.card DL) := Odd.of_dvd_nat hm hDLdvdE
  have hDKodd : Odd (Nat.card DK) := Odd.of_dvd_nat hm hDKdvdE
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hKmem hSz
  have hDLdvd : Nat.card DL ∣ 2 ^ n - 1 := by
    have h := Subgroup.card_dvd_of_le hDLle
    rw [uc22r3e5c_card_normalizer_barImage hL hSz] at h
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; ring
    rw [h2] at h
    exact ((hDLodd.coprime_two_right).pow_right (2 * n)).dvd_of_dvd_mul_left h
  have hDKdvd : Nat.card DK ∣ 2 ^ n - 1 := by
    have h := Subgroup.card_dvd_of_le hDKle
    rw [uc22r3e5c_card_normalizer_barImage hKC hSzK] at h
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; ring
    rw [h2] at h
    exact ((hDKodd.coprime_two_right).pow_right (2 * n)).dvd_of_dvd_mul_left h
  exact ⟨hDLodd, hDKodd, hDLdvd, hDKdvd⟩

private theorem uc22r3e5c_cartan_proj_card {L K : Subgroup G}
    {E : Subgroup (Bar2 L × Bar2 K)}
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)} {n : ℕ}
    (hn0 : n ≠ 0) (hEsub : E ≤ DL.prod DK)
    (hEcard : Nat.card ↥E = (2 ^ n - 1) ^ 2)
    (hDLdvd : Nat.card DL ∣ 2 ^ n - 1) (hDKdvd : Nat.card DK ∣ 2 ^ n - 1) :
    Nat.card DL = 2 ^ n - 1 ∧ Nat.card DK = 2 ^ n - 1 ∧ E = DL.prod DK := by
  have hcpos : 0 < 2 ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn0)
  have hprod : Nat.card DL * Nat.card DK = (2 ^ n - 1) ^ 2 := by
    refine le_antisymm ?_ ?_
    · obtain ⟨x, hx⟩ := hDLdvd
      obtain ⟨y, hy⟩ := hDKdvd
      have hxpos : 0 < x := Nat.pos_of_mul_pos_left (by rw [← hx]; exact hcpos)
      have hypos : 0 < y := Nat.pos_of_mul_pos_left (by rw [← hy]; exact hcpos)
      calc Nat.card DL * Nat.card DK ≤ (Nat.card DL * x) * (Nat.card DK * y) :=
            Nat.mul_le_mul (Nat.le_mul_of_pos_right (Nat.card DL) hxpos)
              (Nat.le_mul_of_pos_right (Nat.card DK) hypos)
        _ = (2 ^ n - 1) * (2 ^ n - 1) := by rw [← hx, ← hy]
        _ = (2 ^ n - 1) ^ 2 := by ring
    · calc (2 ^ n - 1) ^ 2 = Nat.card ↥E := hEcard.symm
        _ ≤ Nat.card ↥(DL.prod DK) := Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_dvd_of_le hEsub)
        _ = Nat.card DL * Nat.card DK := uc22r3e5c_card_prod DL DK
  have hDLcard : Nat.card DL = 2 ^ n - 1 := by
    obtain ⟨x, hx⟩ := hDLdvd
    have hb : Nat.card DK = x * (2 ^ n - 1) := by
      refine Nat.mul_left_cancel (Nat.card_pos (α := ↥DL)) ?_
      rw [hprod, hx]
      ring
    have hxdvd : 2 ^ n - 1 ∣ Nat.card DK := ⟨x, by rw [hb, mul_comm]⟩
    have hDKcard : Nat.card DK = 2 ^ n - 1 := Nat.dvd_antisymm hDKdvd hxdvd
    refine Nat.mul_right_cancel hcpos ?_
    calc Nat.card DL * (2 ^ n - 1) = Nat.card DL * Nat.card DK := by rw [hDKcard]
      _ = (2 ^ n - 1) * (2 ^ n - 1) := by rw [hprod]; ring_nf
  have hDKcard : Nat.card DK = 2 ^ n - 1 := by
    refine Nat.mul_left_cancel hcpos ?_
    calc (2 ^ n - 1) * Nat.card DK = Nat.card DL * Nat.card DK := by rw [hDLcard]
      _ = (2 ^ n - 1) ^ 2 := hprod
      _ = (2 ^ n - 1) * (2 ^ n - 1) := by ring
  have hEeq : E = DL.prod DK := by
    refine Subgroup.eq_of_le_of_card_ge hEsub ?_
    rw [uc22r3e5c_card_prod, hDLcard, hDKcard, hEcard]
    exact le_of_eq (by ring)
  exact ⟨hDLcard, hDKcard, hEeq⟩

private theorem uc22r3e5c_bar2_inclusion_injective {D : Data G} {L C : Subgroup G}
    (hCX : C ≤ conjClosure D.M L)
    (hcap : C ⊓ pCoreOf 2 (conjClosure D.M L) = ⊥) :
    Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L))).comp
      (Subgroup.inclusion hCX)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxQ : ((x : C) : G) ∈ pCoreOf 2 (conjClosure D.M L) :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := conjClosure D.M L)
      (Subgroup.inclusion hCX x)).mpr
      ((QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥(conjClosure D.M L)) _).mp hx)
  have hxbot : ((x : C) : G) ∈ C ⊓ pCoreOf 2 (conjClosure D.M L) := ⟨x.2, hxQ⟩
  rw [hcap] at hxbot
  exact Subtype.ext (Subgroup.mem_bot.mp hxbot)

private theorem uc22r3e5c_cartan_isMulCommutative {D : Data G} {L K : Subgroup G}
    {C : Subgroup G}
    (hCX : C ≤ conjClosure D.M L) (hcap : C ⊓ pCoreOf 2 (conjClosure D.M L) = ⊥)
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    {E : Subgroup (Bar2 L × Bar2 K)} {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hEdef : E = (barImage (conjClosure D.M L) C).map e.toMonoidHom)
    (hEeq : E = DL.prod DK) (hDLcomm : IsMulCommutative ↥DL)
    (hDKcomm : IsMulCommutative ↥DK) : IsMulCommutative ↥C := by
  haveI : IsMulCommutative ↥E := by
    rw [hEeq]
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (Subgroup.prodEquiv DL DK).injective
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  have hφinj := uc22r3e5c_bar2_inclusion_injective hCX hcap
  let g : ↥C →* Bar2 L × Bar2 K := e.toMonoidHom.comp
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure D.M L))).comp (Subgroup.inclusion hCX))
  have hgmem : ∀ x : ↥C, g x ∈ E := by
    intro x
    rw [hEdef]
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCX x, x.2, rfl⟩)
  let ψ : ↥C →* ↥E := g.codRestrict E hgmem
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hφinj
    exact e.injective (congrArg Subtype.val hxy)
  refine ⟨⟨fun x y => ?_⟩⟩
  apply hψinj
  rw [map_mul, map_mul]
  exact IsMulCommutative.is_comm.comm _ _

theorem uc22r3e5c_exists_cartan_image {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {C : Subgroup G} (hCX : C ≤ conjClosure D.M L)
    (hCβ : C ≤ conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))
    (hcardC : Nat.card C = (2 ^ n - 1) ^ 2) (hoddC : Odd (Nat.card C)) :
    ∃ (e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K) (DL : Subgroup (Bar2 L))
      (DK : Subgroup (Bar2 K)),
      (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
        e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1)) ∧
      (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
        e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) ∧
      (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK ∧
      DL ≤ normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)) ∧
      DK ≤ normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)) ∧
      Nat.card DL = 2 ^ n - 1 ∧ Nat.card DK = 2 ^ n - 1 ∧
      IsMulCommutative ↥C := by
  obtain ⟨e, heL, heK⟩ := uc22r3e5c_exists_bar2_mulEquiv_link hL hKC hKne hset hSz
  have hcap := uc22r3e5c_cartan_cap_pCore (D := D) (L := L) hoddC
  have hCbar := uc22r3e5c_card_barImage_cartan hCX hcap
  obtain ⟨E, DL, DK, hEdef, hDLdef, hDKdef, hEprod, hDLle, hDKle, hEsub, hEcard⟩ :=
    uc22r3e5c_cartan_proj_bounds hL hKC hKne hset hSz hCβ hCbar hcardC heL heK
  obtain ⟨hDLodd, hDKodd, hDLdvd, hDKdvd⟩ :=
    uc22r3e5c_cartan_proj_dvd hL hKC hset hSz hDLdef hDKdef hDLle hDKle hEcard
  have hn0 : n ≠ 0 := uc22r3e5c_ne_zero_of_isSz hSz
  obtain ⟨hDLcard, hDKcard, hEeq⟩ :=
    uc22r3e5c_cartan_proj_card hn0 hEsub hEcard hDLdvd hDKdvd
  have hm1 : Odd (2 ^ n - 1) := by
    rw [← hDLcard]; exact hDLodd
  have hULsyl : IsSylowTwoOf (barImage L (D.T ⊓ L)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  have hUKsyl : IsSylowTwoOf (barImage K (D.T ⊓ K)) ⊤ :=
    uc22r3e5c_isSylowTwoOf_barImage_inf_T hKC
  let QL : Sylow 2 (Bar2 L) := hULsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage L (D.T ⊓ L))]; exact hULsyl.2.2)
  let QK : Sylow 2 (Bar2 K) := hUKsyl.2.1.toSylow (by
    rw [← Subgroup.relIndex_top_right (H := barImage K (D.T ⊓ K))]; exact hUKsyl.2.2)
  have hQL : (QL : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) := IsPGroup.toSylow_coe _ _
  have hQK : (QK : Subgroup (Bar2 K)) = barImage K (D.T ⊓ K) := IsPGroup.toSylow_coe _ _
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hSzK : IsSz (Bar2 K) n := uc22r3e5c_isSz_of_mem_conjSetOf hKmem hSz
  haveI hDLcomm : IsMulCommutative ↥DL :=
    uc22r3e5c_isMulCommutative_of_odd_le_normalizer
      (uc22r3e5c_quasithin_isSz_of_isSz hSz) QL (by rwa [hQL]) (by rw [hDLcard]; exact hm1)
  haveI hDKcomm : IsMulCommutative ↥DK :=
    uc22r3e5c_isMulCommutative_of_odd_le_normalizer
      (uc22r3e5c_quasithin_isSz_of_isSz hSzK) QK (by rwa [hQK]) (by rw [hDKcard]; exact hm1)
  have hcomm := uc22r3e5c_cartan_isMulCommutative hCX hcap hEdef hEeq hDLcomm hDKcomm
  exact ⟨e, DL, DK, heL, heK, hEdef ▸ hEeq, hDLle, hDKle, hDLcard, hDKcard, hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
