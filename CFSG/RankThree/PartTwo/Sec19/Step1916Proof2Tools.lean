module

public import CFSG.RankThree.PartTwo.Sec19.Statements
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate3086
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1914E
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

namespace Step1916Proof2

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem mem_A (hctx : Ctx1912 G A c L E M) : c ∈ A :=
  hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)

theorem orderOf_eq (hctx : Ctx1912 G A c L E M) : orderOf c = 3 := by
  rw [← Nat.card_zpowers]
  exact hctx.zpowers_mem_omegaA.2.1

theorem mem_E (hctx : Ctx1912 G A c L E M) : c ∈ E :=
  mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hctx.mem_partTwoT.1
    (hctx.mem_partTwoE.1.2 c (mem_A hctx)) hctx.le_centralizer

theorem not_mem_L (hctx : Ctx1912 G A c L E M) : c ∉ L :=
  hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA

theorem isE27_E (hctx : Ctx1912 G A c L E M) : IsE27 E :=
  isE27_of_mem_partTwoE hctx.mem_partTwoT.1

theorem isE27_A (hctx : Ctx1912 G A c L E M) : IsE27 A :=
  isE27_of_mem_partTwoE hctx.mem_partTwoE

theorem ne_E (hctx : Ctx1912 G A c L E M) : A ≠ E := fun h =>
  hctx.not_mem_partTwoT (h ▸ hctx.mem_partTwoT)

theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx y']
  rw [hY, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans e.map_one.symm)

theorem lBar_facts
    (h1913 : Step1913) (hctx : Ctx1912 G A c L E M) :
    aschbacherSolvableCore 3 L = CFSG.pCore 2 L ∧
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧ 3 ∣ Nat.card L := by
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | hM12
  · obtain ⟨hXs, -⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
    have hθ : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
      Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
    have hZ : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ :=
      Step1914TriProof.center_eq_bot_of_isSimpleGroup_of_isPerfect
    refine ⟨hθ, center_eq_bot_of_mulEquiv' (QuotientGroup.quotientMulEquivOfEq hθ) hZ,
      (Step1914TriProof.three_dvd_card_of_isoLThreePi he hiso).trans
        (Subgroup.card_quotient_dvd_card _)⟩
  · obtain ⟨h3, hZ, -, hsol⟩ := KFacts.ks18M12 _ hM12
    have hθ : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
      theta_eq_pCore_two_of_solvable fun N hN hs => hsol N hN hs
    exact ⟨hθ, center_eq_bot_of_mulEquiv' (QuotientGroup.quotientMulEquivOfEq hθ) hZ,
      h3.trans (Subgroup.card_quotient_dvd_card _)⟩

theorem le_normalizer_E (hctx : Ctx1912 G A c L E M) (hL3 : 3 ∣ Nat.card L) :
    E ≤ Subgroup.normalizer (L : Set G) :=
  (hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c)).trans
    (Step1914TriProof.normalizer_zpowers_le_of_three_dvd hctx hL3)

theorem exists_mem_of_normal {T S : Subgroup G} (hT : IsPGroup 3 T) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hS : S ≠ ⊥) :
    ∃ z ∈ S, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (S.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mpr hTS
  have hS' : S.subgroupOf T ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hST hx⟩ : T) ∈ S.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  have : Group.IsNilpotent T := hT.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hS'
  set W := S.subgroupOf T ⊓ Subgroup.center T with hW
  have hW3 : IsPGroup 3 W := hT.to_subgroup W
  have hnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hne
  obtain ⟨n, hn⟩ := hW3.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' (by simpa using hn)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 3
    (by rw [hn]; exact dvd_pow_self 3 hn0)
  have hwS : (((w : T) : G)) ∈ S := Subgroup.mem_subgroupOf.mp w.2.1
  have hwZ := w.2.2
  refine ⟨((w : T) : G), hwS, ?_, ?_, ?_⟩
  · intro h1
    have : w = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hw
    norm_num at hw
  · have h3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    simpa using congrArg (fun x : W => ((x : T) : G)) h3
  · intro t ht
    have := (Subgroup.mem_center_iff.mp hwZ) ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem exists_mem_inf_of_three_dvd (hctx : Ctx1912 G A c L E M) (hL3 : 3 ∣ Nat.card L) :
    ∃ z ∈ A ⊓ E, z ∈ L ∧ z ≠ 1 ∧ z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := E ⊔ A with hP
  have hP3 : IsPGroup 3 P := hctx.isPGroup_sup
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (le_normalizer_E hctx hL3) hctx.mem_lA.2.1
  set Y := P ⊔ L with hY
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hPN Subgroup.le_normalizer
  obtain ⟨Q, hPQ⟩ := (hP3.comap_subtype (K := Y)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup Y).map Y.subtype with hT
  have hTY : IsSylowOf 3 T Y := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun x hx =>
    ⟨⟨x, le_sup_left (b := L) hx⟩, hPQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTL : IsSylowOf 3 (T ⊓ L) L := hTY.inf_of_le_normalizer le_sup_right hYN
  have hTL1 : T ⊓ L ≠ ⊥ := by
    intro h
    have hcard := hTL.card_eq
    rw [h, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card L).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hL3
    have h3 : 3 ≤ 3 ^ (Nat.card L).factorization 3 :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hpos)
    omega
  obtain ⟨z, hzTL, hz1, hz3, hzT⟩ := exists_mem_of_normal hTY.isPGroup inf_le_left
    (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hYN (hTY.le ht)⟩) hTL1
  have hC : ∀ X : Subgroup G, X ≤ T → X ≤ Subgroup.centralizer ({z} : Set G) := fun X hXT x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzT x (hXT hx))
  have hzA : z ∈ A := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq
    hctx.mem_partTwoE hz3 (hC A (le_sup_right.trans hPT))
  have hzE : z ∈ E := mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq
    hctx.mem_partTwoT.1 hz3 (hC E (le_sup_left.trans hPT))
  exact ⟨z, ⟨hzA, hzE⟩, hzTL.2, hz1, hz3⟩

theorem card_inf_eq_nine (hctx : Ctx1912 G A c L E M) (hL3 : 3 ∣ Nat.card L) :
    Nat.card (A ⊓ E : Subgroup G) = 9 := by
  obtain ⟨z, hz, hzL, hz1, -⟩ := exists_mem_inf_of_three_dvd hctx hL3
  have hA := isE27_A hctx
  have hE := isE27_E hctx
  have hzc : z ∉ Subgroup.zpowers c := by
    intro h
    have hbot := Step1914TriProof.zpowers_inf_eq_bot_of_not_mem (orderOf_eq hctx)
      (not_mem_L hctx)
    have : z ∈ Subgroup.zpowers c ⊓ L := ⟨h, hzL⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 this
  have h9 : 9 ≤ Nat.card (A ⊓ E : Subgroup G) :=
    Step1914TriProof.nine_le_card_of_mem_of_not_mem hA inf_le_left (orderOf_eq hctx)
      ⟨mem_A hctx, mem_E hctx⟩ hz hzc
  have hdvd : Nat.card (A ⊓ E : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · rw [hk] at h9; norm_num at h9
  · rw [hk] at h9; norm_num at h9
  · rw [hk]; norm_num
  · exfalso
    have h1 : A ⊓ E = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA.2]; norm_num)
    have h2 : A ⊓ E = E := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hE.2]; norm_num)
    exact ne_E hctx (h1.symm.trans h2)

theorem eq_one_of_forall_commutator_mem
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {Y : Subgroup G} (hLY : L ≤ Y)
    {a : G} (haL : a ∈ L) {k : ℕ} (ha : a ^ 3 ^ k = 1)
    (h : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) : a = 1 := by
  set θL := aschbacherSolvableCore 3 L with hθL
  set a' : L := ⟨a, haL⟩ with ha'
  have hcen : (a' : L ⧸ θL) ∈ Subgroup.center (L ⧸ θL) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : a * l * a⁻¹ * (l : G)⁻¹ ∈ θL.map L.subtype :=
      Step1910Proof.inf_pCoreOf_le_theta hLY
        ⟨L.mul_mem (L.mul_mem (L.mul_mem haL l.2) (L.inv_mem haL)) (L.inv_mem l.2), h l l.2⟩
    obtain ⟨x, hx, hxe⟩ := hmem
    have hx' : x = a' * l * a'⁻¹ * l⁻¹ := Subtype.ext (by simpa using hxe)
    have h1 : ((a' * l * a'⁻¹ * l⁻¹ : L) : L ⧸ θL) = 1 := by
      rw [QuotientGroup.eq_one_iff, ← hx']
      exact hx
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (l : L ⧸ θL) * a' = ((a' : L ⧸ θL) * l * (a' : L ⧸ θL)⁻¹ * (l : L ⧸ θL)⁻¹)⁻¹ *
          ((a' : L ⧸ θL) * l) := by group
      _ = (a' : L ⧸ θL) * l := by rw [h1, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have h1 : a' ^ 3 ^ k = 1 := Subtype.ext (by simpa using ha)
  have := Step1914TriProof.eq_one_of_mem_theta' hcen h1
  simpa [ha'] using congrArg Subtype.val this

end Step1916Proof2

end CFSG.RankThree.PartTwo.Sec19
