module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.Background.F6Amalgams
import CFSG.Quasithin.Background.F9Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaAssembly
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullBasic
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cQ8

public section

namespace CFSG.Quasithin.St84

open CFSG.Open

open scoped commutatorElement

private theorem isMulCommutative_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) : IsMulCommutative G := by
  have h2 : Nat.card G ∣ 2 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]
  haveI := isCyclic_of_card_dvd_prime (p := 2) h2
  infer_instance

private theorem relIndex_inf_le_two {G : Type*} [Group G] {H K L : Subgroup G}
    (hH : H ≤ L) (hKL : K.relIndex L = 2) : (H ⊓ K).relIndex H ≤ 2 := by
  rw [Subgroup.inf_relIndex_left]
  refine (Subgroup.relIndex_le_of_le_right hH ?_).trans_eq hKL
  rw [hKL]; norm_num

private theorem card_le_two_of_inf_eq_bot {G : Type*} [Group G] {Qs Qs' St : Subgroup G}
    (hQs : Qs ≤ St) (hi' : Qs'.relIndex St = 2) (hA : Qs ⊓ Qs' = ⊥) :
    Nat.card ↥Qs ≤ 2 := by
  rw [← Subgroup.relIndex_bot_left, ← hA]
  exact relIndex_inf_le_two hQs hi'


private theorem isMulCommutative_sup_of_central {G : Type*} [Group G] {A Z : Subgroup G}
    (hA : IsMulCommutative A) (hZ : Z ≤ Subgroup.centralizer ((A ⊔ Z : Subgroup G) : Set G)) :
    IsMulCommutative ↥(A ⊔ Z) := by
  have hpair : ((A : Set G) ∪ (Z : Set G)).Pairwise Commute := by
    intro a ha b hb _
    rw [Set.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg (fun t : ↥A => (t : G)) (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · exact Subgroup.mem_centralizer_iff.mp (hZ hb) a (Subgroup.mem_sup_left ha)
    · exact (Subgroup.mem_centralizer_iff.mp (hZ ha) b (Subgroup.mem_sup_left hb)).symm
    · exact (Subgroup.mem_centralizer_iff.mp (hZ ha) b (Subgroup.mem_sup_right hb)).symm
  rw [Subgroup.sup_eq_closure]
  exact Subgroup.isMulCommutative_closure (k := (A : Set G) ∪ (Z : Set G)) hpair

private theorem card_eq_one_or_two_or_four_or_eight {G : Type*} [Group G] {Q : Subgroup G}
    [Finite ↥Q] (hQ2 : IsPGroup 2 Q) (h8 : Nat.card ↥Q ≤ 8) :
    Nat.card ↥Q = 1 ∨ Nat.card ↥Q = 2 ∨ Nat.card ↥Q = 4 ∨ Nat.card ↥Q = 8 := by
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hk3 : k ≤ 3 := by
    have h1 : 2 ^ k ≤ 2 ^ 3 := by
      rw [← hk]
      simpa using h8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  interval_cases k <;> simp_all

private theorem not_mem_of_isPGroup_two {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsPGroup 2 P) {x : G} (hx : orderOf x = 3) : x ∉ P := by
  intro hxP
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [hx] at h1
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
  omega

private theorem centerOf_eq_map_center {G : Type*} [Group G] (S : Subgroup G) :
    centerOf S = (Subgroup.center ↥S).map S.subtype := by
  ext x
  constructor
  · rintro ⟨hxS, hxc⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hxc y y.2
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)

private theorem le_normalizer_centerOf {G : Type*} [Group G] {Q J : Subgroup G}
    (hJN : J ≤ Subgroup.normalizer (Q : Set G)) :
    J ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) := by
  show J ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G)
  exact F7.le_normalizer_inf hJN (hJN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)))

private theorem centerOf_le_centerOf_of_card_eq_two {G : Type*} [Group G] {Q S : Subgroup G}
    (hQS : Q ≤ S) (hSN : S ≤ Subgroup.normalizer (Q : Set G))
    (hZ2 : Nat.card ↥(centerOf Q) = 2) : centerOf Q ≤ centerOf S := by
  show centerOf Q ≤ S ⊓ Subgroup.centralizer (S : Set G)
  exact le_inf (inf_le_left.trans hQS) (Subgroup.le_centralizer_iff.mp
    ((le_normalizer_centerOf hSN).trans
      (CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two hZ2).le))

private theorem card_modEq_card_inf_centralizer {G : Type*} [Group G] {Q : Subgroup G}
    {d : G} [Finite ↥Q] (hdN : d ∈ Subgroup.normalizer (Q : Set G))
    (hd3 : orderOf d = 3) :
    Nat.card ↥Q ≡ Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) [MOD 3] := by
  have hdQ : Subgroup.zpowers d ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  letI : MulAction ↥(Subgroup.zpowers d) ↥Q :=
    { smul := fun g x =>
        ⟨(g : G) * (x : G) * (g : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hdQ g.2) x.1).mp x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        group
      mul_smul := fun g h x => by
        apply Subtype.ext
        show ((g : G) * (h : G)) * (x : G) * ((g : G) * (h : G))⁻¹ =
          (g : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (g : G)⁻¹
        group }
  have h3 : IsPGroup 3 ↥(Subgroup.zpowers d) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hd3]
    norm_num
  have hmod := IsPGroup.card_modEq_card_fixedPoints (p := 3) h3 (α := ↥Q)
  have hsub : ∀ x : ↥Q, (x ∈ MulAction.fixedPoints ↥(Subgroup.zpowers d) ↥Q) ↔
      (x : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    intro x
    constructor
    · intro hx
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h' : d * (x : G) * d⁻¹ = (x : G) :=
        congrArg (fun y : ↥Q => (y : G)) (hx ⟨d, Subgroup.mem_zpowers d⟩)
      calc d * (x : G) = (d * (x : G) * d⁻¹) * d := by group
        _ = (x : G) * d := by rw [h']
    · intro hx g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hcomm : d * (x : G) = (x : G) * d :=
        Subgroup.mem_centralizer_iff.mp hx d (Set.mem_singleton d)
      apply Subtype.ext
      show (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
      rw [← hk]
      have hc : Commute (d ^ k) ((x : G)) :=
        (show Commute d ((x : G)) from hcomm).zpow_left k
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers d) ↥Q) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) := by
    have hcard_eq : Nat.card (Subtype (fun x : ↥Q =>
        (x : G) ∈ Subgroup.centralizer ({d} : Set G))) =
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    rw [← hcard_eq]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(MulAction.fixedPoints ↥(Subgroup.zpowers d) ↥Q) =>
        (⟨x.1, (hsub x.1).mp x.2⟩ :
          Subtype (fun y : ↥Q => (y : G) ∈ Subgroup.centralizer ({d} : Set G)))) ⟨?_, ?_⟩)
    · intro a b hab
      have h1 : (a : ↥Q) = (b : ↥Q) := by
        have h2 := congrArg (fun z : Subtype (fun y : ↥Q =>
          (y : G) ∈ Subgroup.centralizer ({d} : Set G)) => (z : ↥Q)) hab
        simpa using h2
      exact Subtype.ext h1
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, (hsub y).mpr hy⟩, rfl⟩
  rw [hfix] at hmod
  exact hmod

private theorem four_mul_card_centralizer {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    [Finite ↥Q] (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3)
    (hcard : Nat.card ↥Q = 4 ∨ Nat.card ↥Q = 8)
    (hne : Q ⊓ Subgroup.centralizer ({d} : Set G) ≠ Q) :
    Nat.card ↥Q = 4 * Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have hmod := card_modEq_card_inf_centralizer hdN hd3
  have hCQ : Q ⊓ Subgroup.centralizer ({d} : Set G) ≤ Q := inf_le_left
  have hdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) ∣ Nat.card ↥Q := by
    have h := Subgroup.relIndex_mul_card (H := Q ⊓ Subgroup.centralizer ({d} : Set G)) (K := Q)
    rw [inf_eq_left.mpr hCQ] at h
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  have hCne : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) ≠ Nat.card ↥Q := by
    intro h
    exact hne (Subgroup.eq_of_le_of_card_ge hCQ (le_of_eq h.symm))
  rcases hcard with h4 | h8
  · have hc4 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 from by norm_num, ← h4]
      exact hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc4
    have hmod4 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) % 3 = 1 := by
      have h := hmod
      rw [Nat.ModEq, h4] at h
      omega
    rw [hk] at hmod4 hCne ⊢
    interval_cases k
    · rw [h4]; norm_num
    · norm_num at hmod4
    · exact absurd (by rw [h4]; norm_num) hCne
  · have hc8 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 from by norm_num, ← h8]
      exact hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc8
    have hmod8 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) % 3 = 2 := by
      have h := hmod
      rw [Nat.ModEq, h8] at h
      omega
    rw [hk] at hmod8 hCne ⊢
    interval_cases k
    · norm_num at hmod8
    · rw [h8]; norm_num
    · norm_num at hmod8
    · exact absurd (by rw [h8]; norm_num) hCne

private theorem map_ker_eq_inf_centralizer {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    (f : ↥Q →* ↥Q)
    (hfval : ∀ x : ↥Q, ((f x : ↥Q) : G) = (x : G) * d * (x : G)⁻¹ * d⁻¹) :
    f.ker.map Q.subtype = Q ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : f y = 1 := MonoidHom.mem_ker.mp hy
    have h : (y : G) * d * (y : G)⁻¹ * d⁻¹ = 1 := by
      have h2 := congrArg (fun w : ↥Q => (w : G)) hy'
      rw [hfval] at h2
      simpa using h2
    have h1 : (y : G) * d * (y : G)⁻¹ = d := by
      calc (y : G) * d * (y : G)⁻¹ =
          ((y : G) * d * (y : G)⁻¹ * d⁻¹) * d := by group
        _ = 1 * d := by rw [h]
        _ = d := one_mul d
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc d * (y : G) = ((y : G) * d * (y : G)⁻¹) * (y : G) := by rw [h1]
      _ = (y : G) * d := by group
  · intro hz
    obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
    refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
    show f ⟨z, hzQ⟩ = 1
    apply Subtype.ext
    rw [hfval]
    show z * d * z⁻¹ * d⁻¹ = ((1 : ↥Q) : G)
    simp only [Subgroup.coe_one]
    have hcomm : d * z = z * d :=
      Subgroup.mem_centralizer_iff.mp hzC d (Set.mem_singleton d)
    rw [show z * d = d * z from hcomm.symm]
    group

private theorem map_range_eq_commutator {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3) (f : ↥Q →* ↥Q)
    (hfval : ∀ x : ↥Q, ((f x : ↥Q) : G) = (x : G) * d * (x : G)⁻¹ * d⁻¹) :
    f.range.map Q.subtype = ⁅Q, Subgroup.zpowers d⁆ := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨x, rfl⟩ := hy
    have heq : ((f x : ↥Q) : G) = ⁅(x : G), d⁆ := by
      rw [hfval, commutatorElement_def]
    show ((f x : ↥Q) : G) ∈ ⁅Q, Subgroup.zpowers d⁆
    rw [heq]
    exact Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_zpowers d)
  · rw [Subgroup.commutator_le]
    intro q hq k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have h3d : d ^ (3 : ℤ) = 1 := by
      have h := pow_orderOf_eq_one d
      rw [hd3] at h
      simpa using h
    have hred : d ^ j = d ^ (j % 3) := zpow_eq_zpow_emod j h3d
    rw [hred]
    have hj := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
    have hj' := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
    have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0]
      simp only [zpow_zero, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [h1]
      simp only [zpow_one]
      have heq : ((f ⟨q, hq⟩ : ↥Q) : G) = ⁅q, d⁆ := by
        rw [hfval, commutatorElement_def]
      rw [← heq]
      exact ⟨f ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    · rw [h2]
      have heq : ((f (⟨q, hq⟩ * ⟨d * q * d⁻¹,
          (Subgroup.mem_normalizer_iff.mp hdN q).mp hq⟩) : ↥Q) : G) =
          ⁅q, d ^ (2 : ℤ)⁆ := by
        rw [map_mul, Subgroup.coe_mul, hfval, hfval, Subgroup.coe_mk,
          commutatorElement_def, zpow_two]
        group
      rw [← heq]
      exact ⟨f (⟨q, hq⟩ * ⟨d * q * d⁻¹,
          (Subgroup.mem_normalizer_iff.mp hdN q).mp hq⟩),
        ⟨⟨q, hq⟩ * ⟨d * q * d⁻¹,
          (Subgroup.mem_normalizer_iff.mp hdN q).mp hq⟩, rfl⟩, rfl⟩

private theorem exists_hom_ker_range {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3)
    (habel : IsMulCommutative Q) :
    ∃ f : ↥Q →* ↥Q,
      f.ker.map Q.subtype = Q ⊓ Subgroup.centralizer ({d} : Set G) ∧
        f.range.map Q.subtype = ⁅Q, Subgroup.zpowers d⁆ ∧
        ∀ x : ↥Q, ((f x : ↥Q) : G) = (x : G) * d * (x : G)⁻¹ * d⁻¹ := by
  letI : CommGroup ↥Q :=
    { (inferInstance : Group ↥Q) with mul_comm := fun a b => habel.is_comm.comm a b }
  have hmem : ∀ x : ↥Q, d * (x : G) * d⁻¹ ∈ Q := fun x =>
    (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp x.2
  let φ : ↥Q →* ↥Q :=
    { toFun := fun x => ⟨d * (x : G) * d⁻¹, hmem x⟩
      map_one' := Subtype.ext (by show d * 1 * d⁻¹ = 1; group)
      map_mul' := fun x y => Subtype.ext (by
        show d * ((x : G) * (y : G)) * d⁻¹ = (d * (x : G) * d⁻¹) * (d * (y : G) * d⁻¹)
        group) }
  let f : ↥Q →* ↥Q :=
    { toFun := fun x => x * (φ x)⁻¹
      map_one' := Subtype.ext (by show (1 : G) * (d * 1 * d⁻¹)⁻¹ = 1; group)
      map_mul' := fun x y => by
        rw [map_mul]
        show x * y * ((φ x) * (φ y))⁻¹ = (x * (φ x)⁻¹) * (y * (φ y)⁻¹)
        rw [mul_inv_rev]
        ac_rfl }
  have hfval : ∀ x : ↥Q, ((f x : ↥Q) : G) = (x : G) * d * (x : G)⁻¹ * d⁻¹ := by
    intro x
    show (x : G) * (d * (x : G) * d⁻¹)⁻¹ = (x : G) * d * (x : G)⁻¹ * d⁻¹
    group
  exact ⟨f, map_ker_eq_inf_centralizer f hfval, map_range_eq_commutator hdN hd3 f hfval,
    hfval⟩

private theorem commutator_card {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    [Finite ↥Q] (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3)
    (habel : IsMulCommutative Q)
    (h4 : Nat.card ↥Q = 4 * Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G))) :
    Nat.card ↥⁅Q, Subgroup.zpowers d⁆ = 4 := by
  obtain ⟨f, hker, hrange, -⟩ := exists_hom_ker_range hdN hd3 habel
  haveI hCfin : Finite ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have h1 : Nat.card ↥f.ker = Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [← hker]
    exact (Subgroup.card_map_of_injective (f := Q.subtype) Subtype.coe_injective
      (K := f.ker)).symm
  have h2 : Nat.card ↥f.range = Nat.card ↥⁅Q, Subgroup.zpowers d⁆ := by
    rw [← hrange]
    exact (Subgroup.card_map_of_injective (f := Q.subtype) Subtype.coe_injective
      (K := f.range)).symm
  have h3 : Nat.card ↥f.ker * Nat.card ↥f.range = Nat.card ↥Q :=
    Subgroup.card_ker_mul_card_range f
  rw [h1, h2, h4] at h3
  have hpos : 0 < Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G)) := Nat.card_pos
  refine Nat.mul_left_cancel hpos ?_
  rw [mul_comm (Nat.card ↥(Q ⊓ Subgroup.centralizer ({d} : Set G))) 4]
  exact h3

private theorem inf_centralizer_commutator {G : Type*} [Group G] {Q : Subgroup G} {d : G}
    [Finite ↥Q] (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3)
    (habel : IsMulCommutative Q) (hQ2 : IsPGroup 2 Q) :
    Q ⊓ Subgroup.centralizer ({d} : Set G) ⊓ ⁅Q, Subgroup.zpowers d⁆ = ⊥ := by
  obtain ⟨f, -, hrange, hfval⟩ := exists_hom_ker_range hdN hd3 habel
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨⟨hzQ, hzC⟩, hzE⟩ := Subgroup.mem_inf.mp hz
  rw [← hrange] at hzE
  obtain ⟨y, hy, hyz⟩ := hzE
  obtain ⟨x, rfl⟩ := hy
  have hzval : z = (x : G) * d * (x : G)⁻¹ * d⁻¹ := by
    rw [← hyz]
    exact hfval x
  have hdz : d * z * d⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp hzC d (Set.mem_singleton d)
    calc d * z * d⁻¹ = (z * d) * d⁻¹ := by rw [← h]
      _ = z := by group
  have hd3z : d * d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd3] at h
    calc d * d * d = d ^ 3 := by rw [pow_three]; group
      _ = 1 := h
  have hz3 : z ^ 3 = 1 := by
    calc z ^ 3 = z * (d * z * d⁻¹) * (d * (d * z * d⁻¹) * d⁻¹) := by
          rw [pow_three, hdz, hdz]
          group
      _ = (x : G) * (d * d * d) * (x : G)⁻¹ * (d * d * d)⁻¹ := by
          rw [hzval]; group
      _ = 1 := by rw [hd3z]; group
  have hord3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have hord2 : orderOf z ∣ Nat.card ↥Q := Subgroup.orderOf_dvd_natCard Q hzQ
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hcop : Nat.Coprime 3 (2 ^ k) := (by norm_num : Nat.Coprime 3 2).pow_right k
  have hone : orderOf z = 1 := by
    have hdvd : orderOf z ∣ Nat.gcd 3 (Nat.card ↥Q) := Nat.dvd_gcd hord3 hord2
    rw [hk] at hdvd
    rw [show Nat.gcd 3 (2 ^ k) = 1 from hcop] at hdvd
    exact Nat.dvd_one.mp hdvd
  simpa [Subgroup.mem_bot, orderOf_eq_one_iff.mp hone]

private theorem center_le_inf_of_nonabelian {G : Type*} [Group G] {Qs Qs' : Subgroup G}
    (hQs8 : Nat.card ↥Qs = 8) (hnon : ¬ IsMulCommutative Qs)
    (hA4 : Nat.card ↥(Qs ⊓ Qs') = 4) : centerOf Qs ≤ Qs ⊓ Qs' := by
  haveI hQfin : Finite ↥Qs := Nat.finite_of_card_ne_zero (by rw [hQs8]; norm_num)
  haveI hAfin : Finite ↥(Qs ⊓ Qs') := Nat.finite_of_card_ne_zero (by rw [hA4]; norm_num)
  have hAab : IsMulCommutative ↥(Qs ⊓ Qs') :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hA4]; norm_num)
  intro z hzZ
  by_contra hzA
  have hz1 : z ≠ 1 := by
    intro h
    exact hzA (h ▸ (Qs ⊓ Qs').one_mem)
  have hle' : Qs ⊓ Qs' ⊔ centerOf Qs ≤ Qs := sup_le inf_le_left inf_le_left
  haveI hjoinfin : Finite ↥(Qs ⊓ Qs' ⊔ centerOf Qs) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle')
  have hsup : Qs ⊓ Qs' ⊔ centerOf Qs = Qs := by
    have hlt : Qs ⊓ Qs' < Qs ⊓ Qs' ⊔ centerOf Qs :=
      lt_of_le_of_ne le_sup_left (by
        intro heq
        exact hzA (heq.symm ▸ Subgroup.mem_sup_right hzZ))
    have hltcard := Subgroup.card_lt_of_lt hlt
    have hlecard : Nat.card ↥(Qs ⊓ Qs' ⊔ centerOf Qs) ≤ 8 := by
      rw [← hQs8]
      exact Subgroup.card_le_of_le hle'
    have hdvd : Nat.card ↥(Qs ⊓ Qs') ∣ Nat.card ↥(Qs ⊓ Qs' ⊔ centerOf Qs) :=
      Subgroup.card_dvd_of_le le_sup_left
    rw [hA4] at hdvd
    have hcard : Nat.card ↥(Qs ⊓ Qs' ⊔ centerOf Qs) = 8 := by omega
    exact Subgroup.eq_of_le_of_card_ge hle' (le_of_eq (hQs8.trans hcard.symm))
  have hZcent : centerOf Qs ≤
      Subgroup.centralizer ((Qs ⊓ Qs' ⊔ centerOf Qs : Subgroup G) : Set G) := by
    rw [hsup]
    exact inf_le_right
  have hcomm := isMulCommutative_sup_of_central hAab hZcent
  rw [hsup] at hcomm
  exact hnon hcomm

private theorem card_inf_eq_four {G : Type*} [Group G] {Qs Qs' St : Subgroup G}
    (hQsSt : Qs ≤ St) (hi' : Qs'.relIndex St = 2) (hQs8 : Nat.card ↥Qs = 8)
    (hAne : Qs ⊓ Qs' ≠ Qs) : Nat.card ↥(Qs ⊓ Qs') = 4 := by
  have hrel_le : (Qs ⊓ Qs').relIndex Qs ≤ 2 := relIndex_inf_le_two hQsSt hi'
  have hrel_ne1 : (Qs ⊓ Qs').relIndex Qs ≠ 1 := by
    intro h1
    exact hAne (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h1))
  have hrel : (Qs ⊓ Qs').relIndex Qs = 2 := by
    have hpos : 0 < (Qs ⊓ Qs').relIndex Qs := by
      by_contra h0
      rw [Nat.not_lt, Nat.le_zero] at h0
      have h := Subgroup.relIndex_mul_card (H := Qs ⊓ Qs') (K := Qs)
      rw [inf_eq_left.mpr (inf_le_left : Qs ⊓ Qs' ≤ Qs), hQs8] at h
      rw [h0] at h
      simp only [zero_mul] at h
      omega
    omega
  have h := Subgroup.relIndex_mul_card (H := Qs ⊓ Qs') (K := Qs)
  rw [inf_eq_left.mpr (inf_le_left : Qs ⊓ Qs' ≤ Qs), hrel, hQs8] at h
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) (by rw [h])

private theorem centerOf_eq_centerOf_of_card_eq_two {G : Type*} [Group G]
    {Qs Qs' St : Subgroup G} (hQsSt : Qs ≤ St)
    (hZcard : Nat.card ↥(centerOf Qs) = 2) (hZcard' : Nat.card ↥(centerOf Qs') = 2)
    (hA4 : Nat.card ↥(Qs ⊓ Qs') = 4) (hZA : centerOf Qs ≤ Qs ⊓ Qs')
    (hZA' : centerOf Qs' ≤ Qs ⊓ Qs') (hZe : centerOf Qs ≤ centerOf St)
    (hZe' : centerOf Qs' ≤ centerOf St) : centerOf Qs = centerOf Qs' := by
  by_contra heq
  haveI hZfin : Finite ↥(centerOf Qs) :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  haveI hZ'fin : Finite ↥(centerOf Qs') :=
    Nat.finite_of_card_ne_zero (by rw [hZcard']; norm_num)
  haveI hAfin : Finite ↥(Qs ⊓ Qs') := Nat.finite_of_card_ne_zero (by rw [hA4]; norm_num)
  have hjoinA : centerOf Qs ⊔ centerOf Qs' ≤ Qs ⊓ Qs' := sup_le hZA hZA'
  haveI hjoinfin : Finite ↥(centerOf Qs ⊔ centerOf Qs') :=
    Finite.of_injective _ (Subgroup.inclusion_injective hjoinA)
  have hjoinZ : centerOf Qs ⊔ centerOf Qs' ≤ centerOf St := sup_le hZe hZe'
  have hjoin_gt : 2 < Nat.card ↥(centerOf Qs ⊔ centerOf Qs') := by
    have hAle : centerOf Qs ≤ centerOf Qs ⊔ centerOf Qs' := le_sup_left
    have hne : centerOf Qs ≠ centerOf Qs ⊔ centerOf Qs' := by
      intro h
      apply heq
      have hZ'le : centerOf Qs' ≤ centerOf Qs := by
        rw [h]; exact le_sup_right
      exact (Subgroup.eq_of_le_of_card_ge hZ'le
        (le_of_eq (hZcard.trans hZcard'.symm))).symm
    have hle2 : Nat.card ↥(centerOf Qs) ≤ Nat.card ↥(centerOf Qs ⊔ centerOf Qs') :=
      Subgroup.card_le_of_le hAle
    have hne2 : Nat.card ↥(centerOf Qs) ≠ Nat.card ↥(centerOf Qs ⊔ centerOf Qs') :=
      fun h => hne (Subgroup.eq_of_le_of_card_ge hAle (le_of_eq h.symm))
    omega
  have hjoin4 : Nat.card ↥(centerOf Qs ⊔ centerOf Qs') = 4 := by
    have h2dvd : 2 ∣ Nat.card ↥(centerOf Qs ⊔ centerOf Qs') := by
      have hdvd := Subgroup.card_dvd_of_le
        (le_sup_left : centerOf Qs ≤ centerOf Qs ⊔ centerOf Qs')
      rwa [hZcard] at hdvd
    have hle4 : Nat.card ↥(centerOf Qs ⊔ centerOf Qs') ≤ 4 := by
      rw [← hA4]
      exact Subgroup.card_le_of_le hjoinA
    omega
  have hAeq : centerOf Qs ⊔ centerOf Qs' = Qs ⊓ Qs' :=
    Subgroup.eq_of_le_of_card_ge hjoinA (le_of_eq (hA4.trans hjoin4.symm))
  have hA_le_ZQ : Qs ⊓ Qs' ≤ centerOf Qs := by
    rw [← hAeq]
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hjoinA.trans inf_le_left hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hjoinZ hz).2 y (hQsSt hy)
  have hle : Nat.card ↥(Qs ⊓ Qs') ≤ Nat.card ↥(centerOf Qs) :=
    Subgroup.card_le_of_le hA_le_ZQ
  omega

private theorem isMulCommutative_of_card_le_eight {G : Type*} [Group G]
    {J J' Qs Qs' St : Subgroup G} {g : G}
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hQ' : J' ≤ Subgroup.normalizer (Qs' : Set G))
    (hSt : Qs ⊔ Qs' ≤ St) (hStJ : St ≤ J ⊓ J')
    (hi' : Qs'.relIndex St = 2)
    (hgQ : Qs.map (MulAut.conj g).toMonoidHom = Qs')
    (hc : ∀ X : Subgroup G, X ≤ St → J ≤ Subgroup.normalizer (X : Set G) →
      J' ≤ Subgroup.normalizer (X : Set G) → X = ⊥)
    (h8 : Nat.card Qs ≤ 8) (hp : IsPGroup 2 St) [Finite ↥St] :
    IsMulCommutative Qs := by
  have hQsSt : Qs ≤ St := le_sup_left.trans hSt
  have hQs'St : Qs' ≤ St := le_sup_right.trans hSt
  have hSt_le_J : St ≤ J := hStJ.trans inf_le_left
  have hSt_le_J' : St ≤ J' := hStJ.trans inf_le_right
  have hStNQs : St ≤ Subgroup.normalizer (Qs : Set G) := hSt_le_J.trans hQ
  have hStNQs' : St ≤ Subgroup.normalizer (Qs' : Set G) := hSt_le_J'.trans hQ'
  haveI hQsfin : Finite ↥Qs := Finite.of_injective _ (Subgroup.inclusion_injective hQsSt)
  have hQs2 : IsPGroup 2 ↥Qs := hp.to_le hQsSt
  rcases card_eq_one_or_two_or_four_or_eight hQs2 h8 with h1 | h2 | h4 | h8q
  · exact isMulCommutative_of_card_le_two (by omega)
  · exact isMulCommutative_of_card_le_two (by omega)
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
  · by_contra hnon
    have hZcard : Nat.card ↥(centerOf Qs) = 2 := by
      rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Qs.subtype_injective]
      exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_eq_two_of_card_eight
        h8q fun h => hnon (isMulCommutative_iff.mpr h)
    have hcardQ' : Nat.card ↥Qs' = 8 := by
      rw [← hgQ]
      exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans h8q
    have hnon' : ¬ IsMulCommutative Qs' := by
      intro hc'
      apply hnon
      have e : ↥Qs ≃* ↥Qs' := by
        rw [← hgQ]
        exact Subgroup.equivMapOfInjective Qs (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective
      exact e.symm.surjective.isMulCommutative hc'
    haveI hQs'fin : Finite ↥Qs' :=
      Finite.of_injective _ (Subgroup.inclusion_injective hQs'St)
    have hQne : Qs ≠ Qs' := by
      intro heq
      have hbot : Qs = ⊥ := hc Qs hQsSt hQ (by rw [heq]; exact hQ')
      rw [hbot, Subgroup.card_bot] at h8q
      omega
    have hAne : Qs ⊓ Qs' ≠ Qs := by
      intro heq
      have hle : Qs ≤ Qs' := by rw [← heq]; exact inf_le_right
      exact hQne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardQ'.trans h8q.symm)))
    have hZcard' : Nat.card ↥(centerOf Qs') = 2 := by
      rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Qs'.subtype_injective]
      exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_eq_two_of_card_eight
        hcardQ' fun h => hnon' (isMulCommutative_iff.mpr h)
    have hA4 : Nat.card ↥(Qs ⊓ Qs') = 4 := card_inf_eq_four hQsSt hi' h8q hAne
    have hZA : centerOf Qs ≤ Qs ⊓ Qs' := center_le_inf_of_nonabelian h8q hnon hA4
    have hZA' : centerOf Qs' ≤ Qs ⊓ Qs' := by
      have h := center_le_inf_of_nonabelian hcardQ' hnon' (by rw [inf_comm]; exact hA4)
      rwa [inf_comm] at h
    have hZe : centerOf Qs ≤ centerOf St :=
      centerOf_le_centerOf_of_card_eq_two hQsSt hStNQs hZcard
    have hZe' : centerOf Qs' ≤ centerOf St :=
      centerOf_le_centerOf_of_card_eq_two hQs'St hStNQs' hZcard'
    have heq : centerOf Qs = centerOf Qs' :=
      centerOf_eq_centerOf_of_card_eq_two hQsSt hZcard hZcard' hA4 hZA hZA' hZe hZe'
    have hZbot : centerOf Qs = ⊥ := by
      refine hc (centerOf Qs) (hZA.trans inf_le_left |>.trans hQsSt)
        (le_normalizer_centerOf hQ) ?_
      rw [heq]
      exact le_normalizer_centerOf hQ'
    rw [hZbot, Subgroup.card_bot] at hZcard
    omega

private theorem not_le_normalizer_of_centerOf_ne_bot {G : Type*} [Group G]
    {J J' St : Subgroup G} {g : G}
    (hStJ : St ≤ J ⊓ J') (hp : IsPGroup 2 St) (h3 : St.relIndex J = 3)
    (hgJ : J.map (MulAut.conj g).toMonoidHom = J') [Finite ↥J]
    (hc : ∀ X : Subgroup G, X ≤ St → J ≤ Subgroup.normalizer (X : Set G) →
      J' ≤ Subgroup.normalizer (X : Set G) → X = ⊥)
    (hZ : centerOf St ≠ ⊥) :
    ¬ (J ≤ Subgroup.normalizer (St : Set G)) := by
  intro hJN
  have hSt_le_J : St ≤ J := hStJ.trans inf_le_left
  have hSt_le_J' : St ≤ J' := hStJ.trans inf_le_right
  have hcardJ' : Nat.card ↥J' = Nat.card ↥J := by
    rw [← hgJ]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective (K := J)
  have hTnorm : J' ≤ Subgroup.normalizer ((conjSub g St : Subgroup G) : Set G) := by
    rw [← hgJ]
    exact conjSub_le_normalizer hJN
  have hTle : conjSub g St ≤ J' := by
    rw [← hgJ]
    exact Subgroup.map_mono hSt_le_J
  have hTcard : Nat.card ↥(conjSub g St) = Nat.card ↥St :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective (K := St)
  have hTrel : (conjSub g St).relIndex J' = 3 := by
    rw [show conjSub g St = St.map (MulAut.conj g).toMonoidHom from rfl,
      show J' = J.map (MulAut.conj g).toMonoidHom from hgJ.symm]
    rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) St J
      (MulAut.conj g).injective, h3]
  haveI hJ'fin : Finite ↥J' :=
    Nat.finite_of_card_ne_zero (by rw [hcardJ']; exact (Nat.card_pos (α := ↥J)).ne')
  haveI hTfin : Finite ↥(conjSub g St) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hTle)
  have hStT : St = conjSub g St := by
    have hle : St ≤ conjSub g St :=
      CFSG.ComponentClassification.AS76b.Lemma22Full.le_of_isPGroup_of_odd_relIndex
        hTle hTnorm (by rw [hTrel]; decide) hSt_le_J' hp
    exact Subgroup.eq_of_le_of_card_ge hle hTcard.le
  have hJ'N : J' ≤ Subgroup.normalizer (St : Set G) := hStT.symm ▸ hTnorm
  exact hZ (hc (centerOf St) inf_le_left (le_normalizer_centerOf hJN)
    (le_normalizer_centerOf hJ'N))

private theorem isElemAbelian_of_card_eq_four_of_inf_centralizer_eq_bot {G : Type*}
    [Group G] {E : Subgroup G} {d : G} (hE4 : Nat.card ↥E = 4)
    (hdN : d ∈ Subgroup.normalizer (E : Set G))
    (hfix : E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) : IsElemAbelian 2 E := by
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  have hEab : IsMulCommutative ↥E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hE4]; norm_num)
  refine ⟨hEab, fun y hy => ?_⟩
  by_contra h2
  have hyord : orderOf y = 4 := by
    have hdvd : orderOf y ∣ 4 := by
      rw [← hE4]
      exact Subgroup.orderOf_dvd_natCard E hy
    have hdvd' : orderOf y ∣ 2 ^ 2 := by simpa using hdvd
    have hne1 : orderOf y ≠ 1 := by
      intro h
      apply h2
      simp [pow_two, orderOf_eq_one_iff.mp h]
    have hne2 : orderOf y ≠ 2 := by
      intro h
      apply h2
      rw [← h]
      exact pow_orderOf_eq_one y
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    interval_cases k
    · rw [hk] at hne1; norm_num at hne1
    · rw [hk] at hne2; norm_num at hne2
    · rw [hk]; norm_num
  have hwE : MulAut.conj d y ∈ E := by
    have hmem : MulAut.conj d y ∈ E.map (MulAut.conj d).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rwa [show E.map (MulAut.conj d).toMonoidHom = E from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN] at hmem
  have hword : orderOf (MulAut.conj d y) = 4 :=
    (orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective y).trans hyord
  have hEeq' : Subgroup.zpowers y = E := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_
    rw [Nat.card_zpowers, hyord, hE4]
  have hEeq : E = Subgroup.zpowers y := hEeq'.symm
  have hwmem : MulAut.conj d y ∈ Subgroup.zpowers y := by
    rw [← hEeq]; exact hwE
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
  have hsq : (MulAut.conj d y) * (MulAut.conj d y) = y * y := by
    have hy2ord : orderOf (y * y) = 2 := by
      have hpow : y * y = y ^ 2 := (pow_two _).symm
      rw [hpow]
      have hsq1 : (y ^ 2) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one y
        rw [hyord] at h
        rw [← pow_mul]
        norm_num
        exact h
      have hdvd2 : orderOf (y ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq1
      have hne : orderOf (y ^ 2) ≠ 1 := by
        intro h1
        exact h2 (orderOf_eq_one_iff.mp h1)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact absurd h hne
      · exact h
    have hmem2 : (MulAut.conj d y) * (MulAut.conj d y) ∈
        Subgroup.zpowers (y * y) := by
      have hEq : (y ^ k) * (y ^ k) = (y * y) ^ k := ((Commute.refl y).mul_zpow k).symm
      rw [← hk, hEq]
      exact Subgroup.zpow_mem_zpowers _ _
    have hmem1 : y * y ∈ Subgroup.zpowers (y * y) :=
      Subgroup.mem_zpowers _
    have hne1 : y * y ≠ 1 := by
      intro h
      exact h2 (by rw [pow_two]; exact h)
    have hne2 : (MulAut.conj d y) * (MulAut.conj d y) ≠ 1 := by
      intro h
      have hpow : (MulAut.conj d y) ^ 2 = 1 := by rw [pow_two]; exact h
      have hdvd3 : orderOf (MulAut.conj d y) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
      rw [hword] at hdvd3
      norm_num at hdvd3
    exact CFSG.Quasithin.F6.eq_of_card_eq_two
      (by rw [Nat.card_zpowers, hy2ord]) hmem2 hmem1 hne2 hne1
  have hconj : d * (y * y) * d⁻¹ =
      (MulAut.conj d y) * (MulAut.conj d y) := by
    rw [MulAut.conj_apply d y]
    group
  have hfixy : y * y ∈ E ⊓ Subgroup.centralizer ({d} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨E.mul_mem hy hy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : d * (y * y) * d⁻¹ = y * y := hconj.trans hsq
    calc (y * y) * d = (d * (y * y) * d⁻¹) * d := by rw [hcomm]
      _ = d * (y * y) := by group
  rw [hfix] at hfixy
  have h1 : y * y = 1 := by simpa using hfixy
  exact h2 (by rw [pow_two]; exact h1)

private theorem isMulCommutative_of_center_relIndex_le_two {G : Type*} [Group G]
    {S : Subgroup G} [Finite ↥S] (h : (centerOf S).relIndex S ≤ 2) :
    IsMulCommutative ↥S := by
  have hZ : (centerOf S).subgroupOf S = Subgroup.center ↥S := by
    rw [centerOf_eq_map_center]
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  have hidx : (Subgroup.center ↥S).index ≤ 2 := by
    rw [← hZ]
    exact h
  have hdvd : Nat.card (↥S ⧸ Subgroup.center ↥S) ∣ 2 := by
    rw [← Subgroup.index_eq_card]
    have hpos : 0 < (Subgroup.center ↥S).index := Nat.card_pos
    rcases (by omega : (Subgroup.center ↥S).index = 1 ∨
      (Subgroup.center ↥S).index = 2) with h | h <;> simp [h]
  haveI : IsCyclic (↥S ⧸ Subgroup.center ↥S) := isCyclic_of_card_dvd_prime hdvd
  exact isMulCommutative_of_isCyclic_quotient_center_self ↥S

private theorem exists_mul_zpow_of_mem_sup {G : Type*} [Group G] {Q A : Subgroup G} {d : G}
    (hA : A = Q ⊔ Subgroup.zpowers d)
    (hQN : A ≤ Subgroup.normalizer (Q : Set G))
    (hd3 : orderOf d = 3) :
    ∀ a ∈ A, ∃ q ∈ Q, ∃ i : ℤ, (i = 0 ∨ i = 1 ∨ i = 2) ∧ a = q * d ^ i := by
  intro a ha
  have hQN' : Q ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (Q : Set G) := hA ▸ hQN
  haveI hQnA : (Q.subgroupOf A).Normal := by
    rw [hA]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hQN'
  have hsup : Q.subgroupOf A ⊔ (Subgroup.zpowers d).subgroupOf A = ⊤ := by
    rw [hA, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (Q ⊔ Subgroup.zpowers d)
  have hmem : (⟨a, ha⟩ : ↥A) ∈ Q.subgroupOf A ⊔ (Subgroup.zpowers d).subgroupOf A := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨q', hq', z', hz', hqz'⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q.subgroupOf A)
      (t := (Subgroup.zpowers d).subgroupOf A)).mp hmem
  have hq : (q' : A).1 ∈ Q := (Subgroup.mem_subgroupOf).mp hq'
  have hz : (z' : A).1 ∈ Subgroup.zpowers d := (Subgroup.mem_subgroupOf).mp hz'
  have hqz : (q' : A).1 * (z' : A).1 = a := by
    have h := congrArg (fun y : ↥A => (y : G)) hqz'
    simpa using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd3z : d ^ (3 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd3] at h
    simpa using h
  have hred : d ^ k = d ^ (k % 3) := zpow_eq_zpow_emod k hd3z
  have hk0 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have h1 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  exact ⟨(q' : A).1, hq, k % 3, hk0, by rw [← hqz, ← hk, hred]⟩

private theorem exists_mul_of_mem_sup_of_orderOf_eq_three {G : Type*} [Group G]
    {Q : Subgroup G} {d a : G} (hQ2 : IsPGroup 2 Q)
    (hdN : d ∈ Subgroup.normalizer (Q : Set G)) (hd3 : orderOf d = 3)
    (ha : a ∈ Q ⊔ Subgroup.zpowers d) (ha3 : orderOf a = 3) :
    ∃ q ∈ Q, a = q * d ∨ a = q * d⁻¹ := by
  obtain ⟨q, hq, i, hi, rfl⟩ := exists_mul_zpow_of_mem_sup (A := Q ⊔ Subgroup.zpowers d) rfl
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hdN)) hd3 a ha
  have hi0 : i ≠ 0 := by
    intro h0
    exact not_mem_of_isPGroup_two hQ2 ha3 (by rw [h0, zpow_zero, mul_one]; exact hq)
  rcases hi with h0 | h1 | h2
  · exact absurd h0 hi0
  · exact ⟨q, hq, Or.inl (by rw [h1, zpow_one])⟩
  · refine ⟨q, hq, Or.inr ?_⟩
    rw [h2, zpow_two]
    exact congrArg (fun t => q * t) (eq_inv_of_mul_eq_one_left (by
      have h := pow_orderOf_eq_one d
      rw [hd3] at h
      calc d * d * d = d ^ 3 := by rw [pow_three]; group
        _ = 1 := h))

private theorem commutator_zpowers_mul {G : Type*} [Group G] {Q : Subgroup G} {c q : G}
    (hQ : IsMulCommutative Q) (hq : q ∈ Q) (hcN : c ∈ Subgroup.normalizer (Q : Set G))
    (hc3 : orderOf c = 3) (hqc3 : orderOf (q * c) = 3) :
    ⁅Q, Subgroup.zpowers (q * c)⁆ = ⁅Q, Subgroup.zpowers c⁆ := by
  have haN : q * c ∈ Subgroup.normalizer (Q : Set G) :=
    mul_mem (Subgroup.le_normalizer hq) hcN
  obtain ⟨f, -, hfr, hfv⟩ := exists_hom_ker_range haN hqc3 hQ
  obtain ⟨g, -, hgr, hgv⟩ := exists_hom_ker_range hcN hc3 hQ
  have hfg : f = g := by
    refine MonoidHom.ext fun y => Subtype.ext ?_
    rw [hfv, hgv]
    have hcQ : c * (y : G)⁻¹ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hcN (y : G)⁻¹).mp (Q.inv_mem y.2)
    have hqc : q * (c * (y : G)⁻¹ * c⁻¹) = (c * (y : G)⁻¹ * c⁻¹) * q :=
      congrArg Subtype.val (hQ.is_comm.comm ⟨q, hq⟩ ⟨_, hcQ⟩)
    calc (y : G) * (q * c) * (y : G)⁻¹ * (q * c)⁻¹
        = (y : G) * (q * (c * (y : G)⁻¹ * c⁻¹)) * q⁻¹ := by group
      _ = (y : G) * ((c * (y : G)⁻¹ * c⁻¹) * q) * q⁻¹ := by rw [hqc]
      _ = (y : G) * c * (y : G)⁻¹ * c⁻¹ := by group
  have hrange : f.range = g.range := by rw [hfg]
  rw [← hfr, ← hgr]
  exact congrArg (fun H : Subgroup ↥Q => H.map Q.subtype) hrange

private theorem centerOf_card_le_four {G : Type*} [Group G]
    {J Qs St : Subgroup G} {d : G}
    [Finite ↥St]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hQsSt : Qs ≤ St) (hStJ : St ≤ J)
    (hp : IsPGroup 2 ↥St)
    (h3 : St.relIndex J = 3)
    (hdJ : d ∈ J)
    (hSt_not_normal : ¬ (J ≤ Subgroup.normalizer (St : Set G)))
    (hcard_le_two_of_commute : (∀ q ∈ Qs, q * d = d * q) → Nat.card ↥Qs ≤ 2)
    (h8 : Nat.card ↥Qs ≤ 8)
    (hcardSt : Nat.card ↥St = 2 * Nat.card ↥Qs) :
    Nat.card (centerOf St) ≤ 4 := by
  by_contra hle
  push Not at hle
  have hZle : centerOf St ≤ St := inf_le_left
  have hSt16 : Nat.card ↥St ≤ 16 := by rw [hcardSt]; omega
  have hZleSt : Nat.card ↥(centerOf St) ≤ Nat.card ↥St := Subgroup.card_le_of_le hZle
  have hdvd : Nat.card ↥(centerOf St) ∣ Nat.card ↥St := Subgroup.card_dvd_of_le hZle
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hZdvd : Nat.card ↥(centerOf St) ∣ 2 ^ k := hk ▸ hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hZdvd
  have hj3 : 3 ≤ j := by
    by_contra hcon
    have h2 : 2 ^ j ≤ 4 := by
      calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have hZ8 : 8 ≤ Nat.card ↥(centerOf St) := by
    rw [hj]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
  have hrel : (centerOf St).relIndex St ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := centerOf St) (K := St)
    rw [inf_eq_left.mpr hZle] at h
    by_contra hcon
    push Not at hcon
    have h2 : 3 * Nat.card ↥(centerOf St) ≤
        (centerOf St).relIndex St * Nat.card ↥(centerOf St) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hab : IsMulCommutative ↥St := isMulCommutative_of_center_relIndex_le_two hrel
  have hStC : St ≤ Subgroup.centralizer (Qs : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hab).trans
      (Subgroup.centralizer_le hQsSt)
  have hStK : St ≤ J ⊓ Subgroup.centralizer (Qs : Set G) := le_inf hStJ hStC
  have hJNK : J ≤ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer (Qs : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf Subgroup.le_normalizer
      (hQ.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)))
  have hKJ : J ⊓ Subgroup.centralizer (Qs : Set G) ≤ J := inf_le_left
  have hrel_dvd : (J ⊓ Subgroup.centralizer (Qs : Set G)).relIndex J ∣ 3 := by
    have h := Subgroup.relIndex_mul_relIndex (H := St)
      (K := J ⊓ Subgroup.centralizer (Qs : Set G)) (L := J) hStK hKJ
    rw [h3] at h
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hrel_dvd with h1 | h1
  ·
    have hKJeq : J ⊓ Subgroup.centralizer (Qs : Set G) = J :=
      le_antisymm hKJ (Subgroup.relIndex_eq_one.mp h1)
    have hdK : d ∈ J ⊓ Subgroup.centralizer (Qs : Set G) := hKJeq.symm ▸ hdJ
    have hdcent : ∀ q ∈ Qs, q * d = d * q := fun q hq =>
      Subgroup.mem_centralizer_iff.mp hdK.2 q hq
    have hQs2 : Nat.card ↥Qs ≤ 2 := hcard_le_two_of_commute hdcent
    omega
  ·
    have hone : St.relIndex (J ⊓ Subgroup.centralizer (Qs : Set G)) = 1 := by
      have h := Subgroup.relIndex_mul_relIndex (H := St)
        (K := J ⊓ Subgroup.centralizer (Qs : Set G)) (L := J) hStK hKJ
      rw [h1, h3] at h
      omega
    have hKSt : J ⊓ Subgroup.centralizer (Qs : Set G) = St :=
      le_antisymm (Subgroup.relIndex_eq_one.mp hone) hStK
    exact hSt_not_normal (hKSt ▸ hJNK)

private theorem card_inf_centralizer_le_two {G : Type*} [Group G]
    {J Qs : Subgroup G} {d : G}
    [Finite ↥Qs]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hdJ : d ∈ J)
    (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs)
    (h8 : Nat.card ↥Qs ≤ 8)
    (hne : Qs ⊓ Subgroup.centralizer ({d} : Set G) ≠ Qs) :
    Nat.card ↥(Qs ⊓ Subgroup.centralizer (J : Set G)) ≤ 2 := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  have hcard_le_two : Nat.card ↥Qs ≤ 2 → False := by
    intro hcard
    have hab : IsMulCommutative ↥Qs := isMulCommutative_of_card_le_two hcard
    have hfix : ∀ q ∈ Qs, d * q * d⁻¹ = q := by
      intro q hq
      exact mul_inv_eq_of_eq_mul
        (CFSG.AGLEmbeddingD2.Wilson.Coordinator.comm_of_card_le_two hcard hq
          ((Subgroup.mem_normalizer_iff.mp hdN q).mp hq))
    have hle : Qs ≤ Subgroup.centralizer ({d} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hfix q hq
      calc q * d = (d * q * d⁻¹) * d := by rw [h]
        _ = d * q := by group
    exact hne (inf_eq_left.mpr hle)
  have h4or8 : Nat.card ↥Qs = 4 ∨ Nat.card ↥Qs = 8 := by
    rcases card_eq_one_or_two_or_four_or_eight hQs2 h8 with h1 | h2 | h4 | h8'
    · exact absurd (by omega : Nat.card ↥Qs ≤ 2) hcard_le_two
    · exact absurd (by omega : Nat.card ↥Qs ≤ 2) hcard_le_two
    · exact Or.inl h4
    · exact Or.inr h8'

  haveI hCfin : Finite ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective
      (fun a : ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) => (⟨a.1, a.2.1⟩ : ↥Qs))
      (fun a b h => Subtype.ext (congrArg (fun y : ↥Qs => (y : G)) h))
  have hQ4 := four_mul_card_centralizer hdN hd3 h4or8 hne
  have hCcard : Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 := by
    have hpos : 0 < Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) := Nat.card_pos
    omega
  have hle : Qs ⊓ Subgroup.centralizer (J : Set G) ≤
      Qs ⊓ Subgroup.centralizer ({d} : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdJ))
  exact (Subgroup.card_le_of_le hle).trans hCcard

private theorem isElemAbelian_of_card_le_two {G : Type*} [Group G] {C : Subgroup G}
    [Finite ↥C] (hC : Nat.card ↥C ≤ 2) : IsElemAbelian 2 C := by
  refine ⟨isMulCommutative_of_card_le_two hC, fun x hx => ?_⟩
  have hdvd : orderOf x ∣ Nat.card ↥C := Subgroup.orderOf_dvd_natCard C hx
  have hcard : Nat.card ↥C = 1 ∨ Nat.card ↥C = 2 := by
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    omega
  have h2 : orderOf x ∣ 2 := by
    rcases hcard with h | h
    · rw [h] at hdvd
      rw [Nat.dvd_one.mp hdvd]
      exact one_dvd 2
    · rwa [h] at hdvd
  exact orderOf_dvd_iff_pow_eq_one.mp h2

private theorem isElemAbelian_and_commutator {G : Type*} [Group G]
    {J Qs : Subgroup G} {d : G}
    [Finite ↥Qs]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (habel : IsMulCommutative Qs)
    (hQs2 : IsPGroup 2 ↥Qs)
    (h4 : 4 ≤ Nat.card ↥Qs) (h8 : Nat.card ↥Qs ≤ 8)
    (hne : Qs ⊓ Subgroup.centralizer ({d} : Set G) ≠ Qs) :
    IsElemAbelian 2 Qs ∧ Nat.card ↥⁅Qs, Subgroup.zpowers d⁆ = 4 ∧
      ⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  have hE_le : ⁅Qs, Subgroup.zpowers d⁆ ≤ Qs :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers d) (K := Qs)).mp
      (Subgroup.zpowers_le.mpr hdN)
  haveI hCfin : Finite ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have h4or8 : Nat.card ↥Qs = 4 ∨ Nat.card ↥Qs = 8 := by
    rcases card_eq_one_or_two_or_four_or_eight hQs2 h8 with h1 | h2 | h4' | h8'
    · omega
    · omega
    · exact Or.inl h4'
    · exact Or.inr h8'

  have hQ4 := four_mul_card_centralizer hdN hd3 h4or8 hne
  have hCcard : Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 := by
    have hpos : 0 < Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) := Nat.card_pos
    omega
  have hE4 : Nat.card ↥⁅Qs, Subgroup.zpowers d⁆ = 4 :=
    commutator_card hdN hd3 habel hQ4
  have hCE : (Qs ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ ⁅Qs, Subgroup.zpowers d⁆ = ⊥ :=
    inf_centralizer_commutator hdN hd3 habel hQs2
  have hCE' : ⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ (Qs ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ ⁅Qs, Subgroup.zpowers d⁆ :=
      ⟨⟨hE_le hx.1, hx.2⟩, hx.1⟩
    rw [hCE] at h1
    simpa using h1
  have hEelem : IsElemAbelian 2 ⁅Qs, Subgroup.zpowers d⁆ :=
    isElemAbelian_of_card_eq_four_of_inf_centralizer_eq_bot hE4
      (Subgroup.normalizer_commutator_ge_right Qs (Subgroup.zpowers d)
        (Subgroup.mem_zpowers d)) hCE'
  have hCelem : IsElemAbelian 2 (Qs ⊓ Subgroup.centralizer ({d} : Set G)) :=
    isElemAbelian_of_card_le_two hCcard
  have hcommCE : ∀ a ∈ (Qs ⊓ Subgroup.centralizer ({d} : Set G)),
      ∀ b ∈ ⁅Qs, Subgroup.zpowers d⁆, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (habel.is_comm.comm ⟨a, ha.1⟩ ⟨b, hE_le hb⟩)
  have hnormal : ⁅Qs, Subgroup.zpowers d⁆ ≤
      Subgroup.normalizer ((Qs ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := by
    have hQsc : Qs ≤ Subgroup.centralizer (Qs : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr habel
    have h1 : Qs ≤ Subgroup.centralizer ((Qs ⊓ Subgroup.centralizer ({d} : Set G) :
        Subgroup G) : Set G) :=
      hQsc.trans (Subgroup.centralizer_le (by intro x hx; exact hx.1))
    exact hE_le.trans (h1.trans (Subgroup.centralizer_le_normalizer _))
  have hsup : Qs ⊓ Subgroup.centralizer ({d} : Set G) ⊔ ⁅Qs, Subgroup.zpowers d⁆ = Qs := by
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Qs ⊓ Subgroup.centralizer ({d} : Set G)) ⁅Qs, Subgroup.zpowers d⁆ hnormal
      (disjoint_iff.mpr hCE)
    have hle : (Qs ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ ⁅Qs, Subgroup.zpowers d⁆ ≤ Qs :=
      sup_le inf_le_left hE_le
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, hE4, hQ4, mul_comm]
  exact ⟨by rw [← hsup]; exact IsElemAbelian.sup_of_commute hCelem hEelem hcommCE, hE4, hCE'⟩

private theorem le_normalizer_sup_zpowers {G : Type*} [Group G]
    {J Qs : Subgroup G} {d : G}
    [Finite ↥Qs]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hQsJ : Qs ≤ J) (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs)
    (hcardJ : Nat.card ↥J = 6 * Nat.card ↥Qs) :
    J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  have hdisj : Disjoint Qs (Subgroup.zpowers d) := by
    obtain ⟨k, hk⟩ := hQs2.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk, Nat.card_zpowers, hd3]
    exact Nat.Coprime.pow_left k (by norm_num)
  have hAJ : Qs ⊔ Subgroup.zpowers d ≤ J :=
    sup_le hQsJ (Subgroup.zpowers_le.mpr hdJ)
  have hcardA : Nat.card ↥(Qs ⊔ Subgroup.zpowers d) = 3 * Nat.card ↥Qs := by
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      Qs (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdN) hdisj
    rw [hcard, Nat.card_zpowers, hd3, mul_comm]
  have hArelJ : (Qs ⊔ Subgroup.zpowers d).relIndex J = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Qs ⊔ Subgroup.zpowers d) (K := J)
    rw [inf_eq_left.mpr hAJ, hcardA, hcardJ] at h
    have h' : (Qs ⊔ Subgroup.zpowers d).relIndex J * (3 * Nat.card ↥Qs) =
        2 * (3 * Nat.card ↥Qs) := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by norm_num) Nat.card_pos) h'
  have hAnormal : ((Qs ⊔ Subgroup.zpowers d).subgroupOf J).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    change (Qs ⊔ Subgroup.zpowers d).relIndex J = 2
    exact hArelJ
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAJ).mp hAnormal

private theorem inf_centralizer_singleton_eq_inf_centralizer {G : Type*} [Group G]
    {J Qs : Subgroup G} {d : G}
    [Finite ↥Qs]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs) (habel : IsMulCommutative Qs)
    (hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    (hCcard : Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2) :
    Qs ⊓ Subgroup.centralizer ({d} : Set G) = Qs ⊓ Subgroup.centralizer (J : Set G) := by
  haveI hCfin : Finite ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hyQ : j * x * j⁻¹ ∈ Qs :=
      (Subgroup.mem_normalizer_iff.mp (hQ hj) x).mp hxQ
    have hyC : j * x * j⁻¹ ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbA : j⁻¹ * d * j ∈ Qs ⊔ Subgroup.zpowers d := by
        have h := (Subgroup.mem_normalizer_iff.mp (hAJN (J.inv_mem hj)) d).mp
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
        simpa using h
      have hb3 : orderOf (j⁻¹ * d * j) = 3 := by
        have h1 : j⁻¹ * d * j = MulAut.conj j⁻¹ d := by
          rw [MulAut.conj_apply]
          group
        rw [h1]
        exact (orderOf_injective (MulAut.conj j⁻¹).toMonoidHom
          (MulAut.conj j⁻¹).injective d).trans hd3
      set a : G := j⁻¹ * d * j with ha
      have hbA' : a ∈ Qs ⊔ Subgroup.zpowers d := by rw [ha]; exact hbA
      have hb3' : orderOf a = 3 := by rw [ha]; exact hb3
      obtain ⟨q, hq, hbi⟩ :=
        exists_mul_of_mem_sup_of_orderOf_eq_three (a := a) hQs2 (hQ hdJ) hd3 hbA' hb3'
      have hxq : Commute x q := show Commute x q from
        congrArg Subtype.val (habel.is_comm.comm ⟨x, hxQ⟩ ⟨q, hq⟩)
      have hxd : Commute x d := show Commute x d from
        Subgroup.mem_centralizer_singleton_iff.mp hxC
      have h1 : x * a = a * x :=
        hbi.elim
          (fun hbi => (congrArg (fun t => x * t) hbi).trans
            ((hxq.mul_right hxd).eq.trans (congrArg (fun t => t * x) hbi).symm))
          (fun hbi => (congrArg (fun t => x * t) hbi).trans
            ((hxq.mul_right hxd.inv_right).eq.trans
              (congrArg (fun t => t * x) hbi).symm))
      have h2 : (j * x * j⁻¹) * d = d * (j * x * j⁻¹) := by
        have h := congrArg (fun y => j * y * j⁻¹) h1
        simp only [ha] at h
        simpa [mul_assoc] using h
      exact h2
    exact CFSG.AGLEmbeddingD2.Wilson.Coordinator.comm_of_card_le_two hCcard
      (Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩) (Subgroup.mem_inf.mpr ⟨hyQ, hyC⟩)
  · exact le_inf inf_le_left (inf_le_right.trans
      (Subgroup.centralizer_le (s := ({d} : Set G)) (t := (J : Set G))
        (Set.singleton_subset_iff.mpr hdJ)))

private theorem le_normalizer_commutator_zpowers {G : Type*} [Group G]
    {J Qs : Subgroup G} {d : G}
    [Finite ↥Qs]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs)
    (habel : IsMulCommutative Qs)
    (hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G)) :
    J ≤ Subgroup.normalizer ((⁅Qs, Subgroup.zpowers d⁆ : Subgroup G) : Set G) := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  intro j hj
  have hjA : j * d * j⁻¹ ∈ Qs ⊔ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (hAJN hj) d).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have ha3 : orderOf (j * d * j⁻¹) = 3 := by
    have h1 : j * d * j⁻¹ = MulAut.conj j d := by rw [MulAut.conj_apply]
    rw [h1]
    exact (orderOf_injective (MulAut.conj j).toMonoidHom (MulAut.conj j).injective d).trans hd3
  have hcomm : ⁅Qs, Subgroup.zpowers (j * d * j⁻¹)⁆ = ⁅Qs, Subgroup.zpowers d⁆ := by
    obtain ⟨q, hq, hqi | hqi⟩ :=
      exists_mul_of_mem_sup_of_orderOf_eq_three hQs2 hdN hd3 hjA ha3
    · rw [hqi]
      exact commutator_zpowers_mul habel hq hdN hd3 (by rw [← hqi]; exact ha3)
    · rw [hqi]
      rw [commutator_zpowers_mul habel hq (inv_mem hdN) ((orderOf_inv d).trans hd3)
        (by rw [← hqi]; exact ha3), Subgroup.zpowers_inv]
  have hconjz : conjSub j (Subgroup.zpowers d) = Subgroup.zpowers (j * d * j⁻¹) := by
    show (Subgroup.zpowers d).map (MulAut.conj j).toMonoidHom = _
    rw [MonoidHom.map_zpowers]
    rfl
  have hconjE : conjSub j ⁅Qs, Subgroup.zpowers d⁆ = ⁅Qs, Subgroup.zpowers d⁆ := by
    rw [← conjSub_commutator, show conjSub j Qs = Qs from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ hj), hconjz, hcomm]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjE

private theorem exists_conj_eq_mul_inv {G : Type*} [Group G] {J Qs St : Subgroup G}
    {d t : G} (hQ : J ≤ Subgroup.normalizer (Qs : Set G)) (hQsSt : Qs ≤ St)
    (hStJ : St ≤ J) (hdJ : d ∈ J) (hd3 : orderOf d = 3) (hQs2 : IsPGroup 2 ↥Qs)
    (hQsrelSt : Qs.relIndex St = 2) (hJ_eq : J = St ⊔ Subgroup.zpowers d)
    (hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    (hSt_not_normal : ¬ (J ≤ Subgroup.normalizer (St : Set G)))
    (htSt : t ∈ St) (htQ : t ∉ Qs) : ∃ q ∈ Qs, t * d * t⁻¹ = q * d⁻¹ := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  have htJ : t ∈ J := hStJ htSt
  have hSt_eq : St = Qs ⊔ Subgroup.zpowers t := by
    have hle : Qs ⊔ Subgroup.zpowers t ≤ St :=
      sup_le hQsSt (Subgroup.zpowers_le.mpr htSt)
    have hdiv : Qs.relIndex (Qs ⊔ Subgroup.zpowers t) ∣ 2 := by
      have h := Subgroup.relIndex_mul_relIndex (H := Qs)
        (K := Qs ⊔ Subgroup.zpowers t) (L := St) le_sup_left hle
      rw [hQsrelSt] at h
      exact ⟨_, h.symm⟩
    have hne1 : Qs.relIndex (Qs ⊔ Subgroup.zpowers t) ≠ 1 := by
      intro h1
      exact htQ ((Subgroup.relIndex_eq_one.mp h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
    have h2' : Qs.relIndex (Qs ⊔ Subgroup.zpowers t) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
      · exact absurd h hne1
      · exact h
    have hone : (Qs ⊔ Subgroup.zpowers t).relIndex St = 1 := by
      have h := Subgroup.relIndex_mul_relIndex (H := Qs)
        (K := Qs ⊔ Subgroup.zpowers t) (L := St) le_sup_left hle
      rw [h2', hQsrelSt] at h
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle
  have htdtA : t * d * t⁻¹ ∈ Qs ⊔ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (hAJN htJ) d).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have htdt3 : orderOf (t * d * t⁻¹) = 3 := by
    have h1 : t * d * t⁻¹ = MulAut.conj t d := by
      rw [MulAut.conj_apply]
    rw [h1]
    exact (orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective d).trans hd3
  obtain ⟨q, hq, hqi | hqi⟩ :=
    exists_mul_of_mem_sup_of_orderOf_eq_three hQs2 hdN hd3 htdtA htdt3
  · exfalso
    have ha : t * d * t⁻¹ = q * d := hqi
    have hdt : d * t * d⁻¹ = q⁻¹ * t := by
      have h1' : t * d = q * d * t := by
        calc t * d = (t * d * t⁻¹) * t := by group
          _ = (q * d) * t := by rw [ha]
      calc d * t * d⁻¹ = q⁻¹ * (q * (d * t * d⁻¹)) := by group
        _ = q⁻¹ * (q * d * t * d⁻¹) := by group
        _ = q⁻¹ * (t * d * d⁻¹) := by rw [← h1']
        _ = q⁻¹ * t := by group
    have hdSt : d ∈ Subgroup.normalizer (St : Set G) := by
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      have h1 : conjSub d Qs = Qs := Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN
      have h2 : conjSub d (Subgroup.zpowers t) = Subgroup.zpowers (d * t * d⁻¹) := by
        show (Subgroup.zpowers t).map (MulAut.conj d).toMonoidHom = _
        rw [MonoidHom.map_zpowers]
        rfl
      have hle : conjSub d St ≤ St := by
        rw [hSt_eq, conjSub_sup, h1, h2]
        refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
        rw [hdt]
        exact Subgroup.mul_mem_sup (Qs.inv_mem hq) (Subgroup.mem_zpowers t)
      have hge : St ≤ conjSub d St := by
        rw [hSt_eq, conjSub_sup, h1, h2]
        refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
        rw [hdt]
        have hmem : q * (q⁻¹ * t) ∈ Qs ⊔ Subgroup.zpowers (q⁻¹ * t) :=
          (Qs ⊔ Subgroup.zpowers (q⁻¹ * t)).mul_mem (Subgroup.mem_sup_left hq)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers (q⁻¹ * t)))
        rwa [show q * (q⁻¹ * t) = t by group] at hmem
      exact le_antisymm hle hge
    have hJN : J ≤ Subgroup.normalizer (St : Set G) := by
      rw [hJ_eq]
      exact sup_le (Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hdSt)
    exact hSt_not_normal hJN
  · exact ⟨q, hq, hqi⟩

private theorem inf_centralizer_ne_of_conj_eq_mul_inv {G : Type*} [Group G]
    {Qs : Subgroup G} {d t q : G}
    (hdN : d ∈ Subgroup.normalizer (Qs : Set G))
    (hd3 : orderOf d = 3) (habel : IsMulCommutative Qs) (hq : q ∈ Qs)
    (htdt : t * d * t⁻¹ = q * d⁻¹) (hE4 : Nat.card ↥⁅Qs, Subgroup.zpowers d⁆ = 4)
    (hCE : ⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) :
    ⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({t} : Set G) ≠
      ⁅Qs, Subgroup.zpowers d⁆ := by
  let E : Subgroup G := ⁅Qs, Subgroup.zpowers d⁆
  let F : Subgroup G := E ⊓ Subgroup.centralizer ({t} : Set G)
  change F ≠ E
  have hE_le : E ≤ Qs :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers d) (K := Qs)).mp
      (Subgroup.zpowers_le.mpr hdN)
  have hdE : d ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.normalizer_commutator_ge_right Qs (Subgroup.zpowers d) (Subgroup.mem_zpowers d)
  haveI hEfin : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  have hE4' : Nat.card ↥E = 4 := hE4
  intro hEq
  have hEcent : E ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [← hEq]
    exact inf_le_right
  have hEd : E ≤ Subgroup.centralizer ({d} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hte : t * e * t⁻¹ = e := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hEcent he)
      calc t * e * t⁻¹ = (e * t) * t⁻¹ := by rw [← h]
        _ = e := by group
    have hde : d * e * d⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hdE e).mp he
    have h1 : t * (d * e * d⁻¹) * t⁻¹ = d * e * d⁻¹ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hEcent hde)
      calc t * (d * e * d⁻¹) * t⁻¹ = ((d * e * d⁻¹) * t) * t⁻¹ := by rw [← h]
        _ = d * e * d⁻¹ := by group
    have h2 : t * (d * e * d⁻¹) * t⁻¹ = (q * d⁻¹) * e * (q * d⁻¹)⁻¹ := by
      calc t * (d * e * d⁻¹) * t⁻¹
          = (t * d * t⁻¹) * (t * e * t⁻¹) * (t * d * t⁻¹)⁻¹ := by group
        _ = (q * d⁻¹) * e * (q * d⁻¹)⁻¹ := by rw [htdt, hte]
    have hqde : d⁻¹ * e * d ∈ Qs :=
      (Subgroup.mem_normalizer_iff''.mp hdN e).mp (hE_le he)
    have hqe : q * (d⁻¹ * e * d) = (d⁻¹ * e * d) * q :=
      congrArg Subtype.val (habel.is_comm.comm ⟨q, hq⟩ ⟨_, hqde⟩)
    have h3 : (q * d⁻¹) * e * (q * d⁻¹)⁻¹ = d⁻¹ * e * d := by
      calc (q * d⁻¹) * e * (q * d⁻¹)⁻¹ = q * (d⁻¹ * e * d) * q⁻¹ := by group
        _ = (d⁻¹ * e * d) * q * q⁻¹ := by rw [hqe]
        _ = d⁻¹ * e * d := by group
    have h4 : d * e * d⁻¹ = d⁻¹ * e * d := h1.symm.trans (h2.trans h3)
    have hd2 : d * d = d⁻¹ := by
      have h3z : d ^ 3 = 1 := by
        have h := pow_orderOf_eq_one d
        rwa [hd3] at h
      have h33 : d * d * d = 1 := by
        calc d * d * d = d * (d * d) := by rw [mul_assoc]
          _ = d ^ 3 := (pow_three d).symm
          _ = 1 := h3z
      calc d * d = (d * d * d) * d⁻¹ := by group
        _ = 1 * d⁻¹ := by rw [h33]
        _ = d⁻¹ := one_mul _
    have h5 : d * d * e * (d * d)⁻¹ = e := by
      calc d * d * e * (d * d)⁻¹ = d * (d * e * d⁻¹) * d⁻¹ := by group
        _ = d * (d⁻¹ * e * d) * d⁻¹ := by rw [h4]
        _ = e := by group
    have h6 : d * d * e = e * (d * d) := by
      calc d * d * e = (d * d * e * (d * d)⁻¹) * (d * d) := by group
        _ = e * (d * d) := by rw [h5]
    rw [hd2] at h6
    have hcd : Commute d e := by
      simpa using (Commute.inv_left (show Commute (d⁻¹) e from h6))
    simpa using hcd.symm.eq
  have hbot : E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := hCE
  have hEeq : E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ E ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hx, hEd hx⟩
    rw [hbot] at hx'
    simpa using hx'
  rw [hEeq, Subgroup.card_bot] at hE4'
  omega

private theorem card_inf_centralizer_singleton_eq_two {G : Type*} [Group G]
    {Qs E : Subgroup G} {t : G} (habel : IsMulCommutative Qs) (hE_le : E ≤ Qs)
    (hE4 : Nat.card ↥E = 4) (hEelem : IsElemAbelian 2 E)
    (htN : t ∈ Subgroup.normalizer (E : Set G)) (ht2 : t ^ 2 ∈ Qs)
    (hFE : E ⊓ Subgroup.centralizer ({t} : Set G) ≠ E) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({t} : Set G)) = 2 := by
  let F : Subgroup G := E ⊓ Subgroup.centralizer ({t} : Set G)
  change Nat.card ↥F = 2
  haveI hEfin : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  haveI hFfin : Finite ↥F :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hE4' : Nat.card ↥E = 4 := hE4
  have hEelem' : IsElemAbelian 2 E := hEelem
  have hex : ∃ e ∈ E, t * e * t⁻¹ ≠ e := by
    by_contra h
    push Not at h
    apply hFE
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := h e he
    calc e * t = (t * e * t⁻¹) * t := by rw [h']
      _ = t * e := by group
  obtain ⟨e, he, hene⟩ := hex
  have hteE : t * e * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp htN e).mp he
  have hxE : e * (t * e * t⁻¹) ∈ E := E.mul_mem he hteE
  have hx1 : e * (t * e * t⁻¹) ≠ 1 := by
    intro h
    apply hene
    have h2 : t * e * t⁻¹ = e⁻¹ := by
      calc t * e * t⁻¹ = e⁻¹ * (e * (t * e * t⁻¹)) := by group
        _ = e⁻¹ * 1 := by rw [h]
        _ = e⁻¹ := mul_one _
    rw [h2]
    have he2 : e * e = 1 := by
      have h := hEelem'.2 e he
      rwa [pow_two] at h
    calc e⁻¹ = e⁻¹ * 1 := by rw [mul_one]
      _ = e⁻¹ * (e * e) := by rw [he2]
      _ = e := by group
  have ht2e : t ^ 2 * e * (t ^ 2)⁻¹ = e := by
    have hcomm : t ^ 2 * e = e * (t ^ 2) :=
      congrArg Subtype.val (habel.is_comm.comm ⟨_, ht2⟩ ⟨e, hE_le he⟩)
    calc t ^ 2 * e * (t ^ 2)⁻¹ = (e * t ^ 2) * (t ^ 2)⁻¹ := by rw [hcomm]
      _ = e := by group
  have hfix : t * (e * (t * e * t⁻¹)) * t⁻¹ = e * (t * e * t⁻¹) := by
    calc t * (e * (t * e * t⁻¹)) * t⁻¹
        = (t * e * t⁻¹) * (t ^ 2 * e * (t ^ 2)⁻¹) := by group
      _ = (t * e * t⁻¹) * e := by rw [ht2e]
      _ = e * (t * e * t⁻¹) :=
          congrArg Subtype.val (hEelem'.1.is_comm.comm ⟨_, hteE⟩ ⟨_, he⟩)
  have hxF : e * (t * e * t⁻¹) ∈ F := by
    refine Subgroup.mem_inf.mpr ⟨hxE, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (e * (t * e * t⁻¹)) * t
        = (t * (e * (t * e * t⁻¹)) * t⁻¹) * t := by
          conv_lhs => rw [← hfix]
      _ = t * (e * (t * e * t⁻¹)) := by group
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxF
    exact hx1 (by simpa using hxF)
  have hFdiv : Nat.card ↥F ∣ 4 := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_eq_left.mpr inf_le_left, hE4'] at h
    exact ⟨F.relIndex E, by rw [mul_comm]; exact h.symm⟩
  have hF1 : Nat.card ↥F ≠ 1 := by
    intro h1
    exact hFne (Subgroup.card_eq_one.mp h1)
  have hF4 : Nat.card ↥F ≠ 4 := by
    intro h4
    exact hFE (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hE4', h4]))
  have hFdiv' : Nat.card ↥F ∣ 2 ^ 2 := by simpa using hFdiv
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp hFdiv'
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with h0 | h1 | h2
  · rw [hk, h0] at hF1
    norm_num at hF1
  · rw [hk, h1]
    norm_num
  · rw [hk, h2] at hF4
    norm_num at hF4

private theorem card_commutator_inf_centralizer {G : Type*} [Group G]
    {J Qs St : Subgroup G} {d t : G}
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hQsSt : Qs ≤ St) (hStJ : St ≤ J)
    (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs)
    (habel : IsMulCommutative Qs)
    (hQsrelSt : Qs.relIndex St = 2)
    (hJ_eq : J = St ⊔ Subgroup.zpowers d)
    (hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    (hSt_not_normal : ¬ (J ≤ Subgroup.normalizer (St : Set G)))
    (hE4 : Nat.card ↥⁅Qs, Subgroup.zpowers d⁆ = 4)
    (hCE : ⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥)
    (hJE : J ≤ Subgroup.normalizer ((⁅Qs, Subgroup.zpowers d⁆ : Subgroup G) : Set G))
    (hEelem : IsElemAbelian 2 ⁅Qs, Subgroup.zpowers d⁆)
    (htSt : t ∈ St) (htQ : t ∉ Qs) :
    Nat.card ↥(⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({t} : Set G)) = 2 := by
  have hdN : d ∈ Subgroup.normalizer (Qs : Set G) := hQ hdJ
  have hE_le : ⁅Qs, Subgroup.zpowers d⁆ ≤ Qs :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers d) (K := Qs)).mp
      (Subgroup.zpowers_le.mpr hdN)
  have ht2 : t ^ 2 ∈ Qs := by
    have h := Subgroup.sq_mem_of_index_two (H := Qs.subgroupOf St) hQsrelSt
      (⟨t, htSt⟩ : ↥St)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨q, hq, htdt⟩ :=
    exists_conj_eq_mul_inv hQ hQsSt hStJ hdJ hd3 hQs2 hQsrelSt hJ_eq hAJN hSt_not_normal
      htSt htQ
  exact card_inf_centralizer_singleton_eq_two habel hE_le hE4 hEelem (hJE (hStJ htSt)) ht2
    (inf_centralizer_ne_of_conj_eq_mul_inv hdN hd3 habel hq htdt hE4 hCE)

private theorem eq_sup_zpowers_conj {G : Type*} [Group G] {J J' St : Subgroup G} {d g : G}
    (hSt_le_J' : St ≤ J') (hp : IsPGroup 2 St)
    (hgJ : J.map (MulAut.conj g).toMonoidHom = J') (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hcardStJ' : St.relIndex J' = 3) : J' = St ⊔ Subgroup.zpowers (g * d * g⁻¹) := by
  set d' : G := g * d * g⁻¹ with hd'def
  have hd'J' : d' ∈ J' := by
    rw [← hgJ]
    exact Subgroup.mem_map.mpr ⟨d, hdJ, rfl⟩
  have hd'3 : orderOf d' = 3 := by
    have h1 : d' = (MulAut.conj g).toMonoidHom d := by rw [hd'def]; rfl
    rw [h1, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hd3]
  have hd'notSt : d' ∉ St := not_mem_of_isPGroup_two hp hd'3
  have hKle : St ⊔ Subgroup.zpowers d' ≤ J' :=
    sup_le hSt_le_J' (Subgroup.zpowers_le.mpr hd'J')
  have htower := Subgroup.relIndex_mul_relIndex (H := St) (K := St ⊔ Subgroup.zpowers d')
    (L := J') le_sup_left hKle
  have hdvd : St.relIndex (St ⊔ Subgroup.zpowers d') ∣ 3 :=
    ⟨_, (htower.trans hcardStJ').symm⟩
  have hne1 : St.relIndex (St ⊔ Subgroup.zpowers d') ≠ 1 := by
    intro h1
    have hle : St ⊔ Subgroup.zpowers d' ≤ St := Subgroup.relIndex_eq_one.mp h1
    exact hd'notSt (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers d')))
  have h3' : St.relIndex (St ⊔ Subgroup.zpowers d') = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hone : (St ⊔ Subgroup.zpowers d').relIndex J' = 1 := by
    have h := htower
    rw [h3', hcardStJ'] at h
    omega
  exact (le_antisymm hKle (Subgroup.relIndex_eq_one.mp hone)).symm

private theorem card_le_two_of_commute {G : Type*} [Group G]
    {J J' Qs Qs' St : Subgroup G} {d g : G} (hQsSt : Qs ≤ St)
    (hi' : Qs'.relIndex St = 2) (hStNQs : St ≤ Subgroup.normalizer (Qs : Set G))
    (hStNQs' : St ≤ Subgroup.normalizer (Qs' : Set G))
    (hgQ : Qs.map (MulAut.conj g).toMonoidHom = Qs')
    (hJ_eq : J = St ⊔ Subgroup.zpowers d)
    (hJ'eq : J' = St ⊔ Subgroup.zpowers (g * d * g⁻¹))
    (hc : ∀ X : Subgroup G, X ≤ St → J ≤ Subgroup.normalizer (X : Set G) →
      J' ≤ Subgroup.normalizer (X : Set G) → X = ⊥)
    (hcomm : ∀ q ∈ Qs, q * d = d * q) : Nat.card ↥Qs ≤ 2 := by
  have hStNA : St ≤ Subgroup.normalizer ((Qs ⊓ Qs' : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hStNQs hStNQs'
  have hd_cent : d ∈ Subgroup.centralizer ((Qs ⊓ Qs' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨haQ, -⟩
    exact hcomm a haQ
  have hd'n : g * d * g⁻¹ ∈ Subgroup.centralizer ((Qs ⊓ Qs' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨haQ, haQ'⟩
    have hga : g⁻¹ * a * g ∈ Qs := by
      have hmem : a ∈ conjSub g Qs := by
        rw [show conjSub g Qs = Qs.map (MulAut.conj g).toMonoidHom from rfl, hgQ]
        exact haQ'
      rwa [mem_conjSub] at hmem
    have hconj : (g * d * g⁻¹) * a * (g * d * g⁻¹)⁻¹ = a := by
      have hc' := hcomm (g⁻¹ * a * g) hga
      calc g * d * g⁻¹ * a * (g * d * g⁻¹)⁻¹
          = g * (d * (g⁻¹ * a * g) * d⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [← hc']; group
        _ = a := by group
    have h2 : (g * d * g⁻¹) * a = a * (g * d * g⁻¹) := by
      calc (g * d * g⁻¹) * a =
          ((g * d * g⁻¹) * a * (g * d * g⁻¹)⁻¹) * (g * d * g⁻¹) := by group
        _ = a * (g * d * g⁻¹) := by rw [hconj]
    exact h2.symm
  have hA_bot : Qs ⊓ Qs' = ⊥ := by
    refine hc (Qs ⊓ Qs') (inf_le_left.trans hQsSt) ?_ ?_
    · rw [hJ_eq]
      exact sup_le hStNA (Subgroup.zpowers_le.mpr
        (Subgroup.centralizer_le_normalizer _ hd_cent))
    · rw [hJ'eq]
      exact sup_le hStNA (Subgroup.zpowers_le.mpr
        (Subgroup.centralizer_le_normalizer _ hd'n))
  exact card_le_two_of_inf_eq_bot hQsSt hi' hA_bot

private theorem isElemAbelian_and_commutator_of_four_le_card {G : Type*} [Group G]
    {J Qs St : Subgroup G} {d : G}
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G))
    (hQsSt : Qs ≤ St) (hStJ : St ≤ J)
    (hdJ : d ∈ J) (hd3 : orderOf d = 3)
    (hQs2 : IsPGroup 2 ↥Qs) (habel : IsMulCommutative Qs)
    (hQsrelSt : Qs.relIndex St = 2)
    (hJ_eq : J = St ⊔ Subgroup.zpowers d)
    (hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G) : Set G))
    (hSt_not_normal : ¬ (J ≤ Subgroup.normalizer (St : Set G)))
    (h8 : Nat.card ↥Qs ≤ 8) (h4 : 4 ≤ Nat.card ↥Qs)
    (hne : Qs ⊓ Subgroup.centralizer ({d} : Set G) ≠ Qs)
    (hcardJ6 : Nat.card ↥J = 6 * Nat.card ↥Qs) :
    IsElemAbelian 2 Qs ∧ Nat.card ↥⁅Qs, Subgroup.zpowers d⁆ = 4 ∧
      Qs ⊓ Subgroup.centralizer ({d} : Set G) = Qs ⊓ Subgroup.centralizer (J : Set G) ∧
      J ≤ Subgroup.normalizer ((⁅Qs, Subgroup.zpowers d⁆ : Subgroup G) : Set G) ∧
      ∀ t ∈ St, t ∉ Qs →
        Nat.card ↥(⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({t} : Set G)) = 2 := by
  haveI hQsfin : Finite ↥Qs := Nat.finite_of_card_ne_zero (by omega)
  haveI hStfin : Finite ↥St := by
    have hQssub : Finite ↥(Qs.subgroupOf St) :=
      Finite.of_injective (Subgroup.subgroupOfEquivOfLe hQsSt)
        (Subgroup.subgroupOfEquivOfLe hQsSt).injective
    haveI : (Qs.subgroupOf St).FiniteIndex :=
      ⟨by
        have hidx : (Qs.subgroupOf St).index = 2 := hQsrelSt
        rw [hidx]; norm_num⟩
    exact (Subgroup.finite_iff_finite_and_finiteIndex (Qs.subgroupOf St)).mpr
      ⟨hQssub, inferInstance⟩
  obtain ⟨hEelemQs, hE4, hCE⟩ :=
    isElemAbelian_and_commutator hQ hdJ hd3 habel hQs2 h4 h8 hne
  have h4or8 : Nat.card ↥Qs = 4 ∨ Nat.card ↥Qs = 8 := by
    rcases card_eq_one_or_two_or_four_or_eight hQs2 h8 with h1 | h2 | h4' | h8'
    · omega
    · omega
    · exact Or.inl h4'
    · exact Or.inr h8'
  have hCcard : Nat.card ↥(Qs ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 := by
    have hQ4 := four_mul_card_centralizer (hQ hdJ) hd3 h4or8 hne
    omega
  have hJE : J ≤ Subgroup.normalizer
      ((⁅Qs, Subgroup.zpowers d⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_zpowers hQ hdJ hd3 hQs2 habel hAJN
  have hCeq : Qs ⊓ Subgroup.centralizer ({d} : Set G) =
      Qs ⊓ Subgroup.centralizer (J : Set G) :=
    inf_centralizer_singleton_eq_inf_centralizer hQ hdJ hd3 hQs2 habel hAJN hCcard
  have hE_le : ⁅Qs, Subgroup.zpowers d⁆ ≤ Qs :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers d) (K := Qs)).mp
      (Subgroup.zpowers_le.mpr (hQ hdJ))
  have hEelem : IsElemAbelian 2 (⁅Qs, Subgroup.zpowers d⁆) := hEelemQs.mono hE_le
  exact ⟨hEelemQs, hE4, hCeq, hJE, fun t htSt htQ =>
    card_commutator_inf_centralizer hQ hQsSt hStJ hdJ hd3 hQs2 habel hQsrelSt hJ_eq
      hAJN hSt_not_normal hE4 hCE hJE hEelem htSt htQ⟩

theorem goldschmidt_small {G₀ : Type*} [Group G₀] {J J' Qs Qs' St : Subgroup G₀} {d : G₀}
    [Finite ↥J]
    (hQ : J ≤ Subgroup.normalizer (Qs : Set G₀))
    (hQ' : J' ≤ Subgroup.normalizer (Qs' : Set G₀))
    (hSt : Qs ⊔ Qs' ≤ St) (hStJ : St ≤ J ⊓ J')
    (hp : IsPGroup 2 St) (h3 : St.relIndex J = 3)
    (hi : Qs.relIndex St = 2) (hi' : Qs'.relIndex St = 2)
    (hJ : J = St ⊔ Subgroup.zpowers d ⊔ Qs) (hd3 : orderOf d = 3)
    (hg : ∃ g : G₀, J.map (MulAut.conj g).toMonoidHom = J' ∧
      Qs.map (MulAut.conj g).toMonoidHom = Qs')
    (hc : ∀ X : Subgroup G₀, X ≤ St → J ≤ Subgroup.normalizer (X : Set G₀) →
      J' ≤ Subgroup.normalizer (X : Set G₀) → X = ⊥)
    (h8 : Nat.card Qs ≤ 8) :
    IsMulCommutative Qs ∧ Nat.card ↥(Qs ⊓ Subgroup.centralizer (J : Set G₀)) ≤ 2 ∧
      Nat.card (centerOf St) ≤ 4 ∧
        (4 ≤ Nat.card Qs → IsElemAbelian 2 Qs ∧
          Nat.card ↥(⁅Qs, Subgroup.zpowers d⁆) = 4 ∧
          Qs ⊓ Subgroup.centralizer ({d} : Set G₀) =
            Qs ⊓ Subgroup.centralizer (J : Set G₀) ∧
          J ≤ Subgroup.normalizer ((⁅Qs, Subgroup.zpowers d⁆ : Subgroup G₀) : Set G₀) ∧
          ∀ t ∈ St, t ∉ Qs →
            Nat.card ↥(⁅Qs, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({t} : Set G₀)) = 2) := by
  obtain ⟨g, hgJ, hgQ⟩ := hg
  have hQsSt : Qs ≤ St := le_sup_left.trans hSt
  have hQs'St : Qs' ≤ St := le_sup_right.trans hSt
  have hSt_le_J : St ≤ J := hStJ.trans inf_le_left
  have hSt_le_J' : St ≤ J' := hStJ.trans inf_le_right
  have hQsJ : Qs ≤ J := hQsSt.trans hSt_le_J
  have hdJ : d ∈ J := by
    rw [hJ]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hStNQs : St ≤ Subgroup.normalizer (Qs : Set G₀) := hSt_le_J.trans hQ
  have hStNQs' : St ≤ Subgroup.normalizer (Qs' : Set G₀) := hSt_le_J'.trans hQ'
  haveI hStfin : Finite ↥St :=
    Finite.of_injective _ (Subgroup.inclusion_injective hSt_le_J)
  haveI hQsfin : Finite ↥Qs :=
    Finite.of_injective _ (Subgroup.inclusion_injective hQsSt)
  have hcardSt : Nat.card ↥St = 2 * Nat.card ↥Qs := by
    have h := Subgroup.relIndex_mul_card (H := Qs) (K := St)
    rw [hi, inf_eq_left.mpr hQsSt] at h
    omega
  have hcardJ : Nat.card ↥J = 3 * Nat.card ↥St := by
    have h := Subgroup.relIndex_mul_card (H := St) (K := J)
    rw [h3, inf_eq_left.mpr hSt_le_J] at h
    omega
  have hcardJ' : Nat.card ↥J' = Nat.card ↥J := by
    rw [← hgJ]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective (K := J)
  have hcardStJ' : St.relIndex J' = 3 := by
    have h := Subgroup.relIndex_mul_card (H := St) (K := J')
    rw [inf_eq_left.mpr hSt_le_J'] at h
    rw [hcardJ', hcardJ] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥St)) h
  have hSt_ne_bot : St ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥St = 1 := by rw [hbot]; simp
    rw [hcardSt] at h1
    omega
  haveI hStnt : Nontrivial ↥St := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hSt_ne_bot
  have hQs2 : IsPGroup 2 ↥Qs := hp.to_le hQsSt
  have hZ_ne_bot : centerOf St ≠ ⊥ := by
    intro hbot
    rw [centerOf_eq_map_center] at hbot
    have hcenter : Subgroup.center ↥St = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥St)
        St.subtype_injective).mp hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hp.center_nontrivial hcenter
  have hSt_not_normal : ¬ (J ≤ Subgroup.normalizer (St : Set G₀)) :=
    not_le_normalizer_of_centerOf_ne_bot hStJ hp h3 hgJ hc hZ_ne_bot
  have hJ_eq : J = St ⊔ Subgroup.zpowers d := by
    rw [hJ]
    exact sup_eq_left.mpr (hQsSt.trans le_sup_left)
  have hJ'eq : J' = St ⊔ Subgroup.zpowers (g * d * g⁻¹) :=
    eq_sup_zpowers_conj hSt_le_J' hp hgJ hdJ hd3 hcardStJ'
  have hcard_le_two_of_commute : (∀ q ∈ Qs, q * d = d * q) → Nat.card ↥Qs ≤ 2 :=
    card_le_two_of_commute (J := J) (J' := J') (Qs := Qs) (Qs' := Qs') (St := St)
      (d := d) (g := g) hQsSt hi' hStNQs hStNQs' hgQ hJ_eq hJ'eq hc
  have habel : IsMulCommutative Qs :=
    isMulCommutative_of_card_le_eight hQ hQ' hSt hStJ hi' hgQ hc h8 hp
  have hne_of_not_central : ¬ (∀ q ∈ Qs, q * d = d * q) →
      Qs ⊓ Subgroup.centralizer ({d} : Set G₀) ≠ Qs := by
    intro hcent heq
    apply hcent
    intro q hq
    have hqC : q ∈ Subgroup.centralizer ({d} : Set G₀) := (inf_eq_left.mp heq) hq
    have h := Subgroup.mem_centralizer_iff.mp hqC d (Set.mem_singleton d)
    exact h.symm
  have hCJ_le_Qs : Nat.card ↥(Qs ⊓ Subgroup.centralizer (J : Set G₀)) ≤ Nat.card ↥Qs :=
    Subgroup.card_le_of_le inf_le_left
  have hCJ : Nat.card ↥(Qs ⊓ Subgroup.centralizer (J : Set G₀)) ≤ 2 := by
    by_cases hcent : ∀ q ∈ Qs, q * d = d * q
    · exact hCJ_le_Qs.trans (hcard_le_two_of_commute hcent)
    · exact card_inf_centralizer_le_two hQ hdJ hd3 hQs2 h8
        (hne_of_not_central hcent)
  have hZcard : Nat.card (centerOf St) ≤ 4 :=
    centerOf_card_le_four hQ hQsSt hSt_le_J hp h3 hdJ hSt_not_normal
      hcard_le_two_of_commute h8 hcardSt
  refine ⟨habel, hCJ, hZcard, fun h4 => ?_⟩
  have hne : Qs ⊓ Subgroup.centralizer ({d} : Set G₀) ≠ Qs :=
    hne_of_not_central fun h => by
      have := hcard_le_two_of_commute h
      omega
  have hcardJ6 : Nat.card ↥J = 6 * Nat.card ↥Qs := by
    rw [hcardJ, hcardSt]
    ring
  have hAJN : J ≤ Subgroup.normalizer ((Qs ⊔ Subgroup.zpowers d : Subgroup G₀) : Set G₀) :=
    le_normalizer_sup_zpowers hQ hQsJ hdJ hd3 hQs2 hcardJ6
  exact isElemAbelian_and_commutator_of_four_le_card hQ hQsSt hSt_le_J hdJ hd3 hQs2 habel
    hi hJ_eq hAJN hSt_not_normal h8 h4 hne hcardJ6

end CFSG.Quasithin.St84
