module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointAction
import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SuzukiSubgroups.Facts
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_card_prod {A B : Type} [Group A] [Group B] (P : Subgroup A)
    (Q : Subgroup B) : Nat.card ↥(P.prod Q) = Nat.card ↥P * Nat.card ↥Q := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv P Q).toEquiv

theorem uc22r3e5c_map_fst_prod {A B : Type} [Group A] [Group B] (P : Subgroup A)
    (Q : Subgroup B) : (P.prod Q).map (MonoidHom.fst A B) = P := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    exact (Subgroup.mem_prod.mp hx).1
  · intro hx
    exact ⟨(x, 1), Subgroup.mem_prod.mpr ⟨hx, Q.one_mem⟩, rfl⟩

theorem uc22r3e5c_map_snd_prod {A B : Type} [Group A] [Group B] (P : Subgroup A)
    (Q : Subgroup B) : (P.prod Q).map (MonoidHom.snd A B) = Q := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    exact (Subgroup.mem_prod.mp hx).2
  · intro hx
    exact ⟨(1, x), Subgroup.mem_prod.mpr ⟨P.one_mem, hx⟩, rfl⟩

theorem uc22r3e5c_normalizer_prod {A B : Type} [Group A] [Group B]
    (P : Subgroup A) (Q : Subgroup B) :
    Subgroup.normalizer ((P.prod Q : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (P : Set A)).prod (Subgroup.normalizer (Q : Set B)) := by
  ext x
  constructor
  · intro hx
    have h2a := fun a => (Subgroup.mem_normalizer_iff.mp hx) (a, 1)
    have h2b := fun b => (Subgroup.mem_normalizer_iff.mp hx) (1, b)
    refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have h1 : (x : A × B) * (a, 1) * x⁻¹ ∈ P.prod Q :=
          (h2a a).mp (Subgroup.mem_prod.mpr ⟨ha, Q.one_mem⟩)
        have h3 : (x : A × B) * (a, 1) * x⁻¹ = (x.1 * a * x.1⁻¹, 1) := by
          ext <;> simp [mul_assoc]
        rw [h3] at h1
        exact (Subgroup.mem_prod.mp h1).1
      · intro ha
        have hmem : (x.1 * a * x.1⁻¹, 1) ∈ P.prod Q :=
          Subgroup.mem_prod.mpr ⟨ha, Q.one_mem⟩
        have h3 : (x : A × B) * (a, 1) * x⁻¹ = (x.1 * a * x.1⁻¹, 1) := by
          ext <;> simp [mul_assoc]
        have h1 : (x : A × B) * (a, 1) * x⁻¹ ∈ P.prod Q := by
          rw [h3]
          exact hmem
        exact (Subgroup.mem_prod.mp ((h2a a).mpr h1)).1
    · rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        have h1 : (x : A × B) * (1, b) * x⁻¹ ∈ P.prod Q :=
          (h2b b).mp (Subgroup.mem_prod.mpr ⟨P.one_mem, hb⟩)
        have h3 : (x : A × B) * (1, b) * x⁻¹ = (1, x.2 * b * x.2⁻¹) := by
          ext <;> simp [mul_assoc]
        rw [h3] at h1
        exact (Subgroup.mem_prod.mp h1).2
      · intro hb
        have hmem : (1, x.2 * b * x.2⁻¹) ∈ P.prod Q :=
          Subgroup.mem_prod.mpr ⟨P.one_mem, hb⟩
        have h3 : (x : A × B) * (1, b) * x⁻¹ = (1, x.2 * b * x.2⁻¹) := by
          ext <;> simp [mul_assoc]
        have h1 : (x : A × B) * (1, b) * x⁻¹ ∈ P.prod Q := by
          rw [h3]
          exact hmem
        exact (Subgroup.mem_prod.mp ((h2b b).mpr h1)).2
  · intro hx
    obtain ⟨hxP, hxQ⟩ := Subgroup.mem_prod.mp hx
    rw [Subgroup.mem_normalizer_iff] at hxP hxQ ⊢
    rintro ⟨a, b⟩
    constructor
    · intro h
      rw [Subgroup.mem_prod] at h ⊢
      exact ⟨(hxP a).mp h.1, (hxQ b).mp h.2⟩
    · intro h
      rw [Subgroup.mem_prod] at h ⊢
      exact ⟨(hxP a).mpr h.1, (hxQ b).mpr h.2⟩

theorem uc22r3e5c_eq_of_isSylowTwoOf_le {H S K : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSK : S ≤ K) (hKH : K ≤ H) (hK : IsPGroup 2 K) : K = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.IsSylowOf.eq_of_le
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hS) hSK hKH hK

theorem uc22r3e5c_card_ker_mul_card_map {A B : Type} [Group A] [Group B] (f : A →* B)
    (K : Subgroup A) :
    Nat.card ↥(f.ker ⊓ K) * Nat.card ↥(K.map f) = Nat.card ↥K := by
  classical
  let φ : ↥K →* ↥(K.map f) := f.subgroupMap K
  have hφsurj : Function.Surjective φ := f.subgroupMap_surjective K
  have hφker : φ.ker = (f.ker ⊓ K).subgroupOf K := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨congrArg Subtype.val (MonoidHom.mem_ker.mp hx), x.2⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (Subgroup.mem_subgroupOf.mp hx).1
  have hcard : Nat.card ↥K = Nat.card (↥K ⧸ φ.ker) * Nat.card ↥φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hquot : Nat.card (↥K ⧸ φ.ker) = Nat.card ↥(K.map f) := by
    have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφsurj
    have h1 : Nat.card (↥K ⧸ φ.ker) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hrange, Subgroup.card_top] at h1
    exact h1
  have hker : Nat.card ↥φ.ker = Nat.card ↥(f.ker ⊓ K) := by
    rw [hφker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [hcard, hquot, hker, mul_comm]

theorem uc22r3e5c_card_of_isHall_two {K : Type} [Group K] [Finite K]
    {H : Subgroup K} (hH : IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H)
    {a m : ℕ} (hm : Odd m) (hcard : Nat.card K = 2 ^ a * m) : Nat.card H = m := by
  have hodd : Odd (Nat.card H) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact (hH.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ (even_iff_two_dvd.mp he)) rfl
  have hcop2 : Nat.Coprime (Nat.card H) (2 ^ a) :=
    (Nat.Coprime.pow_right a hodd.coprime_two_right)
  have hdivH : Nat.card H ∣ m := by
    have h1 : Nat.card H ∣ 2 ^ a * m := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card H
    exact hcop2.dvd_of_dvd_mul_left h1
  have hcopm : Nat.Coprime m H.index := by
    refine Nat.coprime_of_dvd fun p hp hpm hpi => ?_
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
    exact (hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpi) hp2
  have hdivm : m ∣ Nat.card H := by
    have h1 : m ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index, hcard]
      exact dvd_mul_left m (2 ^ a)
    exact hcopm.dvd_of_dvd_mul_right h1
  exact Nat.dvd_antisymm hdivH hdivm

private theorem uc22r3e5c_exists_ne_sylow {H : Type} [Group H] [Finite H] {n : ℕ}
    (hSz : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) : ∃ Q₂ : Sylow 2 H, Q₂ ≠ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := szPointActionFacts_holds H n (CFSG.Blueprint.LieModel.twistedB2_iff.mpr ⟨rfl, hSz⟩)
  haveI hfin : Finite (Sylow 2 H) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  have hcard : Nat.card (Sylow 2 H) = (2 ^ n) ^ 2 + 1 := T.card_points
  have h1 : 1 < Nat.card (Sylow 2 H) := by
    rw [hcard]
    have h0 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by norm_num)
    omega
  haveI : Nontrivial (Sylow 2 H) := Finite.one_lt_card_iff_nontrivial.mp h1
  exact exists_ne Q

private theorem uc22r3e5c_index_normalizer_subgroupOf
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) :
    ((Q : Subgroup H).subgroupOf (Subgroup.normalizer ((Q : Subgroup H) : Set H))).index =
      2 ^ n - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := szPointActionFacts_holds H n (CFSG.Blueprint.LieModel.twistedB2_iff.mpr ⟨rfl, hSz⟩)
  let N : Subgroup H := Subgroup.normalizer ((Q : Subgroup H) : Set H)
  let Q' : Subgroup ↥N := (Q : Subgroup H).subgroupOf N
  have hQcard : Nat.card ↥(Q : Subgroup H) = (2 ^ n) ^ 2 := T.card_sylow Q
  have hNcard : Nat.card ↥N = (2 ^ n) ^ 2 * (2 ^ n - 1) :=
    CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz hSz Q
  have hQ'card : Nat.card ↥Q' = (2 ^ n) ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer
      (H := (Q : Subgroup H))))).trans hQcard
  have h := Subgroup.card_mul_index Q'
  rw [hQ'card, hNcard] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

private theorem uc22r3e5c_exists_torus_coprime
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) :
    ∃ K : Subgroup H, K ≤ Subgroup.normalizer ((Q : Subgroup H) : Set H) ∧
      IsCyclic ↥K ∧ Nat.card ↥K = 2 ^ n - 1 ∧ K ⊓ (Q : Subgroup H) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := szPointActionFacts_holds H n (CFSG.Blueprint.LieModel.twistedB2_iff.mpr ⟨rfl, hSz⟩)
  obtain ⟨Q₂, hQ₂⟩ := uc22r3e5c_exists_ne_sylow hSz Q
  let K : Subgroup H := CFSG.GroupTheory.SuzukiTorusData.torus Q Q₂
  have hKcyc : IsCyclic ↥K := CFSG.GroupTheory.SuzukiTorusData.torus_isCyclic T hQ₂.symm
  have hKcard : Nat.card ↥K = 2 ^ n - 1 :=
    CFSG.GroupTheory.SuzukiTorusData.torus_card T hQ₂.symm
  have hKle : K ≤ Subgroup.normalizer ((Q : Subgroup H) : Set H) :=
    CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_left
  have hQcard : Nat.card ↥(Q : Subgroup H) = (2 ^ n) ^ 2 := T.card_sylow Q
  have hn3 : 3 ≤ n :=
    (CFSG.LocalAnalysis.WeakClosure81.SevenK.odd_and_three_le_of_isSz hSz).2
  have hKodd : Odd (Nat.card ↥K) := by
    rw [hKcard]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Even.pow_of_ne_zero (by norm_num) (by omega : n ≠ 0)) odd_one
  have hKodd' : Odd (2 ^ n - 1) := by rwa [← hKcard]
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(Q : Subgroup H)) := by
    rw [hKcard, hQcard]
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right n hKodd'.coprime_two_right)
  exact ⟨K, hKle, hKcyc, hKcard, Subgroup.inf_eq_bot_of_coprime hcop⟩

private theorem uc22r3e5c_exists_surjective_torus_quotient
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) :
    ∃ (K : Subgroup H),
      ∃ f : ↥K →* (↥(Subgroup.normalizer ((Q : Subgroup H) : Set H)) ⧸
        ((Q : Subgroup H).subgroupOf (Subgroup.normalizer ((Q : Subgroup H) : Set H)))),
        IsCyclic ↥K ∧ Function.Surjective f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := szPointActionFacts_holds H n (CFSG.Blueprint.LieModel.twistedB2_iff.mpr ⟨rfl, hSz⟩)
  let N : Subgroup H := Subgroup.normalizer ((Q : Subgroup H) : Set H)
  let Q' : Subgroup ↥N := (Q : Subgroup H).subgroupOf N
  haveI hQ'norm : Q'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨K, hKle, hKcyc, hKcard, hKinf⟩ := uc22r3e5c_exists_torus_coprime hSz Q
  let fK : ↥K →* ↥N ⧸ Q' := (QuotientGroup.mk' Q').comp (Subgroup.inclusion hKle)
  have hfKbot : fK.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : fK x = 1 := MonoidHom.mem_ker.mp hx
    have hxQ' : (⟨(x : K), hKle x.2⟩ : ↥N) ∈ Q' :=
      (QuotientGroup.eq_one_iff (⟨(x : K), hKle x.2⟩ : ↥N)).mp hx1
    have hxQ : ((x : K) : H) ∈ (Q : Subgroup H) := Subgroup.mem_subgroupOf.mp hxQ'
    have hxbot : ((x : K) : H) ∈ K ⊓ (Q : Subgroup H) := ⟨x.2, hxQ⟩
    rw [hKinf] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hfKinj : Function.Injective fK := (MonoidHom.ker_eq_bot_iff fK).mp hfKbot
  have hcardimg : Nat.card ↥fK.range = 2 ^ n - 1 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfKinj, Subgroup.card_top,
      hKcard]
  have hcardquot : Nat.card (↥N ⧸ Q') = 2 ^ n - 1 := by
    rw [← Subgroup.index_eq_card, uc22r3e5c_index_normalizer_subgroupOf hSz Q]
  have hrange : fK.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcardimg, hcardquot])
  refine ⟨K, fK, hKcyc, fun y => ?_⟩
  exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top y)

theorem uc22r3e5c_isCyclic_normalizer_quotient
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) :
    IsCyclic (↥(Subgroup.normalizer ((Q : Subgroup H) : Set H)) ⧸
      ((Q : Subgroup H).subgroupOf (Subgroup.normalizer ((Q : Subgroup H) : Set H)))) := by
  obtain ⟨K, f, hKcyc, hsurj⟩ := uc22r3e5c_exists_surjective_torus_quotient hSz Q
  haveI : IsCyclic ↥K := hKcyc
  exact isCyclic_of_surjective f hsurj

theorem uc22r3e5c_isMulCommutative_of_odd_le_normalizer
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H)
    (Q : Sylow 2 H) {D : Subgroup H}
    (hD : D ≤ Subgroup.normalizer ((Q : Subgroup H) : Set H))
    (hodd : Odd (Nat.card D)) : IsMulCommutative ↥D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup H := Subgroup.normalizer ((Q : Subgroup H) : Set H)
  let Q' : Subgroup ↥N := (Q : Subgroup H).subgroupOf N
  haveI hQ'norm : Q'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  haveI hcyc : IsCyclic (↥N ⧸ Q') := uc22r3e5c_isCyclic_normalizer_quotient hSz Q
  haveI : IsMulCommutative (↥N ⧸ Q') := IsCyclic.isMulCommutative
  have hDinf : D ⊓ (Q : Subgroup H) = ⊥ := by
    have hcop : Nat.Coprime (Nat.card D) (Nat.card (Q : Subgroup H)) := by
      obtain ⟨a, ha⟩ := (Q : Sylow 2 H).isPGroup'.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow_right a hodd.coprime_two_right
    exact Subgroup.inf_eq_bot_of_coprime hcop
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hxN : (x : H) ∈ N := hD x.2
  have hyN : (y : H) ∈ N := hD y.2
  let x' : ↥N := ⟨x, hxN⟩
  let y' : ↥N := ⟨y, hyN⟩
  have hcomm : (QuotientGroup.mk' Q') x' * (QuotientGroup.mk' Q') y' =
      (QuotientGroup.mk' Q') y' * (QuotientGroup.mk' Q') x' :=
    IsMulCommutative.is_comm.comm _ _
  have h1 : (QuotientGroup.mk' Q') ⁅x', y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hmemQ' : ⁅x', y'⁆ ∈ Q' := (QuotientGroup.eq_one_iff ⁅x', y'⁆).mp h1
  have hmemQ : ⁅(x : H), (y : H)⁆ ∈ (Q : Subgroup H) := by
    have hval : ((⁅x', y'⁆ : ↥N) : H) = ⁅(x : H), (y : H)⁆ :=
      map_commutatorElement (Subgroup.subtype N) x' y'
    have h := Subgroup.mem_subgroupOf.mp hmemQ'
    rw [hval] at h
    exact h
  have hmemD : ⁅(x : H), (y : H)⁆ ∈ D :=
    Subgroup.commutator_le_self D (Subgroup.commutator_mem_commutator x.2 y.2)
  have hbot : ⁅(x : H), (y : H)⁆ ∈ D ⊓ (Q : Subgroup H) := ⟨hmemD, hmemQ⟩
  rw [hDinf] at hbot
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)

theorem uc22r3e5c_isSolvable_normalizer_sylow
    {H : Type} [Group H] [Finite H] {n : ℕ} (hSz : CFSG.Quasithin.IsSz n H)
    (Q : Sylow 2 H) :
    Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup H) : Set H)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup H := Subgroup.normalizer ((Q : Subgroup H) : Set H)
  let Q' : Subgroup ↥N := (Q : Subgroup H).subgroupOf N
  haveI hQ'norm : Q'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  haveI hcyc : IsCyclic (↥N ⧸ Q') := uc22r3e5c_isCyclic_normalizer_quotient hSz Q
  haveI : IsMulCommutative (↥N ⧸ Q') := IsCyclic.isMulCommutative
  haveI : Group.IsSolvable (↥N ⧸ Q') := inferInstance
  have hQ2' : IsPGroup 2 ↥Q' :=
    (Q : Sylow 2 H).isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer (H := (Q : Subgroup H)))).symm
  haveI : Group.IsNilpotent ↥Q' := IsPGroup.isNilpotent (p := 2) hQ2'
  haveI : Group.IsSolvable ↥Q' := IsNilpotent.to_isSolvable
  exact Group.isSolvable_of_subgroup_quotient Q'

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
