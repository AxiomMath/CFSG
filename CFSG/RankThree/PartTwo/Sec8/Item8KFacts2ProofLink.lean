module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLinkFacts
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace Item8KFacts2Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_inSubgroup_perfectResidual_of_pow_three {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hC : ∀ y : barCentralizer (Subgroup.zpowers a) L, y ^ 3 = 1 →
      y ∈ perfectResidual (barCentralizer (Subgroup.zpowers a) L))
    {u : G} (huL : u ∈ L) (hua : u ∈ Subgroup.centralizer ({a} : Set G)) (hu3 : u ^ 3 = 1) :
    u ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  set M := L ⊓ Subgroup.centralizer ({a} : Set G) with hM
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  have hd3 : ∃ j : ℕ, a ^ 3 ^ j = 1 := ⟨1, by rwa [pow_one]⟩
  have huM : u ∈ M := ⟨huL, hua⟩
  have hu' : q ⟨u, huL⟩ ∈ barCentralizer (Subgroup.zpowers a) L := by
    rw [← KFacts.imageModTheta_centralizer_eq haN hd3]
    exact ⟨⟨u, huL⟩, huM, rfl⟩
  have huL3 : (⟨u, huL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
  have hy3 : (⟨q ⟨u, huL⟩, hu'⟩ : barCentralizer (Subgroup.zpowers a) L) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, huL3, map_one, Subgroup.coe_one]
  have hmem : q ⟨u, huL⟩ ∈ imageModTheta L (inSubgroup perfectResidual M) := by
    rw [KFacts.imageModTheta_perfectResidual_centralizer_eq haN hd3]
    exact ⟨_, hC _ hy3, rfl⟩
  obtain ⟨r, hrR, hr⟩ := hmem
  have ht : r⁻¹ * ⟨u, huL⟩ ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hr
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hto : ¬ 3 ∣ orderOf ((r : G)⁻¹ * u) := by
    intro h3
    apply hθ3
    have e : orderOf ((r : G)⁻¹ * u) =
        orderOf (⟨r⁻¹ * ⟨u, huL⟩, ht⟩ : aschbacherSolvableCore 3 L) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      rfl
    rw [e] at h3
    exact h3.trans (orderOf_dvd_natCard _)
  have hrR' : (r : G) ∈ inSubgroup perfectResidual M := Subgroup.mem_subgroupOf.mp hrR
  have hrM : (r : G) ∈ M := Item87Proof.residual_le M hrR'
  set rM : M := ⟨r, hrM⟩ with hrMdef
  set uM : M := ⟨u, huM⟩ with huMdef
  have hrP : rM ∈ perfectResidual M := by
    obtain ⟨x, hx, hxr⟩ := hrR'
    have : x = rM := Subtype.ext hxr
    rw [← this]
    exact hx
  set φ := QuotientGroup.mk' (perfectResidual M) with hφ
  have hφr : φ rM = 1 := (QuotientGroup.eq_one_iff _).mpr hrP
  have hφu : φ uM = φ (rM⁻¹ * uM) := by rw [map_mul, map_inv, hφr, inv_one, one_mul]
  have huM3 : uM ^ 3 = 1 := Subtype.ext (by simpa using hu3)
  have h1 : orderOf (φ uM) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, huM3, map_one])
  have h2 : orderOf (φ uM) ∣ orderOf ((r : G)⁻¹ * u) := by
    rw [hφu]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [← Subgroup.orderOf_coe]
    rfl
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · rw [orderOf_eq_one_iff] at h
    exact ⟨uM, (QuotientGroup.eq_one_iff uM).mp h, rfl⟩
  · rw [h] at h2
    exact absurd h2 hto

theorem false_of_commutator_mem {X : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (X : Set G)) (ha3 : a ^ 3 = 1)
    (hs : IsSimpleGroup (perfectResidual (barCentralizer (Subgroup.zpowers a) X)))
    (hnc : ∃ x y : perfectResidual (barCentralizer (Subgroup.zpowers a) X), x * y ≠ y * x)
    {S : Subgroup G} (hSs : Group.IsSolvable S)
    (hSn : ∀ j ∈ sec8J X a, ∀ s ∈ S, j * s * j⁻¹ ∈ S)
    {u : G} (huJ : u ∈ sec8J X a) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hcomm : ∀ j ∈ sec8J X a, ⁅u, j⁆ ∈ S) : False := by
  classical
  set J := sec8J X a with hJdef
  set B := barCentralizer (Subgroup.zpowers a) X with hB
  set D := perfectResidual B with hD
  have : IsSimpleGroup D := hs
  have hJX : J ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hq
  set ψ₀ : J →* X ⧸ aschbacherSolvableCore 3 X := q.comp (Subgroup.inclusion hJX) with hψ₀
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rwa [pow_one]⟩
  have hψD : ∀ j : J, ∃ d : D, ((d : B) : X ⧸ aschbacherSolvableCore 3 X) = ψ₀ j := by
    intro j
    have hj : ψ₀ j ∈ imageModTheta X
        (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G))) :=
      ⟨Subgroup.inclusion hJX j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩
    rw [himg] at hj
    obtain ⟨d, hd, hdj⟩ := hj
    exact ⟨⟨d, hd⟩, hdj⟩
  have hψB : ∀ j : J, ψ₀ j ∈ B := fun j => by
    obtain ⟨d, hd⟩ := hψD j
    rw [← hd]
    exact (d : B).2
  set ψ₁ : J →* B := ψ₀.codRestrict B hψB with hψ₁
  have hψ₁D : ∀ j : J, ψ₁ j ∈ D := fun j => by
    obtain ⟨d, hd⟩ := hψD j
    have e : ψ₁ j = (d : B) := Subtype.ext hd.symm
    rw [e]
    exact d.2
  set ψ : J →* D := ψ₁.codRestrict D hψ₁D with hψ
  have hψs : Function.Surjective ψ := by
    intro d
    have hd : ((d : B) : X ⧸ aschbacherSolvableCore 3 X) ∈ imageModTheta X
        (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G))) := by
      rw [himg]
      exact ⟨d, d.2, rfl⟩
    obtain ⟨x, hx, hxd⟩ := hd
    refine ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact hxd
  set T := S.subgroupOf J with hT
  have hTn : T.Normal := ⟨fun t ht g => by
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    simpa using hSn g g.2 t ht⟩
  have hTs : Group.IsSolvable T := by
    let f : T →* S :=
      { toFun := fun t => ⟨((t : J) : G), t.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h := congrArg (fun s : S => (s : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hTD : T.map ψ = ⊥ := by
    have hn : (T.map ψ).Normal := hTn.map ψ hψs
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hsol : Group.IsSolvable (T.map ψ) := Group.isSolvable_of_surjective
        (ψ.subgroupMap_surjective T)
      have hsolD : Group.IsSolvable D := by
        rw [h] at hsol
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := D)).toMonoidHom)
          Subgroup.topEquiv.surjective
      have hP : Group.IsPerfect D := Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
      exact Group.IsPerfect.not_isSolvable D hsolD
  set u' : J := ⟨u, huJ⟩ with hu'
  have hcen : ψ u' ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨j, rfl⟩ := hψs d
    have hc : ⁅u', j⁆ ∈ T := by
      rw [Subgroup.mem_subgroupOf]
      exact hcomm j j.2
    have h1 : ψ ⁅u', j⁆ = 1 := by
      have : ψ ⁅u', j⁆ ∈ T.map ψ := Subgroup.mem_map_of_mem ψ hc
      rwa [hTD, Subgroup.mem_bot] at this
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hZ : Subgroup.center D = ⊥ := by
    rcases (Subgroup.center D).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx : x ∈ Subgroup.center D := by
        rw [h]
        exact Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  rw [hZ, Subgroup.mem_bot] at hcen
  have hq1 : q (Subgroup.inclusion hJX u') = 1 := by
    have := congrArg (fun d : D => ((d : B) : X ⧸ aschbacherSolvableCore 3 X)) hcen
    simpa [hψ, hψ₁, hψ₀] using this
  have huθ : Subgroup.inclusion hJX u' ∈ aschbacherSolvableCore 3 X :=
    (QuotientGroup.eq_one_iff _).mp hq1
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  apply hθ3
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have e : orderOf u =
      orderOf (⟨Subgroup.inclusion hJX u', huθ⟩ : aschbacherSolvableCore 3 X) := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rfl
  have hdvd := orderOf_dvd_natCard (⟨Subgroup.inclusion hJX u', huθ⟩ :
    aschbacherSolvableCore 3 X)
  rw [← e, hord] at hdvd
  exact hdvd

end Item8KFacts2Proof

open Item8KFacts2Proof


theorem kF87LinkOne_of
    (h84 : Pair84A) :
    KF87LinkOne := by
  intro G _ _ A c L a b X h hU _ _ hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hIdef : sec8I L a =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hU, ↓reduceIte]
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKX : K ≤ X := h.pairRel.2.2.2.1
  have hbA : b ∈ A := h.isGammaIndex.1
  have hba : b * a = a * b :=
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨b, hbA⟩ ⟨a, h.a_mem⟩)
  have haK : a ∈ Subgroup.normalizer (K : Set G) := by
    have ha := h.a_mem_normalizer
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hba.symm)
    have haLb : a ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
        (Subgroup.mem_normalizer_iff.mp haC y)]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLb
  have h3K : 3 ∣ Nat.card K := by
    have hq : 3 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
      rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with
        ⟨-, F, _, _, hF, ⟨φ⟩⟩ | ⟨φ⟩
      · have hUF : UnitaryFieldData 2 (3 * 1) F :=
          ⟨Nat.prime_two, by norm_num, by rw [hF, ← pow_mul, mul_comm]⟩
        have hc : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
            Nat.card (unitarySU 2 (3 * 1) F 3) := Nat.card_congr φ.toEquiv
        rw [hc, KFacts.card_unitarySU_three hUF]
        norm_num
      · obtain ⟨φ⟩ := φ
        rw [Nat.card_congr φ.toEquiv]
        exact Item87Proof.three_dvd_card_projSL_two (by norm_num)
    exact hq.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨u, ⟨huK, huC⟩, hu⟩ := KFacts.exists_mem_centralizer_orderOf_eq
    (Item87Res2Proof.isPGroup_zpowers_of_pow_three ha3) (Subgroup.zpowers_le.mpr haK) h3K
  have hua : u ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a)) huC
  have hu3 : u ^ 3 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    norm_num at hu
  have hFL := residualFacts_barCentralizer (le_refl 1)
    (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) (by simpa using hU) ha3
    h.inducesStdKind h.gTwo
  obtain ⟨-, -, -, -, -, e, m, hem⟩ := h.mem_pairOmega
  have hk84 := h84 G A c L a b X 1 h
  have haX : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk84 with hk | hk
    · exact hk.mem_normalizer
    · exact hk.mem_normalizer
  have hFX := residualFacts_barCentralizer hem.2.2.1
    (Item87Proof.isGammaType_of_isGammaIndex hem) (h.not_unitary (3 * m)) ha3 hk84
    (h.gTwoPartner m)
  have huI : u ∈ sec8I L a := by
    rw [hIdef]
    exact mem_inSubgroup_perfectResidual_of_pow_three h.a_mem_normalizer ha3 hFL.1 (hKL huK)
      hua hu3
  have huJ : u ∈ sec8J X a :=
    mem_inSubgroup_perfectResidual_of_pow_three haX ha3 hFX.1 (hKX huK) hua hu3
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  have hθs : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) Ca) := by
    have := (solvable_prime_complement_core_characterization (H := Ca) Nat.prime_three).1
    exact Group.isSolvable_of_surjective
      (Ca.subtype.subgroupMap_surjective (aschbacherSolvableCore 3 Ca))
  have hθn : ∀ j ∈ sec8J X a, ∀ s ∈ inSubgroup (aschbacherSolvableCore 3) Ca,
      j * s * j⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Ca := by
    intro j hj s hs
    have hjC : j ∈ Ca := ((Item87Proof.residual_le _) hj).2
    obtain ⟨s', hs', rfl⟩ := hs
    have hn : (aschbacherSolvableCore 3 Ca).Normal := inferInstance
    exact ⟨⟨j, hjC⟩ * s' * ⟨j, hjC⟩⁻¹, hn.conj_mem s' hs' _, rfl⟩
  exact false_of_commutator_mem haX ha3 hFX.2.1 hFX.2.2 hθs hθn huJ hu3 hu1
    fun j hj => hle (Subgroup.commutator_mem_commutator huI hj)

end CFSG.RankThree.PartTwo.Sec8
