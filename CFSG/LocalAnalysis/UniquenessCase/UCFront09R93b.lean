module

public import CFSG.GroupTheory.ThreeTranspositions.CyclicSylow
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.Quasithin.Background.F918V3E2
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.RankThree.PartOne.K1214.CycAlg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GroupTheory.ThreeTranspositions (HasE9 isCyclic_of_isPGroup_three
  mem_of_normal_of_three_dvd_card isSimpleGroup_of_generated_by_order_three)

variable {Q : Type} [Group Q] [Finite Q]

theorem three_dvd_card_of_not_isPGroup (hO : CFSG.pPrimeCore 3 Q = ⊥) (hnp : ¬ IsPGroup 3 Q) :
    3 ∣ Nat.card Q := by
  by_contra h
  apply hnp
  have htop := (CFSG.pPrimeCore_eq_bot_iff.mp hO) ⊤ inferInstance
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by rwa [Subgroup.card_top]))
  exact IsPGroup.of_card (n := 0)
    (by rw [pow_zero, ← Subgroup.card_top, htop, Subgroup.card_bot])

theorem exists_conj_eq_inv_of_sylow (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hnp : ¬ IsPGroup 3 Q) (P : Sylow 3 Q) :
    ∃ g : Q, ∀ y ∈ (P : Subgroup Q), g * y * g⁻¹ = y⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hP : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q)
  · refine absurd ?_ hnp
    have hker : (MonoidHom.transferSylow P hP).ker = ⊥ :=
      (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ inferInstance
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (MonoidHom.not_dvd_card_ker_transferSylow P hP))
    exact P.isPGroup'.of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp hker)
  · obtain ⟨g, hgN, hgC⟩ := SetLike.not_le_iff_exists.mp hP
    exact ⟨g, CFSG.Quasithin.F918V3E2.inv_of_mem_normalizer_not_mem_centralizer P
      (P.ne_bot_of_dvd_card (three_dvd_card_of_not_isPGroup hO hnp))
      (isCyclic_of_isPGroup_three hE9 P.isPGroup') hgN hgC⟩

theorem mem_commutator_of_mem_sylow (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hnp : ¬ IsPGroup 3 Q) (P : Sylow 3 Q) {y : Q} (hy : y ∈ (P : Subgroup Q)) :
    y ∈ commutator Q := by
  obtain ⟨g, hg⟩ := exists_conj_eq_inv_of_sylow hE9 hO hnp P
  have h1 : y⁻¹ * y⁻¹ ∈ commutator Q := by
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top y)
    rwa [commutatorElement_def, hg y hy, ← _root_.commutator_def] at h
  have hy2 : y ^ 2 ∈ commutator Q := by
    have h := (commutator Q).inv_mem h1
    rwa [mul_inv_rev, inv_inv, ← pow_two] at h
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
  have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hy' : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by rw [hm]; ring, pow_succ, hyk, one_mul]
  rw [hy']
  exact (commutator Q).pow_mem hy2 _

theorem isPerfect_of_not_hasE9 (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hgen : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) (hnp : ¬ IsPGroup 3 Q) :
    Group.IsPerfect Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨eq_top_iff.mpr ?_⟩
  rw [← hgen, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨P, hP⟩ := hxP.exists_le_sylow
  exact mem_commutator_of_mem_sylow hE9 hO hnp P (hP (Subgroup.mem_zpowers x))

theorem exists_conj_eq_inv_of_orderOf_eq_three (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hnp : ¬ IsPGroup 3 Q) {a : Q} (ha : orderOf a = 3) : ∃ g : Q, g * a * g⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haP : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨P, hP⟩ := haP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_eq_inv_of_sylow hE9 hO hnp P
  exact ⟨g, hg a (hP (Subgroup.mem_zpowers a))⟩

theorem false_of_commute_conj (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hgen : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) (hnp : ¬ IsPGroup 3 Q)
    {a : Q} (ha : orderOf a = 3) (hc : ∀ c : Q, Commute a (c * a * c⁻¹)) : False := by
  have hD : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
  have hmem : ∀ c : Q, c * a * c⁻¹ ∈ Subgroup.zpowers a := fun c => by
    by_contra hn
    exact hE9 ⟨a, c * a * c⁻¹, ha, (MulEquiv.orderOf_eq (MulAut.conj c) a).trans ha, hc c, hn⟩
  have hcD : ∀ c : Q, ∀ d ∈ Subgroup.zpowers a, c * d * c⁻¹ ∈ Subgroup.zpowers a := by
    intro c d hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [← conj_zpow]
    exact (Subgroup.zpowers a).zpow_mem (hmem c) j
  have hcen : (⊤ : Subgroup Q) ≤ Subgroup.centralizer {a} := by
    rw [← hgen, Subgroup.closure_le]
    rintro c ⟨k, hk⟩
    have hca := CFSG.RankThree.PartOne.K1214.conj_eq_of_card_prime Nat.prime_three hD (hcD c)
      (m := k) (by rw [← hk]; exact pow_orderOf_eq_one c) a (Subgroup.mem_zpowers a)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hca)
  obtain ⟨g, hg⟩ := exists_conj_eq_inv_of_orderOf_eq_three hE9 hO hnp ha
  have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hcen (Subgroup.mem_top g))
  have hinv : a⁻¹ = a := by rw [← hg, hga, mul_inv_cancel_right]
  have h2 : a ^ 2 = 1 := by
    rw [pow_two]
    calc a * a = a * a⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel a
  have h32 := orderOf_dvd_of_pow_eq_one h2
  rw [ha] at h32
  exact absurd h32 (by decide)

theorem isSimpleGroup_normalClosure_of_not_hasE9 (hE9 : ¬ HasE9 Q)
    (hO : CFSG.pPrimeCore 3 Q = ⊥) {a : Q} (ha : orderOf a = 3) :
    IsSimpleGroup ↥(Subgroup.normalClosure ({a} : Set Q)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haN : a ∈ Subgroup.normalClosure ({a} : Set Q) := Subgroup.subset_normalClosure rfl
  haveI : Nontrivial ↥(Subgroup.normalClosure ({a} : Set Q)) := ⟨⟨⟨a, haN⟩, 1, fun h => by
    have h1 : a = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ha
    exact absurd ha (by decide)⟩⟩
  refine isSimpleGroup_of_generated_by_order_three
    (fun h => hE9 (h.map_injective (Subgroup.normalClosure ({a} : Set Q)).subtype
      (Subgroup.subtype_injective _))) ?_
    (Subgroup.closure_closure_coe_preimage (k := Group.conjugatesOfSet {a})) ?_
  · have hc : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3
        ↥(Subgroup.normalClosure ({a} : Set Q))).map
          (Subgroup.normalClosure ({a} : Set Q)).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.pPrimeCore_coprime_card
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
      ((CFSG.pPrimeCore_eq_bot_iff.mp hO) _ inferInstance hc)
  · intro s hs
    right
    obtain ⟨b, hb, hbs⟩ := Group.mem_conjugatesOfSet_iff.mp hs
    rw [Set.mem_singleton_iff] at hb
    obtain ⟨c, hc⟩ := isConj_iff.mp hbs
    rw [← Subgroup.orderOf_coe, ← hc, hb]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) a).trans ha

theorem exists_mul_ne_mul_of_mem (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hgen : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) (hnp : ¬ IsPGroup 3 Q)
    {N : Subgroup Q} [N.Normal] {a : Q} (ha : orderOf a = 3) (haN : a ∈ N) :
    ∃ x y : ↥N, x * y ≠ y * x := by
  by_contra h
  push Not at h
  exact false_of_commute_conj hE9 hO hgen hnp ha fun c =>
    congrArg Subtype.val (h ⟨a, haN⟩ ⟨c * a * c⁻¹, ‹N.Normal›.conj_mem a haN c⟩)

theorem centralizer_eq_bot_of_mem (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hgen : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) (hnp : ¬ IsPGroup 3 Q)
    {N : Subgroup Q} [N.Normal] {a : Q} (ha : orderOf a = 3) (haN : a ∈ N) :
    Subgroup.centralizer (N : Set Q) = ⊥ := by
  by_cases h3 : 3 ∣ Nat.card (Subgroup.centralizer (N : Set Q))
  · have haC : a ∈ Subgroup.centralizer (N : Set Q) := mem_of_normal_of_three_dvd_card hE9 h3 ha
    exact (false_of_commute_conj hE9 hO hgen hnp ha fun c =>
      ((Subgroup.mem_centralizer_iff.mp haC) _ (‹N.Normal›.conj_mem a haN c)).symm).elim
  · exact (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ inferInstance
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)

theorem isSimpleGroup_of_not_hasE9 (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hK : CFSG.Open.IsKGroup Q) (hE9 : ¬ HasE9 Q) (hO : CFSG.pPrimeCore 3 Q = ⊥)
    (hgen : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤) (hnp : ¬ IsPGroup 3 Q) :
    IsSimpleGroup Q ∧ ∃ x y : Q, x * y ≠ y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_of_not_isPGroup hO hnp)
  have haN : a ∈ Subgroup.normalClosure ({a} : Set Q) := Subgroup.subset_normalClosure rfl
  have hnab := exists_mul_ne_mul_of_mem hE9 hO hgen hnp ha haN
  haveI := isSimpleGroup_normalClosure_of_not_hasE9 hE9 hO ha
  haveI : Group.IsSolvable (Outer ↥(Subgroup.normalClosure ({a} : Set Q))) :=
    hSch _ inferInstance hnab (hK.isCatalogGroup_of_surjective
      (Subgroup.normalClosure ({a} : Set Q)) hnab (MonoidHom.id _) Function.surjective_id)
  haveI := CFSG.RankThree.PartOne.CTP.solvable_quotient_of_outer _
    (centralizer_eq_bot_of_mem hE9 hO hgen hnp ha haN)
  haveI := isPerfect_of_not_hasE9 hE9 hO hgen hnp
  have htop : Subgroup.normalClosure ({a} : Set Q) = ⊤ := by
    by_contra hne
    haveI : Nontrivial (Q ⧸ Subgroup.normalClosure ({a} : Set Q)) :=
      QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.normalClosure ({a} : Set Q)) inferInstance
  haveI : Nontrivial Q := ⟨⟨a, 1, fun h => by
    rw [h, orderOf_one] at ha
    exact absurd ha (by decide)⟩⟩
  obtain ⟨⟨x, _hx⟩, ⟨y, _hy⟩, hxy⟩ := hnab
  refine ⟨IsSimpleGroup.isSimpleGroup_of_surjective (Subgroup.normalClosure ({a} : Set Q)).subtype
    fun z => ⟨⟨z, by rw [htop]; exact Subgroup.mem_top z⟩, rfl⟩, x, y, fun h => hxy ?_⟩
  exact Subtype.ext h

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
