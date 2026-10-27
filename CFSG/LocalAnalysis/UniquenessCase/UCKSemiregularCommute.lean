module

public import CFSG.GroupTheory.Frattini.NormalConjugation
public import CFSG.LocalAnalysis.UniquenessCase.UCKUnfaithful
public import CFSG.RankThree.PartTwo.Sec4.Item420

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.RankThree.PartOne.FixedRank36
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem exists_frattiniRep_ne_one_of_semiregular {E : Subgroup Γ} [E.Normal]
    [Fact (Nat.Prime 2)] [IsElementaryAbelian 2 (↥E ⧸ frattini ↥E)]
    (hE : IsPGroup 2 ↥E) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q Q' : Subgroup Γ}
    (hQ : IsPGroup q ↥Q) (hQ'le : Q' ≤ Q) (hQ'ne : Q' ≠ ⊥)
    (hQE : Q ⊓ Subgroup.centralizer (E : Set Γ) = ⊥) :
    ∃ t ∈ Q', frattiniRep 2 (MulAut.conjNormal (H := E)) t ≠ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra h
  push Not at h
  have hle : Q' ≤ Q ⊓ Subgroup.centralizer (E : Set Γ) := by
    intro t ht
    refine ⟨hQ'le ht, ?_⟩
    exact CFSG.Quasithin.BlueprintB2.mem_centralizer_of_conjNormal_eq_one
      (CFSG.RankThree.PartTwo.Sec4.frattiniRep_eq_one_of_coprime (q := 2) hE
        (MulAut.conjNormal (H := E)) t hq hq2
        (by
          rw [← MonoidHom.map_zpowers (MulAut.conjNormal (H := E)) t]
          exact (hQ.to_le (Subgroup.zpowers_le.mpr (hQ'le ht))).map _)
        (h t ht))
  rw [hQE] at hle
  exact hQ'ne (le_bot_iff.mp hle)

private theorem commute_of_semiregular_normal_two_of_fixV {E : Subgroup Γ} [E.Normal]
    [Fact (Nat.Prime 2)] [Fact (IsPGroup 2 ↥E)]
    [IsElementaryAbelian 2 (↥E ⧸ frattini ↥E)]
    {d : Γ} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdr : orderOf d = r)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqr : q ≠ r) {Q : Subgroup Γ} (hQ : IsPGroup q ↥Q)
    (hdQ : d ∈ Subgroup.normalizer (Q : Set Γ))
    (hQE : Q ⊓ Subgroup.centralizer (E : Set Γ) = ⊥)
    (hfix : ∀ v, frattiniRep 2 (MulAut.conjNormal (H := E)) d v = v → v = 0) :
    ∀ x ∈ Q, d * x = x * d := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI : CommGroup (↥E ⧸ frattini ↥E) := IsMulCommutative.instCommGroup
  letI : AddCommGroup (Additive (↥E ⧸ frattini ↥E)) := Additive.addCommGroup
  let ρ := frattiniRep 2 (MulAut.conjNormal (H := E))
  have hfixV : fixV ρ (Subgroup.zpowers d) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    rw [Submodule.mem_bot]
    exact hfix v ((CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 ρ d v).mp hv)
  let D : Subgroup Γ := Subgroup.zpowers d
  let Q' : Subgroup Γ := ⁅Q, D⁆
  have hQ'le : Q' ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hdQ)
  have hDQ' : D ≤ Subgroup.normalizer (Q' : Set Γ) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.zpowers_le.mpr hdQ hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)]
  have hnotdvd : ¬ r ∣ Nat.card ↥Q := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    exact fun h => hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h)).symm
  have hDQc : ⁅D, Q'⁆ = Q' := by
    rw [Subgroup.commutator_comm]
    exact CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent r hr D Q
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdr, pow_one]))
      hnotdvd (Subgroup.zpowers_le.mpr hdQ)
  suffices hQ'bot : Q' = ⊥ by
    intro x hx
    have hmem : ⁅x, d⁆ ∈ Q' :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers d)
    rw [hQ'bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)).symm
  by_contra hQ'ne
  have hk42 := k42_unfaithful (p := 2) (ρ := ρ) hq hr hq2 hr2 hqr (D := D) (Q := Q')
    (by rw [Nat.card_zpowers, hdr]) hfixV (hQ.to_le hQ'le)
    (exists_frattiniRep_ne_one_of_semiregular
      (Fact.out : IsPGroup 2 ↥E) hq hq2 hQ hQ'le hQ'ne hQE) hDQ' hDQc
  exact hq2 hk42.1

theorem commute_of_semiregular_normal_two {E : Subgroup Γ} [E.Normal] (hE : IsPGroup 2 ↥E)
    {d : Γ} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdr : orderOf d = r)
    (hdE : E ⊓ Subgroup.centralizer ({d} : Set Γ) = ⊥) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqr : q ≠ r) {Q : Subgroup Γ} (hQ : IsPGroup q ↥Q)
    (hdQ : d ∈ Subgroup.normalizer (Q : Set Γ))
    (hQE : Q ⊓ Subgroup.centralizer (E : Set Γ) = ⊥) : ∀ x ∈ Q, d * x = x * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥E) := ⟨hE⟩
  haveI : IsElementaryAbelian 2 (↥E ⧸ frattini ↥E) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hfix : ∀ v, frattiniRep 2 (MulAut.conjNormal (H := E)) d v = v → v = 0 :=
    fun v hv => CFSG.GroupTheory.frattiniRep_conjNormal_eq_zero_of_inf_centralizer_eq_bot
      (q := 2) hE hr hdr hdE v hv
  exact commute_of_semiregular_normal_two_of_fixV hr hr2 hdr hq hq2 hqr hQ hdQ hQE hfix

section Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem inf_centralizer_subgroupOf_eq_bot {M E : Subgroup G} (hEM : E ≤ M) {d : G}
    (hdM : d ∈ M) (h : E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) :
    E.subgroupOf M ⊓ Subgroup.centralizer ({⟨d, hdM⟩} : Set ↥M) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx.1
  have hxc : (x : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp hx.2) ⟨d, hdM⟩ (Set.mem_singleton _))
  have hxbot : (x : G) ∈ E ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hxE, hxc⟩
  rw [h] at hxbot
  exact Subtype.ext (Subgroup.mem_bot.mp hxbot)

private theorem mem_normalizer_subgroupOf {M Q : Subgroup G} {d : G} (hdM : d ∈ M)
    (h : d ∈ Subgroup.normalizer (Q : Set G)) :
    (⟨d, hdM⟩ : ↥M) ∈ Subgroup.normalizer (Q.subgroupOf M : Set ↥M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp h (x : G)).mp hx
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp h (x : G)).mpr hx

private theorem inf_centralizer_subgroupOf_eq_bot' {M Q E : Subgroup G} (hQM : Q ≤ M)
    (hEM : E ≤ M) (h : Q ⊓ Subgroup.centralizer (E : Set G) = ⊥) :
    Q.subgroupOf M ⊓ Subgroup.centralizer (E.subgroupOf M : Set ↥M) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx.1
  have hxc : (x : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp hx.2) ⟨e, hEM he⟩ (Subgroup.mem_subgroupOf.mpr he))
  have hxbot : (x : G) ∈ Q ⊓ Subgroup.centralizer (E : Set G) := ⟨hxQ, hxc⟩
  rw [h] at hxbot
  exact Subtype.ext (Subgroup.mem_bot.mp hxbot)

theorem commute_of_semiregular_normal_two_of_le {M E Q : Subgroup G} (hEM : E ≤ M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) (hE : IsPGroup 2 ↥E) {d : G} (hdM : d ∈ M)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdr : orderOf d = r)
    (hdE : E ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqr : q ≠ r) (hQM : Q ≤ M) (hQ : IsPGroup q ↥Q)
    (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    (hQE : Q ⊓ Subgroup.centralizer (E : Set G) = ⊥) : ∀ x ∈ Q, d * x = x * d := by
  haveI hE'n : (E.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hME
  have hE' : IsPGroup 2 ↥(E.subgroupOf M) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEM).symm
  have hdE' := inf_centralizer_subgroupOf_eq_bot hEM hdM hdE
  have hQ' : IsPGroup q ↥(Q.subgroupOf M) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  have hdQ' := mem_normalizer_subgroupOf hdM hdQ
  have hQE' := inf_centralizer_subgroupOf_eq_bot' hQM hEM hQE
  have hdM' : orderOf (⟨d, hdM⟩ : ↥M) = r := by
    simpa using (Subgroup.orderOf_coe ⟨d, hdM⟩).symm.trans hdr
  have hcomm := commute_of_semiregular_normal_two (Γ := ↥M) (E := E.subgroupOf M) hE'
    (d := ⟨d, hdM⟩) hr hr2 hdM' hdE' hq hq2 hqr hQ' hdQ' hQE'
  intro x hx
  exact congrArg Subtype.val (hcomm ⟨x, hQM hx⟩ (Subgroup.mem_subgroupOf.mpr hx))

end Subgroup

theorem isCyclic_fittingSubgroup_of_isCyclic_pCore {X : Type} [Group X] [Finite X]
    (h : ∀ r : ℕ, r.Prime → IsCyclic ↥(CFSG.pCore r X)) :
    IsCyclic ↥(CFSG.fittingSubgroup X) := by
  let F := CFSG.fittingSubgroup X
  have hZ : IsZGroup ↥F := by
    rw [isZGroup_iff]
    intro r hr P
    haveI : Fact r.Prime := ⟨hr⟩
    have hPmap_le : ((P : Subgroup ↥F).map F.subtype) ≤ CFSG.pCore r X :=
      Sylow.map_le_pCore (inferInstance : F.Normal) (inferInstance : Group.IsNilpotent ↥F) r P
    haveI : IsCyclic ↥(CFSG.pCore r X) := h r hr
    have hcyc_map : IsCyclic ↥((P : Subgroup ↥F).map F.subtype) := isCyclic_of_le hPmap_le
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (P : Subgroup ↥F) F.subtype F.subtype_injective)).mpr hcyc_map
  haveI : IsZGroup ↥F := hZ
  exact inferInstance

end CFSG.LocalAnalysis.UniquenessCase.UCK
