module

public import CFSG.RankThree.PartOne.S12.Sec12Two
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem false_of_quasisimple_le_centralizer (h : Sec12Hyp G p A c L E) (hE4 : Nat.card E = p ^ 4)
    {K : Subgroup G} (hK : IsQuasisimple K) (hKE : K ≤ Subgroup.centralizer (E : Set G)) :
    False := by
  have hp := h.prime
  have : Nontrivial K := LocalCores.isQuasisimple_nontrivial hK
  have hperf : Group.IsPerfect K := hK.1
  have hev : Even (Nat.card K) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact Group.IsPerfect.not_isSolvable K (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hev)
  have hsG : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe, hs]
  have hs1 : (s : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hsG
    omega
  set S : Subgroup G := Subgroup.zpowers (s : G) with hS
  have hS2 : IsPGroup 2 S := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hS, Nat.card_zpowers, hsG, pow_one]
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hs1
    have : (s : G) ∈ S := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hEN : E ≤ Subgroup.normalizer (S : Set G) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : (s : G) * e = e * s := (Subgroup.mem_centralizer_iff.mp (hKE s.2) e he).symm
    exact (Commute.zpow_left (show Commute (s : G) e from hc) i).eq
  have hloc : IsTwoLocal (Subgroup.normalizer (S : Set G)) := ⟨S, hSne, hS2, rfl⟩
  have h4 : 4 ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (S : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (E := E) (k := 4) hEN
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp h.E_elem) hE4
  have h5 := Sec12Two.pRank_le_evenRank_of_isTwoLocal hp (by have := h.three_lt; omega) hloc
  rw [h.evenRank_eq] at h5
  omega

theorem subnormal_inf_subgroupOf (h : Sec12Hyp G p A c L E) {X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer ({c} : Set G)) : ((L ⊓ X).subgroupOf X).IsSubnormal := by
  have hsn := isSubnormal_of_mem_thetaComponentsAt h.L_mem.2
  have h1 := hsn.comap (Subgroup.inclusion hX)
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩

omit [Finite G] in
theorem pElementSubgroup_eq_of_simple {B : Subgroup G} (hB : IsSimpleGroup B) {z : G}
    (hzB : z ∈ B) (hzp : orderOf z = p) (hz1 : z ≠ 1) : pElementSubgroup p B = B := by
  refine le_antisymm ((Subgroup.closure_le B).mpr fun x hx => hx.1) fun b hb => ?_
  set H' : Subgroup B := (pElementSubgroup p B).subgroupOf B with hH'
  have hz' : (⟨z, hzB⟩ : B) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hN : Subgroup.normalClosure {(⟨z, hzB⟩ : B)} = ⊤ := by
    rcases (Subgroup.normalClosure_normal (s := {(⟨z, hzB⟩ : B)})).eq_bot_or_eq_top with h0 | h0
    · exfalso
      have : (⟨z, hzB⟩ : B) ∈ Subgroup.normalClosure {(⟨z, hzB⟩ : B)} :=
        Subgroup.subset_normalClosure rfl
      rw [h0, Subgroup.mem_bot] at this
      exact hz' this
    · exact h0
  have hle : Subgroup.normalClosure {(⟨z, hzB⟩ : B)} ≤ H' := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hord : orderOf (g * ⟨z, hzB⟩ * g⁻¹ : B) = p := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hzp]
    have hmem : (((g * ⟨z, hzB⟩ * g⁻¹ : B)) : G) ∈
        {x : G | x ∈ B ∧ ∃ k : ℕ, orderOf x = p ^ k} :=
      ⟨(g * ⟨z, hzB⟩ * g⁻¹ : B).2, 1, by rw [Subgroup.orderOf_coe, hord, pow_one]⟩
    exact Subgroup.subset_closure hmem
  have : (⟨b, hb⟩ : B) ∈ H' := hle (hN ▸ Subgroup.mem_top _)
  exact this

theorem kZero_eq_of_block (h : Sec12Hyp G p A c L E) (hE4 : Nat.card E = p ^ 4) (t : MulAut E)
    (hct : c ∈ autFixedInG E t) {B : Subgroup G} {z : G} (hBL : B ≤ L)
    (hBX : B ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    (hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hBqs : IsQuasisimple B) (hBc : Subgroup.center B = ⊥) (hzB : z ∈ B) (hzE : z ∈ E)
    (hz1 : z ≠ 1)
    (hE : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i) :
    kZero p E t = B := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer (autFixedInG E t : Set G) with hXdef
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hx y hct
  have hYsn := subnormal_inf_subgroupOf h hXc
  set B' : Subgroup X := B.subgroupOf X with hB'
  have hB'qs : IsQuasisimple B' :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBX).symm hBqs
  have hB'sn : B'.IsSubnormal := by
    refine Subgroup.IsSubnormal.step B' ((L ⊓ X).subgroupOf X)
      (fun b hb => ?_) hYsn ?_
    · rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact Subgroup.mem_inf.mpr ⟨hBL hb, hBX hb⟩
    · refine ⟨fun n hn g => ?_⟩
      have hn' : (((n : (L ⊓ X).subgroupOf X) : X) : G) ∈ B := hn
      have hg : ((((g : (L ⊓ X).subgroupOf X) : X) : G)) ∈ L ⊓ X := g.2
      show ((((g * n * g⁻¹ : (L ⊓ X).subgroupOf X) : X) : G)) ∈ B
      exact hBnorm _ hg _ hn'
  have hcomp : ∀ K : Subgroup X, IsComponent K → K = B' := by
    intro K hK
    by_contra hne
    rcases LocalCores.distinct_components_commute hK ⟨hB'qs, hB'sn⟩ with h1 | h1
    · exact hne h1
    · have hKq : IsQuasisimple (K.map X.subtype) :=
        LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective K X.subtype
          X.subtype_injective) hK.1
      refine false_of_quasisimple_le_centralizer h hE4 hKq fun k hk => ?_
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨u, hu, i, rfl⟩ := hE e he
      have hzX : z ∈ X := hBX hzB
      have hzB' : (⟨z, hzX⟩ : X) ∈ B' := hzB
      have hcomm : k' * ⟨z, hzX⟩ = ⟨z, hzX⟩ * k' := by
        have := Subgroup.commutator_mem_commutator hk' hzB'
        rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have hz2 : (z : G) * (k' : G) = (k' : G) * z := congrArg Subtype.val hcomm.symm
      have hu2 : u * (k' : G) = (k' : G) * u := (Subgroup.mem_centralizer_iff.mp k'.2 u hu)
      have hzi : (z : G) ^ i * (k' : G) = (k' : G) * z ^ i :=
        (Commute.zpow_left (show Commute z (k' : G) from hz2) i).eq
      show u * z ^ i * (k' : G) = (k' : G) * (u * z ^ i)
      rw [mul_assoc, hzi, ← mul_assoc, hu2, mul_assoc]
  have hlayer : layer X = B' :=
    le_antisymm (sSup_le fun K hK => (hcomp K hK).le) (le_sSup ⟨hB'qs, hB'sn⟩)
  have hin : inSubgroup (fun K _ => layer K) X = B := by
    show (layer X).map X.subtype = B
    rw [hlayer, hB', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hBX
  have hsimple : IsSimpleGroup B := by
    have h1 : IsSimpleGroup (B ⧸ Subgroup.center B) := hBqs.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hBc).trans QuotientGroup.quotientBot
      ).symm.isSimpleGroup
  have hzord : orderOf z = p := orderOf_eq_prime (by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian z hzE) hz1
  unfold kZero
  rw [hin]
  exact pElementSubgroup_eq_of_simple hsimple hzB hzord hz1

end CFSG.RankThree.PartOne.KFU
