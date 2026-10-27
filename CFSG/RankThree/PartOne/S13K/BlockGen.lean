module

public import CFSG.RankThree.PartOne.KF.U4Ambient
public import CFSG.RankThree.PartOne.S12.Sec132
import CFSG.RankThree.PartOne.S12.PerfectOddPrime

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kZero_eq_of_block_gen (h : Sec12Hyp G p A c L E) (t : MulAut E)
    (hct : c ∈ autFixedInG E t) {B : Subgroup G} {z : G} (hBL : B ≤ L)
    (hBX : B ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    (hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hBqs : IsQuasisimple B) (hBc : Subgroup.center B = ⊥) (hzB : z ∈ B) (hzE : z ∈ E)
    (hz1 : z ≠ 1) (hE : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i) :
    kZero p E t = B := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
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
  have hB'map : B'.map X.subtype = B := by
    rw [hB', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hBX
  have hzX : z ∈ X := hBX hzB
  have hzB' : (⟨z, hzX⟩ : X) ∈ B' := hzB
  have hcomm : ∀ K : Subgroup X, IsComponent K → K ≠ B' → ⁅K, B'⁆ = ⊥ := by
    intro K hK hne
    rcases LocalCores.distinct_components_commute hK ⟨hB'qs, hB'sn⟩ with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hKE : ∀ K : Subgroup X, IsComponent K → K ≠ B' →
      K.map X.subtype ≤ Subgroup.centralizer (E : Set G) := by
    intro K hK hne k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨u, hu, i, rfl⟩ := hE e he
    have hcm : k' * ⟨z, hzX⟩ = ⟨z, hzX⟩ * k' := by
      have := Subgroup.commutator_mem_commutator hk' hzB'
      rw [hcomm K hK hne, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hz2 : (z : G) * (k' : G) = (k' : G) * z := congrArg Subtype.val hcm.symm
    have hu2 : u * (k' : G) = (k' : G) * u := (Subgroup.mem_centralizer_iff.mp k'.2 u hu)
    have hzi : (z : G) ^ i * (k' : G) = (k' : G) * z ^ i :=
      (Commute.zpow_left (show Commute z (k' : G) from hz2) i).eq
    show u * z ^ i * (k' : G) = (k' : G) * (u * z ^ i)
    rw [mul_assoc, hzi, ← mul_assoc, hu2, mul_assoc]
  set S : Set (Subgroup G) :=
    {M | ∃ K : Subgroup X, IsComponent K ∧ K ≠ B' ∧ K.map X.subtype = M} with hSdef
  set T : Subgroup G := sSup S with hTdef
  have hSE : ∀ M ∈ S, M ≤ Subgroup.centralizer (E : Set G) := by
    rintro M ⟨K, hK, hne, rfl⟩
    exact hKE K hK hne
  have hSB : ∀ M ∈ S, M ≤ Subgroup.centralizer (B : Set G) := by
    rintro M ⟨K, hK, hne, rfl⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hB'map, ← Subgroup.map_commutator,
      hcomm K hK hne, Subgroup.map_bot]
  have hSp : ∀ M ∈ S, Group.IsPerfect M := by
    rintro M ⟨K, hK, -, rfl⟩
    exact isPerfect_map_subtype' hK.1.1
  have hTB : T ≤ Subgroup.centralizer (B : Set G) := sSup_le hSB
  have hTE : T ≤ Subgroup.centralizer (E : Set G) := sSup_le hSE
  have hTp : Group.IsPerfect T := isPerfect_sSup_of_forall_isPerfect' hSp
  have hT3 : ¬ p ∣ Nat.card T := by
    intro hdvd
    obtain ⟨e, he, hecenter⟩ := exists_pow_eq_one_not_mem_center_of_isPerfect hp2 hTp hdvd
    have heE : (e : G) ∈ E :=
      h.mem_of_pow_eq_one_of_commute (by simpa using congrArg Subtype.val he)
        (fun a ha => Subgroup.mem_centralizer_iff.mp (hTE e.2) a ha)
    apply hecenter
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTE w.2) e heE).symm
  have hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) p := by
    intro v hv
    have hdvd : orderOf v ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk v hv]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hT3).symm
  have hlayer : inSubgroup (fun K _ => layer K) X ≤ B ⊔ T := by
    show (layer ↥X).map X.subtype ≤ _
    rw [Subgroup.map_le_iff_le_comap, CFSG.layer]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    by_cases hKB : K = B'
    · rw [hKB, hB'map]
      exact le_sup_left
    · exact (le_sSup ⟨K, hK, hKB, rfl⟩ : K.map X.subtype ≤ T).trans le_sup_right
  have hBlayer : B ≤ inSubgroup (fun K _ => layer K) X := by
    show B ≤ (layer ↥X).map X.subtype
    rw [← hB'map]
    exact Subgroup.map_mono (le_sSup ⟨hB'qs, hB'sn⟩)
  have hK0le : kZero p E t ≤ B := by
    unfold kZero pElementSubgroup
    rw [Subgroup.closure_le]
    rintro x ⟨hxY, k, hk⟩
    have hxk : x ^ (p ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one x
    exact mem_of_pow_eq_one_of_mem_sup_centralizer' hTB hcop (hlayer hxY) hxk
  have hsimple : IsSimpleGroup B := by
    have h1 : IsSimpleGroup (B ⧸ Subgroup.center B) := hBqs.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hBc).trans QuotientGroup.quotientBot
      ).symm.isSimpleGroup
  have hzord : orderOf z = p := orderOf_eq_prime (by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian z hzE) hz1
  have hBK0 : B ≤ kZero p E t := by
    rw [← pElementSubgroup_eq_of_simple hsimple hzB hzord hz1]
    unfold kZero pElementSubgroup
    exact Subgroup.closure_mono fun x hx => ⟨hBlayer hx.1, hx.2⟩
  exact le_antisymm hK0le hBK0

end CFSG.RankThree.PartOne.S13K
