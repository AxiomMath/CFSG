module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem eq_one_of_orderOf_dvd_two_pow_of_dvd_odd {x : G} {k m : ℕ} (hm : Odd m)
    (h2 : orderOf x ∣ 2 ^ k) (hodd : orderOf x ∣ m) : x = 1 := by
  rw [← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h2 ((Nat.coprime_two_left.mpr hm).pow_left k)) hodd

theorem eq_bot_of_isPGroup_two_of_odd [Finite G] {H : Subgroup G} (h2 : IsPGroup 2 H)
    (hodd : Odd (Nat.card H)) : H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rcases k with _ | k
  · exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
  · exact absurd (hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd.not_two_dvd_nat

theorem exists_normal_odd_two_power_index_of_odd_commutator [Finite G]
    (hodd : Odd (Nat.card (commutator G))) :
    ∃ Q₀ : Subgroup G, Q₀.Normal ∧ Odd (Nat.card Q₀) ∧ ∃ k : ℕ, Q₀.index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hNC : normalizer (T : Set G) ≤ centralizer (T : Set G) := by
    intro n hn
    rw [mem_centralizer_iff]
    intro s hs
    have hc1 : n * s * n⁻¹ * s⁻¹ ∈ (T : Subgroup G) :=
      mul_mem ((mem_normalizer_iff.mp hn s).mp hs) (inv_mem hs)
    have hc2 : n * s * n⁻¹ * s⁻¹ ∈ commutator G := by
      rw [_root_.commutator_def, ← commutatorElement_def]
      exact commutator_mem_commutator (mem_top n) (mem_top s)
    have h1 : n * s * n⁻¹ * s⁻¹ = 1 := eq_one_of_orderOf_dvd_two_pow_of_dvd_odd hodd
      (hk ▸ Subgroup.orderOf_dvd_natCard _ hc1) (Subgroup.orderOf_dvd_natCard _ hc2)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  obtain ⟨K, hKn, hK2, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement T hNC
  exact ⟨K, hKn, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK2), k, hKidx.trans hk⟩

theorem cyclic_normal_odd_derived_quotient_normal_hall_odd {M : Type*} [Group M] [Finite M]
    (D : Subgroup M) [D.Normal] (hD : IsCyclic D)
    (hodd : Odd (Nat.card (commutator (M ⧸ D)))) :
    ∃ B : Subgroup M, B.Normal ∧ Odd (Nat.card B) ∧ (∃ k : ℕ, B.index = 2 ^ k) ∧
      ∀ E : Subgroup M, Odd (Nat.card E) → ∀ S : Subgroup M,
        E ≤ B ∧ ⁅S, E⁆ ≤ B ∧ Odd (Nat.card (⁅S, E⁆ : Subgroup M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀n, hQ₀odd, k₀, hQ₀idx⟩ := exists_normal_odd_two_power_index_of_odd_commutator hodd
  set P : Subgroup M := Q₀.comap (QuotientGroup.mk' D) with hPdef
  have hPn : P.Normal := hQ₀n.comap _
  have hPidx : P.index = 2 ^ k₀ := by
    rw [hPdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D), hQ₀idx]
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hSD : (S : Subgroup P).map P.subtype ≤ D := by
    have hle : (S : Subgroup P).map ((QuotientGroup.mk' D).comp P.subtype) ≤ Q₀ := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hbot := eq_bot_of_isPGroup_two_of_odd (S.isPGroup'.map _)
      (Odd.of_dvd_nat hQ₀odd (Subgroup.card_dvd_of_le hle))
    rintro _ ⟨x, hx, rfl⟩
    have hmem : (QuotientGroup.mk' D).comp P.subtype x ∈
        (S : Subgroup P).map ((QuotientGroup.mk' D).comp P.subtype) := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff _).mp hmem
  have hScyc : IsCyclic (S : Subgroup P) := by
    let f : (S : Subgroup P) →* D :=
      { toFun := fun x => ⟨((x : P) : M), hSD ⟨x, x.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine isCyclic_of_injective f fun x y hxy => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : D => (z : M)) hxy))
  obtain ⟨-, -, -, ⟨hKn, hKodd, hKidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  set K := pPrimeCore 2 P with hKdef
  set B : Subgroup M := K.map P.subtype with hBdef
  have hBodd : Odd (Nat.card B) := by
    rwa [hBdef, Subgroup.card_map_of_injective P.subtype_injective]
  have hBidx : B.index = 2 ^ (a + k₀) := by
    rw [hBdef, Subgroup.index_map_subtype, hKidx, ha, hPidx, pow_add]
  have hle : ∀ E : Subgroup M, Odd (Nat.card E) → E ≤ B := by
    intro E hE
    have hEP : E ≤ P := CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient (p := 2) P E
      (IsPGroup.of_card hPidx) hE.not_two_dvd_nat
    have hEK : E.subgroupOf P ≤ K := by
      have : K.Normal := hKn
      refine CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient (p := 2) K _
        (IsPGroup.of_card (hKidx.trans ha)) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv]
      exact hE.not_two_dvd_nat
    intro x hx
    exact ⟨⟨x, hEP hx⟩, hEK hx, rfl⟩
  have hBn : B.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hzp : Odd (Nat.card (zpowers (g * n * g⁻¹))) := by
      rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hn)
    exact hle _ hzp (mem_zpowers _)
  refine ⟨B, hBn, hBodd, ⟨a + k₀, hBidx⟩, fun E hE S' => ?_⟩
  have hEB := hle E hE
  have hcomm : ⁅S', E⁆ ≤ B := (commutator_mono le_rfl hEB).trans (commutator_le_right S' B)
  exact ⟨hEB, hcomm, Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le hcomm)⟩

end CFSG.RankThree.GroupTheory
