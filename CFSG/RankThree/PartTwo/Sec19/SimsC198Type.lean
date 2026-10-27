module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {Y : Type} [Group Y] [Finite Y]

private theorem exists_model (hq : IsQuasisimple Y) (h : Sec4.IsSLThreePi Y) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ 2 < p ^ f ∧ Nonempty (Y ≃* Sec4.slPi π 3 (p ^ f) K) := by
  obtain ⟨π, p, f, K, _, hK, hq3, h2, ⟨e⟩⟩ := Sec4.exists_slPi_model (L := (⊤ : Subgroup Y))
    (Sec13.isSLThreePi_of_mulEquiv Subgroup.topEquiv.symm h)
    (LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq)
  exact ⟨π, p, f, K, inferInstance, hK, hq3, h2, ⟨Subgroup.topEquiv.symm.trans e⟩⟩

private theorem card_of_isTripleCover {S : Type*} [Group S] (h : Sec4.IsTripleCover Y S) :
    Nat.card Y = 3 * Nat.card S := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), h3,
    Nat.card_congr e.toEquiv, mul_comm]

private theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem IsType198.card_center (hq : IsQuasisimple Y) (ht : IsType198 Y) :
    Nat.card (Subgroup.center Y) = 3 := by
  rcases ht with h | h | h
  · obtain ⟨π, p, f, K, _, hK, hq3, -, ⟨e⟩⟩ := exists_model hq h
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact KFacts.card_center_slPi hK hq3
  · exact h.1
  · exact h.1

@[expose] def IsType198Card (N : ℕ) : Prop :=
  (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ p ^ k % 3 = 1 ∧
      N = (p ^ k) ^ 3 * ((p ^ k) ^ 2 - 1) * ((p ^ k) ^ 3 - 1)) ∨
  (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ p ^ k % 3 = 2 ∧ 2 < p ^ k ∧
      N = (p ^ k) ^ 3 * ((p ^ k) ^ 2 - 1) * ((p ^ k) ^ 3 + 1)) ∨
  N = 7560 ∨ N = 3 * Nat.card CFSG.Blueprint.NativeSporadic.M22

theorem IsType198.card_cases (hq : IsQuasisimple Y) (ht : IsType198 Y) :
    IsType198Card (Nat.card Y) := by
  rcases ht with hSL | hA7 | hM22
  · obtain ⟨π, p, f, K, _, hK, hq3, h2, ⟨e⟩⟩ := exists_model hq hSL
    have hcard : Nat.card Y = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) *
        cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
      rw [Nat.card_congr e.toEquiv, Sec13.card_slPi_three hK]
    cases π
    · exact Or.inr (Or.inl ⟨p, f, hK.prime, hK.one_le, hq3, h2, hcard⟩)
    · exact Or.inl ⟨p, f, hK.prime, hK.one_le, hq3, hcard⟩
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [card_of_isTripleCover hA7, card_alternatingGroup_seven]
  · exact Or.inr (Or.inr (Or.inr (card_of_isTripleCover hM22)))

theorem IsType198.le_card (hq : IsQuasisimple Y) (ht : IsType198 Y) : 7560 ≤ Nat.card Y := by
  rcases ht.card_cases hq with ⟨p, k, hp, hk, h3, hN⟩ | ⟨p, k, hp, hk, h3, h2, hN⟩ | hN | hN
  · have hq2 : 2 ≤ p ^ k := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hqdef] at hq2 h3 hN
    have hq4 : 4 ≤ q := by omega
    have h1 : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    have h4 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have h5 : 63 ≤ q ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h4) h5
    omega
  · obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ k := ⟨_, rfl⟩
    rw [← hqdef] at h2 h3 hN
    have hq5 : 5 ≤ q := by omega
    have h1 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
    have h4 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
      omega
    have h5 : 126 ≤ q ^ 3 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h4) h5
    omega
  · omega
  · have := CFSG.Sporadic.Bridge.M22.le_card_native
    omega

theorem IsType198.not_isMulCommutative_sylow (hq : IsQuasisimple Y) (ht : IsType198 Y)
    (P : Sylow 3 Y) : ¬ IsMulCommutative (P : Subgroup Y) := by
  intro hcomm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect Y := hq.1
  have hZ : Nat.card (Subgroup.center Y) = 3 := ht.card_center hq
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3 (by rw [hZ])
  letI : CommGroup (P : Subgroup Y) := IsMulCommutative.instCommGroup
  have key : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * (z : Y) ^ k * g₀ ∈ (P : Subgroup Y) →
      g₀⁻¹ * (z : Y) ^ k * g₀ = (z : Y) ^ k := by
    intro k g₀ _
    have hc : (z : Y) ^ k ∈ Subgroup.center Y := Subgroup.pow_mem _ z.2 k
    rw [Subgroup.mem_center_iff] at hc
    rw [mul_assoc, ← hc g₀, inv_mul_cancel_left]
  have hV := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup Y)) (z : Y) key
  have hV1 : MonoidHom.transfer (MonoidHom.id (P : Subgroup Y)) (z : Y) = 1 := by
    have hle : _root_.commutator Y ≤
        (MonoidHom.transfer (MonoidHom.id (P : Subgroup Y)) : Y →* (P : Subgroup Y)).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.1 (hle Group.IsPerfect.mem_commutator)
  rw [hV1] at hV
  have h1 : (z : Y) ^ (P : Subgroup Y).index = 1 := by
    have := congrArg Subtype.val hV.symm
    simpa using this
  have h3 : orderOf (z : Y) ∣ (P : Subgroup Y).index := orderOf_dvd_of_pow_eq_one h1
  rw [Subgroup.orderOf_coe, hz] at h3
  exact P.not_dvd_index h3

theorem IsType198.twentySeven_dvd (hq : IsQuasisimple Y) (ht : IsType198 Y) :
    27 ∣ Nat.card Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Y) := inferInstance
  have hnc := ht.not_isMulCommutative_sylow hq P
  have hcard : Nat.card (P : Subgroup Y) = 3 ^ (Nat.card Y).factorization 3 :=
    P.card_eq_multiplicity
  have hn : 3 ≤ (Nat.card Y).factorization 3 := by
    by_contra hlt
    push Not at hlt
    apply hnc
    generalize (Nat.card Y).factorization 3 = n at hcard hlt
    interval_cases n
    · have h1 : Nat.card (P : Subgroup Y) = 1 := by simpa using hcard
      haveI : Subsingleton (P : Subgroup Y) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · haveI : IsCyclic (P : Subgroup Y) := isCyclic_of_prime_card (p := 3) (by simpa using hcard)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  calc 27 = 3 ^ 3 := by norm_num
    _ ∣ 3 ^ (Nat.card Y).factorization 3 := pow_dvd_pow 3 hn
    _ ∣ Nat.card Y := Nat.ordProj_dvd _ _

theorem IsType198.exists_elemAbelian (hq : IsQuasisimple Y) (ht : IsType198 Y) :
    ∃ B : Subgroup Y, CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Y) := inferInstance
  have hnc : ¬ IsCyclic (P : Subgroup Y) := fun hc =>
    ht.not_isMulCommutative_sylow hq P inferInstance
  haveI : Fact (IsPGroup 3 (P : Subgroup Y)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  haveI := hSel
  refine ⟨S.map (P : Subgroup Y).subtype, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    have h3 : s ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := S) s hs
    change ((s ^ 3 : (P : Subgroup Y)) : Y) = 1
    rw [h3]
    rfl
  · rw [Subgroup.card_map_of_injective (P : Subgroup Y).subtype_injective, hScard]
    norm_num

end CFSG.RankThree.PartTwo.Sec19.SimsC198
