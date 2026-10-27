module

public import CFSG.Quasithin.EmptyFaithful.S151T1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem s151t_inf_normalizer_inf (S L : Subgroup G) :
    S ⊓ Subgroup.normalizer (L : Set G) ⊓ L = S ⊓ L := by
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩

theorem s151t_between_prime_index [Finite G] {B M P : Subgroup G} (hBM : B ≤ M) (hMP : M ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) : M = B ∨ M = P := by
  have hBP : B ≤ P := hBM.trans hMP
  have hrel : B.relIndex P = 3 := by
    have h1 := Subgroup.relIndex_mul_card B P
    rw [inf_eq_left.mpr hBP] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    have h2 : B.relIndex P * Nat.card ↥B = 3 * Nat.card ↥B := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have h1 := Subgroup.relIndex_mul_relIndex B M P hBM hMP
  rw [hrel] at h1
  have hd : B.relIndex M ∣ 3 := ⟨M.relIndex P, h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h2 | h2
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hBM
  · right
    rw [h2] at h1
    have h3 : M.relIndex P = 1 := by omega
    exact le_antisymm hMP (Subgroup.relIndex_eq_one.mp h3)

namespace WreathCfg

variable {L P S : Subgroup G} {s : G} (c : WreathCfg L P S s)
include c

theorem B_le_P : S ⊓ L ≤ P := by
  have h := c.par.sl
  rwa [s151t_inf_normalizer_inf] at h

theorem S_maximal [Finite G] {K : Subgroup G} (hSK : S ≤ K) (hKH : K ≤ P ⊔ S) :
    K = S ∨ K = P ⊔ S := by
  have hBS : S ⊓ L ≤ S := inf_le_left
  have hBK : S ⊓ L ≤ P ⊓ K := le_inf c.B_le_P (hBS.trans hSK)
  have hPK : P ⊓ K ≤ P := inf_le_left
  have hcard : Nat.card ↥P = 3 * Nat.card ↥(S ⊓ L : Subgroup G) := by
    have h := c.par.idx
    rwa [s151t_inf_normalizer_inf] at h
  rcases s151t_between_prime_index hBK hPK hcard with h | h
  ·
    left
    refine le_antisymm ?_ hSK
    have hP'C : B6.conjSub s P ≤ Subgroup.centralizer (L : Set G) :=
      ((B6.conjSub s).le_iff_le.mpr c.par.le).trans c.L'_le_centralizer
    have aux : ∀ p ∈ P, ∀ p' ∈ B6.conjSub s P, p * p' ∈ K → ∀ b ∈ S ⊓ L, p * b * p⁻¹ ∈ S ⊓ L := by
      intro p hp p' hp' hpp b hb
      have hbL : b ∈ L := hb.2
      have hbp' : b * p' = p' * b := Subgroup.mem_centralizer_iff.mp (hP'C hp') b hbL
      have hbK : b ∈ K := hSK hb.1
      have e1 : (p * p') * b * (p * p')⁻¹ * b⁻¹ = p * b * p⁻¹ * b⁻¹ := by
        calc (p * p') * b * (p * p')⁻¹ * b⁻¹ = p * (p' * b) * p'⁻¹ * p⁻¹ * b⁻¹ := by group
          _ = p * (b * p') * p'⁻¹ * p⁻¹ * b⁻¹ := by rw [hbp']
          _ = p * b * p⁻¹ * b⁻¹ := by group
      have hmem : p * b * p⁻¹ * b⁻¹ ∈ K := by
        rw [← e1]
        exact K.mul_mem (K.mul_mem (K.mul_mem hpp hbK) (K.inv_mem hpp)) (K.inv_mem hbK)
      have hmemP : p * b * p⁻¹ * b⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem (P.mul_mem hp (c.B_le_P hb)) (P.inv_mem hp)) (P.inv_mem (c.B_le_P hb))
      have hmemB : p * b * p⁻¹ * b⁻¹ ∈ S ⊓ L := by
        rw [← h]
        exact ⟨hmemP, hmem⟩
      have e2 : p * b * p⁻¹ = (p * b * p⁻¹ * b⁻¹) * b := by group
      rw [e2]
      exact (S ⊓ L).mul_mem hmemB hb
    have key : ∀ n ∈ P ⊔ B6.conjSub s P, n ∈ K → n ∈ S := by
      intro n hn hnK
      obtain ⟨p, hp, p', hp', rfl⟩ := c.mem_N hn
      have hcomm : p * p' = p' * p :=
        Subgroup.mem_centralizer_iff.mp (c.P'_le_centralizer hp') p hp
      have hinv : p⁻¹ * p'⁻¹ ∈ K := by
        have : p⁻¹ * p'⁻¹ = (p * p')⁻¹ := by rw [hcomm, mul_inv_rev]
        rw [this]
        exact K.inv_mem hnK
      have hpN : p ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => aux p hp p' hp' hnK x hx, fun hx => ?_⟩
        have := aux p⁻¹ (P.inv_mem hp) p'⁻¹ ((B6.conjSub s P).inv_mem hp') hinv _ hx
        have e : p⁻¹ * (p * x * p⁻¹) * p⁻¹⁻¹ = x := by group
        rwa [e] at this
      have hpB : p ∈ S ⊓ L := by
        rcases s151t_between_prime_index (B := S ⊓ L)
          (M := P ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) (P := P)
          (le_inf c.B_le_P Subgroup.le_normalizer) inf_le_left hcard with hM | hM
        · rw [← hM]
          exact ⟨hp, hpN⟩
        · exfalso
          apply c.par.nn
          rw [s151t_inf_normalizer_inf]
          intro x hx
          have : x ∈ P ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
            rw [hM]; exact hx
          exact this.2
      have hp'K : p' ∈ K := by
        have : p' = p⁻¹ * (p * p') := by group
        rw [this]
        exact K.mul_mem (K.inv_mem (hSK hpB.1)) hnK
      have hp'S : p' ∈ S := by
        have h1 : s⁻¹ * p' * s ∈ P := B6.mem_conjSub.mp hp'
        have h2 : s⁻¹ * p' * s ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem (hSK c.hs)) hp'K) (hSK c.hs)
        have h3 : s⁻¹ * p' * s ∈ S ⊓ L := by
          rw [← h]
          exact ⟨h1, h2⟩
        have e : p' = s * (s⁻¹ * p' * s) * s⁻¹ := by group
        rw [e]
        exact S.mul_mem (S.mul_mem c.hs h3.1) (S.inv_mem c.hs)
      exact S.mul_mem hpB.1 hp'S
    intro k hk
    obtain ⟨n, hn, t, ht, rfl⟩ := c.mem_H (hKH hk)
    have hnK : n ∈ K := by
      have := K.mul_mem hk (K.inv_mem (hSK ht))
      simpa using this
    exact S.mul_mem (key n hn hnK) ht
  ·
    right
    refine le_antisymm hKH (sup_le ?_ hSK)
    rw [← h]
    exact inf_le_right

theorem S_not_normal : ¬ (P ⊔ S ≤ Subgroup.normalizer (S : Set G)) := by
  intro hH
  apply c.par.nn
  rw [s151t_inf_normalizer_inf]
  intro x hx
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := hH (Subgroup.mem_sup_left hx)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (c.par.le hx)
  exact zb_mem_normalizer_inf hxS hxL

theorem isMinParabolic [Finite G] (hSyl : IsSylowTwoOf S (P ⊔ S)) :
    IsMinParabolicOf (P ⊔ S) (P ⊔ S) := by
  have hlt : S < P ⊔ S := by
    refine lt_of_le_of_ne le_sup_right fun he => c.S_not_normal ?_
    rw [← he]
    exact Subgroup.le_normalizer
  have hmax : IsMaxSubgroupIn (P ⊔ S) S := by
    refine ⟨hlt, fun K hSK hKH => ?_⟩
    rcases c.S_maximal hSK.le hKH with h' | h'
    · exact absurd h' (ne_of_gt hSK)
    · exact h'
  have huniq : IsUniqueMaxOver (P ⊔ S) S S := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmax, le_rfl⟩, fun N hN => ?_⟩
    rcases c.S_maximal hN.2 hN.1.1.le with h' | h'
    · exact h'
    · exact absurd h' (ne_of_lt hN.1.1)
  exact (minParabolic_iff.mp ⟨hSyl, c.S_not_normal, huniq⟩).1

end WreathCfg

end CFSG.Quasithin
