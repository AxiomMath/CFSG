module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreClasses
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.UniquenessCase.UCFront10ExtraspecialBound
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Blueprint CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.KD.Co1K105
open CFSG.EvenSporadicStandard.TwoCo1 (epsMask eMaskA)

private def G : Array (Array ℕ) := gensOf Aa Ba t24Codes

private def Q : Fin 3 → Array ℕ :=
  ![mulM G[0]! G[0]!, mulM G[0]! G[1]!, mulM G[2]! G[2]!]

private noncomputable def q : Fin 3 → PM24 :=
  ![t24Gen 0 * t24Gen 0, t24Gen 0 * t24Gen 1, t24Gen 2 * t24Gen 2]

private def u : Fin 3 → ℕ := ![601, 109, 193]

private theorem co1Odd_check :
    (∀ i : Fin 3, mulM (Q i) (Q i) = idRows 11) ∧
      (∀ i : Fin 3, vecMulN 11 (Q i) (u i) = u i ^^^ 3) ∧
      (∀ i j : Fin 3, j ≠ i → vecMulN 11 (Q j) (u i) = u i) := by
  decide +kernel

private theorem rep_Q (i : Fin 3) :
    Rep (Q i) (q i) := by
  fin_cases i
  · exact rep_mul (rep_t24Gen 0) (rep_t24Gen 0)
  · exact rep_mul (rep_t24Gen 0) (rep_t24Gen 1)
  · exact rep_mul (rep_t24Gen 2) (rep_t24Gen 2)

private theorem q_sq
    (i : Fin 3) : q i ^ 2 = 1 := by
  rw [pow_two]
  have h1 : Rep (mulM (Q i) (Q i)) (q i * q i) := rep_mul (rep_Q i) (rep_Q i)
  rw [co1Odd_check.1 i] at h1
  exact eq_of_rep h1 rep_one

private theorem q_mem_t24 (i : Fin 3) : q i ∈ t24 := by
  fin_cases i
  · exact mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨0, rfl⟩)
  · exact mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩)
  · exact mul_mem (Subgroup.subset_closure ⟨2, rfl⟩) (Subgroup.subset_closure ⟨2, rfl⟩)

private theorem epsHom_ofAdd_add
    (v w : Fin 11 → ZMod 2) :
    epsHom (Multiplicative.ofAdd (v + w)) =
      epsHom (Multiplicative.ofAdd v) * epsHom (Multiplicative.ofAdd w) :=
  map_mul epsHom _ _

private theorem epsMask_xor
    (a b : ℕ) : epsMask (a ^^^ b) = epsMask a * epsMask b := by
  simp only [epsMask, toVecD_xor, epsHom_ofAdd_add]

private theorem epsMask_zero :
    epsMask 0 = 1 := by
  simp only [epsMask, toVecD_zero]
  exact map_one epsHom

private theorem epsMask_sq
    (m : ℕ) : epsMask m ^ 2 = 1 := by
  rw [pow_two, ← epsMask_xor, Nat.xor_self, epsMask_zero]

private theorem epsMask_mem_co1Sylow
    (m : ℕ) :
    epsMask m ∈ co1Sylow :=
  epsHom_range_le_co1Sylow ⟨Multiplicative.ofAdd (toVecD 11 m), rfl⟩

private theorem iota_q_mem_co1Sylow
    (i : Fin 3) :
    iota (q i) ∈ co1Sylow := by
  rw [← theta_inr]
  refine ⟨SemidirectProduct.inr (q i), ?_, rfl⟩
  simpa using q_mem_t24 i

theorem co1_odd
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (A : Subgroup NativeSporadic.Co1) (hA : CFSG.Open.IsElemAbelian p A) (hA1 : A ≠ ⊥)
    (hTA : co1Sylow ≤ Subgroup.normalizer (A : Set NativeSporadic.Co1)) :
    A ⊓ Subgroup.centralizer {epsMask eMaskA} ≠ ⊥ := by
  classical
  intro hbot
  have hfin : Finite NativeSporadic.Co1 := CFSG.Sporadic.Co1.fam_co1_simplicity.1
  have hxA : ∀ i : Fin 3,
      epsMask (u i) ∈ Subgroup.normalizer (A : Set NativeSporadic.Co1) :=
    fun i => hTA (epsMask_mem_co1Sylow (u i))
  have hyA : ∀ i : Fin 3,
      iota (q i) ∈ Subgroup.normalizer (A : Set NativeSporadic.Co1) :=
    fun i => hTA (iota_q_mem_co1Sylow i)
  have hxy : ∀ i : Fin 3, epsMask (u i) * iota (q i) * (epsMask (u i))⁻¹ *
      (iota (q i))⁻¹ = epsMask eMaskA := by
    intro i
    have hxinv : (epsMask (u i))⁻¹ = epsMask (u i) :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using epsMask_sq (u i))
    have hto : Multiplicative.toAdd (Multiplicative.ofAdd (toVecD 11 (u i))) =
        toVecD 11 (u i) := rfl
    have hconj : iota (q i) * epsMask (u i) * (iota (q i))⁻¹ =
        epsHom (Multiplicative.ofAdd (rho (q i) (toVecD 11 (u i)))) := by
      simp only [epsMask, iota_conj, hto]
    have hqi : rho (q i) (toVecD 11 (u i)) = toVecD 11 (u i ^^^ 3) := by
      rw [rep_apply (rep_Q i), co1Odd_check.2.1 i]
    have hadd : toVecD 11 (u i) + rho (q i) (toVecD 11 (u i)) = toVecD 11 3 := by
      rw [hqi, ← toVecD_xor, show u i ^^^ (u i ^^^ 3) = 3 by
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]]
    calc
      epsMask (u i) * iota (q i) * (epsMask (u i))⁻¹ * (iota (q i))⁻¹
          = epsMask (u i) * (iota (q i) * (epsMask (u i))⁻¹ * (iota (q i))⁻¹) := by
              group
      _ = epsMask (u i) * (iota (q i) * epsMask (u i) * (iota (q i))⁻¹) := by
              rw [hxinv]
      _ = epsMask (u i) * epsHom (Multiplicative.ofAdd (rho (q i) (toVecD 11 (u i)))) := by
              rw [hconj]
      _ = epsHom (Multiplicative.ofAdd (toVecD 11 (u i))) *
            epsHom (Multiplicative.ofAdd (rho (q i) (toVecD 11 (u i)))) := rfl
      _ = epsHom (Multiplicative.ofAdd
            (toVecD 11 (u i) + rho (q i) (toVecD 11 (u i)))) :=
              (epsHom_ofAdd_add _ _).symm
      _ = epsHom (Multiplicative.ofAdd (toVecD 11 3)) := by rw [hadd]
      _ = epsMask eMaskA := by simp [epsMask, eMaskA]
  have hcx : ∀ i j : Fin 3, i ≠ j → Commute (epsMask (u i)) (epsMask (u j)) :=
    fun i j _ => Commute.map (mul_comm (Multiplicative.ofAdd (toVecD 11 (u i)))
      (Multiplicative.ofAdd (toVecD 11 (u j)))) epsHom
  have hcxy : ∀ i j : Fin 3, i ≠ j → Commute (epsMask (u i)) (iota (q j)) := by
    intro i j hij
    have hfix : rho (q j) (toVecD 11 (u i)) = toVecD 11 (u i) := by
      rw [rep_apply (rep_Q j), co1Odd_check.2.2 i j (Ne.symm hij)]
    have hto : Multiplicative.toAdd (Multiplicative.ofAdd (toVecD 11 (u i))) =
        toVecD 11 (u i) := rfl
    have hconj : iota (q j) * epsMask (u i) * (iota (q j))⁻¹ = epsMask (u i) := by
      simp only [epsMask, iota_conj, hto, hfix]
    rw [Commute]
    calc
      epsMask (u i) * iota (q j)
          = (iota (q j) * epsMask (u i) * (iota (q j))⁻¹) * iota (q j) := by rw [hconj]
      _ = iota (q j) * epsMask (u i) := by group
  have hbound : p ^ 8 ≤ Nat.card ↥A := by
    have h := @pow_two_pow_le_card_of_config NativeSporadic.Co1 _ hfin p 3 hp (by omega)
      A hA.isElementaryAbelian hA1 (epsMask eMaskA) (epsMask_sq eMaskA) hbot
      (fun i : Fin 3 => epsMask (u i)) (fun i : Fin 3 => iota (q i))
      hxA hyA (fun i => epsMask_sq (u i)) (fun i => by
        calc iota (q i) ^ 2 = iota ((q i) ^ 2) := (map_pow iota (q i) 2).symm
          _ = iota 1 := by rw [q_sq i]
          _ = 1 := map_one iota)
      hxy hcx hcxy
    simpa using h
  have hfact : Fact p.Prime := ⟨hp⟩
  have hAf : Finite ↥A := @Subtype.finite NativeSporadic.Co1 hfin
    (A : Set NativeSporadic.Co1)
  obtain ⟨k, hk⟩ := @IsPGroup.exists_card_eq p ↥A _ hfact hAf hA.isPGroup
  have hk8 : 8 ≤ k := by
    have hle : p ^ 8 ≤ p ^ k := by rwa [hk] at hbound
    have hp1 : 1 < p := by
      have := hp.two_le
      omega
    exact (Nat.pow_le_pow_iff_right hp1).mp hle
  have hpow : p ^ 8 ∣ Nat.card ↥A := by
    rw [hk]
    exact Nat.pow_dvd_pow p hk8
  have hcardA : Nat.card ↥A ∣ 4157776806543360000 := by
    rw [← CFSG.Sporadic.Co1.card_Co1]
    exact Subgroup.card_subgroup_dvd_card A
  have hpdvd : p ^ 8 ∣ 4157776806543360000 := dvd_trans hpow hcardA
  have hfac : 4157776806543360000 = 2 ^ 21 * 3 ^ 9 * 100725625 := by norm_num
  rw [hfac] at hpdvd
  have hcop : Nat.Coprime (p ^ 8) (2 ^ 21 * 3 ^ 9) := by
    have hp2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd (n := 2)).2 fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hp3 : Nat.Coprime p 3 := (hp.coprime_iff_not_dvd (n := 3)).2 fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact ((hp2.pow_right 21).mul_right (hp3.pow_right 9)).pow_left 8
  have hodd : p ^ 8 ∣ 100725625 := hcop.dvd_of_dvd_mul_left hpdvd
  have hle : p ^ 8 ≤ 100725625 := Nat.le_of_dvd (by norm_num) hodd
  have hp10 : p ≤ 10 := by
    by_contra h
    have hp11 : 11 ≤ p := by omega
    have hge : 11 ^ 8 ≤ p ^ 8 := Nat.pow_le_pow_left hp11 8
    norm_num at hge
    omega
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p <;> first | (norm_num at hp; done) | norm_num
  rcases hp57 with rfl | rfl <;> norm_num at hodd

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
