module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81Tools
public import CFSG.Sporadic.Recognition.McLASThreeLocalCert
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Local

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4

open CFSG.Sporadic.Schreier (mclP)

theorem factorization_three_mcl : (898128000 : ℕ).factorization 3 = 6 := by
  have h : (898128000 : ℕ) = 3 ^ 6 * 1232000 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 1232000 by norm_num)]

theorem not_forall_comm_of_involution_mclP
    {D : Subgroup mclP}
    (hD : IsPGroup 3 D) (h81 : 81 ≤ Nat.card D) {u : mclP} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) :
    ¬ ∀ d ∈ D, u * d = d * u := by
  intro hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hcard, hconj⟩ := CFSG.Sporadic.SmallOddCore.mclT0_facts
  have hu2' : ((u : Equiv.Perm (Fin 275))) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hu2, Subgroup.coe_one]
  have hu1' : (u : Equiv.Perm (Fin 275)) ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨g, hg, hug⟩ := hconj (u : Equiv.Perm (Fin 275)) u.2 (orderOf_eq_prime hu2' hu1')
  set D' : Subgroup (Equiv.Perm (Fin 275)) :=
    (D.map mclP.subtype).map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hD'le : D' ≤ CFSG.Sporadic.SmallOddCore.mclCt := by
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change g⁻¹ * (d : Equiv.Perm (Fin 275)) * g⁻¹⁻¹ ∈ mclP
      exact mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) d.2) (mclP.inv_mem (mclP.inv_mem hg))
    · rw [Subgroup.mem_centralizer_singleton_iff]
      change g⁻¹ * (d : Equiv.Perm (Fin 275)) * g⁻¹⁻¹ * CFSG.Sporadic.SmallOddCore.mclT0 =
        CFSG.Sporadic.SmallOddCore.mclT0 * (g⁻¹ * (d : Equiv.Perm (Fin 275)) * g⁻¹⁻¹)
      have hdu : (d : Equiv.Perm (Fin 275)) * u = u * d := by
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, (hcomm d hd).symm]
      have ht0 : CFSG.Sporadic.SmallOddCore.mclT0 = g⁻¹ * (u : Equiv.Perm (Fin 275)) * g := by
        rw [hug]
        group
      rw [ht0]
      calc g⁻¹ * (d : Equiv.Perm (Fin 275)) * g⁻¹⁻¹ * (g⁻¹ * u * g)
          = g⁻¹ * ((d : Equiv.Perm (Fin 275)) * u) * g := by group
        _ = g⁻¹ * (u * d) * g := by rw [hdu]
        _ = g⁻¹ * u * g * (g⁻¹ * d * g⁻¹⁻¹) := by group
  have hdvd : Nat.card D ∣ 40320 := by
    rw [← hcard]
    have h1 : Nat.card D' = Nat.card D := by
      rw [hD', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
        Subgroup.card_map_of_injective mclP.subtype_injective]
    rw [← h1]
    exact Subgroup.card_dvd_of_le hD'le
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  rw [hk] at hdvd h81
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h81d : 3 ^ 4 ∣ 40320 := (Nat.pow_dvd_pow 3 hk4).trans hdvd
  norm_num at h81d

theorem e81InvAt_mclP :
    E81InvAt mclP := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, R, T, A, -, -, -, -, hL⟩ :=
    CFSG.Sporadic.Recognition.McLAS.threeLocal_of_embedding mclP.subtype mclP.subtype_injective
      (Subgroup.range_subtype mclP) CFSG.Sporadic.Recognition.McLAS.threeFacts_cert'
      CFSG.Sporadic.Recognition.McLAS.threeLocalCheck_eq_true
  have hT : Nat.card T = 3 ^ (Nat.card mclP).factorization 3 := by
    rw [hL.card_T, CFSG.Sporadic.Schreier.card_mclP, factorization_three_mcl]
    norm_num
  have hA : ∀ B : Subgroup mclP, B ≤ T → IsMulCommutative B → 81 ≤ Nat.card B → B = A :=
    fun B hBT hBc h81 =>
      (hL.abelian_subgroups B hBT hBc).2 (le_antisymm (hL.abelian_subgroups B hBT hBc).1 h81)
  obtain ⟨s, -, -, e, heD, hcard, ⟨hs0, hs1, hs2, hs3⟩, -, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9.exists_klein_basis
  set D := Subgroup.closure (Set.range e) with hD
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    isElemAbelian_of_le CFSG.RankThree.PartTwo.Sec4.Item434SporGen.isElemAbelian_mclD
      ((Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr heD))
  have heD' : ∀ i, e i ∈ D := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hsq : ∀ d ∈ D, s ^ 2 * d = d * s ^ 2 := by
    have hle : D ≤ Subgroup.centralizer ({s ^ 2} : Set mclP) := by
      rw [hD, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hconj : s ^ 2 * e i * (s ^ 2)⁻¹ = e i := by
        have e2 : s ^ 2 * e i * (s ^ 2)⁻¹ = s * (s * e i * s⁻¹) * s⁻¹ := by
          rw [pow_two, mul_inv_rev]
          simp only [mul_assoc]
        rw [e2]
        fin_cases i
        · simp only [Fin.zero_eta] at *
          rw [hs0, hs0]
        · simp only [Fin.mk_one] at *
          rw [hs1, hs1]
        · change s * (s * e 2 * s⁻¹) * s⁻¹ = e 2
          rw [hs2, ← MulAut.conj_apply, map_inv, MulAut.conj_apply, hs2, inv_inv]
        · change s * (s * e 3 * s⁻¹) * s⁻¹ = e 3
          rw [hs3, ← MulAut.conj_apply, map_inv, MulAut.conj_apply, hs3, inv_inv]
      calc e i * s ^ 2 = s ^ 2 * e i * (s ^ 2)⁻¹ * s ^ 2 := by rw [hconj]
        _ = s ^ 2 * e i := by group
    exact fun d hd => (Subgroup.mem_centralizer_singleton_iff.mp (hle hd)).symm
  have hcs := card_inf_centralizer_eq_nine hDe hcard hs0 hs1 hs2 hs3
  obtain ⟨d₀, hd₀, hmove⟩ : ∃ d₀ ∈ D, s * d₀ * s⁻¹ ≠ d₀ := by
    by_contra hall
    push Not at hall
    have hle : D ≤ D ⊓ Subgroup.centralizer ({s} : Set mclP) := by
      refine le_inf le_rfl fun d hd => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * s = s * d * s⁻¹ * s := by rw [hall d hd]
        _ = s * d := by group
    have := Subgroup.card_le_of_le hle
    rw [hcs] at this
    omega
  obtain ⟨t, ht1, ht2, hts⟩ := exists_involution_of_sq hsq hd₀ hmove
    (fun u hu1 hu2 => not_forall_comm_of_involution_mclP (isPGroup_of_isElemAbelian hDe) hcard
      hu1 hu2)
  have ht0 : t * e 0 * t⁻¹ = e 0 := by rw [hts _ (heD' 0), hs0]
  have ht1' : t * e 1 * t⁻¹ = e 1 := by rw [hts _ (heD' 1), hs1]
  have ht2' : t * e 2 * t⁻¹ = (e 2)⁻¹ := by rw [hts _ (heD' 2), hs2]
  have ht3' : t * e 3 * t⁻¹ = (e 3)⁻¹ := by rw [hts _ (heD' 3), hs3]
  have htN : t ∈ Subgroup.normalizer (D : Set mclP) := by
    rw [hD]
    refine mem_normalizer_closure_of_conj_mem ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change t * e 0 * t⁻¹ ∈ D
      rw [ht0]
      exact heD' 0
    · change t * e 1 * t⁻¹ ∈ D
      rw [ht1']
      exact heD' 1
    · change t * e 2 * t⁻¹ ∈ D
      rw [ht2']
      exact D.inv_mem (heD' 2)
    · change t * e 3 * t⁻¹ ∈ D
      rw [ht3']
      exact D.inv_mem (heD' 3)
  exact e81InvAt_of_unique hT hA hDe hcard htN ht1 ht2
    (card_inf_centralizer_eq_nine hDe hcard ht0 ht1' ht2' ht3')

theorem e81InvAt_of_mulEquiv_mcl
    {X : Type*} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.McL) : E81InvAt X :=
  e81InvAt_of_mulEquiv (φ.trans CFSG.Sporadic.Schreier.mclPermEquiv) e81InvAt_mclP

end CFSG.RankThree.PartTwo.Sec6.Res611Res4
