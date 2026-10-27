module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3Dickson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_normalizer_three_eq_or_top
    (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hq3 : Nat.card K % 3 = 1) (hq13 : 13 ≤ Nat.card K)
    {A H : Subgroup (PSL2MatrixGroup K)} (hA : Nat.card A = 3)
    (hAH : Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) ≤ H) :
    H = Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) ∨ H = ⊤ := by
  have hp : p.Prime := Fact.out
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hK
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK]
    exact Nat.odd_iff.1 (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ Nat.card K := hK ▸ dvd_pow_self 3 hf0
    omega
  set N : Subgroup (PSL2MatrixGroup K) := Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  obtain ⟨a, haA, s, hsN, hao, hsa⟩ := exists_inverting hK hp3 hq3 hA
  have haH : a ∈ H := hAH (hAN haA)
  have hsH : s ∈ H := hAH hsN
  have hsa_not : ¬ s * a = a * s := fun hc => false_of_comm hao hsa hc
  obtain ⟨z, g, t, hz3, hg0, hg2, hzg, ht⟩ := exists_torus_element hK hp3
  have hzg' : z * g = Nat.card K - 1 := by
    rcases hzg with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ z * g := Dvd.dvd.mul_right hz3 g
      rw [h] at h3
      omega
  obtain ⟨x, hxo, hxc⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_mem_centralizer
    (isCyclic_of_isPGroup_three hK hp3) hA (t := t) (by rw [ht]; exact hz3)
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup K)) hxc
  have hxH : x ∈ H := hAH hxN
  have hxo' : orderOf x = z := hxo.trans ht
  have hxoH : orderOf (⟨x, hxH⟩ : H) = z := (Subgroup.orderOf_coe ⟨x, hxH⟩).symm.trans hxo'
  have hzq : Nat.card K ≤ 2 * z + 1 := by
    have : z * g ≤ z * 2 := Nat.mul_le_mul_left z hg2
    omega
  have hNcard : Nat.card K - 1 ≤ Nat.card N := by
    set C : Subgroup (PSL2MatrixGroup K) := Subgroup.centralizer (A : Set (PSL2MatrixGroup K)) with hC
    have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup K))
    have hxz : Nat.card (Subgroup.zpowers x) = z := by rw [Nat.card_zpowers, hxo']
    have hzC : z ≤ Nat.card C := by
      have hle : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hxc
      have := Subgroup.card_le_of_le hle
      omega
    have hCne : Nat.card C ≠ Nat.card N := by
      intro heq
      have hCeq : C = N := Subgroup.eq_of_le_of_card_ge hCN (le_of_eq heq.symm)
      apply hsa_not
      have hsC : s ∈ C := hCeq ▸ hsN
      exact (Subgroup.mem_centralizer_iff.mp hsC a haA).symm
    have hdvd : Nat.card C ∣ Nat.card N := Subgroup.card_dvd_of_le hCN
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · have : 0 < Nat.card N := Nat.card_pos
        omega
      · exact absurd (by simpa using hk.symm) hCne
      · omega
    have : 2 * Nat.card C ≤ Nat.card N := by rw [hk]; nlinarith
    omega
  have hNH : Nat.card N ∣ Nat.card H := Subgroup.card_dvd_of_le hAH
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hK H with
    hE | ⟨z', -, -, hC⟩ | ⟨z', hz'd, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t', -, -, NB, CB, hNn, hNe, hNcard', hCc, -, -, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  · exact (hsa_not (congrArg Subtype.val (hE.is_comm.comm ⟨s, hsH⟩ ⟨a, haH⟩))).elim
  · exact (hsa_not (congrArg Subtype.val (hC.commGroup.mul_comm ⟨s, hsH⟩ ⟨a, haH⟩))).elim
  ·
    left
    have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := Nat.gcd_eq_right (by omega)
    rw [hgcd] at hz'd
    have hz'le : z' ≤ (Nat.card K + 1) / 2 := by
      rcases hz'd with h | h
      · exact (Nat.le_of_dvd (by omega) h).trans (Nat.div_le_div_right (by omega))
      · exact Nat.le_of_dvd (by omega) h
    have hH2 : Nat.card H = 2 * z' := hcard
    have hHle : Nat.card H ≤ Nat.card K + 1 := by omega
    obtain ⟨k, hk⟩ := hNH
    have hk1 : k = 1 := by
      rcases k with _ | _ | k
      · have : 0 < Nat.card H := Nat.card_pos
        omega
      · rfl
      · exfalso
        have : 2 * Nat.card N ≤ Nat.card H := by rw [hk]; nlinarith
        omega
    subst hk1
    exact (Subgroup.eq_of_le_of_card_ge hAH (by omega)).symm
  ·
    exfalso
    have ha3 : a ^ 3 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [hao] at this
    have hsa2 : s * a * s⁻¹ = a ^ 2 := by
      rw [hsa, inv_eq_iff_mul_eq_one, ← pow_succ']
      exact ha3
    have h3 := a4_normalizer (e ⟨a, haH⟩) (e ⟨s, hsH⟩)
      (by rw [← map_pow]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext ha3))
      (fun h => by
        have : a = 1 := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
        rw [this, orderOf_one] at hao
        omega)
      (Or.inr (by
        rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hsa2)))
    apply hsa_not
    rcases h3 with h | h | h
    · have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      rw [show s = 1 from this]
      simp
    · have := congrArg Subtype.val (e.injective h)
      rw [show s = a from this]
    · have := congrArg Subtype.val (e.injective (h.trans (map_pow e _ 2).symm))
      rw [show s = a ^ 2 from this]
      exact (Commute.pow_left (Commute.refl a) 2).eq
  ·
    exfalso
    have hall : ∀ σ : Equiv.Perm (Fin 4), σ ^ 4 = 1 ∨ σ ^ 3 = 1 := by decide +kernel
    have hz4 : z ≤ 4 := by
      have hord : orderOf (e ⟨x, hxH⟩) = z := by rw [MulEquiv.orderOf_eq]; exact hxoH
      rcases hall (e ⟨x, hxH⟩) with h4 | h3
      · exact Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h4)
      · exact (Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)
    omega
  ·
    exfalso
    have h35 := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_five
      e ⟨x, hxH⟩
    rw [hxoH] at h35
    rcases h35 with h | h | h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
  ·
    exfalso
    exact false_of_borel hp3 hNn hNcard' hCc hsup (a := ⟨a, haH⟩) (s := ⟨s, hsH⟩)
      ((Subgroup.orderOf_coe ⟨a, haH⟩).symm.trans hao) (Subtype.ext (by simpa using hsa))
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h2 : p ^ m ≠ 2 := by
      intro h
      have : p ∣ 2 := h ▸ dvd_pow_self p hm0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have ha := four_le_pow hp3 hm0 h2
    by_cases hmeq : m = f
    · right
      obtain ⟨φ⟩ := nonempty_galoisField_ringHom hK hmf
      have hcardle : Nat.card K ≤ Nat.card (GaloisField p m) := by rw [hK, hGF, hmeq]
      have hbij := φ.injective.bijective_of_nat_card_le hcardle
      let ψ : K ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
      have hle : Nat.card (PSL2MatrixGroup K) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_le_card_of_injective _ (psl2Map_injective ψ.toRingHom)
      have htop : H = ⊤ := by
        refine Subgroup.eq_top_of_card_eq H ?_
        refine le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card H)) ?_
        rw [Nat.card_congr e.toEquiv]
        exact hle
      exact htop
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      have hf2 : 2 * m ≤ f := by nlinarith
      have hpow : (p ^ m) ^ 2 ≤ Nat.card K := by
        rw [hK, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right hp.pos hf2
      have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
        (GaloisField p m) (e ⟨x, hxH⟩)
      rw [MulEquiv.orderOf_eq, hxoH, hGF] at hord
      exact false_of_subfield_bound ha hord hpow hzq
  ·
    exfalso
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h2 : p ^ m ≠ 2 := by
      intro h
      have : p ∣ 2 := h ▸ dvd_pow_self p hm0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have ha := four_le_pow hp3 hm0 h2
    have hpow : (p ^ m) ^ 2 ≤ Nat.card K := by
      rw [hK, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right hp.pos hf2
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
      (GaloisField p m) (e ⟨x, hxH⟩)
    rw [MulEquiv.orderOf_eq, hxoH, hGF] at hord
    exact false_of_subfield_bound ha hord hpow hzq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
