module

public import CFSG.RankThree.PartOne.Q1327.Quasi

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem eq_one_of_orderOf_pPow (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {z : G} (hzc : ∀ j ∈ Jc, z * j = j * z) {k : ℕ}
    (hk : orderOf z = p ^ k) : z = 1 := by
  have h := H.h12
  have hp := h.prime
  by_contra hz1
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hdvd : p ∣ orderOf z := by
    rw [hk]
    exact dvd_pow_self p hk0
  have hwo : orderOf (z ^ (orderOf z / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne' hdvd
  have hwc : ∀ j ∈ Jc, z ^ (orderOf z / p) * j = j * z ^ (orderOf z / p) := fun j hj =>
    ((show Commute z j from hzc j hj).pow_left _).eq
  have hwp : (z ^ (orderOf z / p)) ^ p = 1 := by
    have := pow_orderOf_eq_one (z ^ (orderOf z / p))
    rwa [hwo] at this
  have hw1 : z ^ (orderOf z / p) = 1 := eq_one_of_pow_commute H hJ hwc hwp
  rw [hw1, orderOf_one] at hwo
  exact hp.one_lt.ne hwo

theorem Jof_le_Jc_of_out (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc)
    (hOut : ∀ x ∈ Subgroup.normalizer (Jc : Set G), (∃ k : ℕ, orderOf x = p ^ k) →
      x ∈ Jc ⊔ Subgroup.centralizer (Jc : Set G)) : Jof p R ≤ Jc := by
  have h := H.h12
  have hp := h.prime
  have hnorm := Jof_le_normalizer H hJ
  rw [Jof_def]
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxM, k, hk⟩
  have hxN : x ∈ Subgroup.normalizer (Jc : Set G) := hnorm (mem_Jof hxM k hk)
  obtain ⟨j, hj, z, hz, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute (K := Jc)
    (L := Subgroup.centralizer (Jc : Set G))
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) (hOut x hxN ⟨k, hk⟩)
  have hzc : ∀ i ∈ Jc, z * i = i * z := fun i hi =>
    (Subgroup.mem_centralizer_iff.mp hz i hi).symm
  have hcomm : Commute j z := (hzc j hj).symm
  obtain ⟨e, m', hm', hzm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.ne_one
  have hzpow : (z ^ m') ^ (p ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hzm]
    exact pow_orderOf_eq_one z
  have hz'c : ∀ i ∈ Jc, z ^ m' * i = i * z ^ m' := fun i hi =>
    ((show Commute z i from hzc i hi).pow_left _).eq
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hzpow)
  have hz1 : z ^ m' = 1 := eq_one_of_orderOf_pPow H hJ hz'c hb
  have hxm : (j * z) ^ m' = j ^ m' := by rw [hcomm.mul_pow, hz1, mul_one]
  have hcop : Nat.Coprime m' (orderOf (j * z)) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm').symm
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn, hxm]
  exact pow_mem (pow_mem hj m') n

end CFSG.RankThree.PartOne.Q1327
