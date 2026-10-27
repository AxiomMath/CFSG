module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Equiv Equiv.Perm Subgroup

private theorem card_centralizer_of_orderOf_eq_five {x : Perm (Fin 7)} (hx : orderOf x = 5) :
    Nat.card (centralizer ({x} : Set (Perm (Fin 7)))) = 10 := by
  have hcyc : x.IsCycle := isCycle_of_prime_order' (by rw [hx]; norm_num)
    (by rw [hx, Fintype.card_fin]; norm_num)
  have hsupp : x.support.card = 5 := by rw [← hcyc.orderOf, hx]
  rw [nat_card_centralizer, hcyc.cycleType, hsupp]
  simp [Fintype.card_fin, Nat.factorial]

private noncomputable def orb (P : Subgroup (Perm (Fin 10))) (i : Fin 10) :
    Finset (Fin 10) := by
  classical
  exact Finset.univ.filter fun j => ∃ p ∈ P, p i = j

private noncomputable def fixd (P : Subgroup (Perm (Fin 10))) : Finset (Fin 10) := by
  classical
  exact Finset.univ.filter fun j => ∀ p ∈ P, p j = j

private theorem mem_orb {P : Subgroup (Perm (Fin 10))} {i j : Fin 10} :
    j ∈ orb P i ↔ ∃ p ∈ P, p i = j := by
  simp [orb]

private theorem mem_fixd {P : Subgroup (Perm (Fin 10))} {j : Fin 10} :
    j ∈ fixd P ↔ ∀ p ∈ P, p j = j := by
  simp [fixd]

private theorem self_mem_orb (P : Subgroup (Perm (Fin 10))) (i : Fin 10) : i ∈ orb P i :=
  mem_orb.mpr ⟨1, P.one_mem, rfl⟩

private theorem orb_eq_of_mem {P : Subgroup (Perm (Fin 10))} {i j : Fin 10} (h : j ∈ orb P i) :
    orb P j = orb P i := by
  obtain ⟨p, hp, rfl⟩ := mem_orb.mp h
  ext x
  simp only [mem_orb]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q * p, P.mul_mem hq hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q * p⁻¹, P.mul_mem hq (P.inv_mem hp), by simp [Perm.mul_apply]⟩

private theorem apply_mem_orb_apply_iff {P : Subgroup (Perm (Fin 10))} {g : Perm (Fin 10)}
    (hg : g ∈ normalizer (P : Set (Perm (Fin 10)))) {i x : Fin 10} :
    g x ∈ orb P (g i) ↔ x ∈ orb P i := by
  simp only [mem_orb]
  constructor
  · rintro ⟨q, hq, hqx⟩
    refine ⟨g⁻¹ * q * g, ?_, ?_⟩
    · simpa using (mem_normalizer_iff.mp (inv_mem hg) q).mp hq
    · simp [Perm.mul_apply, hqx]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨g * p * g⁻¹, (mem_normalizer_iff.mp hg p).mp hp, by simp [Perm.mul_apply]⟩

private theorem card_orb_apply {P : Subgroup (Perm (Fin 10))} {g : Perm (Fin 10)}
    (hg : g ∈ normalizer (P : Set (Perm (Fin 10)))) (i : Fin 10) :
    (orb P (g i)).card = (orb P i).card := by
  classical
  have h : orb P (g i) = (orb P i).image g := by
    ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      refine ⟨g⁻¹ x, ?_, by simp⟩
      rw [← apply_mem_orb_apply_iff hg]
      simpa using hx
    · rintro ⟨w, hw, rfl⟩
      exact (apply_mem_orb_apply_iff hg).mpr hw
  rw [h, Finset.card_image_of_injective _ g.injective]

private theorem exists_card_orb_eq {P : Subgroup (Perm (Fin 10))} (hP : IsPGroup 2 P)
    (i : Fin 10) : ∃ n : ℕ, (orb P i).card = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.card_orbit i
  refine ⟨n, ?_⟩
  have h : MulAction.orbit P i = (orb P i : Set (Fin 10)) := by
    ext j
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_orb, Subtype.exists,
      Subgroup.mk_smul, Perm.smul_def, exists_prop]
  rw [← hn, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem apply_mem_fixd_iff {P : Subgroup (Perm (Fin 10))} {g : Perm (Fin 10)}
    (hg : g ∈ normalizer (P : Set (Perm (Fin 10)))) {j : Fin 10} :
    g j ∈ fixd P ↔ j ∈ fixd P := by
  simp only [mem_fixd]
  constructor
  · intro h p hp
    have h1 := h (g * p * g⁻¹) ((mem_normalizer_iff.mp hg p).mp hp)
    simpa [Perm.mul_apply] using h1
  · intro h p hp
    have h1 := h (g⁻¹ * p * g) (by simpa using (mem_normalizer_iff.mp (inv_mem hg) p).mp hp)
    have h2 : g⁻¹ (p (g j)) = j := by simpa [Perm.mul_apply] using h1
    calc p (g j) = g (g⁻¹ (p (g j))) := by simp
      _ = g j := by rw [h2]

private theorem two_dvd_card_fixd {P : Subgroup (Perm (Fin 10))} (hP : IsPGroup 2 P) :
    2 ∣ (fixd P).card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.card_modEq_card_fixedPoints (Fin 10)
  have h2 : MulAction.fixedPoints P (Fin 10) = (fixd P : Set (Fin 10)) := by
    ext j
    simp only [MulAction.mem_fixedPoints, Finset.mem_coe, mem_fixd, Subtype.forall,
      Subgroup.mk_smul, Perm.smul_def]
  rw [h2, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  unfold Nat.ModEq at h
  omega

private theorem exists_not_mem_fixd {P : Subgroup (Perm (Fin 10))} (hP1 : P ≠ ⊥) :
    ∃ j, j ∉ fixd P := by
  by_contra h
  push Not at h
  apply hP1
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun j => ?_
  rw [Perm.one_apply]
  exact mem_fixd.mp (h j) p hp

private theorem exists_pair_invariant {P : Subgroup (Perm (Fin 10))} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) {y : Perm (Fin 10)} (hyN : y ∈ normalizer (P : Set (Perm (Fin 10))))
    (hy : orderOf y = 7) :
    ∃ S : Finset (Fin 10), S.card = 2 ∧
      ∀ g ∈ normalizer (P : Set (Perm (Fin 10))), ∀ x ∈ S, g x ∈ S := by
  classical
  have hcyc : y.IsCycle := isCycle_of_prime_order' (by rw [hy]; norm_num)
    (by rw [hy, Fintype.card_fin]; norm_num)
  have hsupp : y.support.card = 7 := by rw [← hcyc.orderOf, hy]
  by_cases h1 : ∃ j ∈ y.support, j ∈ fixd P
  ·
    obtain ⟨j, hj, hjF⟩ := h1
    have hYF : y.support ⊆ fixd P := by
      intro k hk
      obtain ⟨n, rfl⟩ := hcyc.exists_pow_eq (mem_support.mp hj) (mem_support.mp hk)
      exact (apply_mem_fixd_iff (pow_mem hyN n)).mpr hjF
    refine ⟨(fixd P)ᶜ, ?_, fun g hg x hx => ?_⟩
    · have hle := Finset.card_le_card (Finset.compl_subset_compl.mpr hYF)
      obtain ⟨j', hj'⟩ := exists_not_mem_fixd hP1
      have hpos : 0 < (fixd P)ᶜ.card := Finset.card_pos.mpr ⟨j', Finset.mem_compl.mpr hj'⟩
      have heven := two_dvd_card_fixd hP
      have hF := Finset.card_le_univ (fixd P)
      simp only [Finset.card_compl, hsupp, Fintype.card_fin] at hle hpos hF ⊢
      omega
    · rw [Finset.mem_compl] at hx ⊢
      exact fun h => hx ((apply_mem_fixd_iff hg).mp h)
  push Not at h1
  by_cases h2 : ∃ j ∈ y.support, ∃ k ∈ y.support, j ≠ k ∧ k ∈ orb P j
  ·
    obtain ⟨j, hj, k, hk, hjk, hkj⟩ := h2
    obtain ⟨d, hd⟩ := hcyc.exists_pow_eq (mem_support.mp hj) (mem_support.mp hk)
    have hz1 : y ^ d ≠ 1 := by
      intro h
      apply hjk
      rw [← hd, h]
      rfl
    have hz7 : orderOf (y ^ d) = 7 := by
      have h := orderOf_pow_dvd (x := y) d
      rw [hy] at h
      rcases (Nat.dvd_prime (by norm_num)).mp h with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hz1
      · exact h'
    have hzc : (y ^ d).IsCycle := isCycle_of_prime_order' (by rw [hz7]; norm_num)
      (by rw [hz7, Fintype.card_fin]; norm_num)
    have hzsupp : (y ^ d).support = y.support :=
      Finset.eq_of_subset_of_card_le (support_pow_le y d)
        (by rw [hsupp, ← hzc.orderOf, hz7])
    have hzN : y ^ d ∈ normalizer (P : Set (Perm (Fin 10))) := pow_mem hyN d
    have hclosed : ∀ x ∈ orb P j, (y ^ d) x ∈ orb P j := by
      intro x hx
      have h := (apply_mem_orb_apply_iff hzN (i := j)).mpr hx
      rwa [hd, orb_eq_of_mem hkj] at h
    have hclosed' : ∀ n : ℕ, ((y ^ d) ^ n) j ∈ orb P j := by
      intro n
      induction n with
      | zero => simpa using self_mem_orb P j
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hclosed _ ih
    have hYO : y.support ⊆ orb P j := by
      intro l hl
      rw [← hzsupp] at hl
      have hj' : j ∈ (y ^ d).support := hzsupp ▸ hj
      obtain ⟨n, hn⟩ := hzc.exists_pow_eq (mem_support.mp hj') (mem_support.mp hl)
      rw [← hn]
      exact hclosed' n
    have h8 : (orb P j).card = 8 := by
      obtain ⟨n, hn⟩ := exists_card_orb_eq hP j
      have h7 : 7 ≤ (orb P j).card := hsupp ▸ Finset.card_le_card hYO
      have h10 : (orb P j).card ≤ 10 := by
        have := Finset.card_le_univ (orb P j)
        rwa [Fintype.card_fin] at this
      rw [hn] at h7 h10 ⊢
      rcases n with _ | _ | _ | _ | n
      · norm_num at h7
      · norm_num at h7
      · norm_num at h7
      · norm_num
      · rw [pow_succ, pow_succ, pow_succ, pow_succ] at h10
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
    refine ⟨(orb P j)ᶜ, by rw [Finset.card_compl, h8, Fintype.card_fin], fun g hg x hx => ?_⟩
    have hgj : orb P (g j) = orb P j := by
      have hc : (orb P (g j)).card = 8 := (card_orb_apply hg j).trans h8
      obtain ⟨w, hw1, hw2⟩ : ∃ w, w ∈ orb P (g j) ∧ w ∈ orb P j := by
        by_contra hcon
        push Not at hcon
        have hdisj : Disjoint (orb P (g j)) (orb P j) := Finset.disjoint_left.mpr hcon
        have hu := Finset.card_union_of_disjoint hdisj
        have hle := Finset.card_le_univ (orb P (g j) ∪ orb P j)
        rw [Fintype.card_fin] at hle
        omega
      rw [← orb_eq_of_mem hw1, orb_eq_of_mem hw2]
    rw [Finset.mem_compl] at hx ⊢
    intro h
    rw [← hgj] at h
    exact hx ((apply_mem_orb_apply_iff hg).mp h)
  ·
    exfalso
    push Not at h2
    have hdisj : (y.support : Set (Fin 10)).PairwiseDisjoint (orb P) := by
      intro j hj k hk hjk
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxj hxk
      apply h2 j (Finset.mem_coe.mp hj) k (Finset.mem_coe.mp hk) hjk
      rw [← orb_eq_of_mem hxj, orb_eq_of_mem hxk]
      exact self_mem_orb P k
    have h2le : ∀ j ∈ y.support, 2 ≤ (orb P j).card := by
      intro j hj
      have hjF := h1 j hj
      rw [mem_fixd] at hjF
      push Not at hjF
      obtain ⟨p, hp, hpj⟩ := hjF
      have hsub : ({j, p j} : Finset (Fin 10)) ⊆ orb P j := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨self_mem_orb P j, mem_orb.mpr ⟨p, hp, rfl⟩⟩
      have h := Finset.card_le_card hsub
      rwa [Finset.card_pair (Ne.symm hpj)] at h
    have hsum : 14 ≤ ∑ j ∈ y.support, (orb P j).card := by
      calc 14 = ∑ _j ∈ y.support, 2 := by rw [Finset.sum_const, hsupp]; rfl
        _ ≤ _ := Finset.sum_le_sum h2le
    have hle := Finset.card_le_univ (y.support.biUnion (orb P))
    rw [Finset.card_biUnion hdisj, Fintype.card_fin] at hle
    omega

theorem ks154A10 :
    ∀ K : Subgroup (Equiv.Perm (Fin 10)), K ≤ alternatingGroup (Fin 10) → 189 ∣ Nat.card K →
      ∀ P : Subgroup (Equiv.Perm (Fin 10)), IsPGroup 2 P →
        K ≤ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 10))) → P = ⊥ := by
  intro K _ h189 P hP hKP
  classical
  by_contra hne
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨y, hyK⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 7
    (dvd_trans (by norm_num) h189)
  rw [Subgroup.orderOf_mk] at hy
  obtain ⟨S, hS, hSinv⟩ := exists_pair_invariant hP hne (hKP hyK) hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have hKC : K ≤ centralizer ({swap a b} : Set (Perm (Fin 10))) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    have ha := hSinv g (hKP hg) a (by simp)
    have hb := hSinv g (hKP hg) b (by simp)
    have hgab : g a ≠ g b := g.injective.ne hab
    have hsw : g * swap a b * g⁻¹ = swap a b := by
      rw [← swap_apply_apply]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hgab ⊢ <;>
        first | exact absurd rfl hgab | exact swap_comm _ _
    calc g * swap a b = g * swap a b * g⁻¹ * g := by group
      _ = swap a b * g := by rw [hsw]
  have hC : Nat.card (centralizer ({swap a b} : Set (Perm (Fin 10)))) = 80640 := by
    rw [nat_card_centralizer, isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr hab)]
    simp [Fintype.card_fin, Nat.factorial]
  have h := dvd_trans h189 (hC ▸ Subgroup.card_dvd_of_le hKC)
  norm_num at h

end CFSG.RankThree.PartTwo.Sec15.Wales154
