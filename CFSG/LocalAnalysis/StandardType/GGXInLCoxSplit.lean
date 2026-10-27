module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType.GGXInL

open scoped Pointwise

attribute [local instance] commutatorElement

private lemma lup8a_exists_sq_eq_of_mem_of_odd {G : Type*} [Group G] (A : Subgroup G) {x : G}
    (hx : x ∈ A) (hodd : Odd (orderOf x)) : ∃ c ∈ A, c ^ 2 = x := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨x ^ (k + 1), pow_mem hx (k + 1), ?_⟩
  rw [← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, ← hk,
    pow_orderOf_eq_one, one_mul]

private lemma lup8a_eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {a : G}
    (hodd : Odd (orderOf a)) (h2 : a ^ 2 = 1) : a = 1 := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    rw [h] at hk
    omega

theorem exists_section_of_central_odd_coxeter
    {Q W : Type*} [Group Q] [Group W] {ι : Type*} {M : CoxeterMatrix ι}
    (cs : CoxeterSystem M W) (π : Q →* W) (hsurj : Function.Surjective π)
    (hcent : π.ker ≤ Subgroup.center Q) (hodd : ∀ q ∈ π.ker, Odd (orderOf q)) :
    ∃ s : W →* Q, π.comp s = MonoidHom.id W := by
  choose u hu using fun i => hsurj (cs.simple i)
  have hv : ∀ i, (u i ^ 2)⁻¹ ∈ π.ker := by
    intro i
    rw [MonoidHom.mem_ker, map_inv, map_pow, hu i, CoxeterSystem.simple_sq, inv_one]
  choose c hcA hc using fun i =>
    lup8a_exists_sq_eq_of_mem_of_odd π.ker (hv i) (hodd _ (hv i))
  let t : ι → Q := fun i => u i * c i
  have ht_simple : ∀ i, π (t i) = cs.simple i := by
    intro i
    simp only [t, map_mul, hu i, MonoidHom.mem_ker.mp (hcA i), mul_one]
  have ht_sq : ∀ i, t i ^ 2 = 1 := by
    intro i
    have hcomm : Commute (u i) (c i) := Subgroup.mem_center_iff.mp (hcent (hcA i)) (u i)
    calc t i ^ 2 = (u i * c i) ^ 2 := rfl
      _ = u i ^ 2 * c i ^ 2 := hcomm.mul_pow 2
      _ = u i ^ 2 * (u i ^ 2)⁻¹ := by rw [hc i]
      _ = 1 := mul_inv_cancel _
  have hlift : M.IsLiftable t := by
    intro i j
    set m := M i j with hm
    have hz_ker : (t i * t j) ^ m ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, ht_simple i, ht_simple j]
      rw [hm, CoxeterSystem.simple_mul_simple_pow]
    have hz_cent : (t i * t j) ^ m ∈ Subgroup.center Q := hcent hz_ker
    have hi : t i * t i = 1 := by rw [← pow_two]; exact ht_sq i
    have hj : t j * t j = 1 := by rw [← pow_two]; exact ht_sq j
    have hinv_i : (t i)⁻¹ = t i := inv_eq_of_mul_eq_one_right hi
    have hinv_j : (t j)⁻¹ = t j := inv_eq_of_mul_eq_one_right hj
    have hconj : t i * (t i * t j) * (t i)⁻¹ = (t i * t j)⁻¹ := by
      calc t i * (t i * t j) * (t i)⁻¹
          = (t i * t i) * (t j * (t i)⁻¹) := by
            rw [← mul_assoc (t i) (t i) (t j), mul_assoc]
        _ = t j * (t i)⁻¹ := by rw [hi, one_mul]
        _ = t j * t i := by rw [hinv_i]
        _ = (t i * t j)⁻¹ := by rw [mul_inv_rev, hinv_j, hinv_i]
    have hz_inv : (t i * t j) ^ m = ((t i * t j) ^ m)⁻¹ := by
      have h2 : t i * (t i * t j) ^ m * (t i)⁻¹ = (t i * t j) ^ m := by
        rw [Subgroup.mem_center_iff.mp hz_cent (t i), mul_assoc, mul_inv_cancel, mul_one]
      calc (t i * t j) ^ m = t i * (t i * t j) ^ m * (t i)⁻¹ := h2.symm
        _ = (t i * (t i * t j) * (t i)⁻¹) ^ m := conj_pow.symm
        _ = ((t i * t j)⁻¹) ^ m := by rw [hconj]
        _ = ((t i * t j) ^ m)⁻¹ := inv_pow (t i * t j) m
    have hz2 : ((t i * t j) ^ m) ^ 2 = 1 := by
      rw [pow_two, eq_inv_iff_mul_eq_one.mp hz_inv]
    exact lup8a_eq_one_of_sq_eq_one_of_odd (hodd _ hz_ker) hz2
  refine ⟨cs.lift ⟨t, hlift⟩, ?_⟩
  apply CoxeterSystem.ext_simple cs
  intro i
  show π (cs.lift ⟨t, hlift⟩ (cs.simple i)) = (MonoidHom.id W) (cs.simple i)
  rw [CoxeterSystem.lift_apply_simple cs hlift i]
  exact ht_simple i

private lemma lup8a_commutatorElement_mul_of_mem_center {G : Type*} [Group G] {k₁ k₂ a b : G}
    (h1 : k₁ ∈ Subgroup.center G) (h2 : k₂ ∈ Subgroup.center G) :
    ⁅k₁ * a, k₂ * b⁆ = ⁅a, b⁆ := by
  have hk1 : ∀ x : G, k₁ * x = x * k₁ := fun x => (Subgroup.mem_center_iff.mp h1 x).symm
  have hk2 : ∀ x : G, k₂ * x = x * k₂ := fun x => (Subgroup.mem_center_iff.mp h2 x).symm
  have hc1 : ∀ x : G, ⁅k₁, x⁆ = 1 := by
    intro x
    have hx : ⁅k₁, x⁆ ∈ (⊥ : Subgroup G) := by
      rw [← Subgroup.commutator_center_left (⊤ : Subgroup G)]
      exact Subgroup.commutator_mem_commutator h1 (Subgroup.mem_top x)
    simpa using hx
  have hc2 : ∀ x : G, ⁅x, k₂⁆ = 1 := by
    intro x
    have hx : ⁅x, k₂⁆ ∈ (⊥ : Subgroup G) := by
      rw [← Subgroup.commutator_center_right (⊤ : Subgroup G)]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) h2
    simpa using hx
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj]
  simp only [hc1, hc2, one_mul, mul_one]
  rw [show k₂ * ⁅a, b⁆ * k₂⁻¹ = ⁅a, b⁆ by rw [hk2, mul_assoc, mul_inv_cancel, mul_one],
    show k₁ * ⁅a, b⁆ * k₁⁻¹ = ⁅a, b⁆ by rw [hk1, mul_assoc, mul_inv_cancel, mul_one]]

theorem inf_commutator_eq_commutator_of_coxeter_quotient
    {L : Type*} [Group L] (N T : Subgroup L) (hTN : T ≤ N) [(T.subgroupOf N).Normal]
    {ι : Type*} {M : CoxeterMatrix ι} (cs : CoxeterSystem M (N ⧸ T.subgroupOf N))
    (hTodd : ∀ t ∈ T, Odd (orderOf t)) :
    T ⊓ ⁅N, N⁆ = ⁅T, N⁆ := by
  let D : Subgroup L := ⁅T, N⁆
  have hDT : D ≤ T := by
    change ⁅T, N⁆ ≤ T
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ T := by
      have h := (inferInstance : (T.subgroupOf N).Normal).conj_mem
        (⟨a⁻¹, hTN (T.inv_mem ha)⟩ : N)
        (Subgroup.mem_subgroupOf.mpr (T.inv_mem ha)) (⟨b, hb⟩ : N)
      simpa using Subgroup.mem_subgroupOf.mp h
    rw [commutatorElement_def]
    convert T.mul_mem ha hconj using 1
    simp only [mul_assoc]
  have hDN : D ≤ N := le_trans hDT hTN
  have hDnorm : (D.subgroupOf N).Normal := by
    have h : (⁅T, N⁆.subgroupOf (T ⊔ N)).Normal := Subgroup.normal_subgroupOf_commutator_sup T N
    rw [sup_eq_right.mpr hTN] at h
    simpa only [D] using h
  have hπle : D.subgroupOf N ≤ Subgroup.comap (MonoidHom.id N) (T.subgroupOf N) := by
    intro x hx
    simpa only [MonoidHom.id_apply, Subgroup.mem_comap] using Subgroup.subgroupOf_mono N hDT hx
  let π : N ⧸ D.subgroupOf N →* N ⧸ T.subgroupOf N :=
    QuotientGroup.map (D.subgroupOf N) (T.subgroupOf N) (MonoidHom.id N) hπle
  have hπ_mk : ∀ n : N,
      π (QuotientGroup.mk' (D.subgroupOf N) n) = QuotientGroup.mk' (T.subgroupOf N) n := by
    intro n
    rw [QuotientGroup.map_mk']
    rfl
  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf N) x
    exact ⟨QuotientGroup.mk' (D.subgroupOf N) n, hπ_mk n⟩
  have hle : ⁅T.subgroupOf N, (⊤ : Subgroup N)⁆ ≤ D.subgroupOf N := by
    rw [Subgroup.commutator_le]
    intro a ha b _
    rw [Subgroup.mem_subgroupOf]
    change N.subtype ⁅a, b⁆ ∈ D
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha) b.2
  have hcenter : (T.subgroupOf N).map (QuotientGroup.mk' (D.subgroupOf N)) ≤
      Subgroup.center (N ⧸ D.subgroupOf N) := by
    rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
    have hmap : ⁅(T.subgroupOf N).map (QuotientGroup.mk' (D.subgroupOf N)),
        (⊤ : Subgroup (N ⧸ D.subgroupOf N))⁆
        = (⁅T.subgroupOf N, (⊤ : Subgroup N)⁆).map (QuotientGroup.mk' (D.subgroupOf N)) := by
      rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        ← Subgroup.map_commutator]
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  have hker : π.ker = (T.subgroupOf N).map (QuotientGroup.mk' (D.subgroupOf N)) := by
    ext q
    constructor
    · intro hq
      rw [MonoidHom.mem_ker] at hq
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf N) q
      rw [hπ_mk n] at hq
      refine Subgroup.mem_map.mpr ⟨n, ?_, rfl⟩
      rw [← QuotientGroup.eq_one_iff]
      exact hq
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hπ_mk n, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
  have hodd' : ∀ q ∈ π.ker, Odd (orderOf q) := by
    intro q hq
    rw [hker] at hq
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hq
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' (D.subgroupOf N)) n)
    rw [← Subgroup.orderOf_coe n]
    exact hTodd (n : L) (Subgroup.mem_subgroupOf.mp hn)
  have hcent : π.ker ≤ Subgroup.center (N ⧸ D.subgroupOf N) := by
    rw [hker]
    exact hcenter
  obtain ⟨s, hs⟩ := exists_section_of_central_odd_coxeter cs π hsurj hcent hodd'
  have hπs : ∀ w : N ⧸ T.subgroupOf N, π (s w) = w := by
    intro w
    have := DFunLike.congr_fun hs w
    simpa using this
  have hcomm : ⁅(⊤ : Subgroup (N ⧸ D.subgroupOf N)), ⊤⁆ ≤ s.range := by
    rw [Subgroup.commutator_le]
    intro q1 _ q2 _
    let k1 : N ⧸ D.subgroupOf N := q1 * (s (π q1))⁻¹
    let k2 : N ⧸ D.subgroupOf N := q2 * (s (π q2))⁻¹
    have hk1 : k1 ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [k1, map_mul, map_inv, hπs]
      rw [mul_inv_cancel]
    have hk2 : k2 ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [k2, map_mul, map_inv, hπs]
      rw [mul_inv_cancel]
    have hq1 : q1 = k1 * s (π q1) := by
      simp only [k1]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hq2 : q2 = k2 * s (π q2) := by
      simp only [k2]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hceq : ⁅q1, q2⁆ = ⁅s (π q1), s (π q2)⁆ := by
      calc ⁅q1, q2⁆ = ⁅k1 * s (π q1), k2 * s (π q2)⁆ := by rw [← hq1, ← hq2]
        _ = ⁅s (π q1), s (π q2)⁆ :=
            lup8a_commutatorElement_mul_of_mem_center (hcent hk1) (hcent hk2)
    rw [hceq]
    exact Subgroup.commutator_le_self s.range
      (Subgroup.commutator_mem_commutator ⟨π q1, rfl⟩ ⟨π q2, rfl⟩)
  have hdisj : π.ker ⊓ s.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hx2
    rw [MonoidHom.mem_ker, hπs w] at hx1
    rw [hx1, map_one]
  apply le_antisymm
  · intro t ht
    rw [Subgroup.mem_inf] at ht
    obtain ⟨htT, htNN⟩ := ht
    let t' : N ⧸ D.subgroupOf N := QuotientGroup.mk' (D.subgroupOf N) ⟨t, hTN htT⟩
    have ht'ker : t' ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπ_mk]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr htT
    have ht'comm : t' ∈ ⁅(⊤ : Subgroup (N ⧸ D.subgroupOf N)),
        (⊤ : Subgroup (N ⧸ D.subgroupOf N))⁆ := by
      have hsub : ((⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map (Subgroup.subtype N)) = ⁅N, N⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      have hmap2 : ((⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map (QuotientGroup.mk' (D.subgroupOf N)))
          = ⁅(⊤ : Subgroup (N ⧸ D.subgroupOf N)),
              (⊤ : Subgroup (N ⧸ D.subgroupOf N))⁆ := by
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      have htm : (⟨t, hTN htT⟩ : N) ∈ ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ := by
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hsub.symm ▸ htNN)
        have hy' : y = ⟨t, hTN htT⟩ := Subtype.ext (by simpa using hyeq)
        exact hy' ▸ hy
      rw [← hmap2]
      exact Subgroup.mem_map.mpr ⟨⟨t, hTN htT⟩, htm, rfl⟩
    have hfin : t' ∈ π.ker ⊓ s.range := ⟨ht'ker, hcomm ht'comm⟩
    rw [hdisj, Subgroup.mem_bot] at hfin
    have hmem : (⟨t, hTN htT⟩ : N) ∈ D.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff]
      exact hfin
    exact Subgroup.mem_subgroupOf.mp hmem
  · refine le_inf hDT ?_
    simpa only [D] using Subgroup.commutator_mono hTN (le_refl N)

end CFSG.StandardType.GGXInL

end
