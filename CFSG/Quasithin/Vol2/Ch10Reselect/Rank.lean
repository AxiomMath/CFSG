module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Basic
public import CFSG.Quasithin.Vol2.Ch10Reselect.Counting

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isPGroup_zpowers_of_orderOf_eq {r : ℕ} {z : G} (hz : orderOf z = r) :
    IsPGroup r (Subgroup.zpowers z) := by
  intro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz, pow_orderOf_eq_one,
    one_zpow]

theorem commute_of_mem_closure_pair {a z x : G} (hxa : x * a = a * x) (hxz : x * z = z * x)
    {y : G} (hy : y ∈ Subgroup.closure ({a, z} : Set G)) : x * y = y * x := by
  induction hy using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    · exact hxa
    · exact hxz
  | one => simp
  | mul y₁ y₂ _ _ h₁ h₂ =>
    calc x * (y₁ * y₂) = y₁ * x * y₂ := by rw [← mul_assoc, h₁, mul_assoc]
      _ = y₁ * y₂ * x := by rw [mul_assoc, h₂, ← mul_assoc]
  | inv y _ h =>
    have : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [h]
        _ = y⁻¹ * x := by group
    exact this

theorem isPGroup_closure_pair {r : ℕ} {a z : G} (ha : orderOf a = r) (hz : orderOf z = r)
    (h : a * z = z * a) : IsPGroup r (Subgroup.closure ({a, z} : Set G)) := by
  have hmain : ∀ g ∈ Subgroup.closure ({a, z} : Set G),
      g ^ r = 1 ∧ g * a = a * g ∧ g * z = z * g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl
      · exact ⟨by rw [← ha]; exact pow_orderOf_eq_one _, rfl, h⟩
      · exact ⟨by rw [← hz]; exact pow_orderOf_eq_one _, h.symm, rfl⟩
    | one => simp
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx1, hx2, hx3⟩ := ihx
      obtain ⟨hy1, hy2, hy3⟩ := ihy
      have hxy : x * y = y * x := commute_of_mem_closure_pair hx2 hx3 hy
      refine ⟨?_, ?_, ?_⟩
      · rw [(show Commute x y from hxy).mul_pow, hx1, hy1, one_mul]
      · rw [mul_assoc, hy2, ← mul_assoc, hx2, mul_assoc]
      · rw [mul_assoc, hy3, ← mul_assoc, hx3, mul_assoc]
    | inv x hx ihx =>
      obtain ⟨hx1, hx2, hx3⟩ := ihx
      refine ⟨by rw [inv_pow, hx1, inv_one], ?_, ?_⟩
      · calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * a) * x⁻¹ := by rw [← hx2]
          _ = a * x⁻¹ := by group
      · calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← hx3]
          _ = z * x⁻¹ := by group
  intro ⟨g, hg⟩
  exact ⟨1, Subtype.ext (by simpa using (hmain g hg).1)⟩

theorem eq_one_of_mem_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) {x : G} (hx : x ∈ X)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : x ^ r = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hxr
  have hcop : Nat.Coprime (2 ^ k) r :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  have h3 : orderOf x ∣ Nat.gcd (2 ^ k) r := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem mem_fsuL0_of_orderOf_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L)
    {z : G} (hz : z ∈ fsuM T L) (hzr : orderOf z = r) : z ∈ fsuL0 T L := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  have hloc := hfsu.maximal.1
  have hodd : Odd (orderOf z) := by rw [hzr]; exact hr.out.odd_of_ne_two hr2
  have hzL := mem_normalizer_of_odd_orderOf h37 h38 hfsu hlt hz hodd
  have hzLt := mem_normalizer_conjugate_of_mem_normalizer h37 h38 hfsu hlt ht htn hz hzL
  obtain ⟨a, haL, har, hac⟩ := exists_orderOf_eq_mem_centralizer (r := r)
    (isPGroup_zpowers_of_orderOf_eq hzr) (Subgroup.zpowers_le.mpr hzL) hrL
  have haz : a * z = z * a := (hac z (Subgroup.mem_zpowers z)).symm
  have hP' := isPGroup_closure_pair har hzr haz
  have hP'N : Subgroup.closure ({a, z} : Set G) ≤
      Subgroup.normalizer ((CFSG.conjugate L t : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact le_normalizer_conjugate hloc (le_fsuM T L ht) haL
    · exact hzLt
  have hrLt : r ∣ Nat.card (CFSG.conjugate L t) := by rwa [card_conjugate L t]
  obtain ⟨b, hbLt, hbr, hbc⟩ := exists_orderOf_eq_mem_centralizer hP' hP'N hrLt
  have hab : a * b = b * a := hbc a (Subgroup.subset_closure (Or.inl rfl))
  have hbz : b * z = z * b := (hbc z (Subgroup.subset_closure (Or.inr rfl))).symm
  by_contra hzL0
  have hind : ∀ i j k : ℕ, a ^ i * b ^ j * z ^ k = 1 → r ∣ i ∧ r ∣ j ∧ r ∣ k := by
    intro i j k h
    have hk : r ∣ k := by
      by_contra hk
      apply hzL0
      have h1 : z ^ k = (a ^ i * b ^ j)⁻¹ := eq_inv_of_mul_eq_one_right h
      have hmem : z ^ k ∈ fsuL0 T L := by
        rw [h1]
        exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (le_fsuL0 T L haL) i)
          (Subgroup.pow_mem _ (conjugate_le_fsuL0 ht hbLt) j))
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := z) (n := k)
        (by rw [hzr]; exact ((Nat.Prime.coprime_iff_not_dvd hr.out).mpr hk).symm)
      rw [← hm]
      exact Subgroup.pow_mem _ hmem m
    have hzk : z ^ k = 1 := by
      obtain ⟨c, rfl⟩ := hk
      have : z ^ r = 1 := by rw [← hzr]; exact pow_orderOf_eq_one z
      rw [pow_mul, this, one_pow]
    rw [hzk, mul_one] at h
    have hai : a ^ i = (b ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hcU : a ^ i ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hmemLt : a ^ i ∈ CFSG.conjugate L t := by
        rw [hai]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hbLt j)
      exact (Subgroup.mem_centralizer_iff.mp ((hA t ht htn).2.2 hu) (a ^ i) hmemLt).symm
    have hcV := mem_centralizer_fsuVM_of_UL h37 h38 hfsu hlt hA (Subgroup.pow_mem _ haL i) hcU
    have hO := fsuL0_inf_centralizer_le_of_fsu h37 h38 hfsu hnn
      ⟨le_fsuL0 T L (Subgroup.pow_mem _ haL i), hcV⟩
    have har1 : a ^ r = 1 := by rw [← har]; exact pow_orderOf_eq_one a
    have hbr1 : b ^ r = 1 := by rw [← hbr]; exact pow_orderOf_eq_one b
    have hai1 : a ^ i = 1 := by
      refine eq_one_of_mem_isPGroup_two (X := pCoreOf 2 (fsuL0 T L))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hO hr.out hr2 ?_
      rw [← pow_mul, mul_comm, pow_mul, har1, one_pow]
    have hi : r ∣ i := by
      have := orderOf_dvd_iff_pow_eq_one.mpr hai1
      rwa [har] at this
    rw [hai1, one_mul] at h
    have hj : r ∣ j := by
      have := orderOf_dvd_iff_pow_eq_one.mpr h
      rwa [hbr] at this
    exact ⟨hi, hj, hk⟩
  obtain ⟨E, hEcl, -, -, -, hEc, hEe, hEcard⟩ :=
    exists_elemAbelian_card_pow_three har hbr hzr hab haz hbz hind
  have hEM : E ≤ fsuM T L := by
    refine hEcl.trans ((Subgroup.closure_le (fsuM T L)).mpr ?_)
    rintro x (rfl | rfl | rfl)
    · exact (fsuL0_le_fsuM T L) (le_fsuL0 T L haL)
    · exact (fsuL0_le_fsuM T L) (conjugate_le_fsuL0 ht hbLt)
    · exact hz
  have h3 : 3 ≤ CFSG.Open.pRank r (fsuM T L) :=
    CFSG.SectionRank.le_pRank hr.out.one_lt hEM ⟨hEc, hEe⟩ hEcard
  have h2 := pRank_fsuM_le_two hfsu hr.out hr2
  omega

theorem false_of_mem_centralizer_of_orderOf_eq
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) (hA : Concl326A T L I) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrL : r ∣ Nat.card L) {c : G} (hc : c ∈ fsuM T L)
    (hcA : c ∈ Subgroup.centralizer (fsuVM T L I : Set G)) (hcr : orderOf c = r) : False := by
  have hcL0 := mem_fsuL0_of_orderOf_eq h37 h38 hfsu hlt hA hr2 hrL hc hcr
  have hO := fsuL0_inf_centralizer_le_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt)
    ⟨hcL0, hcA⟩
  have hcr1 : c ^ r = 1 := by rw [← hcr]; exact pow_orderOf_eq_one c
  have hc1 := eq_one_of_mem_isPGroup_two (X := pCoreOf 2 (fsuL0 T L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hO hr.out hr2 hcr1
  rw [hc1, orderOf_one] at hcr
  exact hr.out.one_lt.ne hcr

end CFSG.Quasithin.Vol2.Ch10Reselect
