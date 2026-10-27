module

public import CFSG.RankThree.PartOne.S11d.Sec11Common
import CFSG.RankThree.PartOne.S12.Sec12Two

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Assembly.RankThreeEven (localRank)

theorem exists_nat_pow_zpow_eq_self {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {a : G}
    (hap : a ^ p = 1) {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : ∃ m : ℕ, (a ^ k) ^ (m : ℤ) = a := by
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → a ^ n = 1 := fun n hn => by
    obtain ⟨t', rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) hk (-1)
  refine ⟨m, ?_⟩
  rw [← zpow_mul]
  have h2 : a ^ (k * (m : ℤ) + -1) = 1 := hzpow _ hm
  calc a ^ (k * (m : ℤ)) = a ^ (k * (m : ℤ) + -1) * a := by
        rw [zpow_add, zpow_neg_one]
        group
    _ = a := by rw [h2, one_mul]

namespace Sec11Indeed

namespace Sit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}
  {a d : G}

theorem a_mem_sup_of_coords (sit : Sit p A c L a d) {f : G} {i j : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) :
    a ∈ zpowers c ⊔ zpowers f := by
  have : Fact p.Prime := ⟨sit.prime⟩
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  obtain ⟨m, h1⟩ := exists_nat_pow_zpow_eq_self hap hi
  have hai : a ^ i = f * (c ^ j)⁻¹ := by rw [hij]; group
  have hcR : c ∈ zpowers c ⊔ zpowers f := Subgroup.mem_sup_left (mem_zpowers c)
  have hfR : f ∈ zpowers c ⊔ zpowers f := Subgroup.mem_sup_right (mem_zpowers f)
  rw [← h1, hai]
  exact zpow_mem (mul_mem hfR (inv_mem (zpow_mem hcR j))) _

theorem ne_one_of_coords (sit : Sit p A c L a d) {f : G} {i j : ℤ} (hij : f = a ^ i * c ^ j)
    (hi : ¬ (p : ℤ) ∣ i) : f ≠ 1 := by
  intro h
  apply hi
  have := sit.coords_eq_one (x := i) (y := j) (z := 0) (by rw [zpow_zero, mul_one, ← hij]; exact h)
  exact this.1

theorem swap (h112 : InSec11Two) (sit : Sit p A c L a d) {f : G} {i j : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) {K : Subgroup G}
    (hK : K ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) f)
    (hALK : A ⊓ L ≤ K) (hcK : InducesFieldAut p c K) :
    A ⊓ K = zpowers d ∧ Sit p A f K c d := by
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : f ≠ 1 := sit.ne_one_of_coords hij hi
  have hfA : f ∈ A := by
    rw [hij]
    exact mul_mem (zpow_mem sit.a_mem i) (zpow_mem sit.c_mem j)
  obtain ⟨hEvenK, hndvdK, -, d', -, hd'A, hd'1, -, hd'K, -⟩ :=
    h112 G p A sit.setup f hfA hf1 K hK
  have hdAL : d ∈ A ⊓ L := by
    rw [← sit.d_gen]
    exact mem_zpowers d
  have hdAK : d ∈ A ⊓ K := ⟨sit.d_mem, hALK hdAL⟩
  have hdd' : zpowers d = zpowers d' := by
    have hle : zpowers d ≤ zpowers d' := by
      rw [hd'K]
      exact zpowers_le.mpr hdAK
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (sit.pow_eq_one sit.d_mem)
      sit.d_ne_one, orderOf_eq_prime (sit.pow_eq_one hd'A) hd'1]
  have hdgen : zpowers d = A ⊓ K := hdd'.trans hd'K
  refine ⟨hdgen.symm, ?_⟩
  have hAeq' : A = zpowers c ⊔ zpowers f ⊔ zpowers d := by
    refine le_antisymm ?_ (sup_le (sup_le (zpowers_le.mpr sit.c_mem) (zpowers_le.mpr hfA))
      (zpowers_le.mpr sit.d_mem))
    rw [sit.A_eq]
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact zpowers_le.mpr (Subgroup.mem_sup_left (sit.a_mem_sup_of_coords hij hi))
    · exact le_sup_left.trans le_sup_left
  exact ⟨sit.setup, hfA, hf1, hK, fun K' hK' hle =>
    sit.fail K' hK' ((le_inf inf_le_left hALK).trans hle), sit.c_mem, sit.d_mem, sit.d_ne_one,
    hAeq', hdgen, hcK, hEvenK, hndvdK⟩

theorem replace_a (sit : Sit p A c L a d) {f : G} {i j : ℤ} (hij : f = a ^ i * c ^ j)
    (hi : ¬ (p : ℤ) ∣ i) : Sit p A c L f d := by
  have hfA : f ∈ A := by
    rw [hij]
    exact mul_mem (zpow_mem sit.a_mem i) (zpow_mem sit.c_mem j)
  have hAeq : A = zpowers f ⊔ zpowers c ⊔ zpowers d := by
    refine le_antisymm ?_ (sup_le (sup_le (zpowers_le.mpr hfA) (zpowers_le.mpr sit.c_mem))
      (zpowers_le.mpr sit.d_mem))
    have haR : a ∈ zpowers f ⊔ zpowers c ⊔ zpowers d := by
      have h := sit.a_mem_sup_of_coords hij hi
      rw [sup_comm] at h
      exact Subgroup.mem_sup_left h
    have hcR : zpowers c ≤ zpowers f ⊔ zpowers c ⊔ zpowers d :=
      (le_sup_right : zpowers c ≤ zpowers f ⊔ zpowers c).trans le_sup_left
    rw [sit.A_eq]
    exact sup_le (sup_le (zpowers_le.mpr haR) hcR) le_sup_right
  exact ⟨sit.setup, sit.c_mem, sit.c_ne_one, sit.L_mem, sit.fail, hfA, sit.d_mem, sit.d_ne_one,
    hAeq, sit.d_gen, hij ▸ sit.inducesFieldAut_mul j hi, sit.even, sit.p_ndvd⟩

theorem not_mem_zpowers_c_of_coords (sit : Sit p A c L a d) {f : G} {i j : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) : f ∉ zpowers c := by
  intro hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have h1 : a ^ i * c ^ (j - k) = 1 := by
    calc a ^ i * c ^ (j - k) = (a ^ i * c ^ j) * (c ^ k)⁻¹ := by rw [zpow_sub, mul_assoc]
      _ = f * f⁻¹ := by rw [← hij, hk]
      _ = 1 := mul_inv_cancel f
  have := sit.coords_eq_one (x := i) (y := j - k) (z := 0) (by rw [zpow_zero, mul_one]; exact h1)
  exact hi this.1

theorem c_not_mem_sup_L (sit : Sit p A c L a d) : c ∉ zpowers a ⊔ L := by
  have : Fact p.Prime := ⟨sit.prime⟩
  intro hc
  have haN : zpowers a ≤ normalizer (L : Set G) := zpowers_le.mpr sit.a_field.1
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers a) L haN
  have hc' : c ∈ ((zpowers a : Subgroup G) : Set G) * (L : Set G) := by
    rw [← hcoe]
    exact hc
  obtain ⟨x, hx, l, hl, hxl⟩ := Set.mem_mul.mp hc'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hak : a ^ k = c * l⁻¹ := eq_mul_inv_of_mul_eq hxl
  have hcC : c ∈ centralizer (L : Set G) := by simpa using sit.zpow_c_mem_centralizer 1
  by_cases hdiv : (p : ℤ) ∣ k
  · have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
    have h1 : a ^ k = 1 := by
      obtain ⟨t, rfl⟩ := hdiv
      rw [zpow_mul, zpow_natCast, hap, one_zpow]
    rw [h1] at hak
    have hcl : c = l := by
      have := hak.symm
      rw [mul_inv_eq_one] at this
      exact this
    have hcAL : c ∈ A ⊓ L := ⟨sit.c_mem, hcl ▸ hl⟩
    rw [← sit.d_gen] at hcAL
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hcAL
    have := sit.coords_eq_one (x := 0) (y := 1) (z := -m) (by
      rw [zpow_zero, one_mul, zpow_one, zpow_neg, hm]
      exact mul_inv_cancel c)
    have h1' : (p : ℤ) ∣ 1 := this.2.1
    have := Int.eq_one_of_dvd_one (by positivity) h1'
    exact sit.prime.one_lt.ne' (by exact_mod_cast this)
  · obtain ⟨m, hm⟩ := exists_nat_pow_zpow_eq_self (sit.pow_eq_one sit.a_mem) hdiv
    have hakL : a ^ k ∈ L ⊔ centralizer (L : Set G) := by
      rw [hak]
      exact mul_mem (Subgroup.mem_sup_right hcC) (inv_mem (Subgroup.mem_sup_left hl))
    apply sit.a_field.2.1
    rw [← hm]
    exact zpow_mem hakL _

theorem localRank_le_two (sit : Sit p A c L a d) : localRank p ↥(L ⊔ zpowers a) ≤ 2 := by
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    have := sit.five_le
    omega
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq sit.setup).le
  by_cases hpos : 0 < localRank p ↥(L ⊔ zpowers a)
  · have hcp : c ^ p = 1 := sit.pow_eq_one sit.c_mem
    have hc1 := sit.c_ne_one
    have hP : IsElemAbelian p (zpowers c) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp
        (IsElementaryAbelian.zpowers_of_pow_eq_one hcp)
    have hMc : L ⊔ zpowers a ≤ centralizer ({c} : Set G) := by
      refine sup_le sit.L_le_centralizer ?_
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (sit.A_comm sit.a_mem sit.c_mem)
    have hPM : zpowers c ≤ centralizer ((L ⊔ zpowers a : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hMc hx)
    have hcM : c ∉ L ⊔ zpowers a := by
      rw [sup_comm]
      exact sit.c_not_mem_sup_L
    have hdisj : zpowers c ⊓ (L ⊔ zpowers a) = ⊥ := by
      rw [inf_comm]
      exact Sec12Two.inf_zpowers_eq_bot hp hcp hcM
    have hk : Nat.card (zpowers c) = p ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hcp hc1, pow_one]
    have := Sec12Two.localRank_add_le_evenRank hp hp2 (M := L ⊔ zpowers a) (P := zpowers c)
      hpos hP hPM hdisj hk
    omega
  · omega

end Sit

end Sec11Indeed

end CFSG.RankThree.PartOne
