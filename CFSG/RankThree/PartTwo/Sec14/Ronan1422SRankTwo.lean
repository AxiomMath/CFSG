module

public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

theorem false_of_inverted_of_fixed {V : Type} [CommGroup V] [Finite V] {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hexp : ∀ v : V, v ^ r = 1) (hcard : Nat.card V ≤ r ^ 2)
    (g h : MulAut V) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hfix : ∃ v : V, v ≠ 1 ∧ g v = v)
    (hinv : h * g * h⁻¹ = g⁻¹) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨dl, hdl⟩ : ∃ dl : V →* V, ∀ v, dl v = g v * v⁻¹ :=
    ⟨MonoidHom.mk' (fun v => g v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv]; ac_rfl), fun v => rfl⟩
  have hg3' : ∀ y, g (g (g y)) = y := by
    intro y
    have := congrArg (fun f : MulAut V => f y) hg3
    simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply] using this
  have hginv : ∀ y, g⁻¹ y = g (g y) := by
    intro y
    have h1 : g (g⁻¹ y) = y := MulAut.apply_inv_self V g y
    have h2 := hg3' (g⁻¹ y)
    rw [h1] at h2
    exact h2.symm
  have hhg : ∀ y, h (g y) = g⁻¹ (h y) := by
    intro y
    have h1 : h * g = g⁻¹ * h := mul_inv_eq_iff_eq_mul.mp hinv
    have := congrArg (fun f : MulAut V => f y) h1
    simpa only [MulAut.mul_apply] using this
  have hgdl : ∀ v, g (dl v) = dl (g v) := by
    intro v
    simp only [hdl, map_mul, map_inv]
  have hhdl : ∀ u, h (dl u) = dl ((g⁻¹ (h u))⁻¹) := by
    intro u
    simp only [hdl, map_mul, map_inv, inv_inv, MulAut.apply_inv_self, hhg]
    exact mul_comm _ _
  have hdl3 : ∀ v, dl v * g (dl v) * g (g (dl v)) = 1 := by
    intro v
    have e1 : g (dl v) = g (g v) * (g v)⁻¹ := by rw [hdl, map_mul, map_inv]
    have e2 : g (g (dl v)) = v * (g (g v))⁻¹ := by rw [e1, map_mul, map_inv, hg3']
    rw [e2, e1, hdl]
    calc g v * v⁻¹ * (g (g v) * (g v)⁻¹) * (v * (g (g v))⁻¹)
        = (g v * (g v)⁻¹) * (v⁻¹ * v) * (g (g v) * (g (g v))⁻¹) := by ac_rfl
      _ = 1 := by simp
  obtain ⟨v₀, hv₀1, hv₀⟩ := hfix
  have hK : r ≤ Nat.card dl.ker := by
    have hle : Subgroup.zpowers v₀ ≤ dl.ker := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker, hdl, hv₀, mul_inv_cancel]
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, orderOf_eq_prime (hexp v₀) hv₀1] at this
  obtain ⟨u, hu⟩ : ∃ u, g u ≠ u := by
    by_contra hc
    push Not at hc
    exact hg1 (MulEquiv.ext fun w => by rw [MulAut.one_apply]; exact hc w)
  have hx1 : dl u ≠ 1 := by
    rw [hdl]
    exact fun hc => hu (mul_inv_eq_one.mp hc)
  have hord : orderOf (dl u) = r := orderOf_eq_prime (hexp _) hx1
  have hRle : Subgroup.zpowers (dl u) ≤ dl.range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨u, rfl⟩)
  have hR : r ≤ Nat.card dl.range := by
    have := Subgroup.card_le_of_le hRle
    rwa [Nat.card_zpowers, hord] at this
  have hmul : Nat.card dl.ker * Nat.card dl.range = Nat.card V := by
    have := Subgroup.card_mul_index (H := dl.ker)
    rwa [Subgroup.index_ker] at this
  have hRr : Nat.card dl.range = r := by
    have h1 : r * Nat.card dl.range ≤ Nat.card dl.ker * Nat.card dl.range :=
      Nat.mul_le_mul_right _ hK
    have h2 : r * Nat.card dl.range ≤ r * r := by
      rw [← sq]
      exact (h1.trans hmul.le).trans hcard
    have h3 : Nat.card dl.range ≤ r := Nat.le_of_mul_le_mul_left h2 hr.pos
    omega
  have hzR : Subgroup.zpowers (dl u) = dl.range :=
    Subgroup.eq_of_le_of_card_ge hRle (le_of_eq (by rw [Nat.card_zpowers, hord, hRr]))
  have hmemR : ∀ w, dl w ∈ dl.range := fun w => MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hgx : g (dl u) ∈ Subgroup.zpowers (dl u) := by
    rw [hzR, hgdl]
    exact hmemR (g u)
  have hhx : h (dl u) ∈ Subgroup.zpowers (dl u) := by
    rw [hzR, hhdl]
    exact hmemR _
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hgx
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hhx
  set x := dl u
  have hgi : g⁻¹ x = x ^ (a * a) := by
    rw [hginv, ← ha, map_zpow, ← ha, ← zpow_mul]
  have hgb : g⁻¹ (h x) = x ^ (a * a * b) := by
    rw [← hb, map_zpow, hgi, ← zpow_mul]
  have h2 : h (g x) = x ^ (b * a) := by
    rw [← ha, map_zpow, ← hb, ← zpow_mul]
  have hrel : x ^ (b * a) = x ^ (a * a * b) := by
    have := hhg x
    rw [h2, hgb] at this
    exact this
  have hkey : x ^ (b * a - a * a * b) = 1 := by
    rw [zpow_sub, hrel, mul_inv_cancel]
  have hdvd : (r : ℤ) ∣ a * b * (1 - a) := by
    have h1 : ((orderOf x : ℕ) : ℤ) ∣ b * a - a * a * b :=
      orderOf_dvd_iff_zpow_eq_one.mpr hkey
    rw [hord] at h1
    have e : a * b * (1 - a) = b * a - a * a * b := by ring
    rw [e]
    exact h1
  have hpZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have hxn : ∀ n : ℤ, (r : ℤ) ∣ n → x ^ n = 1 := fun n hn =>
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord]; exact hn)
  rcases hpZ.dvd_or_dvd hdvd with h1 | h1
  · rcases hpZ.dvd_or_dvd h1 with h2' | h2'
    · have hgx1 : g x = 1 := by rw [← ha, hxn a h2']
      exact hx1 ((MulEquiv.map_eq_one_iff g).mp hgx1)
    · have hhx1 : h x = 1 := by rw [← hb, hxn b h2']
      exact hx1 ((MulEquiv.map_eq_one_iff h).mp hhx1)
  ·
    have hxa1 : x ^ a = x := by
      calc x ^ a = x ^ a * x ^ (1 - a) := by rw [hxn (1 - a) h1, mul_one]
        _ = x ^ (a + (1 - a)) := (zpow_add x a (1 - a)).symm
        _ = x := by simp
    have hgxx : g x = x := ha.symm.trans hxa1
    have h3x : x * g x * g (g x) = 1 := hdl3 u
    rw [hgxx, hgxx] at h3x
    have hx3 : x ^ 3 = 1 := by rw [pow_three']; exact h3x
    have hg' : x ^ (Nat.gcd 3 r) = 1 := pow_gcd_eq_one.mpr ⟨hx3, hexp x⟩
    have hcop : Nat.gcd 3 r = 1 := (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
    rw [hcop, pow_one] at hg'
    exact hx1 hg'

theorem exists_fixed_of_elemAbelian_nine {V : Type} [CommGroup V] [Finite V] {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (hexp : ∀ v : V, v ^ r = 1) (hV : ∃ v : V, v ≠ 1)
    (E : Subgroup (MulAut V)) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hEexp : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9) :
    ∃ g ∈ E, g ≠ 1 ∧ ∃ v : V, v ≠ 1 ∧ g v = v := by
  haveI : Finite (MulAut V) := inferInstance
  by_contra hcon
  have H : ∀ e ∈ E, e ≠ 1 → ∀ w : V, w ≠ 1 → e w ≠ w := fun e he he1 w hw hew =>
    hcon ⟨e, he, he1, w, hw, hew⟩
  have hcube : ∀ e ∈ E, ∀ z : V, e (e (e z)) = z := by
    intro e he z
    have := congrArg (fun f : MulAut V => f z) (hEexp e he)
    simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply] using this
  have hline : ∀ e ∈ E, e ≠ 1 → ∀ y : V, y * e y * e (e y) = 1 := by
    intro e he he1 y
    by_contra hne
    apply H e he he1 _ hne
    simp only [map_mul, hcube e he]
    ac_rfl
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : E)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have ha3 : a ^ 3 = 1 := hEexp a ha
  have hzpow : orderOf a ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha3)
  obtain ⟨b, hb, hbn⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hc
    push Not at hc
    have := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from fun b hb => hc b hb)
    rw [hE9, Nat.card_zpowers] at this
    omega
  have hb3 : b ^ 3 = 1 := hEexp b hb
  have hab : a * b = b * a := hEc a ha b hb
  have hcomm : ∀ z, b (a z) = a (b z) := fun z => by
    have := congrArg (fun f : MulAut V => f z) hab
    simp only [MulAut.mul_apply] at this
    exact this.symm
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbn (Subgroup.one_mem _)
  have hab1 : a * b ≠ 1 := by
    intro hc
    apply hbn
    rw [eq_inv_of_mul_eq_one_right hc]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hab2 : a * b ^ 2 ≠ 1 := by
    intro hc
    apply hbn
    have h1 : a = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hc
    have h2 : (b ^ 2)⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hb3)
    rw [h1.trans h2]
    exact Subgroup.mem_zpowers b
  have hLa : ∀ y : V, y * a y * a (a y) = 1 := hline a ha ha1
  have hLb : ∀ y : V, y * b y * b (b y) = 1 := hline b hb hb1
  have hLab : ∀ y : V, y * a (b y) * a (a (b (b y))) = 1 := by
    intro y
    have := hline (a * b) (E.mul_mem ha hb) hab1 y
    simpa only [MulAut.mul_apply, hcomm] using this
  have hLab2 : ∀ y : V, y * a (b (b y)) * a (a (b y)) = 1 := by
    intro y
    have := hline (a * b ^ 2) (E.mul_mem ha (E.pow_mem hb 2)) hab2 y
    simpa only [MulAut.mul_apply, pow_two, hcomm, hcube b hb] using this
  have key : ∀ x : V, x ^ 3 = 1 := by
    intro x
    have ident : (x * a x * a (a x)) * (x * b x * b (b x)) * (x * a (b x) * a (a (b (b x))))
        * (x * a (b (b x)) * a (a (b x))) =
        x * x * x * ((x * a x * a (a x)) * (b x * a (b x) * a (a (b x)))
          * (b (b x) * a (b (b x)) * a (a (b (b x))))) := by
      ac_rfl
    rw [hLa x, hLb x, hLab x, hLab2 x, hLa (b x), hLa (b (b x))] at ident
    rw [pow_three']
    simp only [one_mul, mul_one] at ident
    exact ident.symm
  obtain ⟨v, hv1⟩ := hV
  have hgcd : v ^ (Nat.gcd 3 r) = 1 := pow_gcd_eq_one.mpr ⟨key v, hexp v⟩
  have hcop : Nat.gcd 3 r = 1 := (Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3)
  rw [hcop, pow_one] at hgcd
  exact hv1 hgcd

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
