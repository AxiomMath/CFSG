module

public import CFSG.RankThree.PartOne.S11c.HSPairCentralize
import CFSG.GroupTheory.PrimeOrderSubgroups

public section

namespace CFSG.RepresentationTheory.GF2

open CFSG.RankThree.PartOne.HNRed
open CFSG.GroupTheory

variable {Γ : Type*} [Group Γ]

@[expose] noncomputable def fiveSqSubgroup (a b : Γ) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hab : a * b = b * a) : Subgroup Γ :=
  (fiveHom2 a b ha hb hab).range

theorem mem_fiveSqSubgroup_iff {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} {x : Γ} :
    x ∈ fiveSqSubgroup a b ha hb hab ↔
      ∃ p : ZMod 5 × ZMod 5, x = a ^ p.1.val * b ^ p.2.val := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.toAdd, ?_⟩
    exact fiveHom2_apply a b ha hb hab p.toAdd
  · rintro ⟨⟨i, j⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (i, j), ?_⟩
    exact fiveHom2_apply a b ha hb hab (Multiplicative.ofAdd (i, j))

theorem mem_fiveSqSubgroup_left {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} : a ∈ fiveSqSubgroup a b ha hb hab := by
  rw [mem_fiveSqSubgroup_iff]
  exact ⟨(1, 0), by simp [ZMod.val_one, ZMod.val_zero]⟩

theorem mem_fiveSqSubgroup_right {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} : b ∈ fiveSqSubgroup a b ha hb hab := by
  rw [mem_fiveSqSubgroup_iff]
  exact ⟨(0, 1), by simp [ZMod.val_one, ZMod.val_zero]⟩

theorem five_dvd_exponents_of_mul_eq_one {a b : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 5 = 1) (hab : a * b = b * a) (hb' : ∀ i : ℕ, b ≠ a ^ i)
    {i j : ℕ} (h : a ^ i * b ^ j = 1) : 5 ∣ i ∧ 5 ∣ j := by
  classical
  have hb1 : b ≠ 1 := by simpa using hb' 0
  have hb_not_A : b ∉ Subgroup.zpowers a := by
    intro hbA
    have hpow : b ∈ Submonoid.powers a :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, ha⟩).mem_powers_iff_mem_zpowers.mpr hbA
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff b a).mp hpow
    exact hb' n hn.symm
  have hb_ord : orderOf b = 5 := orderOf_eq_prime hb hb1
  have hj : 5 ∣ j := by
    by_contra hj
    have hbjA : b ^ j ∈ Subgroup.zpowers a := by
      have h' : b ^ j = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h']
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)
    have hcop : Nat.Coprime j 5 := by
      rw [Nat.coprime_comm, (Nat.prime_five).coprime_iff_not_dvd]
      exact hj
    have hb_in_bj : b ∈ Subgroup.zpowers (b ^ j) := by
      rw [mem_zpowers_pow_iff, hb_ord]
      exact hcop.gcd_eq_one
    exact hb_not_A (Subgroup.zpowers_le.mpr hbjA hb_in_bj)
  have hi : 5 ∣ i := by
    have hbj : b ^ j = 1 := by
      rw [← hb_ord] at hj
      exact orderOf_dvd_iff_pow_eq_one.mp hj
    have hai : a ^ i = 1 := by rw [← h, hbj, mul_one]
    have : orderOf a ∣ i := orderOf_dvd_iff_pow_eq_one.mpr hai
    rwa [orderOf_eq_prime ha ha1] at this
  exact ⟨hi, hj⟩

@[expose] noncomputable def fiveSqEquiv {a b : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 5 = 1) (hab : a * b = b * a) (hb' : ∀ i : ℕ, b ≠ a ^ i) :
    Multiplicative (ZMod 5 × ZMod 5) ≃* fiveSqSubgroup a b ha hb hab :=
  MonoidHom.ofInjective <|
    fiveHom2_injective a b ha hb hab fun i j h =>
      five_dvd_exponents_of_mul_eq_one ha ha1 hb hab hb' h

theorem card_fiveSqSubgroup {a b : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 5 = 1) (hab : a * b = b * a) (hb' : ∀ i : ℕ, b ≠ a ^ i) :
    Nat.card (fiveSqSubgroup a b ha hb hab) = 25 := by
  let e := fiveSqEquiv ha ha1 hb hab hb'
  calc
    Nat.card (fiveSqSubgroup a b ha hb hab) =
        Nat.card (Multiplicative (ZMod 5 × ZMod 5)) := Nat.card_congr e.toEquiv.symm
    _ = Nat.card (ZMod 5 × ZMod 5) := Nat.card_congr Multiplicative.toAdd
    _ = 25 := by simp [Nat.card_prod, Nat.card_zmod]

theorem fiveSqSubgroup_comm {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} : ∀ x ∈ fiveSqSubgroup a b ha hb hab,
      ∀ y ∈ fiveSqSubgroup a b ha hb hab, x * y = y * x := by
  rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_five_eq_one_of_mem_fiveSqSubgroup {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} {x : Γ} (hx : x ∈ fiveSqSubgroup a b ha hb hab) : x ^ 5 = 1 := by
  rcases hx with ⟨p, rfl⟩
  exact fiveHom2_pow_five a b ha hb hab p

end CFSG.RepresentationTheory.GF2


namespace CFSG.RepresentationTheory.GF2

open CFSG.GroupTheory

variable {Γ : Type*} [Group Γ]

theorem pow_five_eq_one {a b : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a} (x : fiveSqSubgroup a b ha hb hab) : x ^ 5 = 1 := by
  apply Subtype.ext
  exact pow_five_eq_one_of_mem_fiveSqSubgroup x.2

private theorem eq_one_of_lt_five_of_pow_three_modEq_one {n : ℕ} (h : n < 5)
    (hmod : n ^ 3 ≡ 1 [MOD 5]) : n = 1 := by
  interval_cases n <;> first | rfl | norm_num at hmod

private theorem eq_zero_of_lt_five_of_three_mul_modEq_zero {n : ℕ} (h : n < 5)
    (hmod : n * 3 ≡ 0 [MOD 5]) :
    n = 0 := by
  interval_cases n <;> first | rfl | norm_num at hmod

private theorem aut_fixes_generator_of_fixes_line {E : Type*} [Group E] [Finite E]
    {c : MulAut E} (hc3 : c ^ 3 = 1) {L : Subgroup E} {x : E}
    (hxL : x ∈ L) (hxord : orderOf x = 5)
    (hLx : L = Subgroup.zpowers x) (hfix : L.map c.toMonoidHom = L) :
    c x = x := by
  classical
  have hcxL : c x ∈ L := by
    rw [← hfix]
    exact ⟨x, hxL, rfl⟩
  have hmem :=
    (isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp (by rwa [hLx] at hcxL)
  rw [Finset.mem_image] at hmem
  obtain ⟨i, hi_mem, hi⟩ := hmem
  have hi_lt : i < 5 := by
    have := Finset.mem_range.mp hi_mem
    rwa [hxord] at this
  have hc3x : c (c (c x)) = x := by
    have h := congrArg (fun f : MulAut E => f x) hc3
    simpa [pow_three] using h
  have hc3x_pow : c (c (c x)) = x ^ (i ^ 3) := by
    calc
      c (c (c x)) = c (c (x ^ i)) := by rw [hi]
      _ = c ((c x) ^ i) := by rw [map_pow]
      _ = c ((x ^ i) ^ i) := by rw [← hi]
      _ = (c (x ^ i)) ^ i := by rw [map_pow]
      _ = ((c x) ^ i) ^ i := by rw [map_pow]
      _ = (((x ^ i) ^ i) ^ i) := by rw [← hi]
      _ = x ^ (i ^ 3) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have hpow_eq : x ^ (i ^ 3) = x := by rw [← hc3x_pow, hc3x]
  have hmod : i ^ 3 ≡ 1 [MOD 5] := by
    have h := (pow_eq_pow_iff_modEq (x := x) (n := i ^ 3) (m := 1)).mp (by simpa using hpow_eq)
    rwa [hxord] at h
  have hi1 : i = 1 := eq_one_of_lt_five_of_pow_three_modEq_one hi_lt hmod
  rw [← hi, hi1, pow_one]

private theorem complement_coordinates {E : Type*} [CommGroup E] [Finite E]
    {L M : Subgroup E} {x y : E}
    (hLx : L = Subgroup.zpowers x) (hMy : M = Subgroup.zpowers y)
    (hxord : orderOf x = 5) (hyord : orderOf y = 5)
    {z : E} (hz : z ∈ L ⊔ M) :
    ∃ a b : ℕ, a < 5 ∧ b < 5 ∧ z = x ^ a * y ^ b := by
  classical
  obtain ⟨u, huL, v, hvM, huv⟩ := Subgroup.mem_sup.mp hz
  have hmemu :=
    (isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp (by rwa [hLx] at huL)
  rw [Finset.mem_image] at hmemu
  obtain ⟨a, ha_mem, ha⟩ := hmemu
  have hmemv :=
    (isOfFinOrder_of_finite y).mem_zpowers_iff_mem_range_orderOf.mp (by rwa [hMy] at hvM)
  rw [Finset.mem_image] at hmemv
  obtain ⟨b, hb_mem, hb⟩ := hmemv
  have ha_lt : a < 5 := by
    have := Finset.mem_range.mp ha_mem
    rwa [hxord] at this
  have hb_lt : b < 5 := by
    have := Finset.mem_range.mp hb_mem
    rwa [hyord] at this
  exact ⟨a, b, ha_lt, hb_lt, by rw [← huv, ← ha, ← hb]⟩

private theorem aut_cube_complement_coordinates {E : Type*} [CommGroup E]
    {c : MulAut E} (hc3 : c ^ 3 = 1) {L M : Subgroup E}
    (hmul_inj : Function.Injective fun p : L × M => ((p.1 : E) * (p.2 : E)))
    {x y : E} (hLx : L = Subgroup.zpowers x) (hMy : M = Subgroup.zpowers y)
    (hxord : orderOf x = 5) (hyord : orderOf y = 5) (hcx : c x = x)
    {a b : ℕ} (ha : a < 5) (hb : b < 5) (hcy : c y = x ^ a * y ^ b) :
    a = 0 ∧ b = 1 := by
  have hc2y : c (c y) = x ^ (a + a * b) * y ^ (b * b) := by
    rw [hcy, map_mul, map_pow, map_pow, hcx, hcy]
    rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
  have hc3y : c (c (c y)) = x ^ (a * (1 + b + b ^ 2)) * y ^ (b ^ 3) := by
    rw [hc2y, map_mul, map_pow, map_pow, hcx, hcy]
    rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
    ring_nf
  have hc3y_eq : c (c (c y)) = y := by
    have h := congrArg (fun f : MulAut E => f y) hc3
    simpa [pow_three] using h
  have hxy_eq : x ^ (a * (1 + b + b ^ 2)) * y ^ (b ^ 3) = y := by
    rw [← hc3y, hc3y_eq]
  let pair1 : L × M :=
    ((⟨x ^ (a * (1 + b + b ^ 2)), by
        rw [hLx]
        exact Subgroup.npow_mem_zpowers x _⟩ : L),
      (⟨y ^ (b ^ 3), by
        rw [hMy]
        exact Subgroup.npow_mem_zpowers y _⟩ : M))
  let pair2 : L × M :=
    ((⟨1, Subgroup.one_mem L⟩ : L), (⟨y, by rw [hMy]; exact Subgroup.mem_zpowers y⟩ : M))
  have hpair : pair1 = pair2 := hmul_inj (by
    change ((pair1.1 : E) * (pair1.2 : E)) = ((pair2.1 : E) * (pair2.2 : E))
    simpa [pair1, pair2] using hxy_eq)
  have hxB : x ^ (a * (1 + b + b ^ 2)) = 1 :=
    congrArg (fun z : L => (z : E)) (congrArg Prod.fst hpair)
  have hyB : y ^ (b ^ 3) = y :=
    congrArg (fun z : M => (z : E)) (congrArg Prod.snd hpair)
  have hBmod : b ^ 3 ≡ 1 [MOD 5] := by
    have h := (pow_eq_pow_iff_modEq (x := y) (n := b ^ 3) (m := 1)).mp (by simpa using hyB)
    rwa [hyord] at h
  have hb1 : b = 1 := eq_one_of_lt_five_of_pow_three_modEq_one hb hBmod
  have hAmod : a * 3 ≡ 0 [MOD 5] := by
    have h := (pow_eq_pow_iff_modEq (x := x) (n := a * (1 + b + b ^ 2))
      (m := 0)).mp (by simpa using hxB)
    rwa [hxord, hb1] at h
  have ha0 : a = 0 := eq_zero_of_lt_five_of_three_mul_modEq_zero ha (by simpa [hb1] using hAmod)
  exact ⟨ha0, hb1⟩

private theorem aut_fixes_complement_generator {E : Type*} [CommGroup E] [Finite E]
    {c : MulAut E} (hc3 : c ^ 3 = 1) {L M : Subgroup E}
    (hsup : L ⊔ M = ⊤)
    (hmul_inj : Function.Injective fun p : L × M => ((p.1 : E) * (p.2 : E)))
    {x y : E} (hLx : L = Subgroup.zpowers x) (hMy : M = Subgroup.zpowers y)
    (hxord : orderOf x = 5) (hyord : orderOf y = 5) (hcx : c x = x) :
    c y = y := by
  have hcy_sup : c y ∈ L ⊔ M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨a, b, ha, hb, hcy⟩ := complement_coordinates hLx hMy hxord hyord hcy_sup
  obtain ⟨ha0, hb1⟩ :=
    aut_cube_complement_coordinates hc3 hmul_inj hLx hMy hxord hyord hcx ha hb hcy
  rw [hcy, ha0, hb1]
  simp

theorem aut_eq_one_of_fixes_generators {E : Type*} [CommGroup E]
    {c : MulAut E} {L M : Subgroup E} (hsup : L ⊔ M = ⊤) {x y : E}
    (hLx : L = Subgroup.zpowers x) (hMy : M = Subgroup.zpowers y)
    (hcx : c x = x) (hcy : c y = y) : c = 1 := by
  ext z
  have hz : z ∈ L ⊔ M := by rw [hsup]; exact Subgroup.mem_top z
  obtain ⟨u, huL, v, hvM, huv⟩ := Subgroup.mem_sup (s := L) (t := M) |>.mp hz
  have hcu : c u = u := by
    rw [hLx, Subgroup.mem_zpowers_iff] at huL
    obtain ⟨m, rfl⟩ := huL
    rw [map_zpow, hcx]
  have hcv : c v = v := by
    rw [hMy, Subgroup.mem_zpowers_iff] at hvM
    obtain ⟨n, rfl⟩ := hvM
    rw [map_zpow, hcy]
  rw [← huv, map_mul, hcu, hcv]
  rfl

theorem fiveSq_zpowers_lines_ne {a b : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 5 = 1) (hab : a * b = b * a) (hb' : ∀ i : ℕ, b ≠ a ^ i) :
    Subgroup.zpowers (⟨a, mem_fiveSqSubgroup_left⟩ : fiveSqSubgroup a b ha hb hab) ≠
      Subgroup.zpowers (⟨b, mem_fiveSqSubgroup_right⟩ : fiveSqSubgroup a b ha hb hab) := by
  intro hAB
  have hb_not_A : b ∉ Subgroup.zpowers a := by
    intro hbA
    have hpow : b ∈ Submonoid.powers a :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, ha⟩).mem_powers_iff_mem_zpowers.mpr hbA
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff b a).mp hpow
    exact hb' n hn.symm
  have hbA : (⟨b, mem_fiveSqSubgroup_right⟩ : fiveSqSubgroup a b ha hb hab) ∈
      Subgroup.zpowers (⟨a, mem_fiveSqSubgroup_left⟩ : fiveSqSubgroup a b ha hb hab) := by
    rw [hAB]
    exact Subgroup.mem_zpowers _
  rw [Subgroup.mem_zpowers_iff] at hbA
  obtain ⟨k, hk⟩ := hbA
  apply hb_not_A
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, congrArg Subtype.val hk⟩

theorem fiveSq_no_fixed_line_of_order_three {a b : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hb : b ^ 5 = 1) (hab : a * b = b * a) (hb' : ∀ i : ℕ, b ≠ a ^ i)
    (c : MulAut (fiveSqSubgroup a b ha hb hab)) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) {L : Subgroup (fiveSqSubgroup a b ha hb hab)} (hL : Nat.card L = 5) :
    L.map c.toMonoidHom ≠ L := by
  classical
  let E := fiveSqSubgroup a b ha hb hab
  have hEcard : Nat.card E = 25 := card_fiveSqSubgroup ha ha1 hb hab hb'
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hcommE : ∀ x y : E, x * y = y * x := fun x y =>
    Subtype.ext (fiveSqSubgroup_comm (x := (x : Γ)) x.2 (y := (y : Γ)) y.2)
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcommE }
  let ea : E := ⟨a, mem_fiveSqSubgroup_left⟩
  let eb : E := ⟨b, mem_fiveSqSubgroup_right⟩
  have hA5 : ea ^ 5 = 1 := pow_five_eq_one ea
  have hA1 : ea ≠ 1 := by
    intro h
    exact ha1 (congrArg Subtype.val h)
  have hB5 : eb ^ 5 = 1 := pow_five_eq_one eb
  have hB1 : eb ≠ 1 := by
    have hb1 : b ≠ 1 := by simpa using hb' 0
    intro h
    exact hb1 (congrArg Subtype.val h)
  have hAcard : Nat.card (Subgroup.zpowers ea) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hA5 hA1]
  have hBcard : Nat.card (Subgroup.zpowers eb) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hB5 hB1]
  have hA_ne_B := fiveSq_zpowers_lines_ne ha ha1 hb hab hb'
  obtain ⟨M, hMcard, hM_ne_L, hcompl⟩ :=
    exists_complement_line_of_prime Nat.prime_five hEcard hAcard hBcard hA_ne_B hL
  have hdisj : Disjoint L M := hcompl.disjoint
  have hsup : L ⊔ M = ⊤ := codisjoint_iff.mp hcompl.codisjoint
  obtain ⟨x, hxL, hxord, hLx⟩ :=
    exists_generator_of_card_prime Nat.prime_five (E := E) hL
  obtain ⟨y, hyM, hyord, hMy⟩ :=
    exists_generator_of_card_prime Nat.prime_five (E := E) hMcard
  have hmul_inj : Function.Injective fun p : L × M => ((p.1 : E) * (p.2 : E)) :=
    Subgroup.mul_injective_of_disjoint hdisj
  intro hfix
  have hcx : c x = x := aut_fixes_generator_of_fixes_line hc3 hxL hxord hLx hfix
  have hcy : c y = y :=
    aut_fixes_complement_generator hc3 hsup hmul_inj hLx hMy hxord hyord hcx
  exact hc1 (aut_eq_one_of_fixes_generators hsup hLx hMy hcx hcy)

end CFSG.RepresentationTheory.GF2

namespace CFSG.RepresentationTheory.GF2

open CFSG.RankThree.PartOne.HNRed
open CFSG.GroupTheory

variable {Γ : Type*} [Group Γ]

theorem fiveSqSubgroup_le_normalizer {a b g : Γ} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hab : a * b = b * a)
    (hga : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j)
    (hgb : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j) :
    g ∈ Subgroup.normalizer (fiveSqSubgroup a b ha hb hab : Set Γ) := by
  classical
  let E := fiveSqSubgroup a b ha hb hab
  have haE : a ∈ E := mem_fiveSqSubgroup_left
  have hbE : b ∈ E := mem_fiveSqSubgroup_right
  obtain ⟨i, j, hga'⟩ := hga
  obtain ⟨k, l, hgb'⟩ := hgb
  have hca : MulAut.conj g a ∈ E := by
    rw [MulAut.conj_apply, hga']
    exact E.mul_mem (E.pow_mem haE i) (E.pow_mem hbE j)
  have hcb : MulAut.conj g b ∈ E := by
    rw [MulAut.conj_apply, hgb']
    exact E.mul_mem (E.pow_mem haE k) (E.pow_mem hbE l)
  haveI : Finite E := (Set.finite_range (fiveHom2 a b ha hb hab)).to_subtype
  have hmap_le : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro x ⟨y, hy, rfl⟩
    change y ∈ fiveSqSubgroup a b ha hb hab at hy
    change (MulAut.conj g) y ∈ fiveSqSubgroup a b ha hb hab
    obtain ⟨⟨p, q⟩, rfl⟩ := mem_fiveSqSubgroup_iff.mp hy
    rw [map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hca p.val) (E.pow_mem hcb q.val)
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hmap_eq : E.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmap_eq

@[expose] noncomputable def fiveSqConjAut {a b g : Γ} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hab : a * b = b * a)
    (hgE : g ∈ Subgroup.normalizer (fiveSqSubgroup a b ha hb hab : Set Γ)) :
    MulAut (fiveSqSubgroup a b ha hb hab) :=
  Subgroup.normalizerMonoidHom (H := fiveSqSubgroup a b ha hb hab) ⟨g, hgE⟩

@[simp]
theorem fiveSqConjAut_apply {a b g : Γ} {ha : a ^ 5 = 1} {hb : b ^ 5 = 1}
    {hab : a * b = b * a}
    {hgE : g ∈ Subgroup.normalizer (fiveSqSubgroup a b ha hb hab : Set Γ)}
    (x : fiveSqSubgroup a b ha hb hab) :
    ((fiveSqConjAut ha hb hab hgE x : fiveSqSubgroup a b ha hb hab) : Γ) =
      g * x * g⁻¹ := rfl

theorem fiveSqConjAut_pow_three {a b g : Γ} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hab : a * b = b * a)
    (hgE : g ∈ Subgroup.normalizer (fiveSqSubgroup a b ha hb hab : Set Γ))
    (hg : g ^ 3 = 1) : fiveSqConjAut ha hb hab hgE ^ 3 = 1 := by
  ext x
  simp only [pow_three, MulAut.mul_apply, MulAut.one_apply]
  change (fiveSqConjAut ha hb hab hgE
    (fiveSqConjAut ha hb hab hgE
      (fiveSqConjAut ha hb hab hgE x)) : Γ) = x
  rw [fiveSqConjAut_apply, fiveSqConjAut_apply, fiveSqConjAut_apply]
  calc
    g * (g * (g * (x : Γ) * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * (x : Γ) * (g ^ 3)⁻¹ := by
      rw [pow_three]
      group
    _ = x := by rw [hg]; group

theorem fiveSqConjAut_ne_one {a b g : Γ} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hab : a * b = b * a)
    (hgE : g ∈ Subgroup.normalizer (fiveSqSubgroup a b ha hb hab : Set Γ))
    (hgnc : g * a * g⁻¹ ≠ a ∨ g * b * g⁻¹ ≠ b) :
    fiveSqConjAut ha hb hab hgE ≠ 1 := by
  intro hc
  have haeq : g * a * g⁻¹ = a := by
    have h := congrArg
      (fun f : MulAut (fiveSqSubgroup a b ha hb hab) =>
        f ⟨a, mem_fiveSqSubgroup_left⟩) hc
    have h' := congrArg Subtype.val h
    simpa using h'
  have hbeq : g * b * g⁻¹ = b := by
    have h := congrArg
      (fun f : MulAut (fiveSqSubgroup a b ha hb hab) =>
        f ⟨b, mem_fiveSqSubgroup_right⟩) hc
    have h' := congrArg Subtype.val h
    simpa using h'
  rcases hgnc with h | h
  · exact h haeq
  · exact h hbeq

end CFSG.RepresentationTheory.GF2
