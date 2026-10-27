module

public import CFSG.Certificates.Kernel.C7155.Sound
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.KC.C7155

open CFSG.Quasithin.H13.NQCat.T513.L35 Matrix

@[expose] def xT : G35 := ⟨!![2, 0, 0; 0, 1, 0; 0, 0, 3], by rw [Matrix.det_fin_three]; decide⟩

@[expose] def sT : G35 := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 4], by rw [Matrix.det_fin_three]; decide⟩

@[expose] def dT : G35 := ⟨!![3, 0, 0; 0, 2, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

theorem xT_mem : xT ∈ T0 := mem_T0_iff.mpr (by unfold IsMon xT; decide)

theorem sT_mem : sT ∈ T0 := mem_T0_iff.mpr (by unfold IsMon sT; decide)

theorem dT_mem : dT ∈ T0 := mem_T0_iff.mpr (by unfold IsMon dT; decide)

theorem sx_dT : sT * xT * dT = xT * sT := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, xT, sT, dT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> decide

theorem mulVec_e3 (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) :
    M *ᵥ ![0, 0, 1] = ![M 0 2, M 1 2, M 2 2] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem vec_eq_smul_e3 (w : Fin 3 → ZMod 5) (h0 : w 0 = 0) (h1 : w 1 = 0) :
    w = w 2 • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [h0, h1]

theorem dT_coe : (dT : Matrix (Fin 3) (Fin 3) (ZMod 5)) = !![3, 0, 0; 0, 2, 0; 0, 0, 1] := rfl

theorem sT_coe : (sT : Matrix (Fin 3) (Fin 3) (ZMod 5)) = !![0, 1, 0; 1, 0, 0; 0, 0, 4] := rfl

theorem isMon_mulVec_e3 {t : G35} (ht : t ∈ T0) :
    (t : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ ![0, 0, 1] =
      (t : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 • ![0, 0, 1] := by
  obtain ⟨h02, h12, -, -, -, -⟩ := mem_T0_iff.mp ht
  rw [mulVec_e3, h02, h12]
  ext i
  fin_cases i <;> simp

theorem isMon_22 {t : G35} (ht : t ∈ T0) : (t : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 ≠ 0 :=
  (mem_T0_iff.mp ht).2.2.2.2.1

section Perm

variable {g : G35} (hg : g ^ 11625 = 1)
  (hperm : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g = g ^ a * t')

include hg in
theorem zpow_eq_pow (a : ℤ) : ∃ n : ℕ, g ^ a = g ^ n := by
  have h2 : g ^ (11625 : ℤ) = 1 := by exact_mod_cast hg
  refine ⟨(a % 11625).toNat, ?_⟩
  rw [zpow_eq_zpow_emod a h2, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

include hg hperm in
theorem perm_pow (n : ℕ) : ∀ t ∈ T0, ∃ a : ℕ, ∃ t' ∈ T0, t * g ^ n = g ^ a * t' := by
  induction n with
  | zero => exact fun t ht => ⟨0, t, ht, by simp⟩
  | succ n ih =>
    intro t ht
    obtain ⟨a, t', ht', h1⟩ := ih t ht
    obtain ⟨b, t'', ht'', h2⟩ := hperm t' ht'
    obtain ⟨m, hm⟩ := zpow_eq_pow hg b
    refine ⟨a + m, t'', ht'', ?_⟩
    rw [pow_succ, ← mul_assoc, h1, mul_assoc, h2, hm, ← mul_assoc, pow_add]

@[expose] def permH : Subgroup G35 where
  carrier := {x | ∃ a : ℕ, ∃ t ∈ T0, x = g ^ a * t}
  mul_mem' := by
    rintro _ _ ⟨a, t, ht, rfl⟩ ⟨b, t', ht', rfl⟩
    obtain ⟨c, t'', ht'', h⟩ := perm_pow hg hperm b t ht
    refine ⟨a + c, t'' * t', T0.mul_mem ht'' ht', ?_⟩
    rw [show g ^ a * t * (g ^ b * t') = g ^ a * (t * g ^ b) * t' by simp only [mul_assoc], h,
      pow_add]
    simp only [mul_assoc]
  one_mem' := ⟨0, 1, T0.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, t, ht, rfl⟩
    obtain ⟨c, t'', ht'', h⟩ := perm_pow hg hperm (a * 11624) t⁻¹ (T0.inv_mem ht)
    refine ⟨c, t'', ht'', ?_⟩
    have h1 : g ^ a * g ^ (a * 11624) = 1 := by
      rw [← pow_add, show a + a * 11624 = 11625 * a by ring, pow_mul, hg, one_pow]
    rw [_root_.mul_inv_rev, ← eq_inv_of_mul_eq_one_right h1, h]

include hg hperm in
theorem mem_permH : g ∈ permH hg hperm := ⟨1, 1, T0.one_mem, by simp⟩

include hg hperm in
theorem T0_le_permH : T0 ≤ permH hg hperm := fun t ht => ⟨0, t, ht, by simp⟩

include hg hperm in
theorem card_permH {o : ℕ} (hp : o.Prime) (ho : g ^ o = 1) (h1 : g ≠ 1) (h2 : ¬ 2 ∣ o) :
    Nat.card (permH hg hperm) = o * 32 := by
  have : Fact o.Prime := ⟨hp⟩
  have hord : orderOf g = o := orderOf_eq_prime ho h1
  apply le_antisymm
  · let f : Fin o × T0 → permH hg hperm := fun p => ⟨g ^ (p.1 : ℕ) * p.2, ⟨p.1, p.2, p.2.2, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, a, t, ht, rfl⟩
      refine ⟨(⟨a % o, Nat.mod_lt _ hp.pos⟩, ⟨t, ht⟩), Subtype.ext ?_⟩
      change g ^ (a % o) * t = g ^ a * t
      conv_rhs => rw [← Nat.div_add_mod a o, pow_add, pow_mul, ho, one_pow, one_mul]
    calc Nat.card (permH hg hperm) ≤ Nat.card (Fin o × T0) := Nat.card_le_card_of_surjective f hf
      _ = o * 32 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, card_T0]
  · have hz : Nat.card (Subgroup.zpowers g) ∣ Nat.card (permH hg hperm) :=
      Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr (mem_permH hg hperm))
    rw [Nat.card_zpowers, hord] at hz
    have hT : Nat.card T0 ∣ Nat.card (permH hg hperm) := Subgroup.card_dvd_of_le (T0_le_permH hg hperm)
    rw [card_T0] at hT
    have hcop : Nat.Coprime o 32 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
      exact Nat.Coprime.pow_right 5 ((Nat.coprime_comm.mp ((Nat.coprime_primes Nat.prime_two hp).mpr
        (fun h => h2 (h ▸ dvd_refl 2)))))
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd hz hT)

include hg hperm in
theorem dT_comm (hn : ∀ t ∈ T0, t * g * t⁻¹ ∈ Subgroup.zpowers g) : dT * g = g * dT := by
  obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.mp (hn xT xT_mem)
  obtain ⟨β, hβ⟩ := Subgroup.mem_zpowers_iff.mp (hn sT sT_mem)
  have hE : xT * sT * g * (xT * sT)⁻¹ = g ^ (α * β) := by
    rw [show xT * sT * g * (xT * sT)⁻¹ = xT * (sT * g * sT⁻¹) * xT⁻¹ by group, ← hβ, ← conj_zpow,
      ← hα, zpow_mul]
  have hF : sT * xT * g * (sT * xT)⁻¹ = g ^ (α * β) := by
    rw [show sT * xT * g * (sT * xT)⁻¹ = sT * (xT * g * xT⁻¹) * sT⁻¹ by group, ← hα, ← conj_zpow,
      ← hβ, ← zpow_mul, mul_comm]
  have hd : dT = (sT * xT)⁻¹ * (xT * sT) := eq_inv_mul_of_mul_eq sx_dT
  calc dT * g = (sT * xT)⁻¹ * (xT * sT * g * (xT * sT)⁻¹) * (xT * sT) := by rw [hd]; group
    _ = (sT * xT)⁻¹ * (sT * xT * g * (sT * xT)⁻¹) * (xT * sT) := by rw [hE, hF]
    _ = g * dT := by rw [hd]; group

theorem col_of_dT_comm {g : G35} (h : dT * g = g * dT) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = 0 := by
  have h1 := congrArg (fun x : G35 => (x : Matrix (Fin 3) (Fin 3) (ZMod 5))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, dT_coe] at h1
  have h02 := congrFun (congrFun h1 0) 2
  have h12 := congrFun (congrFun h1 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02 h12
  have key : ∀ a : ZMod 5, 3 * a = a → a = 0 := by decide
  have key2 : ∀ a : ZMod 5, 2 * a = a → a = 0 := by decide
  exact ⟨key _ h02, key2 _ h12⟩

theorem col_of_normal {g : G35} (hn : ∀ t ∈ T0, g⁻¹ * t * g ∈ T0) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = 0 := by
  have hcol : ∀ t ∈ T0, ∃ l : ZMod 5, ∀ i, ((t : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5))) i 2 = (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) i 2 * l := by
    intro t ht
    have h1 := hn t ht
    obtain ⟨h02, h12, -, -, -, -⟩ := mem_T0_iff.mp h1
    refine ⟨((g⁻¹ * t * g : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2, fun i => ?_⟩
    have he : t * g = g * (g⁻¹ * t * g) := by group
    rw [← Matrix.SpecialLinearGroup.coe_mul, he, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_three, h02, h12]
    ring
  obtain ⟨l, hl⟩ := hcol dT dT_mem
  obtain ⟨m, hm⟩ := hcol sT sT_mem
  have hl0 := hl 0
  have hl1 := hl 1
  have hm0 := hm 0
  have hm1 := hm 1
  rw [dT_coe] at hl0 hl1
  rw [sT_coe] at hm0 hm1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hl0 hl1 hm0 hm1
  have key : ∀ a b l m : ZMod 5, 3 * a = a * l → 2 * b = b * l → b = a * m → a = b * m →
      a = 0 ∧ b = 0 := by decide
  exact key _ _ l m hl0 hl1 hm0 hm1

include hg hperm in
theorem fix_e3_of_31 (h31 : g ^ 31 = 1) (h1 : g ≠ 1) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = 0 := by
  have hp31 : Nat.Prime 31 := by decide
  have : Fact (Nat.Prime 31) := ⟨hp31⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := permH hg hperm with hH
  have hcard : Nat.card H = 31 * 32 := card_permH hg hperm hp31 h31 h1 (by norm_num)
  have hgH : g ∈ H := mem_permH hg hperm
  have hTH : T0 ≤ H := T0_le_permH hg hperm
  have hzH : Subgroup.zpowers g ≤ H := (Subgroup.zpowers_le).mpr hgH
  let P : Subgroup H := (Subgroup.zpowers g).subgroupOf H
  have hPcard : Nat.card P = 31 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzH).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime h31 h1]
  have hfac : (Nat.card H).factorization 31 = 1 := by
    rw [hcard, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self hp31, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let PS : Sylow 31 H := Sylow.ofCard P (by rw [hPcard, hfac, pow_one])
  have hidx : (PS : Subgroup H).index = 32 := by
    have h2 : Nat.card P * (PS : Subgroup H).index = Nat.card H :=
      Subgroup.card_mul_index (PS : Subgroup H)
    rw [hPcard, hcard] at h2
    omega
  have hmod := card_sylow_modEq_one (p := 31) (G := H)
  have hdvd := PS.card_dvd_index
  rw [hidx] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hmod' : Nat.card (Sylow 31 H) % 31 = 1 := hmod
  have hPmem : ∀ x : H, x ∈ P ↔ (x : G35) ∈ Subgroup.zpowers g := fun x => Subgroup.mem_subgroupOf
  rcases (by omega : Nat.card (Sylow 31 H) = 1 ∨ Nat.card (Sylow 31 H) = 32) with hn | hn
  · have : Subsingleton (Sylow 31 H) := (Nat.card_eq_one_iff_unique.mp hn).1
    have hnorm := PS.normal_of_subsingleton
    apply col_of_dT_comm
    apply dT_comm hg hperm
    intro t ht
    have h2 := hnorm.conj_mem ⟨g, hgH⟩ ((hPmem _).mpr (Subgroup.mem_zpowers g)) ⟨t, hTH ht⟩
    exact (hPmem _).mp h2
  ·
    have hN : Subgroup.normalizer (PS : Set H) = (PS : Subgroup H) := by
      have h2 : Nat.card (Sylow 31 H) = (Subgroup.normalizer (PS : Set H)).index :=
        PS.card_eq_index_normalizer
      rw [hn] at h2
      have h3 : Nat.card (Subgroup.normalizer (PS : Set H)) *
          (Subgroup.normalizer (PS : Set H)).index = Nat.card H := Subgroup.card_mul_index _
      rw [← h2, hcard] at h3
      have h4 : Nat.card (Subgroup.normalizer (PS : Set H)) ≤ Nat.card (PS : Subgroup H) := by
        change _ ≤ Nat.card P
        rw [hPcard]
        omega
      exact (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer h4).symm
    have hPC : Subgroup.normalizer (PS : Set H) ≤ Subgroup.centralizer (PS : Set H) := by
      rw [hN]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      change x ∈ P at hx
      change y ∈ P at hy
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp ((hPmem x).mp hx)
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp ((hPmem y).mp hy)
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
    have hK := MonoidHom.ker_transferSylow_isComplement' PS hPC
    set K := (MonoidHom.transferSylow PS hPC).ker
    have hKcard : Nat.card K = 32 := by
      have h2 := hK.card_mul_card
      rw [Sylow.coe_ofCard, hPcard, hcard] at h2
      omega
    let T0H : Subgroup H := T0.subgroupOf H
    have hT0card : Nat.card T0H = 32 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_T0]
    have hfac2 : (Nat.card H).factorization 2 = 5 := by
      rw [hcard, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      simp
    let TS : Sylow 2 H := Sylow.ofCard T0H (by rw [hT0card, hfac2]; norm_num)
    have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 5) (by rw [hKcard]; norm_num)
    have hKT : K ≤ T0H := IsPGroup.le_sylow_of_normal hK2 TS
    have hKeq : K = T0H := Subgroup.eq_of_le_of_card_ge hKT (by rw [hKcard, hT0card])
    have hTnorm : T0H.Normal := hKeq ▸ MonoidHom.normal_ker _
    apply col_of_normal
    intro t ht
    have h2 := hTnorm.conj_mem ⟨t, hTH ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨g, hgH⟩⁻¹
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3

include hg hperm in
theorem fix_e3_of_5 (hpt : ptOKL tC = true) (h5 : g ^ 5 = 1)
    (hrec : ∀ v : Fin 3 → ZMod 5, (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) ^ 3 *ᵥ v -
      (3 : ZMod 5) • ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) ^ 2 *ᵥ v) +
      (3 : ZMod 5) • ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ v) - v = 0) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set M := (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) with hMdef
  have hcoe : ∀ n : ℕ, ((g ^ n : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) = M ^ n := fun n =>
    Matrix.SpecialLinearGroup.coe_pow g n
  have hM5 : M ^ 5 = 1 := by rw [← hcoe, h5, Matrix.SpecialLinearGroup.coe_one]
  set e3 : Fin 3 → ZMod 5 := ![0, 0, 1] with he3
  by_contra hne
  have hA : ∀ k j : ℕ, k * j % 5 = 1 → ¬ ((M ^ k *ᵥ e3) 0 = 0 ∧ (M ^ k *ᵥ e3) 1 = 0) := by
    intro k j hkj hax
    have heig : M ^ k *ᵥ e3 = (M ^ k *ᵥ e3) 2 • e3 := vec_eq_smul_e3 _ hax.1 hax.2
    have h1 := pow_mulVec_of_eigen heig j
    rw [← pow_mul, show k * j = 5 * (k * j / 5) + 1 by omega, pow_add, pow_mul, hM5, one_pow,
      one_mul, pow_one, mulVec_e3] at h1
    apply hne
    have h10 := congrFun h1 0
    have h11 := congrFun h1 1
    simp [he3] at h10 h11
    exact ⟨h10, h11⟩
  have hB : ∀ k : ℕ, ¬ ((M ^ k *ᵥ e3) 0 = 0 ∧ (M ^ k *ᵥ e3) 1 = 0) → (M ^ k *ᵥ e3) 2 = 0 := by
    intro k hk
    by_contra hw2
    set w := M ^ k *ᵥ e3 with hwdef
    set x := w 0 * (w 2)⁻¹
    set y := w 1 * (w 2)⁻¹
    have hw : w = w 2 • ![x, y, 1] := by
      ext i
      fin_cases i <;> simp [x, y] <;> field_simp
    have hxy : x ≠ 0 ∨ y ≠ 0 := by
      by_contra hz
      simp only [ne_eq, not_or, not_not, x, y, mul_eq_zero, inv_eq_zero, hw2, or_false] at hz
      exact hk hz
    obtain ⟨t, htT, hdist⟩ := ptOK_sound hpt x y hxy
    have himg : ∀ i, ∃ r : ℕ, 0 < r ∧ r < 5 ∧ ∃ c : ZMod 5, c ≠ 0 ∧
        (t i : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ w = c • (M ^ r *ᵥ e3) := by
      intro i
      obtain ⟨a, t', ht', he⟩ := perm_pow hg hperm k (t i) (htT i)
      have h1 : (t i : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ w =
          (t' : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 • (M ^ (a % 5) *ᵥ e3) := by
        rw [hwdef, mulVec_mulVec, ← hcoe, ← Matrix.SpecialLinearGroup.coe_mul, he,
          Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, he3, isMon_mulVec_e3 ht',
          mulVec_smul, hcoe]
        conv_lhs => rw [← Nat.div_add_mod a 5, pow_add, pow_mul, hM5, one_pow, one_mul]
      refine ⟨a % 5, ?_, Nat.mod_lt _ (by norm_num), _, isMon_22 ht', h1⟩
      by_contra h0
      rw [show a % 5 = 0 by omega, pow_zero, one_mulVec] at h1
      apply hk
      have hinv : ((t i)⁻¹ : G35) * t i = 1 := inv_mul_cancel _
      have h2 : w = ((t i)⁻¹ : G35).1 *ᵥ ((t i : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hinv,
          Matrix.SpecialLinearGroup.coe_one, one_mulVec]
      rw [h1, mulVec_smul, isMon_mulVec_e3 (T0.inv_mem (htT i)), smul_smul] at h2
      rw [h2]
      simp [he3]
    choose r hr0 hr5 c hc hrc using himg
    let f : Fin 5 → Fin 4 := fun i => ⟨r i - 1, by have := hr5 i; omega⟩
    obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    have hrij : r i = r j := by
      have := congrArg Fin.val hf
      simp only [f] at this
      have := hr0 i
      have := hr0 j
      omega
    apply hdist i j hij
    refine ⟨c j * (c i)⁻¹, mul_ne_zero (hc j) (inv_ne_zero (hc i)), ?_⟩
    have hti := hrc i
    have htj := hrc j
    rw [hw, mulVec_smul] at hti htj
    rw [← hrij] at htj
    have hV : M ^ r i *ᵥ e3 = ((c i)⁻¹ * w 2) • ((t i : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ ![x, y, 1]) := by
      rw [← smul_smul, hti, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [hV, smul_smul] at htj
    have h3 := congrArg (fun v => (w 2)⁻¹ • v) htj
    simp only [smul_smul, inv_mul_cancel₀ hw2, one_smul] at h3
    rw [h3]
    congr 1
    field_simp
  have h1 := hB 1 (hA 1 1 (by norm_num))
  have h2 := hB 2 (hA 2 3 (by norm_num))
  have h3 := hB 3 (hA 3 2 (by norm_num))
  have h4 := congrFun (hrec e3) 2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h4
  rw [pow_one] at h1
  rw [h1, h2, h3] at h4
  simp [he3] at h4

end Perm

@[expose] def sig : G35 →* G35 where
  toFun x := ⟨((x⁻¹ : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ, by
    rw [Matrix.det_transpose]
    exact (x⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change (((x * y)⁻¹ : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ =
      ((x⁻¹ : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ * ((y⁻¹ : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem coe_sig (x : G35) :
    (sig x : Matrix (Fin 3) (Fin 3) (ZMod 5)) = ((x⁻¹ : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ :=
  rfl

theorem sig_sig (x : G35) : sig (sig x) = x := by
  apply Subtype.ext
  rw [coe_sig, ← map_inv, coe_sig, inv_inv, Matrix.transpose_transpose]

theorem sig_mem {t : G35} (ht : t ∈ T0) : sig t ∈ T0 := by
  obtain ⟨h02, h12, h20, h21, h22, hm⟩ := mem_T0_iff.mp (T0.inv_mem ht)
  apply mem_T0_iff.mpr
  rw [coe_sig]
  simp only [IsMon, Matrix.transpose_apply]
  refine ⟨h20, h21, h02, h12, h22, ?_⟩
  rcases hm with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨b, a, c, d⟩
  · exact Or.inr ⟨a, b, d, c⟩

theorem perm_sig {g : G35} (hperm : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g = g ^ a * t') :
    ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * sig g = sig g ^ a * t' := by
  intro t ht
  obtain ⟨a, t', ht', he⟩ := hperm (sig t) (sig_mem ht)
  refine ⟨a, sig t', sig_mem ht', ?_⟩
  have h2 := congrArg sig he
  rwa [map_mul, map_mul, map_zpow, sig_sig] at h2

theorem perm_inv {g : G35} (hg : g ^ 11625 = 1)
    (hperm : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g = g ^ a * t') :
    ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g⁻¹ = g⁻¹ ^ a * t' := by
  intro t ht
  obtain ⟨a, t', ht', he⟩ := perm_pow hg hperm 11624 t ht
  refine ⟨-(a : ℤ), t', ht', ?_⟩
  have hinv : g⁻¹ = g ^ 11624 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hg])).symm
  calc t * g⁻¹ = t * g ^ 11624 := by rw [hinv]
    _ = g ^ a * t' := he
    _ = g⁻¹ ^ (-(a : ℤ)) * t' := by rw [inv_zpow', neg_neg, zpow_natCast]

theorem c7155_sound (hb : bucketsOK bits11625 = true) (hp : ptOKL tC = true)
    (hl : levOKL tC = true) (g : G35) (hg : g ^ 11625 = 1)
    (hperm : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g = g ^ a * t') : g ^ 3 = 1 := by
  by_cases h1 : g = 1
  · rw [h1, one_pow]
  rcases bucket_sound hb g with h3 | ⟨h31, hnoeig⟩ | ⟨h5, hrec⟩
  · exact h3 hg
  · exfalso
    obtain ⟨h02, h12⟩ := fix_e3_of_31 hg hperm h31 h1
    apply hnoeig ![0, 0, 1] (fun h => absurd (congrFun h 2) (by decide))
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2)
    rw [mulVec_e3, h02, h12]
    ext i
    fin_cases i <;> simp
  · exfalso
    obtain ⟨h02, h12⟩ := fix_e3_of_5 hg hperm hp h5 hrec
    set k := sig g⁻¹ with hkdef
    have hk11625 : k ^ 11625 = 1 := by rw [hkdef, ← map_pow, inv_pow, hg, inv_one, map_one]
    have hpk := perm_sig (perm_inv hg hperm)
    have hkinj : ∀ n : ℕ, k ^ n = 1 → g ^ n = 1 := by
      intro n hn
      rw [hkdef, ← map_pow] at hn
      have h2 := congrArg sig hn
      rw [sig_sig, map_one, inv_pow] at h2
      exact inv_eq_one.mp h2
    have hcoek : (k : Matrix (Fin 3) (Fin 3) (ZMod 5)) = (g : Matrix (Fin 3) (Fin 3) (ZMod 5))ᵀ := by
      rw [hkdef, coe_sig, inv_inv]
    rcases bucket_sound hb k with hk3 | ⟨hk31, -⟩ | ⟨hk5, hkrec⟩
    · have h3 := hkinj 3 (hk3 hk11625)
      exact h1 (by rw [show g = (g ^ 3) ^ 2 * (g ^ 5)⁻¹ by group, h3, h5]; simp)
    · have h31 := hkinj 31 hk31
      exact h1 (by rw [show g = g ^ 31 * ((g ^ 5)⁻¹) ^ 6 by group, h31, h5]; simp)
    obtain ⟨k02, k12⟩ := fix_e3_of_5 hk11625 hpk hp hk5 hkrec
    rw [hcoek, Matrix.transpose_apply] at k02 k12
    obtain ⟨t, ht, hk⟩ := levOK_sound hl g h02 h12 k02 k12 h5 h1
    obtain ⟨a, t', ht', he⟩ := hperm t ht
    have h52 : g ^ (5 : ℤ) = 1 := by exact_mod_cast h5
    set r := ((-a) % 5).toNat with hrdef
    have hr : r < 5 := by omega
    have hgr : g ^ r = (g ^ a)⁻¹ := by
      rw [← zpow_natCast, hrdef, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)),
        ← zpow_eq_zpow_emod (-a) h52, zpow_neg]
    apply hk r hr
    rw [hgr, mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ht'

end CFSG.KC.C7155

end
