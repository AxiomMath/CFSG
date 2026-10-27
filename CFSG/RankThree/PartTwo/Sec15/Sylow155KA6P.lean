module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921SixFin
public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9A

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155KA6P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.RankThree.PartTwo.Sec15.Push153B.A6
open CFSG.ClassicalInvolution.Q3.TL4.E3C269G9 (m10_le_autA6)

theorem commutator_mem_psl29 {x y : P10} (hx : x ∈ A6Models.autA6) (hy : y ∈ A6Models.autA6) :
    x * y * x⁻¹ * y⁻¹ ∈ A6Models.psl29 := by
  set N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6 with hN
  haveI : N.Normal := ⟨fun n hn g =>
    Subgroup.mem_subgroupOf.mpr (psl29_normal g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hNcard : Nat.card N = 360 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
  have hidx : N.index = 2 ^ 2 := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, card_autA6] at h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative (↥A6Models.autA6 ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hidx
  have hcomm : ((⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥A6Models.autA6) :
      ↥A6Models.autA6 ⧸ N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    rw [mul_comm' (QuotientGroup.mk ⟨x, hx⟩ : ↥A6Models.autA6 ⧸ N)
      (QuotientGroup.mk ⟨y, hy⟩ : ↥A6Models.autA6 ⧸ N)]
    group
  have := (QuotientGroup.eq_one_iff _).mp hcomm
  exact Subgroup.mem_subgroupOf.mp this

theorem eq_one_of_mem_m10_of_coprime {x b : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hb : b ∈ A6Models.m10) (hbx : b * x = x * b) (hb3 : ¬ 3 ∣ orderOf b) :
    b = 1 := by
  have hbA : b ∈ A6Models.autA6 := m10_le_autA6 hb
  have hxA : x ∈ A6Models.autA6 := psl29_le_autA6 hx
  by_contra hb1
  have hord1 : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
  haveI : Fact p.Prime := ⟨hp⟩
  have hordpos : orderOf b ≠ 0 := (orderOf_pos b).ne'
  set c : P10 := b ^ (orderOf b / p)
  have hc : orderOf c = p := orderOf_pow_orderOf_div hordpos hpd
  have hcp : c ^ p = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hc, h, orderOf_one])
  have hcA : c ∈ A6Models.autA6 := Subgroup.pow_mem _ hbA _
  have hcx : c * x = x * c := (Commute.pow_left (show Commute b x from hbx) _).eq
  by_cases hp2 : p = 2
  · subst hp2
    have hcm : c ∈ A6Models.m10 := Subgroup.pow_mem _ hb _
    have hc2 : c * c = 1 := by rw [← pow_two]; exact hcp
    exact hc1 (eq_one_of_mem_m10_involution hx hx3 hx1 hcA hcm hc2 hcx)
  · obtain ⟨hcpsl, hp35⟩ := mem_psl29_of_prime_pow hp hp2 hcA hcp hc1
    rcases hp35 with rfl | rfl
    · exact hb3 hpd
    · have h10 : x ^ 10 = 1 := (five_facts hcpsl hcp hc1).1 x hxA (hcx.symm)
      have h10x : x ^ 10 = x := by
        have h : x ^ (1 + 3 * 3) = x := by
          rw [pow_add, pow_mul, hx3, one_pow, mul_one, pow_one]
        exact h
      exact hx1 (h10x.symm.trans h10)

theorem tAdd_pow_three : A6Models.tAdd ^ 3 = 1 :=
  (cubeC_eq_cid_iff _).mp (by rw [code_tAdd]; decide +kernel)

theorem tAdd_inv : A6Models.tAdd⁻¹ = A6Models.tAdd * A6Models.tAdd := inv_eq_sq tAdd_pow_three

theorem inv_tAdd_check : Core.pslLit.any (fun h =>
    Core.cmul h tAddC == Core.cmul (Core.cmul tAddC tAddC) h) = true := by
  decide +kernel

theorem cent_cube_check : Core.pslLit.all (fun v =>
    !(commC v tAddC) || cubeC v == Core.cid) = true := by
  decide +kernel

theorem cent5_check : Core.pslLit.all (fun f => !(Core.cpow f 5 == Core.cid) || f == Core.cid ||
    [0, 1, 2, 3, 4].all fun j => !(Core.cmul tAddC f == Core.cmul (Core.cpow f j) tAddC)) =
      true := by
  decide +kernel

@[expose] def klL : List (List ℕ) :=
  Core.pslLit.filter fun r => Core.cmul r r == Core.cid && !(r == Core.cid) &&
    commC r (conjC tAddC r)

theorem klL_length : klL.length = 9 := by decide +kernel

theorem swap_check : klL.all (fun r => klL.all fun v => t9c.any fun n =>
    [r, conjC tAddC r, conjC (Core.cmul tAddC tAddC) r].contains (conjC n v)) = true := by
  decide +kernel

theorem e9_check : klL.all (fun v => t9c.all fun b => b == Core.cid || b == tAddC ||
    b == Core.cmul tAddC tAddC ||
      !([v, conjC tAddC v, conjC (Core.cmul tAddC tAddC) v].contains (conjC b v))) = true := by
  decide +kernel

theorem conj_eq_one_iff (g y : P10) : g * y * g⁻¹ = 1 ↔ y = 1 := by
  constructor
  · intro h
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · rintro rfl
    group

theorem conjC_eq_code {n : P10} (hn3 : n ^ 3 = 1) (u : P10) :
    conjC (code n) (code u) = code (n * u * n⁻¹) := by
  rw [code_conjC, inv_eq_sq hn3]

theorem mul_self_mul_self_eq {n : P10} (hn3 : n ^ 3 = 1) : n * n * (n * n) = n := by
  calc n * n * (n * n) = n * n * n * n := by rw [mul_assoc (n * n) n n]
    _ = n ^ 3 * n := by rw [pow_three']
    _ = n := by rw [hn3, one_mul]

theorem inv_mul_inv_eq_of_pow_three {n : P10} (hn3 : n ^ 3 = 1) : n⁻¹ * n⁻¹ = n := by
  rw [inv_eq_sq hn3, mul_self_mul_self_eq hn3]

theorem conjC_sq_eq_code {n : P10} (hn3 : n ^ 3 = 1) (u : P10) :
    conjC (Core.cmul (code n) (code n)) (code u) = code (n⁻¹ * u * n) := by
  rw [← code_mul, code_conjC, mul_self_mul_self_eq hn3, inv_eq_sq hn3]

theorem mem_klL_iff (r : P10) : code r ∈ klL ↔ r ∈ A6Models.psl29 ∧ r * r = 1 ∧ r ≠ 1 ∧
    r * (A6Models.tAdd * r * A6Models.tAdd⁻¹) = (A6Models.tAdd * r * A6Models.tAdd⁻¹) * r := by
  unfold klL
  rw [List.mem_filter, ← mem_psl29_iff, tAdd_inv]
  have hc : commC (code r) (conjC tAddC (code r)) = true ↔
      r * (A6Models.tAdd * r * (A6Models.tAdd * A6Models.tAdd)) =
        (A6Models.tAdd * r * (A6Models.tAdd * A6Models.tAdd)) * r := by
    rw [← code_tAdd, code_conjC, commC_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, hc]
  constructor
  · rintro ⟨h1, ⟨h21, h22⟩, h23⟩
    refine ⟨h1, ?_, ?_, h23⟩
    · apply code_injective
      rw [code_mul, code_one]
      exact h21
    · intro h
      apply h22
      rw [h, code_one]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ⟨?_, ?_⟩, h4⟩
    · rw [← code_mul, h2, code_one]
    · rw [← code_one]
      exact fun h => h3 (code_injective h)

theorem mem_t9c_iff (b : P10) : code b ∈ t9c ↔
    b ∈ A6Models.psl29 ∧ b ^ 3 = 1 ∧ b * A6Models.tAdd = A6Models.tAdd * b := by
  constructor
  · intro hb
    have h := List.all_eq_true.mp t9_check _ hb
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hpsl, hcube⟩, hcomm⟩, -⟩ := h
    refine ⟨(mem_psl29_iff b).mpr (contains_iff.mp hpsl), (cubeC_eq_cid_iff b).mp hcube, ?_⟩
    rw [← commC_iff, code_tAdd]
    exact hcomm
  · rintro ⟨hb, hb3, hbc⟩
    have h := List.all_eq_true.mp ordT9_check (code b) (code_mem_autL (psl29_le_autA6 hb))
    have hc : (commC (code b) tAddC && cubeC (code b) == Core.cid) = true := by
      rw [Bool.and_eq_true, ← code_tAdd, commC_iff, beq_iff_eq, cubeC_eq_cid_iff]
      exact ⟨hbc, hb3⟩
    rw [hc] at h
    simpa using h

theorem exists_of_mem_t9c {nc : List ℕ} (h : nc ∈ t9c) :
    ∃ n ∈ A6Models.psl29, n ^ 3 = 1 ∧ n * A6Models.tAdd = A6Models.tAdd * n ∧ code n = nc := by
  have h1 := List.all_eq_true.mp t9_check _ h
  simp only [Bool.and_eq_true] at h1
  obtain ⟨n, hn, rfl⟩ := exists_psl29_of_code (contains_iff.mp h1.1.1.1)
  obtain ⟨-, h3, h4⟩ := (mem_t9c_iff n).mp h
  exact ⟨n, hn, h3, h4, rfl⟩

theorem cube_eq_one_of_comm {a x : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hx : x ∈ A6Models.psl29) (hxa : x * a = a * x) : x ^ 3 = 1 := by
  obtain ⟨g, hg, hga⟩ := exists_conj_tAdd ha ha3 ha1
  have hx' : g * x * g⁻¹ ∈ A6Models.psl29 := psl29_normal g hg x hx
  have hc : commC (code (g * x * g⁻¹)) tAddC = true := by
    rw [← code_tAdd, commC_iff, ← hga]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have h := List.all_eq_true.mp cent_cube_check (code (g * x * g⁻¹)) ((mem_psl29_iff _).mp hx')
  rw [hc, Bool.not_true, Bool.false_or, beq_iff_eq, cubeC_eq_cid_iff, conj_pow] at h
  exact (conj_eq_one_iff g _).mp h

theorem exists_conj_inv {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) :
    ∃ g ∈ A6Models.psl29, g * x * g⁻¹ = x⁻¹ := by
  by_cases hx1 : x = 1
  · exact ⟨1, Subgroup.one_mem _, by simp [hx1]⟩
  obtain ⟨g₀, hg₀, hg₀x⟩ := exists_conj_tAdd hx hx3 hx1
  obtain ⟨cl, hhc, hhe⟩ := List.any_eq_true.mp inv_tAdd_check
  obtain ⟨h, hh, rfl⟩ := exists_psl29_of_code hhc
  simp only [beq_iff_eq] at hhe
  have hh1 : h * A6Models.tAdd = (A6Models.tAdd * A6Models.tAdd) * h := by
    apply code_injective
    rw [code_mul, code_mul, code_mul, code_tAdd]
    exact hhe
  have h2 : h * A6Models.tAdd * h⁻¹ = A6Models.tAdd⁻¹ := by
    rw [tAdd_inv, mul_inv_eq_iff_eq_mul, hh1]
  refine ⟨g₀⁻¹ * h * g₀, ?_, ?_⟩
  · have := psl29_normal _ (A6Models.autA6.inv_mem hg₀) _ hh
    simpa [mul_assoc] using this
  · have hx' : x = g₀⁻¹ * A6Models.tAdd * g₀ := by rw [← hg₀x]; group
    rw [hx']
    calc g₀⁻¹ * h * g₀ * (g₀⁻¹ * A6Models.tAdd * g₀) * (g₀⁻¹ * h * g₀)⁻¹
        = g₀⁻¹ * (h * A6Models.tAdd * h⁻¹) * g₀ := by group
      _ = g₀⁻¹ * A6Models.tAdd⁻¹ * g₀ := by rw [h2]
      _ = (g₀⁻¹ * A6Models.tAdd * g₀)⁻¹ := by group

theorem conj_not_mem_zpowers_of_five {a f : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hf : f ∈ A6Models.psl29) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1) :
    a * f * a⁻¹ ∉ Subgroup.zpowers f := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨g, hg, hga⟩ := exists_conj_tAdd ha ha3 ha1
  let c : P10 ≃* P10 := MulAut.conj g
  have hc : ∀ y, c y = g * y * g⁻¹ := fun y => MulAut.conj_apply g y
  have hca : c a = A6Models.tAdd := (hc a).trans hga
  have hf'psl : c f ∈ A6Models.psl29 := by rw [hc]; exact psl29_normal g hg f hf
  have hf'5 : c f ^ 5 = 1 := by rw [← map_pow, hf5, map_one]
  have hf'1 : c f ≠ 1 := fun h => hf1 (c.injective (h.trans (map_one c).symm))
  have hk' : c f ^ k = A6Models.tAdd * c f * A6Models.tAdd⁻¹ := by
    have := congrArg c hk
    simpa only [map_zpow, map_mul, map_inv, hca] using this
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (c f) = 5 := orderOf_eq_prime hf'5 hf'1
  have hj5 : (k % 5).toNat < 5 := by omega
  have hfj : c f ^ k = c f ^ (k % 5).toNat := by
    have h1 := zpow_mod_orderOf (c f) k
    rw [hord] at h1
    have h2 : (k % ((5 : ℕ) : ℤ)) = (((k % 5).toNat : ℕ) : ℤ) := by omega
    rw [h2, zpow_natCast] at h1
    exact h1.symm
  have hcomm : c f ^ (k % 5).toNat * A6Models.tAdd = A6Models.tAdd * c f := by
    rw [← hfj]
    exact (mul_inv_eq_iff_eq_mul.mp hk'.symm).symm
  have h := List.all_eq_true.mp cent5_check (code (c f)) ((mem_psl29_iff _).mp hf'psl)
  have e1 : (Core.cpow (code (c f)) 5 == Core.cid) = true := by
    rw [← code_pow, hf'5, code_one]
    simp
  have e2 : (code (c f) == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]
    exact hf'1
  rw [e1, e2] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_false, List.all_eq_true] at h
  have h3 := h (k % 5).toNat (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega)
  have h4 : Core.cmul tAddC (code (c f)) =
      Core.cmul (Core.cpow (code (c f)) (k % 5).toNat) tAddC := by
    rw [← code_tAdd, ← code_pow, ← code_mul, ← code_mul, hcomm]
  rw [h4] at h3
  simp at h3

theorem exists_conj_setup {a : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ c : P10 ≃* P10, c a = A6Models.tAdd ∧ (∀ y ∈ A6Models.psl29, c y ∈ A6Models.psl29) ∧
      (∀ y, c y ∈ A6Models.psl29 → y ∈ A6Models.psl29) := by
  obtain ⟨g, hg, hga⟩ := exists_conj_tAdd ha ha3 ha1
  have hc : ∀ y, (MulAut.conj g : P10 ≃* P10) y = g * y * g⁻¹ := fun y => MulAut.conj_apply g y
  refine ⟨MulAut.conj g, (hc a).trans hga, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hc]
    exact psl29_normal g hg y hy
  · have := psl29_normal g⁻¹ (A6Models.autA6.inv_mem hg) _ hy
    rw [hc] at this
    simpa [mul_assoc] using this

theorem code_mem_klL {a y : P10} {c : P10 ≃* P10} (hca : c a = A6Models.tAdd)
    (hcpsl : ∀ y ∈ A6Models.psl29, c y ∈ A6Models.psl29) (hy : y ∈ A6Models.psl29)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyc : y * (a * y * a⁻¹) = (a * y * a⁻¹) * y) :
    code (c y) ∈ klL := by
  rw [mem_klL_iff]
  refine ⟨hcpsl y hy, ?_, fun h => hy1 (c.injective (h.trans (map_one c).symm)), ?_⟩
  · rw [← map_mul, hy2, map_one]
  · have := congrArg c hyc
    simpa only [map_mul, map_inv, hca] using this

theorem exists_conj_klein {a r v : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hr : r ∈ A6Models.psl29) (hr2 : r * r = 1) (hr1 : r ≠ 1)
    (hrc : r * (a * r * a⁻¹) = (a * r * a⁻¹) * r) (hv : v ∈ A6Models.psl29) (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hvc : v * (a * v * a⁻¹) = (a * v * a⁻¹) * v) :
    ∃ n ∈ A6Models.psl29, n * a = a * n ∧
      (n * v * n⁻¹ = r ∨ n * v * n⁻¹ = a * r * a⁻¹ ∨ n * v * n⁻¹ = a⁻¹ * r * a) := by
  obtain ⟨c, hca, hcpsl, hcpsl'⟩ := exists_conj_setup ha ha3 ha1
  have h := List.all_eq_true.mp (List.all_eq_true.mp swap_check _
    (code_mem_klL hca hcpsl hr hr2 hr1 hrc)) _ (code_mem_klL hca hcpsl hv hv2 hv1 hvc)
  obtain ⟨nc, hnc, hmem⟩ := List.any_eq_true.mp h
  obtain ⟨n', hn'psl, hn'3, hn'a, rfl⟩ := exists_of_mem_t9c hnc
  obtain ⟨n, hn⟩ : ∃ n, c n = n' := ⟨c.symm n', c.apply_symm_apply n'⟩
  have key : ∀ w : P10, c w = n' * c v * n'⁻¹ → n * v * n⁻¹ = w := by
    intro w hw
    apply c.injective
    rw [map_mul, map_mul, map_inv, hn, hw]
  refine ⟨n, hcpsl' n (hn ▸ hn'psl), ?_, ?_⟩
  · apply c.injective
    rw [map_mul, map_mul, hn, hca, hn'a]
  · rw [contains_iff, ← code_tAdd] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rw [conjC_eq_code hn'3, conjC_eq_code tAdd_pow_three, conjC_sq_eq_code tAdd_pow_three] at hmem
    rcases hmem with h1 | h1 | h1
    · exact Or.inl (key r (code_injective h1).symm)
    · refine Or.inr (Or.inl (key _ ?_))
      rw [code_injective h1]
      simp only [map_mul, map_inv, hca]
    · refine Or.inr (Or.inr (key _ ?_))
      rw [code_injective h1]
      simp only [map_mul, map_inv, hca]

theorem conj_ne_of_not_mem_zpowers {a b v : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hb : b ∈ A6Models.psl29) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hbA : b ∉ Subgroup.zpowers a) (hv : v ∈ A6Models.psl29) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvc : v * (a * v * a⁻¹) = (a * v * a⁻¹) * v) :
    b * v * b⁻¹ ≠ v ∧ b * v * b⁻¹ ≠ a * v * a⁻¹ ∧ b * v * b⁻¹ ≠ a⁻¹ * v * a := by
  obtain ⟨c, hca, hcpsl, hcpsl'⟩ := exists_conj_setup ha ha3 ha1
  have hb'3 : c b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hb't9 : code (c b) ∈ t9c := by
    refine (mem_t9c_iff _).mpr ⟨hcpsl b hb, hb'3, ?_⟩
    rw [← hca, ← map_mul, ← map_mul, hab]
  have hb'z : c b ∉ Subgroup.zpowers A6Models.tAdd := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hbA
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, c.injective ?_⟩
    rw [map_zpow, hca, hk]
  have h := List.all_eq_true.mp (List.all_eq_true.mp e9_check _
    (code_mem_klL hca hcpsl hv hv2 hv1 hvc)) _ hb't9
  have e1 : (code (c b) == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]
    exact fun h' => hb'z (h' ▸ Subgroup.one_mem _)
  have e2 : (code (c b) == tAddC) = false := by
    rw [beq_eq_false_iff_ne, Ne, ← code_tAdd]
    exact fun h' => hb'z (code_injective h' ▸ Subgroup.mem_zpowers _)
  have e3 : (code (c b) == Core.cmul tAddC tAddC) = false := by
    rw [beq_eq_false_iff_ne, Ne, ← code_tAdd, ← code_mul]
    intro h'
    apply hb'z
    rw [code_injective h', ← pow_two]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  rw [e1, e2, e3] at h
  simp only [Bool.false_or, Bool.not_eq_true'] at h
  rw [← code_tAdd] at h
  have hnot : ∀ w : P10, (w = c v ∨ w = A6Models.tAdd * c v * A6Models.tAdd⁻¹ ∨
      w = A6Models.tAdd⁻¹ * c v * A6Models.tAdd) → c b * c v * (c b)⁻¹ ≠ w := by
    intro w hw heq
    have hcont : [code (c v), conjC (code A6Models.tAdd) (code (c v)),
        conjC (Core.cmul (code A6Models.tAdd) (code A6Models.tAdd)) (code (c v))].contains
          (conjC (code (c b)) (code (c v))) = true := by
      rw [contains_iff, conjC_eq_code hb'3, conjC_eq_code tAdd_pow_three,
        conjC_sq_eq_code tAdd_pow_three, heq]
      rcases hw with rfl | rfl | rfl <;> simp
    rw [hcont] at h
    exact Bool.noConfusion h
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · apply hnot (c v) (Or.inl rfl)
    have := congrArg c h1
    simpa only [map_mul, map_inv] using this
  · apply hnot (A6Models.tAdd * c v * A6Models.tAdd⁻¹) (Or.inr (Or.inl rfl))
    have := congrArg c h1
    simpa only [map_mul, map_inv, hca] using this
  · apply hnot (A6Models.tAdd⁻¹ * c v * A6Models.tAdd) (Or.inr (Or.inr rfl))
    have := congrArg c h1
    simpa only [map_mul, map_inv, hca] using this

theorem exists_normal_sylow_five {V : Subgroup P10} (hV : Nat.card V ∣ 40) (h5 : 5 ∣ Nat.card V) :
    ∃ F : Subgroup P10, F ≤ V ∧ Nat.card F = 5 ∧ ∀ x ∈ V, x ^ 5 = 1 → x ∈ F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpos : 0 < Nat.card V := Nat.card_pos
  have hcases : Nat.card V = 5 ∨ Nat.card V = 10 ∨ Nat.card V = 20 ∨ Nat.card V = 40 := by
    have hle : Nat.card V ≤ 40 := Nat.le_of_dvd (by norm_num) hV
    generalize Nat.card V = n at *
    interval_cases n <;> omega
  obtain ⟨P⟩ : Nonempty (Sylow 5 ↥V) := inferInstance
  have hP5 : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity P]
    rcases hcases with h | h | h | h <;> rw [h] <;> norm_num [Nat.factorization]
  have hidx : (P : Subgroup ↥V).index * 5 = Nat.card V := by
    have := Subgroup.index_mul_card (P : Subgroup ↥V)
    rwa [hP5] at this
  have hmod := card_sylow_modEq_one 5 ↥V
  have hdvd := Sylow.card_dvd_index P
  have hn : Nat.card (Sylow 5 ↥V) = 1 := by
    have hle : Nat.card (Sylow 5 ↥V) ≤ (P : Subgroup ↥V).index :=
      Nat.le_of_dvd (by omega) hdvd
    unfold Nat.ModEq at hmod
    generalize Nat.card (Sylow 5 ↥V) = n at *
    generalize (P : Subgroup ↥V).index = m at *
    have hm8 : m ≤ 8 := by omega
    have hn8 : n ≤ 8 := by omega
    interval_cases n <;> omega
  have hsub : Subsingleton (Sylow 5 ↥V) := (Nat.card_eq_one_iff_unique.mp hn).1
  refine ⟨(P : Subgroup ↥V).map V.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective V.subtype_injective, hP5]
  · intro x hx hx5
    have hxo : orderOf (⟨x, hx⟩ : ↥V) ∣ 5 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx5))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
      (show orderOf (⟨x, hx⟩ : ↥V) ∣ 5 ^ 1 by simpa using hxo)
    have hxp : IsPGroup 5 (Subgroup.zpowers (⟨x, hx⟩ : ↥V)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    have hxP : (⟨x, hx⟩ : ↥V) ∈ (P : Subgroup ↥V) := hQP ▸ hQ (Subgroup.mem_zpowers _)
    exact ⟨⟨x, hx⟩, hxP, rfl⟩

theorem conj_conj_eq {a : P10} (ha3 : a ^ 3 = 1) (v : P10) :
    a * (a * v * a⁻¹) * a⁻¹ = a⁻¹ * v * a := by
  calc a * (a * v * a⁻¹) * a⁻¹ = (a * a) * v * (a⁻¹ * a⁻¹) := by group
    _ = a⁻¹ * v * a := by rw [← inv_eq_sq ha3, inv_mul_inv_eq_of_pow_three ha3]

theorem conj_inv_mem {a : P10} (ha3 : a ^ 3 = 1) {V : Subgroup P10}
    (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) {v : P10} (hv : v ∈ V) : a⁻¹ * v * a ∈ V := by
  rw [← conj_conj_eq ha3]
  exact haV _ (haV v hv)

theorem eq_bot_or_klein {a : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    {V : Subgroup P10} (hV : V ≤ A6Models.psl29) (hV3 : ¬ 3 ∣ Nat.card V)
    (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    V = ⊥ ∨ ∃ v ∈ V, v * v = 1 ∧ v ≠ 1 ∧ v * (a * v * a⁻¹) = (a * v * a⁻¹) * v ∧
      ∀ y ∈ V, y = 1 ∨ y = v ∨ y = a * v * a⁻¹ ∨ y = a⁻¹ * v * a := by
  have hAAA : a * a * a = 1 := by rw [← pow_three']; exact ha3
  have hconj3 : ∀ v : P10, a * (a * v * a⁻¹) * a⁻¹ = a⁻¹ * v * a := conj_conj_eq ha3
  have haV' : ∀ v ∈ V, a⁻¹ * v * a ∈ V := fun v hv => conj_inv_mem ha3 haV hv
  have hC : ∀ v ∈ V, v * a = a * v → v = 1 := by
    intro v hv hva
    have hv3 : v ^ 3 = 1 := cube_eq_one_of_comm ha ha3 ha1 (hV hv) hva
    have h1 : orderOf v ∣ 3 := orderOf_dvd_of_pow_eq_one hv3
    have h2 : orderOf v ∣ Nat.card V := by
      have := orderOf_dvd_natCard (⟨v, hv⟩ : ↥V)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime 3 (Nat.card V) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have h40 : Nat.card V ∣ 40 := by
    have h360 : Nat.card V ∣ 360 := by
      rw [← card_psl29]
      exact Subgroup.card_dvd_of_le hV
    have hcop9 : Nat.Coprime (Nat.card V) (3 ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3).symm
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop9 (by simpa using h360)
  have h5 : ¬ 5 ∣ Nat.card V := by
    intro h5
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨F, hFV, hF5, hFx⟩ := exists_normal_sylow_five h40 h5
    obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ F, f ≠ 1 := by
      by_contra hcon
      push Not at hcon
      rw [(Subgroup.eq_bot_iff_forall F).mpr hcon, Subgroup.card_bot] at hF5
      omega
    have hf5 : f ^ 5 = 1 := by
      have := pow_card_eq_one' (G := ↥F) (x := ⟨f, hfF⟩)
      rw [hF5] at this
      exact congrArg Subtype.val this
    have huF : a * f * a⁻¹ ∈ F :=
      hFx _ (haV f (hFV hfF)) (by rw [conj_pow, hf5]; group)
    have hFz : F = Subgroup.zpowers f := by
      have hfo : orderOf f = 5 := orderOf_eq_prime hf5 hf1
      symm
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hfF)
      rw [Nat.card_zpowers, hfo, hF5]
    exact conj_not_mem_zpowers_of_five ha ha3 ha1 (hV (hFV hfF)) hf5 hf1 (hFz ▸ huF)
  have hmod : Nat.card V ≡ 1 [MOD 3] := by
    classical
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Fintype ↥V := Fintype.ofFinite _
    let f : Function.End ↥V := fun v => ⟨a * v * a⁻¹, haV v v.2⟩
    have hf3 : ∀ v : ↥V, f (f (f v)) = v := by
      intro v
      apply Subtype.ext
      show a * (a * (a * v * a⁻¹) * a⁻¹) * a⁻¹ = v
      calc a * (a * (a * v * a⁻¹) * a⁻¹) * a⁻¹
          = (a * a * a) * (v : P10) * (a * a * a)⁻¹ := by group
        _ = v := by rw [hAAA]; group
    have hf : f ^ 3 ^ 1 = 1 := by
      rw [pow_one]
      funext v
      exact hf3 v
    have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, ?_⟩, fun y => ?_⟩
      · show f 1 = 1
        apply Subtype.ext
        show a * 1 * a⁻¹ = 1
        group
      · apply Subtype.ext
        apply Subtype.ext
        have hy : f y.1 = y.1 := y.2
        have hy' : a * (y.1 : P10) * a⁻¹ = y.1 := congrArg Subtype.val hy
        have := hC y.1 y.1.2 (mul_inv_eq_iff_eq_mul.mp hy').symm
        exact this
    have := Equiv.Perm.card_fixedPoints_modEq hf
    rw [hfix, ← Nat.card_eq_fintype_card] at this
    exact this
  have hcard : Nat.card V = 1 ∨ Nat.card V = 4 := by
    have hle : Nat.card V ≤ 40 := Nat.le_of_dvd (by norm_num) h40
    have hpos : 0 < Nat.card V := Nat.card_pos
    unfold Nat.ModEq at hmod
    generalize Nat.card V = n at *
    interval_cases n <;> omega
  rcases hcard with h1 | h4
  · exact Or.inl (Subgroup.eq_bot_of_card_eq V h1)
  right
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall V).mpr hcon, Subgroup.card_bot] at h4
    omega
  have huV : a * v * a⁻¹ ∈ V := haV v hv
  have hwV : a⁻¹ * v * a ∈ V := haV' v hv
  have hvu : a * v * a⁻¹ ≠ v := by
    intro h
    apply hv1
    apply hC v hv
    calc v * a = (a * v * a⁻¹) * a := by rw [h]
      _ = a * v := by group
  have hvw : a⁻¹ * v * a ≠ v := by
    intro h
    apply hv1
    apply hC v hv
    calc v * a = a * (a⁻¹ * v * a) := by group
      _ = a * v := by rw [h]
  have huw : a * v * a⁻¹ ≠ a⁻¹ * v * a := by
    intro h
    apply hvw
    calc a⁻¹ * v * a = a * (a * v * a⁻¹) * a⁻¹ := (hconj3 v).symm
      _ = a * (a⁻¹ * v * a) * a⁻¹ := by rw [h]
      _ = v := by group
  have hu1 : a * v * a⁻¹ ≠ 1 := fun h => hv1 ((conj_eq_one_iff a v).mp h)
  have hw1 : a⁻¹ * v * a ≠ 1 := fun h => hv1 ((conj_eq_one_iff a⁻¹ v).mp (by simpa using h))
  have hall : ∀ y ∈ V, y = 1 ∨ y = v ∨ y = a * v * a⁻¹ ∨ y = a⁻¹ * v * a := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨hy1, hyv, hyu, hyw⟩ := hcon
    haveI : Fintype ↥V := Fintype.ofFinite _
    have hnd : [(1 : ↥V), ⟨v, hv⟩, ⟨a * v * a⁻¹, huV⟩, ⟨a⁻¹ * v * a, hwV⟩, ⟨y, hy⟩].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, Subtype.ext_iff, Subgroup.coe_one]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · exact hv1.symm
      · exact hu1.symm
      · exact hw1.symm
      · exact hy1.symm
      · exact hvu.symm
      · exact hvw.symm
      · exact hyv.symm
      · exact huw
      · exact hyu.symm
      · exact hyw.symm
    have := hnd.length_le_card
    rw [← Nat.card_eq_fintype_card, h4] at this
    simp at this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 2 (by rw [h4]; norm_num)
  have ht2 : (t : P10) * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht] at h1
    have h2 : ((t ^ 2 : ↥V) : P10) = 1 := by rw [h1]; rfl
    simpa [pow_two] using h2
  have ht1 : (t : P10) ≠ 1 := by
    intro h
    have h' : t = 1 := Subtype.ext h
    rw [h', orderOf_one] at ht
    omega
  have hv2 : v * v = 1 := by
    rcases hall t t.2 with h | h | h | h
    · exact absurd h ht1
    · rw [h] at ht2
      exact ht2
    · rw [h] at ht2
      have h' : a * (v * v) * a⁻¹ = 1 := by rw [← ht2]; group
      exact (conj_eq_one_iff a _).mp h'
    · rw [h] at ht2
      have h' : a⁻¹ * (v * v) * a⁻¹⁻¹ = 1 := by
        rw [inv_inv, ← ht2]
        group
      exact (conj_eq_one_iff a⁻¹ _).mp h'
  have hu2 : (a * v * a⁻¹) * (a * v * a⁻¹) = 1 := by
    calc (a * v * a⁻¹) * (a * v * a⁻¹) = a * (v * v) * a⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hw2 : (a⁻¹ * v * a) * (a⁻¹ * v * a) = 1 := by
    calc (a⁻¹ * v * a) * (a⁻¹ * v * a) = a⁻¹ * (v * v) * a := by group
      _ = 1 := by rw [hv2]; group
  have hsq : ∀ y ∈ V, y * y = 1 := by
    intro y hy
    rcases hall y hy with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      exact hv2
    · rw [h]
      exact hu2
    · rw [h]
      exact hw2
  have hcomm : v * (a * v * a⁻¹) = (a * v * a⁻¹) * v := by
    have hvu' : (v * (a * v * a⁻¹)) * (v * (a * v * a⁻¹)) = 1 := hsq _ (V.mul_mem hv huV)
    have h1 : (a * v * a⁻¹)⁻¹ = a * v * a⁻¹ := inv_eq_of_mul_eq_one_right hu2
    have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have h3 : (v * (a * v * a⁻¹))⁻¹ = v * (a * v * a⁻¹) := inv_eq_of_mul_eq_one_right hvu'
    rw [mul_inv_rev, h1, h2] at h3
    exact h3.symm
  exact ⟨v, hv, hv2, hv1, hcomm, hall⟩

theorem exists_swap {a : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    {R V : Subgroup P10} (hR : R ≤ A6Models.psl29) (hV : V ≤ A6Models.psl29)
    (hR3 : ¬ 3 ∣ Nat.card R) (hV3 : ¬ 3 ∣ Nat.card V)
    (haR : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    ∃ n ∈ A6Models.psl29, n * a = a * n ∧
      ∀ v ∈ V, n * v * n⁻¹ ∈ Subgroup.normalizer (R : Set P10) := by
  rcases eq_bot_or_klein ha ha3 ha1 hR hR3 haR with hRb | ⟨r, hr, hr2, hr1, hrc, -⟩
  · refine ⟨1, Subgroup.one_mem _, by simp, fun v _ => ?_⟩
    rw [hRb, Subgroup.normalizer_eq_top]
    trivial
  rcases eq_bot_or_klein ha ha3 ha1 hV hV3 haV with hVb | ⟨v, hv, hv2, hv1, hvc, hVall⟩
  · refine ⟨1, Subgroup.one_mem _, by simp, fun y hy => ?_⟩
    rw [hVb, Subgroup.mem_bot] at hy
    rw [hy]
    simpa using Subgroup.one_mem _
  obtain ⟨n, hn, hna, hnv⟩ := exists_conj_klein ha ha3 ha1 (hR hr) hr2 hr1 hrc (hV hv) hv2 hv1 hvc
  have hnvR : n * v * n⁻¹ ∈ R := by
    rcases hnv with h | h | h
    · rw [h]
      exact hr
    · rw [h]
      exact haR r hr
    · rw [h]
      exact conj_inv_mem ha3 haR hr
  have hnc : n * a * n⁻¹ = a := by
    rw [hna]
    group
  have hnc' : n * a⁻¹ * n⁻¹ = a⁻¹ := by
    calc n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [hnc]
  refine ⟨n, hn, hna, fun y hy => Subgroup.le_normalizer ?_⟩
  rcases hVall y hy with h | h | h | h
  · rw [h]
    simpa using R.one_mem
  · rw [h]
    exact hnvR
  · rw [h]
    have e : n * (a * v * a⁻¹) * n⁻¹ = a * (n * v * n⁻¹) * a⁻¹ := by
      calc n * (a * v * a⁻¹) * n⁻¹ = (n * a * n⁻¹) * (n * v * n⁻¹) * (n * a⁻¹ * n⁻¹) := by group
        _ = a * (n * v * n⁻¹) * a⁻¹ := by rw [hnc, hnc']
    rw [e]
    exact haR _ hnvR
  · rw [h]
    have e : n * (a⁻¹ * v * a) * n⁻¹ = a⁻¹ * (n * v * n⁻¹) * a := by
      calc n * (a⁻¹ * v * a) * n⁻¹ = (n * a⁻¹ * n⁻¹) * (n * v * n⁻¹) * (n * a * n⁻¹) := by group
        _ = a⁻¹ * (n * v * n⁻¹) * a := by rw [hnc, hnc']
    rw [e]
    exact conj_inv_mem ha3 haR hnvR

theorem eq_bot_of_invariant_e9 {a b : P10} (ha : a ∈ A6Models.psl29) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hb : b ∈ A6Models.psl29) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hbA : b ∉ Subgroup.zpowers a) {V : Subgroup P10} (hV : V ≤ A6Models.psl29)
    (hV3 : ¬ 3 ∣ Nat.card V) (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (hbV : ∀ v ∈ V, b * v * b⁻¹ ∈ V) : V = ⊥ := by
  rcases eq_bot_or_klein ha ha3 ha1 hV hV3 haV with hVb | ⟨v, hv, hv2, hv1, hvc, hVall⟩
  · exact hVb
  exfalso
  obtain ⟨h1, h2, h3⟩ :=
    conj_ne_of_not_mem_zpowers ha ha3 ha1 hb hb3 hab hbA (hV hv) hv2 hv1 hvc
  rcases hVall _ (hbV v hv) with h | h | h | h
  · exact hv1 ((conj_eq_one_iff b v).mp h)
  · exact h1 h
  · exact h2 h
  · exact h3 h

end CFSG.RankThree.PartTwo.Sec15.Sylow155KA6P
