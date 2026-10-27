module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace GL3

structure Hyp {A N : Type} [CommGroup A] [Group N] [MulDistribMulAction N A]
    (T : Subgroup N) (v₀ : A) (Z₁ Z₂ : Subgroup A) : Prop where
  exp : ∀ a : A, a * a = 1
  fix : ∀ a : A, (∀ n : N, n • a = a) → a = 1
  ne_one : v₀ ≠ 1
  fix_v₀ : ∀ t ∈ T, t • v₀ = v₀
  move : ∃ n : N, n • v₀ ≠ v₀
  tfix : ∀ S : Subgroup A, S ≠ ⊥ → (∀ t ∈ T, ∀ s ∈ S, t • s ∈ S) →
    ∃ s ∈ S, s ≠ 1 ∧ ∀ t ∈ T, t • s = s
  gamma : ∀ Y : Subgroup A, Y ≠ ⊥ → (∀ y ∈ Y, ∀ t ∈ T, t • y = y) →
    ∀ n : N, (∀ y ∈ Y, n • y ∈ Y) → n • v₀ = v₀
  le : Z₂ ≤ Z₁
  idx₁ : Nat.card A ≤ 2 * Nat.card Z₁
  idx₂ : Nat.card Z₁ ≤ 2 * Nat.card Z₂
  ti : ∀ n : N, n • v₀ ≠ v₀ → ∀ z ∈ Z₂, n • z ∈ Z₁ → z = 1

variable {A N : Type} [CommGroup A] [Group N] [MulDistribMulAction N A]
  {T : Subgroup N} {v₀ : A} {Z₁ Z₂ : Subgroup A}

private lemma eq_pair_of_ncard_eq_two {α : Type*} {s : Set α} {a : α}
    (hs : s.ncard = 2) (ha : a ∈ s) : ∃ b, b ≠ a ∧ s = {a, b} := by
  rw [Set.ncard_eq_two] at hs
  obtain ⟨x, y, hxy, rfl⟩ := hs
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h
  · rw [h]; exact ⟨y, hxy.symm, rfl⟩
  · rw [h]; exact ⟨x, hxy, Set.pair_comm x y⟩

private lemma mul_perm_three {M : Type*} [CommMonoid M] [DecidableEq M] {x y z : M} {f : M → M}
    (hf : Function.Injective f) (hx : f x ∈ ({x, y, z} : Finset M))
    (hy : f y ∈ ({x, y, z} : Finset M)) (hz : f z ∈ ({x, y, z} : Finset M))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    f x * f y * f z = x * y * z := by
  have hs : ({x, y, z} : Finset M).image f = {x, y, z} := by
    apply Finset.eq_of_subset_of_card_le
    · rw [Finset.image_subset_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · rw [hw]; exact hx
      · rw [hw]; exact hy
      · rw [hw]; exact hz
    · rw [Finset.card_image_of_injective _ hf]
  have hp : ({x,y,z} : Finset M).prod f = ({x,y,z} : Finset M).prod (fun w => w) := by
    have := Finset.prod_image (s := ({x,y,z} : Finset M)) (g := f) (f := id)
      (hf.injOn.mono (Set.subset_univ _))
    rw [hs] at this
    simpa using this.symm
  have hL : ({x,y,z} : Finset M).prod (fun w => w) = x * y * z := by
    simp [hxy, hxz, hyz, mul_assoc]
  have hR : ({x,y,z} : Finset M).prod f = f x * f y * f z := by
    simp [hxy, hxz, hyz, mul_assoc]
  rw [hR, hL] at hp
  exact hp

theorem Hyp.card_le_eight [Finite A] (h : Hyp T v₀ Z₁ Z₂) : Nat.card A ≤ 8 := by
  obtain ⟨n, hn⟩ := h.move
  let φ : A →* A := MulDistribMulAction.toMonoidHom A n
  let Z₁' : Subgroup A := Z₁.comap φ
  have hcard : Nat.card Z₁' = Nat.card Z₁ := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨φ z, z.2⟩
        invFun := fun w => ⟨n⁻¹ • (w : A), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · show φ (n⁻¹ • (w : A)) ∈ Z₁
      rw [MulDistribMulAction.toMonoidHom_apply]
      rw [show n • (n⁻¹ • (w : A)) = (w : A) by
            rw [← mul_smul, mul_inv_cancel, one_smul]]
      exact w.2
    · intro z
      apply Subtype.ext
      show n⁻¹ • φ (z : A) = (z : A)
      rw [MulDistribMulAction.toMonoidHom_apply, ← mul_smul, inv_mul_cancel, one_smul]
    · intro w
      apply Subtype.ext
      show φ (n⁻¹ • (w : A)) = (w : A)
      rw [MulDistribMulAction.toMonoidHom_apply, ← mul_smul, mul_inv_cancel, one_smul]
  have hdisj : Disjoint Z₂ Z₁' := by
    rw [Subgroup.disjoint_def]
    intro z hz2 hz1
    exact h.ti n hn z hz2 hz1
  have hle : Nat.card Z₂ * Nat.card Z₁' ≤ Nat.card A := by
    have := Nat.card_le_card_of_injective
      (fun p : Z₂ × Z₁' => (p.1 : A) * p.2) (Subgroup.mul_injective_of_disjoint hdisj)
    rwa [Nat.card_prod] at this
  rw [hcard] at hle
  have hc : 0 < Nat.card Z₂ := Nat.card_pos
  have hb : Nat.card Z₁ ≤ 4 := by
    have key : Nat.card Z₂ * Nat.card Z₁ ≤ 4 * Nat.card Z₂ := by
      calc Nat.card Z₂ * Nat.card Z₁ ≤ Nat.card A := hle
        _ ≤ 2 * Nat.card Z₁ := h.idx₁
        _ ≤ 2 * (2 * Nat.card Z₂) := Nat.mul_le_mul_left 2 h.idx₂
        _ = 4 * Nat.card Z₂ := by ring
    have key' : Nat.card Z₁ * Nat.card Z₂ ≤ 4 * Nat.card Z₂ := by
      calc Nat.card Z₁ * Nat.card Z₂ = Nat.card Z₂ * Nat.card Z₁ := Nat.mul_comm _ _
        _ ≤ 4 * Nat.card Z₂ := key
    exact le_of_mul_le_mul_right key' hc
  calc Nat.card A ≤ 2 * Nat.card Z₁ := h.idx₁
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 hb
    _ = 8 := by ring

theorem Hyp.card_eq_four_or_eight [Finite A] (h : Hyp T v₀ Z₁ Z₂) :
    Nat.card A = 4 ∨ Nat.card A = 8 := by
  have hpA : IsPGroup 2 A := fun a => ⟨1, by show a ^ 2 = 1; rw [pow_two]; exact h.exp a⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpA
  obtain ⟨n, hn⟩ := h.move
  have hn1 : n • v₀ ≠ 1 := by
    intro h1
    apply h.ne_one
    calc v₀ = n⁻¹ • (n • v₀) := (inv_smul_smul n v₀).symm
      _ = n⁻¹ • (1 : A) := by rw [h1]
      _ = 1 := smul_one n⁻¹
  have h3 : 3 ≤ Nat.card A := by
    have hset : ({1, v₀, n • v₀} : Set A).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, v₀, n • v₀, h.ne_one.symm, hn1.symm, hn.symm, rfl⟩
    have hle := Set.ncard_le_ncard (Set.subset_univ ({1, v₀, n • v₀} : Set A))
    simpa [hset] using hle
  have hle8 : Nat.card A ≤ 8 := h.card_le_eight
  rw [hk] at h3 hle8
  have hk2 : 2 ≤ k := by
    by_contra hk'
    simp only [not_le] at hk'
    have h1 : k ≤ 1 := by omega
    have hpow : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    norm_num at hpow
    omega
  have hk3 : k ≤ 3 := by
    by_contra hk'
    simp only [not_le] at hk'
    have h4 : 4 ≤ k := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h4
    norm_num at hpow
    omega
  interval_cases k
  · left; rw [hk]; norm_num
  · right; rw [hk]; norm_num

theorem three_le_ncard_orbit [Finite A] (hexp : ∀ a : A, a * a = 1)
    (hfix : ∀ a : A, (∀ n : N, n • a = a) → a = 1) {a : A} (ha : a ≠ 1) :
    3 ≤ (MulAction.orbit N a).ncard := by
  by_contra hlt
  simp only [not_le] at hlt
  have hmem : a ∈ MulAction.orbit N a := MulAction.mem_orbit_self a
  have hpos : 0 < (MulAction.orbit N a).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, hmem⟩
  have hcase : (MulAction.orbit N a).ncard = 1 ∨ (MulAction.orbit N a).ncard = 2 := by omega
  rcases hcase with h1 | h2
  · obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp h1
    have hab : a = b := by simpa [hb] using hmem
    refine ha (hfix a ?_)
    intro n
    have hmem' : n • a ∈ MulAction.orbit N a := MulAction.mem_orbit_iff.mpr ⟨n, rfl⟩
    rw [hb] at hmem'
    simpa [hab] using hmem'
  · obtain ⟨b, hbne, hb⟩ := eq_pair_of_ncard_eq_two h2 hmem
    have hprod : a * b = 1 := by
      apply hfix
      intro n
      have hna : n • a = a ∨ n • a = b := by
        have hmem' : n • a ∈ MulAction.orbit N a := MulAction.mem_orbit_iff.mpr ⟨n, rfl⟩
        rw [hb] at hmem'
        simpa using hmem'
      have hnb : n • b = a ∨ n • b = b := by
        have hbO : b ∈ MulAction.orbit N a := by rw [hb]; simp
        rw [MulAction.mem_orbit_iff] at hbO
        obtain ⟨m, hm⟩ := hbO
        have hmem' : n • b ∈ MulAction.orbit N a :=
          MulAction.mem_orbit_iff.mpr ⟨n * m, by rw [mul_smul, hm]⟩
        rw [hb] at hmem'
        simpa using hmem'
      have hnab : n • a ≠ n • b := fun h => hbne.symm (MulAction.injective n h)
      rw [smul_mul']
      rcases hna with hna | hna <;> rcases hnb with hnb | hnb
      · exfalso; rw [hna, hnb] at hnab; exact hnab rfl
      · rw [hna, hnb]
      · rw [hna, hnb]; exact mul_comm b a
      · exfalso; rw [hna, hnb] at hnab; exact hnab rfl
    have hba : b = a := by
      have : a * b = a * a := by rw [hprod, hexp a]
      exact mul_left_cancel this
    exact hbne hba

theorem exists_plane_of_ncard_orbit_eq_three [Finite A] (hexp : ∀ a : A, a * a = 1)
    (hfix : ∀ a : A, (∀ n : N, n • a = a) → a = 1) {a : A} (ha : a ≠ 1)
    (h3 : (MulAction.orbit N a).ncard = 3) :
    ∃ I : Subgroup A, (I : Set A) = insert 1 (MulAction.orbit N a) ∧ Nat.card I = 4 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hO⟩ := Set.ncard_eq_three.mp h3
  have h1O : 1 ∉ MulAction.orbit N a := by
    intro hmem
    rw [MulAction.mem_orbit_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ha (MulAction.injective n (by show n • a = n • (1 : A); rw [hn, smul_one]))
  have hmul : ∀ n : N, n • (x * y * z) = x * y * z := by
    intro n
    have hxf : n • x ∈ ({x, y, z} : Finset A) := by
      have hxO : x ∈ MulAction.orbit N a := by rw [hO]; simp
      rw [MulAction.mem_orbit_iff] at hxO
      obtain ⟨m, hm⟩ := hxO
      have hmem : n • x ∈ MulAction.orbit N a :=
        MulAction.mem_orbit_iff.mpr ⟨n * m, by rw [mul_smul, hm]⟩
      rw [hO] at hmem
      simpa using hmem
    have hyf : n • y ∈ ({x, y, z} : Finset A) := by
      have hyO : y ∈ MulAction.orbit N a := by rw [hO]; simp
      rw [MulAction.mem_orbit_iff] at hyO
      obtain ⟨m, hm⟩ := hyO
      have hmem : n • y ∈ MulAction.orbit N a :=
        MulAction.mem_orbit_iff.mpr ⟨n * m, by rw [mul_smul, hm]⟩
      rw [hO] at hmem
      simpa using hmem
    have hzf : n • z ∈ ({x, y, z} : Finset A) := by
      have hzO : z ∈ MulAction.orbit N a := by rw [hO]; simp
      rw [MulAction.mem_orbit_iff] at hzO
      obtain ⟨m, hm⟩ := hzO
      have hmem : n • z ∈ MulAction.orbit N a :=
        MulAction.mem_orbit_iff.mpr ⟨n * m, by rw [mul_smul, hm]⟩
      rw [hO] at hmem
      simpa using hmem
    have hp := mul_perm_three (f := fun w => n • w) (MulAction.injective n) hxf hyf hzf hxy hxz hyz
    calc n • (x * y * z) = (n • x) * (n • y) * (n • z) := by simp only [smul_mul']
      _ = x * y * z := hp
  have hprod : x * y * z = 1 := hfix (x * y * z) hmul
  have hxy' : x * y = z := by
    exact mul_right_cancel (by rw [hprod, hexp z])
  have hxz' : x * z = y := by
    calc x * z = x * (x * y) := by rw [hxy']
      _ = (x * x) * y := by rw [← mul_assoc]
      _ = y := by rw [hexp x, one_mul]
  have hyz' : y * z = x := by
    calc y * z = z * y := mul_comm y z
      _ = (x * y) * y := by rw [hxy']
      _ = x * (y * y) := by rw [mul_assoc]
      _ = x := by rw [hexp y, mul_one]
  have hyx' : y * x = z := by rw [mul_comm, hxy']
  have hzx' : z * x = y := by rw [mul_comm, hxz']
  have hzy' : z * y = x := by rw [mul_comm, hyz']
  let I : Subgroup A :=
    { carrier := {1, x, y, z}
      one_mem' := by simp
      mul_mem' := by
        intro p q hp hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
        rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq <;>
          rw [hp, hq] <;> simp [hexp, hxy', hxz', hyx', hyz', hzx', hzy']
      inv_mem' := by
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with hp | hp | hp | hp
        · rw [hp]; simp
        · rw [hp]; simp [inv_eq_of_mul_eq_one_right (hexp x)]
        · rw [hp]; simp [inv_eq_of_mul_eq_one_right (hexp y)]
        · rw [hp]; simp [inv_eq_of_mul_eq_one_right (hexp z)] }
  refine ⟨I, ?_, ?_⟩
  · rw [hO]; rfl
  · have hIset : (I : Set A) = insert 1 (MulAction.orbit N a) := by rw [hO]; rfl
    change Nat.card (I : Set A) = 4
    rw [Nat.card_coe_set_eq, hIset,
      Set.ncard_insert_of_notMem h1O (Set.toFinite (MulAction.orbit N a)), h3]

theorem exists_involutive_move {I : Subgroup A} (hI : Nat.card I = 4)
    (hinv : ∀ n : N, ∀ x ∈ I, n • x ∈ I) {v : A} (hv : v ∈ I) (hv1 : v ≠ 1)
    {t : N} (htv : t • v = v) (htx : ∃ x ∈ I, t • x ≠ x) {s : N} (hs : s • v ≠ v) :
    ∃ g : N, g • v ≠ v ∧ g • (g • v) = v := by
  haveI : Finite I := Nat.finite_of_card_ne_zero (by omega)
  have hI4 : ((I : Set A)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hI
  set J : Set A := (I : Set A) \ {1} with hJdef
  have hJ3 : J.ncard = 3 := by
    rw [hJdef, Set.ncard_sdiff_singleton_of_mem I.one_mem, hI4]
  obtain ⟨x, hxI, htxne⟩ := htx
  have hx1 : x ≠ 1 := by
    intro hx
    exact htxne (by rw [hx, smul_one])
  have hxv : x ≠ v := by
    intro hx
    exact htxne (by rw [hx, htv])
  have hvJ : v ∈ J := by
    rw [hJdef]
    exact ⟨hv, by simpa using hv1⟩
  have hxJ : x ∈ J := by
    rw [hJdef]
    exact ⟨hxI, by simpa using hx1⟩
  have hpaircard : ({v, x} : Set A).ncard = 2 := Set.ncard_pair hxv.symm
  have hpairfin : ({v, x} : Set A).Finite := (Set.finite_singleton x).insert v
  have hlt : ({v, x} : Set A).ncard < J.ncard := by
    rw [hpaircard, hJ3]
    omega
  obtain ⟨y, hyJ, hy_notin⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt hpairfin
  have hyv : y ≠ v := fun h => hy_notin (by simp [h])
  have hyx : y ≠ x := fun h => hy_notin (by simp [h])
  have hy1 : y ≠ 1 := by
    rw [hJdef] at hyJ
    exact fun h => hyJ.2 (by simpa using h)
  have hyI : y ∈ I := by
    rw [hJdef] at hyJ
    exact hyJ.1
  have hsub3 : ({v, x, y} : Set A) ⊆ J := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu | hu
    · rw [hu]; exact hvJ
    · rw [hu]; exact hxJ
    · rw [hu]; exact hyJ
  have h3card : ({v, x, y} : Set A).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hxv.symm, hyv.symm]),
      Set.ncard_insert_of_notMem (by simp [hyx.symm]), Set.ncard_singleton]
  have hJeq : J = ({v, x, y} : Set A) := by
    symm
    apply Set.eq_of_subset_of_ncard_le hsub3
    simp [hJ3, h3card]
  have hcases : ∀ u ∈ J, u = v ∨ u = x ∨ u = y := by
    intro u hu
    have hu' : u ∈ ({v, x, y} : Set A) := by rw [← hJeq]; exact hu
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hu'
  have htxne1 : t • x ≠ 1 := by
    intro h
    exact hx1 (MulAction.injective t (by show t • x = t • (1 : A); rw [h, smul_one]))
  have hty1 : t • y ≠ 1 := by
    intro h
    exact hy1 (MulAction.injective t (by show t • y = t • (1 : A); rw [h, smul_one]))
  have htx_eq : t • x = y := by
    have hmem : t • x ∈ J := by
      rw [hJdef]
      exact ⟨hinv t x hxI, by simpa using htxne1⟩
    rcases hcases (t • x) hmem with h | h | h
    · exact absurd (MulAction.injective t (by show t • x = t • v; rw [h, htv])) hxv
    · exact absurd h htxne
    · exact h
  have hty_eq : t • y = x := by
    have hmem : t • y ∈ J := by
      rw [hJdef]
      exact ⟨hinv t y hyI, by simpa using hty1⟩
    rcases hcases (t • y) hmem with h | h | h
    · exact absurd (MulAction.injective t (by show t • y = t • v; rw [h, htv])) hyv
    · exact h
    · exact absurd (MulAction.injective t (by show t • y = t • x; rw [h, htx_eq])) hyx
  have ht2 : ∀ u ∈ J, t • (t • u) = u := by
    intro u hu
    rcases hcases u hu with hu | hu | hu
    · rw [hu, htv, htv]
    · rw [hu, htx_eq, hty_eq]
    · rw [hu, hty_eq, htx_eq]
  have hfixonly : ∀ u ∈ J, t • u = u → u = v := by
    intro u hu htu
    rcases hcases u hu with hu | hu | hu
    · exact hu
    · rw [hu] at htu
      exact absurd htu htxne
    · rw [hu] at htu
      exact absurd (hty_eq.symm.trans htu) hyx.symm
  set w : A := s⁻¹ • v with hwdef
  have hwI : w ∈ I := by rw [hwdef]; exact hinv s⁻¹ v hv
  have hw1 : w ≠ 1 := by
    intro h
    apply hv1
    have h' : s⁻¹ • v = 1 := by rw [← hwdef]; exact h
    exact MulAction.injective s⁻¹ (by show s⁻¹ • v = s⁻¹ • (1 : A); rw [h', smul_one])
  have hwv_ne : w ≠ v := by
    intro h
    apply hs
    have h' : s⁻¹ • v = v := by rw [← hwdef]; exact h
    calc s • v = s • (s⁻¹ • v) := by rw [h']
      _ = v := by rw [← mul_smul, mul_inv_cancel, one_smul]
  have hwJ : w ∈ J := by
    rw [hJdef]
    exact ⟨hwI, by simpa using hw1⟩
  have htw : t • w ≠ w := fun h => hwv_ne (hfixonly w hwJ h)
  set g : N := s * t * s⁻¹ with hgdef
  have hgv : g • v = s • (t • w) := by
    rw [hgdef, hwdef]
    simp only [mul_smul]
  have hwv_eq : v = s • w := by
    rw [hwdef]
    rw [← mul_smul, mul_inv_cancel, one_smul]
  have hgm : g • v ≠ v := by
    intro h
    apply htw
    apply MulAction.injective s
    calc s • (t • w) = g • v := hgv.symm
      _ = v := h
      _ = s • w := hwv_eq
  have hgg : g • (g • v) = v := by
    calc g • (g • v) = s • (t • (t • w)) := by
          rw [hgv, hgdef]
          simp only [mul_smul, inv_smul_smul]
      _ = s • w := by rw [ht2 w hwJ]
      _ = v := hwv_eq.symm
  exact ⟨g, hgm, hgg⟩

end GL3

end CFSG.LocalAnalysis.WeakClosure81

end
