module

public import CFSG.Sporadic.Recognition.JankoWongLemma10

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem perm_decomp_injective : ∀ i j i' j' : Fin 3,
    permA3 ^ (i : ℕ) * permB3 ^ (j : ℕ) = permA3 ^ (i' : ℕ) * permB3 ^ (j' : ℕ) →
      i = i' ∧ j = j' := by
  unfold permA3 permB3; decide

theorem perm_decomp_support : ∀ i j : Fin 3,
    (Finset.univ.filter fun x => (permA3 ^ (i : ℕ) * permB3 ^ (j : ℕ)) x ≠ x).card = 3 →
      (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) := by
  unfold permA3 permB3; decide

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem P_decomp : ∀ p ∈ c.P, ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ p = c.a ^ i * c.b ^ j := by
  classical
  let f : ℕ × ℕ → S.H := fun q => c.a ^ q.1 * c.b ^ q.2
  let E : Set S.H := f '' ↑(Finset.range 3 ×ˢ Finset.range 3)
  have hEP : E ⊆ (c.P : Set S.H) := by
    rintro _ ⟨q, -, rfl⟩
    exact c.P.mul_mem (c.P.pow_mem c.haP _) (c.P.pow_mem c.hbP _)
  have hρ : ∀ q : ℕ × ℕ, S.ρ (f q) = permA3 ^ q.1 * permB3 ^ q.2 := by
    intro q
    simp [f, map_mul, map_pow, c.ha, c.hb]
  have hinj : Set.InjOn f ↑(Finset.range 3 ×ˢ Finset.range 3) := by
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hij hij'
    have h1 := congrArg S.ρ h
    rw [hρ, hρ] at h1
    have := perm_decomp_injective ⟨i, hij.1⟩ ⟨j, hij.2⟩ ⟨i', hij'.1⟩ ⟨j', hij'.2⟩ h1
    simp only [Fin.mk.injEq] at this
    rw [this.1, this.2]
  have hE : E.ncard = 9 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset]
    simp
  have hP : (c.P : Set S.H).ncard = 9 := by
    have h := Nat.card_coe_set_eq (c.P : Set S.H)
    rw [← h]
    exact c.hP9
  have heq : E = (c.P : Set S.H) :=
    Set.eq_of_subset_of_ncard_le hEP (by rw [hE, hP]) (Set.toFinite _)
  intro p hp
  have hpE : p ∈ E := by rw [heq]; exact hp
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := hpE
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hij
  exact ⟨i, j, hij.1, hij.2, rfl⟩

theorem eq_of_cycleType_three {p : S.H} (hp : p ∈ c.P) (ht : (S.ρ p).cycleType = {3}) :
    p = c.a ∨ p = c.a⁻¹ ∨ p = c.b ∨ p = c.b⁻¹ := by
  obtain ⟨i, j, hi, hj, rfl⟩ := c.P_decomp p hp
  have hsupp : (Finset.univ.filter fun x => (permA3 ^ i * permB3 ^ j) x ≠ x).card = 3 := by
    have h1 : (S.ρ (c.a ^ i * c.b ^ j)).support.card = 3 := by
      rw [← sum_cycleType, ht]; simp
    rw [map_mul, map_pow, map_pow, c.ha, c.hb] at h1
    exact h1
  have := perm_decomp_support ⟨i, hi⟩ ⟨j, hj⟩ hsupp
  simp [Fin.ext_iff] at this
  have ha2 : c.a ^ 2 = c.a⁻¹ := by
    have h : c.a ^ 2 * c.a = 1 := by rw [← pow_succ]; exact c.ha3
    exact eq_inv_of_mul_eq_one_left h
  have hb2 : c.b ^ 2 = c.b⁻¹ := by
    have h : c.b ^ 2 * c.b = 1 := by rw [← pow_succ]; exact c.hb3
    exact eq_inv_of_mul_eq_one_left h
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; simp
  · right; left; simp [ha2]
  · right; right; left; simp
  · right; right; right; simp [hb2]

@[expose] def Xs : Set G := {(c.a : G), (c.a : G)⁻¹, (c.b : G), (c.b : G)⁻¹}

theorem cycleType_a : (S.ρ c.a).cycleType = {3} := by rw [c.ha]; exact cycleType_permA3

theorem cycleType_b : (S.ρ c.b).cycleType = {3} := by rw [c.hb]; exact cycleType_permB3

theorem Xs_prop {x : G} (hx : x ∈ c.Xs) :
    ∃ p : S.H, (p : G) = x ∧ p ∈ c.P ∧ p ^ 3 = 1 ∧ (S.ρ p).cycleType = {3} := by
  rcases hx with h | h | h | h
  · exact ⟨c.a, h.symm, c.haP, c.ha3, c.cycleType_a⟩
  · refine ⟨c.a⁻¹, ?_, c.P.inv_mem c.haP, by rw [inv_pow, c.ha3, inv_one], ?_⟩
    · rw [h]; simp
    · rw [map_inv, cycleType_inv]; exact c.cycleType_a
  · exact ⟨c.b, h.symm, c.hbP, c.hb3, c.cycleType_b⟩
  · refine ⟨c.b⁻¹, ?_, c.P.inv_mem c.hbP, by rw [inv_pow, c.hb3, inv_one], ?_⟩
    · rw [h]; simp
    · rw [map_inv, cycleType_inv]; exact c.cycleType_b

theorem Xs_inv {x : G} (hx : x ∈ c.Xs) : x⁻¹ ∈ c.Xs := by
  rcases hx with h | h | h | h
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inl (by rw [h, inv_inv])
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; exact Set.mem_singleton _)))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, inv_inv])))

theorem Xs_pow_three {x : G} (hx : x ∈ c.Xs) : x ^ 3 = 1 ∧ x ≠ 1 := by
  obtain ⟨p, rfl, -, hp3, hpt⟩ := c.Xs_prop hx
  refine ⟨by have := congrArg Subtype.val hp3; simpa using this, fun e => ?_⟩
  have hp1 : p = 1 := Subtype.ext e
  rw [hp1, map_one, cycleType_one] at hpt
  simp at hpt

theorem Xs_ne_inv {x : G} (hx : x ∈ c.Xs) : x⁻¹ ≠ x := by
  obtain ⟨h3, h1⟩ := c.Xs_pow_three hx
  intro e
  apply h1
  have h2 : x * x = 1 := by
    calc x * x = x⁻¹ * x := by rw [e]
      _ = 1 := inv_mul_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem Xs_ncard : c.Xs.ncard = 4 := by
  have hab : (c.a : G) ≠ (c.b : G) := fun e => by
    have h := congrArg S.ρ (Subtype.ext e : c.a = c.b)
    rw [c.ha, c.hb] at h
    revert h; unfold permA3 permB3; decide
  have habi : (c.a : G) ≠ (c.b : G)⁻¹ := fun e => by
    have h := congrArg S.ρ (Subtype.ext (by simpa using e) : c.a = c.b⁻¹)
    rw [map_inv, c.ha, c.hb] at h
    revert h; unfold permA3 permB3; decide
  have hiab : (c.a : G)⁻¹ ≠ (c.b : G) := fun e => by
    have h := congrArg S.ρ (Subtype.ext (by simpa using e) : c.a⁻¹ = c.b)
    rw [map_inv, c.ha, c.hb] at h
    revert h; unfold permA3 permB3; decide
  have hiabi : (c.a : G)⁻¹ ≠ (c.b : G)⁻¹ := fun e => hab (inv_injective e)
  have haai : (c.a : G) ≠ (c.a : G)⁻¹ := (c.Xs_ne_inv (Or.inl rfl)).symm
  have hbbi : (c.b : G) ≠ (c.b : G)⁻¹ :=
    (c.Xs_ne_inv (Or.inr (Or.inr (Or.inl rfl)))).symm
  unfold Xs
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbbi]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hiab, hiabi⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨haai, hab, habi⟩

theorem conj_mem_Xs {g : G}
    (hg : ∀ p ∈ c.P, ∃ p' ∈ c.P, ((p' : S.H) : G) = g * (p : G) * g⁻¹)
    {x : G} (hx : x ∈ c.Xs) : g * x * g⁻¹ ∈ c.Xs := by
  obtain ⟨p, rfl, hpP, hp3, hpt⟩ := c.Xs_prop hx
  obtain ⟨p', hp'P, hp'e⟩ := hg p hpP
  have hpG3 : (p : G) ^ 3 = 1 := by have := congrArg Subtype.val hp3; simpa using this
  have hp'3 : p' ^ 3 = 1 := by
    apply Subtype.ext
    have : ((p' : S.H) : G) ^ 3 = 1 := by
      rw [hp'e]
      have : (g * (p : G) * g⁻¹) ^ 3 = g * (p : G) ^ 3 * g⁻¹ := by simp [pow_succ, mul_assoc]
      rw [this, hpG3]; simp
    simpa using this
  have hp1 : (p : G) ≠ 1 := fun e => by
    have hp1' : p = 1 := Subtype.ext e
    rw [hp1', map_one, cycleType_one] at hpt
    simp at hpt
  have hp'1 : p' ≠ 1 := fun e => by
    rw [e] at hp'e
    apply hp1
    calc (p : G) = g⁻¹ * (g * (p : G) * g⁻¹) * g := by group
      _ = 1 := by rw [← hp'e]; simp
  have hρ1 : S.ρ p' ≠ 1 := fun e => by
    rcases S.cover.mem_ker_iff.mp e with e1 | e1
    · exact hp'1 e1
    · have : p' ^ 3 = zIn S.z := by rw [e1, pow_succ, S.zIn_sq, one_mul]
      rw [hp'3] at this
      exact S.cover.ne_one this.symm
  have hρ3 : (S.ρ p') ^ 3 = 1 := by rw [← map_pow, hp'3, map_one]
  have hp't : (S.ρ p').cycleType = {3} := by
    rcases cycleType_of_cube_eq_one_ne_one hρ3 hρ1 with h | h
    · exact h
    · exfalso
      exact S.not_isConj_type3_type33 hp3 hp'3 hpt h (isConj_iff.mpr ⟨g, hp'e.symm⟩)
  rw [← hp'e]
  rcases c.eq_of_cycleType_three hp'P hp't with h | h | h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr (Or.inl (by simp))
  · rw [h]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [h]; exact Or.inr (Or.inr (Or.inr (by simp)))

theorem conj_fixes_Xs {g : G} (hg3 : ∃ n : ℕ, g ^ (3 ^ n) = 1)
    (hX : ∀ x ∈ c.Xs, g * x * g⁻¹ ∈ c.Xs) : ∀ x ∈ c.Xs, g * x * g⁻¹ = x := by
  classical
  obtain ⟨n, hn⟩ := hg3
  have : Fintype c.Xs := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Function.End c.Xs := fun x => ⟨g * x.1 * g⁻¹, hX x.1 x.2⟩
  have hfpow : ∀ k : ℕ, ∀ x : c.Xs, ((f ^ k) x).1 = g ^ k * x.1 * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero]; show x.1 = _; simp
    | succ k ih =>
      intro x
      rw [pow_succ']
      show g * ((f ^ k) x).1 * g⁻¹ = _
      rw [ih x, pow_succ']
      group
  have hf1 : f ^ 3 ^ n = 1 := by
    funext x
    apply Subtype.ext
    rw [hfpow, hn]
    show 1 * x.1 * (1 : G)⁻¹ = x.1
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := n) hf1
  have hcard : Fintype.card c.Xs = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, c.Xs_ncard]
  have hodd : ¬ Odd (Nat.card ↑(Function.fixedPoints f)) := by
    intro hodd
    let ι : ↑(Function.fixedPoints f) → ↑(Function.fixedPoints f) := fun x =>
      ⟨⟨(x.1.1)⁻¹, c.Xs_inv x.1.2⟩, by
        have := x.2
        have h1 : g * x.1.1 * g⁻¹ = x.1.1 := congrArg Subtype.val this
        show (⟨g * (x.1.1)⁻¹ * g⁻¹, _⟩ : c.Xs) = ⟨(x.1.1)⁻¹, _⟩
        apply Subtype.ext
        show g * (x.1.1)⁻¹ * g⁻¹ = (x.1.1)⁻¹
        calc g * (x.1.1)⁻¹ * g⁻¹ = (g * x.1.1 * g⁻¹)⁻¹ := by group
          _ = (x.1.1)⁻¹ := by rw [h1]⟩
    have hι : ∀ x, ι (ι x) = x := fun x => Subtype.ext (Subtype.ext (inv_inv _))
    obtain ⟨x, hx⟩ := exists_fixed_of_sq_eq_one_odd hι hodd
    have h1 : (x.1.1)⁻¹ = x.1.1 := congrArg (fun y => y.1.1) hx
    exact c.Xs_ne_inv x.1.2 h1
  have hfix4 : Fintype.card ↑(Function.fixedPoints f) = 4 := by
    have hle : Fintype.card ↑(Function.fixedPoints f) ≤ 4 := by
      rw [← hcard]; exact Fintype.card_subtype_le _
    have heven : Even (Fintype.card ↑(Function.fixedPoints f)) := by
      rw [← Nat.not_odd_iff_even, Nat.card_eq_fintype_card.symm]; exact hodd
    unfold Nat.ModEq at hmod
    obtain ⟨m, hm⟩ := heven
    omega
  intro x hx
  by_contra hne
  have hnotfix : ¬ (⟨x, hx⟩ : c.Xs) ∈ Function.fixedPoints f := by
    intro hfx
    exact hne (congrArg Subtype.val hfx)
  have hlt := Fintype.card_subtype_lt (p := fun y : c.Xs => y ∈ Function.fixedPoints f) hnotfix
  rw [hcard, ← Nat.card_eq_fintype_card] at hlt
  rw [← Nat.card_eq_fintype_card] at hfix4
  have hfix4' : Nat.card {y : c.Xs // y ∈ Function.fixedPoints f} = 4 := hfix4
  omega

theorem exists_three_group_centralizing_P (h : 27 ∣ Nat.card G) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ 27 ∣ Nat.card R ∧
      (∀ r ∈ R, r * (c.a : G) = (c.a : G) * r) ∧ (∀ r ∈ R, r * (c.b : G) = (c.b : G) * r) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set PG : Subgroup G := c.P.map S.H.subtype with hPG
  have hPGp : IsPGroup 3 PG := c.hP.map _
  have hPG9 : Nat.card PG = 9 := by
    rw [hPG, Subgroup.card_map_of_injective S.H.subtype_injective, c.hP9]
  obtain ⟨Q, hQ⟩ := hPGp.exists_le_sylow
  have hQcard : 27 ≤ Nat.card Q := by
    rw [Q.card_eq_multiplicity]
    have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have h3 : 3 ≤ (Nat.card G).factorization 3 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne (k := 3)).mp
        (by simpa using h)
      exact this
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (Nat.card G).factorization 3 := Nat.pow_le_pow_right (by norm_num) h3
  have hQ3 : IsPGroup 3 ↥(Q : Subgroup G) := Q.isPGroup'
  have : Group.IsNilpotent ↥(Q : Subgroup G) := hQ3.isNilpotent
  have hNC : NormalizerCondition ↥(Q : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  set H₀ : Subgroup ↥(Q : Subgroup G) := PG.subgroupOf Q with hH₀
  have hlt : H₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Nat.card H₀ = Nat.card ↥(Q : Subgroup G) := by
      rw [htop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rw [hH₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv, hPG9] at this
    omega
  obtain ⟨g₀, hg₀N, hg₀H⟩ := IsConcreteLE.exists_of_lt (hNC H₀ hlt)
  set g : G := (g₀ : G) with hg
  have hgPG : g ∉ PG := fun hmem => hg₀H (Subgroup.mem_subgroupOf.mpr hmem)
  have hg3 : ∃ n : ℕ, g ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ3) g₀
    refine ⟨n, ?_⟩
    have h1 : g₀ ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one g₀
    exact congrArg Subtype.val h1
  have hnorm : ∀ p ∈ c.P, ∃ p' ∈ c.P, ((p' : S.H) : G) = g * (p : G) * g⁻¹ := by
    intro p hp
    have hpQ : ((p : S.H) : G) ∈ (Q : Subgroup G) := hQ ⟨p, hp, rfl⟩
    have hpH : (⟨(p : G), hpQ⟩ : ↥(Q : Subgroup G)) ∈ H₀ :=
      Subgroup.mem_subgroupOf.mpr ⟨p, hp, rfl⟩
    have hconj := ((Subgroup.mem_normalizer_iff.mp hg₀N _).mp hpH)
    obtain ⟨p', hp'P, hp'e⟩ := Subgroup.mem_subgroupOf.mp hconj
    exact ⟨p', hp'P, hp'e⟩
  have hfix := c.conj_fixes_Xs hg3 (fun x hx => c.conj_mem_Xs hnorm hx)
  have hga : g * (c.a : G) = (c.a : G) * g := by
    have := hfix (c.a : G) (Or.inl rfl)
    calc g * (c.a : G) = (g * (c.a : G) * g⁻¹) * g := by group
      _ = (c.a : G) * g := by rw [this]
  have hgb : g * (c.b : G) = (c.b : G) * g := by
    have := hfix (c.b : G) (Or.inr (Or.inr (Or.inl rfl)))
    calc g * (c.b : G) = (g * (c.b : G) * g⁻¹) * g := by group
      _ = (c.b : G) * g := by rw [this]
  have hPcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := c.P) (by
    rw [c.hP9]; norm_num)
  have hPa : ∀ p ∈ c.P, (p : G) * (c.a : G) = (c.a : G) * (p : G) := fun p hp => by
    have := hPcomm.is_comm.comm ⟨p, hp⟩ ⟨c.a, c.haP⟩
    exact congrArg (fun w : c.P => ((w : S.H) : G)) this
  have hPb : ∀ p ∈ c.P, (p : G) * (c.b : G) = (c.b : G) * (p : G) := fun p hp => by
    have := hPcomm.is_comm.comm ⟨p, hp⟩ ⟨c.b, c.hbP⟩
    exact congrArg (fun w : c.P => ((w : S.H) : G)) this
  set R : Subgroup G := Subgroup.closure (↑PG ∪ {g}) with hR
  have hgQ : g ∈ (Q : Subgroup G) := g₀.2
  have hRQ : R ≤ (Q : Subgroup G) := by
    rw [hR, Subgroup.closure_le]
    rintro y (hy | hy)
    · exact hQ hy
    · rw [Set.mem_singleton_iff.mp hy]; exact hgQ
  have hRa : R ≤ centralizer ({(c.a : G)} : Set G) := by
    rw [hR, Subgroup.closure_le]
    rintro y (⟨p, hp, rfl⟩ | hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hPa p hp)
    · rw [Set.mem_singleton_iff.mp hy]; exact Subgroup.mem_centralizer_singleton_iff.mpr hga
  have hRb : R ≤ centralizer ({(c.b : G)} : Set G) := by
    rw [hR, Subgroup.closure_le]
    rintro y (⟨p, hp, rfl⟩ | hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hPb p hp)
    · rw [Set.mem_singleton_iff.mp hy]; exact Subgroup.mem_centralizer_singleton_iff.mpr hgb
  have hRp : IsPGroup 3 R := hQ3.to_le hRQ
  have hPGR : PG ≤ R := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hgR : g ∈ R := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRp
  have h9 : 9 ∣ Nat.card R := by rw [← hPG9]; exact Subgroup.card_dvd_of_le hPGR
  have hne : Nat.card R ≠ 9 := fun e => hgPG (by
    have heq : PG = R := Subgroup.eq_of_le_of_card_ge hPGR (by rw [e, hPG9])
    rw [heq]; exact hgR)
  refine ⟨R, hRp, ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hm] at h9 hne ⊢
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m <;> simp at h9
    have hm3 : 3 ≤ m := by
      by_contra hlt
      push Not at hlt
      have : m = 2 := by omega
      rw [this] at hne
      norm_num at hne
    calc 27 = 3 ^ 3 := by norm_num
      _ ∣ 3 ^ m := pow_dvd_pow 3 hm3
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hRa hr)
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hRb hr)

theorem twentySeven_dvd_card_centralizer_a (h : 27 ∣ Nat.card G) :
    27 ∣ Nat.card ↥(centralizer ({(c.a : G)} : Set G)) := by
  obtain ⟨R, -, hR27, hRa, -⟩ := c.exists_three_group_centralizing_P h
  have hle : R ≤ centralizer ({(c.a : G)} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRa r hr)
  exact hR27.trans (Subgroup.card_dvd_of_le hle)

theorem twentySeven_dvd_card_Cg (h : 27 ∣ Nat.card G) : 27 ∣ Nat.card c.Cg := by
  obtain ⟨R, -, hR27, hRa, hRb⟩ := c.exists_three_group_centralizing_P h
  have hle : R ≤ c.Cg := by
    intro r hr
    rw [c.mem_cg_iff]
    have h1 := hRa r hr
    have h2 := hRb r hr
    show r * ((c.a * c.b : S.H) : G) * r⁻¹ = ((c.a * c.b : S.H) : G)
    calc r * ((c.a * c.b : S.H) : G) * r⁻¹ = r * (c.a : G) * (c.b : G) * r⁻¹ := by
          simp [mul_assoc]
      _ = (c.a : G) * r * (c.b : G) * r⁻¹ := by rw [h1]
      _ = (c.a : G) * (r * (c.b : G)) * r⁻¹ := by group
      _ = (c.a : G) * ((c.b : G) * r) * r⁻¹ := by rw [h2]
      _ = ((c.a * c.b : S.H) : G) := by simp [mul_assoc]
  exact hR27.trans (Subgroup.card_dvd_of_le hle)

end Ctx




end Setup

end CFSG.Sporadic.Recognition.JankoWong
