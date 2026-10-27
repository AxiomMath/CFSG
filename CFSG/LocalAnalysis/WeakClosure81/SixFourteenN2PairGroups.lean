module

public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.ExceptionalSL3

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open scoped Pointwise

section Generic

theorem mem_zpowers_of_orderOf_three {K : Type*} [Group K] {f x : K}
    (hf3 : orderOf f = 3) (hx : x ∈ Subgroup.zpowers f) :
    x = 1 ∨ x = f ∨ x = f ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hf3]
  have hr : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hr with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero f)
  · exact Or.inr (Or.inl (zpow_one f))
  · exact Or.inr (Or.inr (zpow_ofNat f 2))

theorem perm3_exists_conj_finRotate :
    ∀ (σ : Equiv.Perm (Fin 3)), σ ^ 3 = 1 → σ ≠ 1 →
      ∃ g : Equiv.Perm (Fin 3), g * σ * g⁻¹ = finRotate 3 := by
  decide

theorem perm3_conj_swap_of_conj_finRotate :
    ∀ (τ : Equiv.Perm (Fin 3)), τ ^ 2 = 1 → τ ≠ 1 →
      τ * finRotate 3 * τ⁻¹ = (finRotate 3) ^ 2 →
      ∃ h : Equiv.Perm (Fin 3),
        h * finRotate 3 * h⁻¹ = finRotate 3 ∧ h * τ * h⁻¹ = Equiv.swap 0 1 := by
  decide

theorem perm3_conj_finRotate_swap {σ τ : Equiv.Perm (Fin 3)}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτσ : τ * σ * τ⁻¹ = σ ^ 2) :
    ∃ g : Equiv.Perm (Fin 3),
      g * σ * g⁻¹ = finRotate 3 ∧ g * τ * g⁻¹ = Equiv.swap 0 1 := by
  obtain ⟨g, hg⟩ := perm3_exists_conj_finRotate σ hσ3 hσ1
  have hτ'2 : (g * τ * g⁻¹) ^ 2 = 1 := by
    calc (g * τ * g⁻¹) ^ 2 = g * τ ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hτ2]; group
  have hτ'1 : g * τ * g⁻¹ ≠ 1 := by
    intro h
    apply hτ1
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  have hτ'σ : (g * τ * g⁻¹) * finRotate 3 * (g * τ * g⁻¹)⁻¹ =
      (finRotate 3) ^ 2 := by
    have h1 : (g * τ * g⁻¹) * finRotate 3 * (g * τ * g⁻¹)⁻¹ =
        g * (τ * σ * τ⁻¹) * g⁻¹ := by
      rw [← hg]
      group
    rw [h1, hτσ]
    have h2 : g * σ ^ 2 * g⁻¹ = (g * σ * g⁻¹) ^ 2 := by
      rw [pow_two, pow_two]
      group
    rw [h2, hg]
  obtain ⟨h, hh1, hh2⟩ := perm3_conj_swap_of_conj_finRotate (g * τ * g⁻¹) hτ'2 hτ'1 hτ'σ
  refine ⟨h * g, ?_, ?_⟩
  · calc (h * g) * σ * (h * g)⁻¹ = h * (g * σ * g⁻¹) * h⁻¹ := by group
      _ = h * finRotate 3 * h⁻¹ := by rw [hg]
      _ = finRotate 3 := hh1
  · calc (h * g) * τ * (h * g)⁻¹ = h * (g * τ * g⁻¹) * h⁻¹ := by group
      _ = Equiv.swap 0 1 := hh2

theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {K : Type*} [Group K] {s y : K}
    (hs2 : s * s = 1) (hy : y ∈ Subgroup.zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  by_cases hs1 : s = 1
  · left
    simp [hs1]
  · have hs_ord : orderOf s = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
    rw [← zpow_mod_orderOf, hs_ord]
    have hn : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hn with h | h <;> rw [h]
    · exact Or.inl (zpow_zero s)
    · exact Or.inr (zpow_one s)

theorem not_mem_zpowers_of_conj_eq_sq {K : Type*} [Group K] {x s : K}
    (hx_ne : x ≠ 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    s ∉ Subgroup.zpowers x := by
  intro hs
  have hcomm : s * x = x * s := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [← hn]
    exact (Commute.self_zpow (a := x) (n := n)).symm.eq
  have hx_eq : x = x ^ 2 := by
    calc x = s * x * s⁻¹ := by rw [hcomm]; group
      _ = x ^ 2 := hsx
  have hx1 : x = 1 := by
    have h := congrArg (fun t => t * x⁻¹) hx_eq
    simpa [pow_two, mul_assoc] using h.symm
  exact hx_ne hx1

theorem zpowers_pow_two_eq {K : Type*} [Group K] {x : K} (hx3 : x ^ 3 = 1) :
    Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers x 2
  · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    refine ⟨2, ?_⟩
    rw [zpow_ofNat]
    calc (x ^ 2) ^ 2 = x ^ 4 := by rw [← pow_mul]
      _ = x := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]

theorem zpowers_le_normalizer_zpowers_of_conj_eq_sq {K : Type*} [Group K] {x s : K}
    (hx3 : x ^ 3 = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers x : Set K) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : (Subgroup.zpowers x).map ((MulAut.conj s) : K →* K) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers ((MulAut.conj s) : K →* K) x]
    change Subgroup.zpowers (s * x * s⁻¹) = Subgroup.zpowers x
    rw [hsx, zpowers_pow_two_eq hx3]
  exact hmap

theorem closure_pair_eq_zpowers_sup {K : Type*} [Group K] {x s : K} :
    Subgroup.closure ({x, s} : Set K) = Subgroup.zpowers s ⊔ Subgroup.zpowers x := by
  have hpair : ({x, s} : Set K) = {s} ∪ {x} := by
    ext y
    simp
  rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure s,
    ← Subgroup.zpowers_eq_closure x]

theorem closure_pair_coe_eq_mul {K : Type*} [Group K] {x s : K}
    (hx3 : x ^ 3 = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    (↑(Subgroup.closure ({x, s} : Set K)) : Set K) =
      (Subgroup.zpowers s : Set K) * (Subgroup.zpowers x : Set K) := by
  rw [closure_pair_eq_zpowers_sup]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (zpowers_le_normalizer_zpowers_of_conj_eq_sq hx3 hsx)

theorem exists_pow_mul_pow_of_mem_closure {K : Type*} [Group K] {x s : K}
    (hx3 : x ^ 3 = 1) (hx_ne : x ≠ 1) (hs2 : s * s = 1)
    (hsx : s * x * s⁻¹ = x ^ 2) :
    ∀ a ∈ Subgroup.closure ({x, s} : Set K),
      ∃ i : Fin 3, ∃ j : Fin 2, x ^ (i : ℕ) * s ^ (j : ℕ) = a := by
  have hs_ne : s ≠ 1 := by
    intro h
    apply hx_ne
    have hx_eq : x = x ^ 2 := by
      calc x = s * x * s⁻¹ := by rw [h]; group
        _ = x ^ 2 := hsx
    have h' := congrArg (fun t => t * x⁻¹) hx_eq
    simpa [pow_two, mul_assoc] using h'.symm
  have hx_ord : orderOf x = 3 := orderOf_eq_prime hx3 hx_ne
  have hs_ord : orderOf s = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hs2) hs_ne
  intro a ha
  have hmem : a ∈ (Subgroup.zpowers s : Set K) * (Subgroup.zpowers x : Set K) := by
    rw [← closure_pair_coe_eq_mul hx3 hsx]
    exact ha
  rw [Set.mem_mul] at hmem
  obtain ⟨u, huS, w, hwX, huw⟩ := hmem
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp huS
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwX
  have hsmod : s ^ m = s ^ ((m % 2).toNat) := by
    have hz : s ^ m = s ^ ((m % 2).toNat : ℤ) := by
      rw [← zpow_mod_orderOf s m, hs_ord]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))).symm
    rw [hz, zpow_natCast]
  have hxmod : x ^ n = x ^ ((n % 3).toNat) := by
    have hz : x ^ n = x ^ ((n % 3).toNat : ℤ) := by
      rw [← zpow_mod_orderOf x n, hx_ord]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))).symm
    rw [hz, zpow_natCast]
  have hj_lt : (m % 2).toNat < 2 := by
    rw [Int.toNat_lt_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)]
    exact Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
  have hi_lt : (n % 3).toNat < 3 := by
    rw [Int.toNat_lt_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)]
    exact Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
  have ha_eq : s ^ ((m % 2).toNat) * x ^ ((n % 3).toNat) = a := by
    rw [← huw, hsmod, hxmod]
  have hj_cases : (m % 2).toNat = 0 ∨ (m % 2).toNat = 1 := by omega
  rcases hj_cases with hj0 | hj1
  · rw [hj0, pow_zero, one_mul] at ha_eq
    exact ⟨⟨(n % 3).toNat, hi_lt⟩, ⟨0, by norm_num⟩, by simpa using ha_eq⟩
  · have hswap : s * x ^ ((n % 3).toNat) = x ^ (2 * (n % 3).toNat) * s := by
      have hconj : s * x ^ ((n % 3).toNat) * s⁻¹ = (x ^ 2) ^ ((n % 3).toNat) := by
        calc s * x ^ ((n % 3).toNat) * s⁻¹ =
            (MulAut.conj s) (x ^ ((n % 3).toNat)) := rfl
          _ = ((MulAut.conj s) x) ^ ((n % 3).toNat) := map_pow (MulAut.conj s) x _
          _ = (s * x * s⁻¹) ^ ((n % 3).toNat) := by rw [MulAut.conj_apply]
          _ = (x ^ 2) ^ ((n % 3).toNat) := by rw [hsx]
      calc s * x ^ ((n % 3).toNat) = (s * x ^ ((n % 3).toNat) * s⁻¹) * s := by group
        _ = (x ^ 2) ^ ((n % 3).toNat) * s := by rw [hconj]
        _ = x ^ (2 * (n % 3).toNat) * s := by rw [← pow_mul]
    rw [hj1, pow_one] at ha_eq
    refine ⟨⟨(2 * (n % 3).toNat) % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨1, by norm_num⟩, ?_⟩
    rw [show ((⟨1, by norm_num⟩ : Fin 2) : ℕ) = 1 by rfl, pow_one]
    rw [← ha_eq, hswap]
    congr 1
    have hpow : x ^ ((2 * (n % 3).toNat) % orderOf x) = x ^ (2 * (n % 3).toNat) :=
      pow_mod_orderOf x (2 * (n % 3).toNat)
    rw [hx_ord] at hpow
    exact hpow

theorem zpowers_inf_zpowers_eq_bot_of_conj_eq_sq {K : Type*} [Group K] {x s : K}
    (hx_ne : x ≠ 1) (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x ^ 2) :
    Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hys : y ∈ Subgroup.zpowers s := hy.1
  have hyx : y ∈ Subgroup.zpowers x := hy.2
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hs2 hys with rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd hyx (not_mem_zpowers_of_conj_eq_sq hx_ne hsx)

theorem card_closure_pair_of_three_two {K : Type*} [Group K] {x s : K}
    (hx3 : x ^ 3 = 1) (hx_ne : x ≠ 1) (hs2 : s * s = 1)
    (hsx : s * x * s⁻¹ = x ^ 2) :
    Nat.card (Subgroup.closure ({x, s} : Set K)) = 6 := by
  have hs_ne : s ≠ 1 := by
    intro h
    apply hx_ne
    have hx_eq : x = x ^ 2 := by
      calc x = s * x * s⁻¹ := by rw [h]; group
        _ = x ^ 2 := hsx
    have h' := congrArg (fun t => t * x⁻¹) hx_eq
    simpa [pow_two, mul_assoc] using h'.symm
  have hx_ord : orderOf x = 3 := orderOf_eq_prime hx3 hx_ne
  have hs_ord : orderOf s = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hs2) hs_ne
  have hSX := closure_pair_coe_eq_mul hx3 hsx
  have hdisj := zpowers_inf_zpowers_eq_bot_of_conj_eq_sq hx_ne hs2 hsx
  let f : ↥(Subgroup.zpowers s) × ↥(Subgroup.zpowers x) →
      ↥(Subgroup.closure ({x, s} : Set K)) :=
    fun p => ⟨(p.1 : K) * p.2, by
      change (p.1 : K) * p.2 ∈ (↑(Subgroup.closure ({x, s} : Set K)) : Set K)
      rw [hSX]
      exact Set.mul_mem_mul p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u1, w1⟩ ⟨u2, w2⟩ h
      have hK : (u1 : K) * w1 = (u2 : K) * w2 := congrArg Subtype.val h
      have hrel : (u1 : K)⁻¹ * u2 = (w1 : K) * (w2 : K)⁻¹ := by
        have := congrArg (fun t => (u1 : K)⁻¹ * t * (w2 : K)⁻¹) hK
        simpa [mul_assoc] using this.symm
      have hmem : (u1 : K)⁻¹ * u2 ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
        constructor
        · exact (Subgroup.zpowers s).mul_mem ((Subgroup.zpowers s).inv_mem u1.2) u2.2
        · rw [hrel]
          exact (Subgroup.zpowers x).mul_mem w1.2 ((Subgroup.zpowers x).inv_mem w2.2)
      rw [hdisj] at hmem
      have h1 : (u1 : K)⁻¹ * u2 = 1 := Subgroup.mem_bot.mp hmem
      have hu_eq : u1 = u2 := by
        apply Subtype.ext
        have := congrArg (fun t => (u1 : K) * t) h1
        simpa [mul_assoc] using this.symm
      have hw_eq : w1 = w2 := by
        apply Subtype.ext
        have h2 : (w1 : K) * (w2 : K)⁻¹ = 1 := by rw [← hrel]; exact h1
        have := congrArg (fun t => t * (w2 : K)) h2
        simpa [mul_assoc] using this
      exact Prod.ext hu_eq hw_eq
    · intro g
      have hg : (g : K) ∈ (Subgroup.zpowers s : Set K) * (Subgroup.zpowers x : Set K) := by
        rw [← hSX]
        exact g.2
      rw [Set.mem_mul] at hg
      obtain ⟨u, hu, w, hw, huw⟩ := hg
      exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), Subtype.ext huw⟩
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hs_ord, hx_ord] at h
  norm_num at h
  exact h.symm

theorem closure_pair_inf_eq_zpowers_of_notMem {K : Type*} [Group K] {x s : K}
    {H : Subgroup K} (hx3 : x ^ 3 = 1) (hx_ne : x ≠ 1) (hs2 : s * s = 1)
    (hsx : s * x * s⁻¹ = x ^ 2) (hxH : x ∈ H) (hsH : s ∉ H) :
    Subgroup.closure ({x, s} : Set K) ⊓ H = Subgroup.zpowers x := by
  apply le_antisymm
  · intro a ha
    obtain ⟨i, j, hij⟩ :=
      exists_pow_mul_pow_of_mem_closure hx3 hx_ne hs2 hsx a ha.1
    have haH : a ∈ H := ha.2
    have hxiH : x ^ (i : ℕ) ∈ H := H.pow_mem hxH i
    have hsjH : s ^ (j : ℕ) ∈ H := by
      have h1 : s ^ (j : ℕ) = (x ^ (i : ℕ))⁻¹ * a := by rw [← hij]; group
      rw [h1]
      exact H.mul_mem (H.inv_mem hxiH) haH
    have hj : (j : ℕ) = 0 := by
      have hjlt : (j : ℕ) < 2 := j.2
      rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h | h
      · exact h
      · exfalso
        apply hsH
        simpa [h] using hsjH
    have haeq : a = x ^ (i : ℕ) := by
      have h1 : s ^ (j : ℕ) = 1 := by rw [hj]; simp
      rw [← hij, h1, mul_one]
    rw [haeq]
    exact Subgroup.npow_mem_zpowers x i
  · intro y hy
    constructor
    · have hle : Subgroup.zpowers x ≤ Subgroup.closure ({x, s} : Set K) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      exact hle hy
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact H.zpow_mem hxH n

theorem exists_mulEquiv_perm3_closure {K : Type*} [Group K] {x s : K}
    (hx3 : x ^ 3 = 1) (hx_ne : x ≠ 1) (hs2 : s * s = 1) (hs_ne : s ≠ 1)
    (hsx : s * x * s⁻¹ = x ^ 2) :
    ∃ α : ↥(Subgroup.closure ({x, s} : Set K)) ≃* Equiv.Perm (Fin 3),
      α ⟨x, Subgroup.subset_closure (by simp)⟩ = finRotate 3 ∧
      α ⟨s, Subgroup.subset_closure (by simp)⟩ = Equiv.swap 0 1 := by
  let A : Subgroup K := Subgroup.closure ({x, s} : Set K)
  let xA : ↥A := ⟨x, Subgroup.subset_closure (by simp)⟩
  let sA : ↥A := ⟨s, Subgroup.subset_closure (by simp)⟩
  have hcard : Nat.card ↥A = 6 := card_closure_pair_of_three_two hx3 hx_ne hs2 hsx
  have hnc : ∃ a b : ↥A, a * b ≠ b * a := by
    refine ⟨xA, sA, ?_⟩
    intro h
    apply hx_ne
    have hxs : x * s = s * x := congrArg Subtype.val h
    have h1 : s * x * s⁻¹ = x := by rw [← hxs]; group
    rw [hsx] at h1
    have := congrArg (fun t => t * x⁻¹) h1
    simpa [pow_two, mul_assoc] using this
  haveI : Finite ↥A := by
    by_contra hfin
    haveI : Infinite ↥A := not_finite_iff_infinite.mp hfin
    have h0 : Nat.card ↥A = 0 := Nat.card_eq_zero_of_infinite
    omega
  obtain ⟨ψ⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six hcard hnc
  let σ : Equiv.Perm (Fin 3) := ψ xA
  let τ : Equiv.Perm (Fin 3) := ψ sA
  have hσ3 : σ ^ 3 = 1 := by
    have h : xA ^ 3 = 1 := by
      apply Subtype.ext
      simpa [xA] using hx3
    calc σ ^ 3 = ψ (xA ^ 3) := by rw [map_pow]
      _ = 1 := by rw [h, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hx_ne
    have h1 : xA = 1 := by
      apply ψ.injective
      rw [show ψ xA = σ from rfl, h, map_one]
    have := congrArg Subtype.val h1
    simpa [xA] using this
  have hτ2 : τ ^ 2 = 1 := by
    have h : sA ^ 2 = 1 := by
      apply Subtype.ext
      simpa [sA, pow_two] using hs2
    calc τ ^ 2 = ψ (sA ^ 2) := by rw [map_pow]
      _ = 1 := by rw [h, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hs_ne
    have h1 : sA = 1 := by
      apply ψ.injective
      rw [show ψ sA = τ from rfl, h, map_one]
    have := congrArg Subtype.val h1
    simpa [sA] using this
  have hτσ : τ * σ * τ⁻¹ = σ ^ 2 := by
    have h : sA * xA * sA⁻¹ = xA ^ 2 := by
      apply Subtype.ext
      simpa [xA, sA, Subgroup.coe_pow] using hsx
    calc τ * σ * τ⁻¹ = ψ (sA * xA * sA⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = ψ (xA ^ 2) := by rw [h]
      _ = σ ^ 2 := by rw [map_pow]
  obtain ⟨g, hg1, hg2⟩ := perm3_conj_finRotate_swap hσ3 hσ1 hτ2 hτ1 hτσ
  refine ⟨ψ.trans (MulAut.conj g), ?_, ?_⟩
  · change g * ψ xA * g⁻¹ = finRotate 3
    exact hg1
  · change g * ψ sA * g⁻¹ = Equiv.swap 0 1
    exact hg2

theorem exists_mulEquiv_prod_of_internal_direct {E : Type*} [Group E]
    {H A B : Subgroup E} (hA : A ≤ H) (hB : B ≤ H)
    (hcomm : ∀ {a b}, a ∈ A → b ∈ B → Commute a b)
    (hdisj : A ⊓ B = ⊥)
    (hdecomp : ∀ {g}, g ∈ H → ∃ a ∈ A, ∃ b ∈ B, a * b = g)
    {P Q : Type*} [Group P] [Group Q]
    (α : ↥A ≃* P) (β : ↥B ≃* Q) :
    ∃ φ : ↥H ≃* (P × Q), ∀ (a : ↥A) (b : ↥B),
      φ (Subgroup.inclusion hA a * Subgroup.inclusion hB b) = (α a, β b) := by
  let f : (↥A × ↥B) →* ↥H :=
  { toFun := fun p => ⟨(p.1 : E) * p.2, H.mul_mem (hA p.1.2) (hB p.2.2)⟩
    map_one' := by ext; simp
    map_mul' := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩
      apply Subtype.ext
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      have hc : (b1 : E) * a2 = a2 * b1 := (hcomm a2.2 b1.2).eq.symm
      calc ((a1 : E) * a2) * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
        _ = a1 * (b1 * a2) * b2 := by rw [← hc]
        _ = (a1 * b1) * (a2 * b2) := by group }
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      have hK : (a1 : E) * b1 = (a2 : E) * b2 := congrArg Subtype.val h
      have hrel : (a1 : E)⁻¹ * a2 = (b1 : E) * (b2 : E)⁻¹ := by
        have := congrArg (fun t => (a1 : E)⁻¹ * t * (b2 : E)⁻¹) hK
        simpa [mul_assoc] using this.symm
      have hmem : (a1 : E)⁻¹ * a2 ∈ A ⊓ B := by
        constructor
        · exact A.mul_mem (A.inv_mem a1.2) a2.2
        · rw [hrel]
          exact B.mul_mem b1.2 (B.inv_mem b2.2)
      rw [hdisj] at hmem
      have h1 : (a1 : E)⁻¹ * a2 = 1 := Subgroup.mem_bot.mp hmem
      have ha_eq : a1 = a2 := by
        apply Subtype.ext
        have := congrArg (fun t => (a1 : E) * t) h1
        simpa [mul_assoc] using this.symm
      have hb_eq : b1 = b2 := by
        apply Subtype.ext
        have h2 : (b1 : E) * (b2 : E)⁻¹ = 1 := by rw [← hrel]; exact h1
        have := congrArg (fun t => t * (b2 : E)) h2
        simpa [mul_assoc] using this
      exact Prod.ext ha_eq hb_eq
    · intro h
      obtain ⟨a, ha, b, hb, hab⟩ := hdecomp h.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  let e : (↥A × ↥B) ≃* ↥H := MulEquiv.ofBijective f hf
  refine ⟨e.symm.trans (α.prodCongr β), ?_⟩
  intro a b
  have h : e (a, b) = Subgroup.inclusion hA a * Subgroup.inclusion hB b := by
    apply Subtype.ext
    rfl
  rw [← h]
  show (α.prodCongr β) (e.symm (e (a, b))) = (α a, β b)
  rw [MulEquiv.symm_apply_apply]
  rfl

end Generic

end CFSG.LocalAnalysis.WeakClosure81
