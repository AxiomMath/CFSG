module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K38B

open Subgroup MulAction
open scoped Pointwise

variable {K : Type} [Group K] {q : ℕ}

theorem mem_smul_iff (a : MulAut K) (P : Sylow q K) (x : K) :
    x ∈ ((a • P : Sylow q K) : Subgroup K) ↔ ∃ y ∈ (P : Subgroup K), a y = x := by
  rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
  rfl

theorem mem_smul_of_fixed {a : MulAut K} {P : Sylow q K} {u : K} (hu : u ∈ (P : Subgroup K))
    (hau : a u = u) : u ∈ ((a • P : Sylow q K) : Subgroup K) :=
  (mem_smul_iff a P u).2 ⟨u, hu, hau⟩

theorem smul_conj_smul (a : MulAut K) (x : K) (P : Sylow q K) :
    a • (x • P) = a x • (a • P) := by
  rw [Sylow.smul_def, Sylow.smul_def, ← mul_smul, ← mul_smul]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

variable [Finite K] [hq : Fact q.Prime]

theorem inf_normalizer_eq {P T : Sylow q K} :
    (P : Subgroup K) ⊓ normalizer ((T : Subgroup K) : Set K) = (P : Subgroup K) ⊓ T :=
  P.isPGroup'.inf_normalizer_sylow T

theorem exists_smul_eq_of_ne {T T' P : Sylow q K} (hTT' : T ≠ T')
    (hinf : (T' : Subgroup K) ⊓ T = ⊥) (hcount : Nat.card (Sylow q K) = Nat.card T + 1)
    (hP : P ≠ T') : ∃ x ∈ (T' : Subgroup K), x • T = P := by
  classical
  let O : Set (Sylow q K) := orbit (T' : Subgroup K) T
  have hstab : stabilizer (T' : Subgroup K) T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_stabilizer_iff] at hx
    have hxN : (x : K) ∈ normalizer ((T : Subgroup K) : Set K) :=
      Sylow.smul_eq_iff_mem_normalizer.1 hx
    have h1 : (x : K) ∈ (T' : Subgroup K) ⊓ normalizer ((T : Subgroup K) : Set K) := ⟨x.2, hxN⟩
    rw [inf_normalizer_eq, hinf, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext h1
  have hO : O.ncard = Nat.card T := by
    have h := index_stabilizer (T' : Subgroup K) T
    rw [hstab, Subgroup.index_bot] at h
    have h' : O.ncard = Nat.card (T' : Subgroup K) := by
      simpa [O, Nat.card_coe_set_eq] using h.symm
    rw [h', Sylow.card_eq_multiplicity T', Sylow.card_eq_multiplicity T]
  have hOsub : O ⊆ {T'}ᶜ := by
    rintro _ ⟨x, rfl⟩ hx
    have hx' : (x : K) • T = T' := hx
    have hxN : (x : K) ∈ normalizer ((T' : Subgroup K) : Set K) := le_normalizer x.2
    have h1 : (x : K)⁻¹ • ((x : K) • T) = (x : K)⁻¹ • T' := by rw [hx']
    rw [inv_smul_smul, Sylow.smul_eq_iff_mem_normalizer.2 (inv_mem hxN)] at h1
    exact hTT' h1
  have hcompl : ({T'}ᶜ : Set (Sylow q K)).ncard = Nat.card T := by
    rw [Set.ncard_compl, Set.ncard_singleton, hcount, Nat.add_sub_cancel]
  have heq : O = {T'}ᶜ :=
    Set.eq_of_subset_of_ncard_le hOsub (by rw [hcompl, hO]) (Set.toFinite _)
  have hPO : P ∈ O := by
    rw [heq]
    exact hP
  obtain ⟨x, hx⟩ := hPO
  exact ⟨x, x.2, hx⟩

theorem exists_fixed_not_mem_normalizer (hq2 : q ≠ 2) (T : Sylow q K)
    (hTI : ∀ P : Sylow q K, P = T ∨ (P : Subgroup K) ⊓ T = ⊥)
    (hcount : Nat.card (Sylow q K) = Nat.card T + 1)
    (V : Subgroup (MulAut K)) (hV : IsPGroup 2 V)
    (hC : ∃ u ∈ (T : Subgroup K), u ≠ 1 ∧ ∀ v ∈ V, v u = u) :
    ∃ k : K, (∀ v ∈ V, v k = k) ∧ k ∉ normalizer ((T : Subgroup K) : Set K) := by
  classical
  obtain ⟨u, huT, hu1, huV⟩ := hC
  have hVT : ∀ v ∈ V, v • T = T := by
    intro v hv
    rcases hTI (v • T) with h | h
    · exact h
    · exfalso
      have hmem : u ∈ ((v • T : Sylow q K) : Subgroup K) ⊓ T :=
        ⟨mem_smul_of_fixed huT (huV v hv), huT⟩
      rw [h, mem_bot] at hmem
      exact hu1 hmem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hV.card_modEq_card_fixedPoints (Sylow q K)
  have hTodd : Odd (Nat.card T) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact (hq.out.odd_of_ne_two hq2).pow
  have hFix : T ∈ fixedPoints V (Sylow q K) := fun v => hVT v v.2
  obtain ⟨T', hT'F, hT'T⟩ : ∃ T' ∈ fixedPoints V (Sylow q K), T' ≠ T := by
    by_contra hall
    push Not at hall
    have hF : fixedPoints V (Sylow q K) = {T} := Set.eq_singleton_iff_unique_mem.2 ⟨hFix, hall⟩
    rw [hF, Nat.card_coe_set_eq, Set.ncard_singleton, hcount] at hmod
    obtain ⟨m, hm⟩ := hTodd
    rw [hm, Nat.ModEq] at hmod
    omega
  have hT'V : ∀ v ∈ V, v • T' = T' := fun v hv => hT'F ⟨v, hv⟩
  have hinf : (T' : Subgroup K) ⊓ T = ⊥ := (hTI T').resolve_left hT'T
  by_cases hA : ∃ u' ∈ (T' : Subgroup K), u' ≠ 1 ∧ ∀ v ∈ V, v u' = u'
  ·
    obtain ⟨u', hu'T', hu'1, hu'V⟩ := hA
    refine ⟨u', hu'V, fun hN => hu'1 ?_⟩
    have h1 : u' ∈ (T' : Subgroup K) ⊓ normalizer ((T : Subgroup K) : Set K) := ⟨hu'T', hN⟩
    rw [inf_normalizer_eq, hinf, mem_bot] at h1
    exact h1
  ·
    exfalso
    push Not at hA
    have hT''V : ∀ v ∈ V, v • (u • T') = u • T' := fun v hv => by
      rw [smul_conj_smul, huV v hv, hT'V v hv]
    have hT''ne : u • T' ≠ T' := by
      intro h
      have huN : u ∈ normalizer ((T' : Subgroup K) : Set K) :=
        Sylow.smul_eq_iff_mem_normalizer.1 h
      have hmem : u ∈ (T : Subgroup K) ⊓ normalizer ((T' : Subgroup K) : Set K) := ⟨huT, huN⟩
      rw [inf_normalizer_eq, inf_comm, hinf, mem_bot] at hmem
      exact hu1 hmem
    have hT''T : u • T' ≠ T := by
      intro h
      apply hT'T
      have h1 : u⁻¹ • (u • T') = T' := inv_smul_smul u T'
      rw [← h1, h]
      exact Sylow.smul_eq_iff_mem_normalizer.2 (inv_mem (le_normalizer huT))
    obtain ⟨x, hxT', hx⟩ := exists_smul_eq_of_ne (Ne.symm hT'T) hinf hcount hT''ne
    have hxV : ∀ v ∈ V, v x = x := by
      intro v hv
      have h1 : v • (x • T) = x • T := by rw [hx]; exact hT''V v hv
      rw [smul_conj_smul, hVT v hv] at h1
      have h2 : (x⁻¹ * v x) • T = T := by rw [mul_smul, h1, inv_smul_smul]
      have h3 : x⁻¹ * v x ∈ normalizer ((T : Subgroup K) : Set K) :=
        Sylow.smul_eq_iff_mem_normalizer.1 h2
      have h4 : v x ∈ (T' : Subgroup K) := by
        have h5 := (mem_smul_iff v T' (v x)).2 ⟨x, hxT', rfl⟩
        rwa [hT'V v hv] at h5
      have h5 : x⁻¹ * v x ∈ (T' : Subgroup K) ⊓ normalizer ((T : Subgroup K) : Set K) :=
        ⟨(T' : Subgroup K).mul_mem ((T' : Subgroup K).inv_mem hxT') h4, h3⟩
      rw [inf_normalizer_eq, hinf, mem_bot] at h5
      exact (eq_of_inv_mul_eq_one h5).symm
    have hx1 : x = 1 := by
      by_contra hx1
      obtain ⟨v, hv, hvx⟩ := hA x hxT' hx1
      exact hvx (hxV v hv)
    rw [hx1, one_smul] at hx
    exact hT''T hx.symm

end CFSG.LocalAnalysis.UniquenessCase.UCK.K38B
