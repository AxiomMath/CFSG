module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_relIndex_q1_trichotomy {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {X : Subgroup G} (hQX : Q1 L1 L2 S ≤ X) (hXS : X ≤ S)
    (hXN : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G)) :
    (Q1 L1 L2 S).relIndex X = 1 ∨ (Q1 L1 L2 S).relIndex X = 2 ^ k ∨
      (Q1 L1 L2 S).relIndex X = (2 ^ k) ^ 3 := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) :=
    isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hqLhat : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) (2 ^ k) := by
    refine Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hVU3Lhat : VU3Big (L1 ⊔ Q1 L1 L2 S) := by
    refine ⟨k, hk, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hrelS : (Q1 L1 L2 S).relIndex S = (2 ^ k) ^ 3 := by
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      have h := relIndex_pCoreOf_sylow_su (L := L1 ⊔ Q1 L1 L2 S) (T := S)
        hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
      rwa [pCoreOf_sup_pCoreOf hF.1] at h
    · obtain ⟨eL⟩ := h
      have h := relIndex_pCoreOf_sylow_psu (L := L1 ⊔ Q1 L1 L2 S) (T := S)
        hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
      rwa [pCoreOf_sup_pCoreOf hF.1] at h
  obtain ⟨X0, hmemX0, -, hrelX0, -⟩ := exists_X0 hqLhat hT
  rw [pCoreOf_sup_pCoreOf hF.1] at hmemX0 hrelX0
  have hXN' : (L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    intro g hg
    obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgP1 : g ∈ P1 L1 L2 S :=
      (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S) (pCoreOf_le 2 (P1 L1 L2 S))) hgL
    exact hXN (str86_p1_inf_normalizer_le_bigB hF.toW hSB (Subgroup.mem_inf.mpr ⟨hgP1, hgN⟩))
  have htrich := vertex_trichotomy (L := L1 ⊔ Q1 L1 L2 S) (T := S) (X := X)
    (Or.inr hVU3Lhat) hT (by rw [pCoreOf_sup_pCoreOf hF.1]; exact hQX) hXS hXN'
  rw [pCoreOf_sup_pCoreOf hF.1] at htrich
  rcases htrich with hXQ | hXS' | hthird
  · left
    rw [hXQ, Subgroup.relIndex_self]
  · right; right
    rw [hXS', hrelS]
  · right; left
    have hXeq : X = X0 := by
      apply le_antisymm
      · intro t ht
        rw [hmemX0 t]
        exact ⟨hXS ht, (hthird t (hXS ht)).mp ht⟩
      · intro t ht
        have htS : t ∈ S := ((hmemX0 t).mp ht).1
        exact (hthird t htS).mpr ((hmemX0 t).mp ht).2
    rw [hXeq, hrelX0]

theorem str86_exists_q1_mul_mem_conj_bigB
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (h1 : VU3Big L1) (hn : 2 ≤ n)
    (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {h : G} (hh : h ∈ P2 L1 L2 S) (hhB : h ∉ bigB L1 L2 S)
    {b : G} (hb : b ∈ bigB L1 L2 S) :
    ∃ q ∈ Q1 L1 L2 S, h⁻¹ * (q * b) * h ∈ bigB L1 L2 S := by
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hbh : b * h ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem (hBP2 hb) hh
  have hbhB : b * h ∉ bigB L1 L2 S := by
    intro hc
    apply hhB
    have : h = b⁻¹ * (b * h) := by group
    rw [this]
    exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb) hc
  obtain ⟨s, hs, hsB⟩ := str86_exists_mem_mul_inv_mem_bigB hF hSB hn hL2 hbh hbhB hh hhB
  have hQS : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf hF.toW hSB (Or.inr h1) hn hL2
  have hQ2N : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)).trans
      (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S))
  rw [← hQS] at hs
  obtain ⟨q, hq, r, hr, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N).mp hs
  have hQ2P2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  have hr' : b⁻¹ * r * b ∈ Q2 L1 L2 S := by
    have := (Subgroup.mem_normalizer_iff.mp (hQ2P2 (hBP2 ((bigB L1 L2 S).inv_mem hb))) r).mp hr
    simpa using this
  have hr'' : h⁻¹ * (b⁻¹ * r * b) * h ∈ bigB L1 L2 S := by
    have := (Subgroup.mem_normalizer_iff.mp (hQ2P2 ((P2 L1 L2 S).inv_mem hh)) _).mp hr'
    rw [inv_inv] at this
    exact (le_sup_right : S ≤ bigB L1 L2 S)
      ((F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)) this)
  refine ⟨q, hq, ?_⟩
  have hinv := (bigB L1 L2 S).inv_mem hsB
  have e : h⁻¹ * (q * b) * h =
      ((q * r * (b * h))⁻¹ * h)⁻¹ * (h⁻¹ * (b⁻¹ * r * b) * h)⁻¹ := by group
  rw [e]
  exact (bigB L1 L2 S).mul_mem hinv ((bigB L1 L2 S).inv_mem hr'')

theorem str86_bigB_le_normalizer_D_sup
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (h1 : VU3Big L1) (hn : 2 ≤ n)
    (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {h : G} (hh : h ∈ P2 L1 L2 S) (hhB : h ∉ bigB L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer
      (((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
  set X : Subgroup G := (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S with hX
  have hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hBQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hc : ∀ c ∈ bigB L1 L2 S, h⁻¹ * c * h ∈ bigB L1 L2 S →
      c ∈ Subgroup.normalizer (X : Set G) := by
    intro c hcB hchB
    have hcQ1h : c ∈ Subgroup.normalizer ((MulAut.conj h • Q1 L1 L2 S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, mem_conj_smul_iff']
      have hN := hBQ1 hchB
      have e : h⁻¹ * (c * x * c⁻¹) * h = (h⁻¹ * c * h) * (h⁻¹ * x * h) * (h⁻¹ * c * h)⁻¹ := by
        group
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp hN _
    have hcD : c ∈ Subgroup.normalizer
        (((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, Subgroup.mem_inf]
      rw [Subgroup.mem_normalizer_iff.mp hcQ1h x, Subgroup.mem_normalizer_iff.mp (hBQ2 hcB) x]
    have hzp : Subgroup.zpowers c ≤ Subgroup.normalizer
        (((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hcD
    have hzp1 : Subgroup.zpowers c ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      Subgroup.zpowers_le.mpr (hBQ1 hcB)
    exact F1.le_normalizer_sup hzp hzp1 (Subgroup.mem_zpowers c)
  intro b hb
  obtain ⟨q, hq, hqb⟩ := str86_exists_q1_mul_mem_conj_bigB hF hSB h1 hn hL2 hh hhB hb
  have hqX : q ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer ((le_sup_right : Q1 L1 L2 S ≤ X) hq)
  have hQ1B : Q1 L1 L2 S ≤ bigB L1 L2 S :=
    (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)).trans le_sup_right
  have hqbX : q * b ∈ Subgroup.normalizer (X : Set G) :=
    hc (q * b) ((bigB L1 L2 S).mul_mem (hQ1B hq) hb) hqb
  have e : b = q⁻¹ * (q * b) := by group
  rw [e]
  exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hqX) hqbX

theorem str86_b2_relIndex_D
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcore : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      Q1 L1 L2 S ⊓ (MulAut.conj h • Q1 L1 L2 S) = str86Core L1 L2 S) :
    ((str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = 1 ∨
      (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = 2 ^ k ∨
      (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = (2 ^ k) ^ 3) ∧
    ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      (Q1 L1 L2 S).relIndex ((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S) =
        (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hKQ2 : str86Core L1 L2 S ≤ Q2 L1 L2 S := str86Core_le_q2 hF hSB hn hL2
  have hQ2P2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  have hstep : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      (Q1 L1 L2 S).relIndex ((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S) =
        (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
    intro h hh hhB
    set D : Subgroup G := (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S with hD
    have hDN : D ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      (inf_le_right.trans hQ2S).trans (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := D) (K := Q1 L1 L2 S) hDN).2
    have hDQ1 : D ⊓ Q1 L1 L2 S = str86Core L1 L2 S := by
      rw [hD, inf_right_comm, inf_comm (MulAut.conj h • Q1 L1 L2 S), hcore h hh hhB]
      exact inf_eq_left.mpr hKQ2
    rw [hsec, hDQ1]
    have hconjD : MulAut.conj h • (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = D := by
      ext x
      rw [hD, mem_conj_smul_iff', Subgroup.mem_inf, Subgroup.mem_inf, mem_conj_smul_iff']
      have hQ2x : h⁻¹ * x * h ∈ Q2 L1 L2 S ↔ x ∈ Q2 L1 L2 S := by
        have := Subgroup.mem_normalizer_iff.mp (hQ2P2 ((P2 L1 L2 S).inv_mem hh)) x
        rw [inv_inv] at this
        exact this.symm
      rw [hQ2x]
    have hconjK : MulAut.conj h • str86Core L1 L2 S = str86Core L1 L2 S := by
      ext x
      rw [mem_conj_smul_iff']
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str86Core L1 L2 S
        ((P2 L1 L2 S).inv_mem hh)) x)
      rw [inv_inv] at this
      exact this.symm
    have := Subgroup.relIndex_pointwise_smul (MulAut.conj h) (str86Core L1 L2 S)
      (Q1 L1 L2 S ⊓ Q2 L1 L2 S)
    rw [hconjD, hconjK] at this
    exact this
  refine ⟨?_, hstep⟩
  obtain ⟨h, hh, hhB⟩ := str86_exists_mem_p2_not_mem_bigB hF hn hL2
  rw [← hstep h hh hhB]
  refine str86_relIndex_q1_trichotomy hF hSB hk hFc hU3 le_sup_right
    (sup_le (inf_le_right.trans hQ2S) hQ1S) ?_
  exact str86_bigB_le_normalizer_D_sup hF hSB h1 hn hL2 hh hhB

end CFSG.Quasithin.Stroth

end
