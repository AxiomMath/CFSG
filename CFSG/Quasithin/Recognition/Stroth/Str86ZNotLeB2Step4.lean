module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2D
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Tools
import CFSG.Quasithin.Recognition.Stroth.Str86U3SylowNonab
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_q2_le_normalizer_D {L1 L2 S : Subgroup G} {h : G} (hh : h ∈ P2 L1 L2 S)
    (hQ2S : Q2 L1 L2 S ≤ S) :
    Q2 L1 L2 S ≤ Subgroup.normalizer
      (((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
  intro x hx
  have hx' : h⁻¹ * x * h ∈ Q2 L1 L2 S := by
    have h' := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) ((P2 L1 L2 S).inv_mem hh)) x).mp hx
    rwa [inv_inv] at h'
  have hN := le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S) (hQ2S hx')
  have hxQ1h : x ∈ Subgroup.normalizer ((MulAut.conj h • Q1 L1 L2 S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, mem_conj_smul_iff']
    have e : h⁻¹ * (x * y * x⁻¹) * h =
        (h⁻¹ * x * h) * (h⁻¹ * y * h) * (h⁻¹ * x * h)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hN _
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp hxQ1h y,
    Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y]

theorem str86_b2_false_of_relIndex_D_eq_cube
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hcore : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      Q1 L1 L2 S ⊓ (MulAut.conj h • Q1 L1 L2 S) = str86Core L1 L2 S)
    (hd : (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = (2 ^ k) ^ 3) : False := by
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hSQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S)
  have hKP2 : P2 L1 L2 S ≤ Subgroup.normalizer (str86Core L1 L2 S : Set G) :=
    le_normalizer_str86Core L1 L2 S
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  have hstep := (str86_b2_relIndex_D hF hSB hk hFc hU3 hn hL2 hcore).2
  have hDS : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S = S := by
    intro h hh hhB
    have hle : (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S ≤ S :=
      sup_le (inf_le_right.trans hQ2S) hQ1S
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right :
      Q1 L1 L2 S ≤ (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S) hle
    rw [hstep h hh hhB, hd, str86_relIndex_q1_s hF hSB hk hFc hU3] at hmul
    have hpos : 0 < (2 ^ k) ^ 3 := by positivity
    have h1 : ((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S).relIndex S = 1 := by
      have h' : (2 ^ k) ^ 3 * ((MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔
          Q1 L1 L2 S).relIndex S = (2 ^ k) ^ 3 * 1 := by rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos h'
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
  have hQ2D : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      Q2 L1 L2 S ≤ (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
    intro h hh hhB
    have e := sup_inf_eq_sup_inf_of_le_normalizer (R := Q2 L1 L2 S)
      (inf_le_right : (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ≤ Q2 L1 L2 S)
      ((inf_le_right.trans hQ2S).trans hSQ1)
    rw [hDS h hh hhB, inf_eq_right.mpr hQ2S] at e
    exact e.le
  obtain ⟨h, hh, hhB⟩ := str86_exists_mem_p2_not_mem_bigB hF hn hL2
  have hSQ2 : ¬ S ≤ Q2 L1 L2 S := by
    intro hle
    have h' := str86_relIndex_q2_s hF.toW hSB hn hL2
    rw [Subgroup.relIndex_eq_one.mpr hle] at h'
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨s, hs, hsQ2⟩ := Set.not_subset.mp hSQ2
  set h' := s * h with hh'def
  have hh' : h' ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem (hBP2 (hSB' hs)) hh
  have hh'B : h' ∉ bigB L1 L2 S := by
    intro hc
    apply hhB
    have e : h = s⁻¹ * h' := by rw [hh'def]; group
    rw [e]
    exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem (hSB' hs)) hc
  have hg : h'⁻¹ * h ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hh') hh
  have hgB : h'⁻¹ * h ∉ bigB L1 L2 S := by
    intro hc
    apply hsQ2
    have hsinv : s⁻¹ ∈ S ⊓ (MulAut.conj h • bigB L1 L2 S) := by
      refine Subgroup.mem_inf.mpr ⟨S.inv_mem hs, ?_⟩
      rw [mem_conj_smul_iff']
      have e : h⁻¹ * s⁻¹ * h = h'⁻¹ * h := by rw [hh'def]; group
      rw [e]
      exact hc
    have h2 := str86_s_inf_conj_bigB_le_q2 hF hSB hn hL2 hh hhB hsinv
    simpa using (Q2 L1 L2 S).inv_mem h2
  have hAC : (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊓
      ((MulAut.conj h' • Q1 L1 L2 S) ⊓ Q2 L1 L2 S) ≤ str86Core L1 L2 S := by
    intro x hx
    obtain ⟨hxA, hxA'⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hx1, -⟩ := Subgroup.mem_inf.mp hxA
    obtain ⟨hx2, -⟩ := Subgroup.mem_inf.mp hxA'
    rw [mem_conj_smul_iff'] at hx1 hx2
    have hy : h'⁻¹ * x * h' ∈ Q1 L1 L2 S ⊓ (MulAut.conj (h'⁻¹ * h) • Q1 L1 L2 S) := by
      refine Subgroup.mem_inf.mpr ⟨hx2, ?_⟩
      rw [mem_conj_smul_iff']
      have e : (h'⁻¹ * h)⁻¹ * (h'⁻¹ * x * h') * (h'⁻¹ * h) = h⁻¹ * x * h := by group
      rw [e]
      exact hx1
    rw [hcore _ hg hgB] at hy
    have h3 := (Subgroup.mem_normalizer_iff.mp (hKP2 hh') _).mp hy
    have e : h' * (h'⁻¹ * x * h') * h'⁻¹ = x := by group
    rwa [e] at h3
  have hAB : (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊓ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ≤
      str86Core L1 L2 S := by
    rw [← hcore h hh hhB]
    exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left)
  have hNinf : Q2 L1 L2 S ≤
      Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hSQ1 (hQ2S hx)) y,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y]
  have hcomm := commutator_le_of_le_sup_of_inf_le (N := Q2 L1 L2 S)
    (A := (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S) (B := Q1 L1 L2 S ⊓ Q2 L1 L2 S)
    (C := (MulAut.conj h' • Q1 L1 L2 S) ⊓ Q2 L1 L2 S) (K := str86Core L1 L2 S)
    inf_le_right inf_le_right inf_le_right (str86_q2_le_normalizer_D hh hQ2S) hNinf
    (str86_q2_le_normalizer_D hh' hQ2S) ((pCoreOf_le 2 (P2 L1 L2 S)).trans hKP2) hAB hAC
    (inf_le_right.trans ((hQ2D h' hh' hh'B).trans (le_of_eq (sup_comm _ _))))
  have hle := commutator_sup_le_of_commutator_le
    (D := (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S) (Q := Q1 L1 L2 S)
    ((inf_le_right.trans hQ2S).trans hSQ1) (hcomm.trans (str86Core_le_q1 L1 L2 S))
  rw [hDS h hh hhB] at hle
  exact str86_not_commutator_le_q1 hF hSB hk hFc hU3 hle

end CFSG.Quasithin.Stroth

end
