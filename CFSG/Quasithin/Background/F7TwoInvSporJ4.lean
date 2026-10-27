module

public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Sporadic.J4.QTRankWitProof
public import CFSG.Sporadic.Schreier.J4SOutOdd
public import Certificates.Certificate7401
public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.ComponentClassification.OuterAutomorphisms

theorem j4_two_pow_ne_one {g : J} {R : Array V2} (hg : Mx g = rowsMatrix R) {s m : ℕ}
    (hm : Odd m) (h1 : eqRows (powRows R (2 ^ s * m)) idRows = true)
    (h2 : eqRows (powRows R (2 ^ s)) idRows = false)
    (hw : wfRows (powRows R (2 ^ s)) = true) (hw' : wfRows idRows = true) :
    ∀ n : ℕ, g ^ 2 ^ n ≠ 1 := by
  refine pow_two_pow_ne_one_of_pow hm (pow_eq_one_of_rows hg h1) fun h => ?_
  have h3 : rowsMatrix (powRows R (2 ^ s)) = rowsMatrix idRows := by
    rw [rowsMatrix_powRows, rowsMatrix_idRows, ← hg, ← map_pow, h, map_one]
  obtain ⟨hs1, hw1⟩ := wfRows_spec hw
  obtain ⟨hs2, hw2⟩ := wfRows_spec hw'
  exact rowsMatrix_ne_of_eqRows_false hs1 hs2 hw1 hw2 h2 h3

section Matrices

variable (hF : J4Facts)
include hF

theorem Mx_j4_b_inv : Mx b⁻¹ = rowsMatrix (gMat 2) := by
  have e : gEl 2 = b⁻¹ := by simp [gEl]
  rw [← e]
  exact (Mx_gEl hF.mat (show 2 < 3 by norm_num)).1

theorem Mx_j4_commEtaA :
    Mx (eta uJ 11 1 * a * (eta uJ 11 1)⁻¹ * a⁻¹) = rowsMatrix (j4CommEtaA ()) := by
  have hM := hF.mat
  rw [inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) 1), a_inv_eq hM]
  simp only [map_mul, Mx_etaR hM, Mx_a hM]
  simp [j4CommEtaA, etaR, rowsMatrix_mulRows]

theorem Mx_j4_commEtaB :
    Mx (eta uJ 11 1 * b * (eta uJ 11 1)⁻¹ * b⁻¹) = rowsMatrix (j4CommEtaB ()) := by
  have hM := hF.mat
  rw [inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) 1)]
  simp only [map_mul, Mx_etaR hM, Mx_b hM, Mx_j4_b_inv hF]
  simp [j4CommEtaB, etaR, rowsMatrix_mulRows]

theorem Mx_j4_commAB : Mx (a * b * a⁻¹ * b⁻¹) = rowsMatrix (j4CommAB ()) := by
  have hM := hF.mat
  rw [a_inv_eq hM]
  simp only [map_mul, Mx_a hM, Mx_b hM, Mx_j4_b_inv hF]
  simp [j4CommAB, rowsMatrix_mulRows]

end Matrices

theorem j4_comm_eta_orders
    (hF : J4Facts) :
    (∀ n : ℕ, (eta uJ 11 1 * a * (eta uJ 11 1)⁻¹ * a⁻¹) ^ 2 ^ n ≠ 1) ∧
    (∀ n : ℕ, (eta uJ 11 1 * b * (eta uJ 11 1)⁻¹ * b⁻¹) ^ 2 ^ n ≠ 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -, hw⟩ := Certificates.certificate7401
  exact ⟨j4_two_pow_ne_one (Mx_j4_commEtaA hF) (s := 0) (m := 5) (by decide) h1 h2 h3 hw,
    j4_two_pow_ne_one (Mx_j4_commEtaB hF) (s := 1) (m := 15) (by decide) h4 h5 h6 hw⟩

theorem j4_comm_ab_orders (hF : J4Facts) :
    ∀ n : ℕ, (a * b * a⁻¹ * b⁻¹) ^ 2 ^ n ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, hw⟩ := Certificates.certificate7401
  exact j4_two_pow_ne_one (Mx_j4_commAB hF) (s := 1) (m := 5) (by decide) h7 h8 h9 hw

theorem j4_invAutGen_of_seeds {r : J}
    (hA : (∀ n : ℕ, (r * a * r⁻¹ * a⁻¹) ^ 2 ^ n ≠ 1) ∨ r * a = a * r)
    (hB : (∀ n : ℕ, (r * b * r⁻¹ * b⁻¹) ^ 2 ^ n ≠ 1) ∨ r * b = b * r)
    (hne : (∀ n : ℕ, (r * a * r⁻¹ * a⁻¹) ^ 2 ^ n ≠ 1) ∨
      ∀ n : ℕ, (r * b * r⁻¹ * b⁻¹) ^ 2 ^ n ≠ 1) :
    InvAutGen J (MulAut.conj r) := by
  refine invAutGen_conj_of_seeds r 1 closure_ab (fun x hx => ?_) ?_
  · simp only [one_mul, inv_one, mul_one]
    rcases hx with rfl | rfl
    · exact hA
    · exact hB
  · simp only [one_mul, inv_one, mul_one]
    rcases hne with h | h
    · exact ⟨a, Set.mem_insert _ _, h⟩
    · exact ⟨b, Set.mem_insert_of_mem _ rfl, h⟩

theorem j4_invAutGen_eta
    (hF : J4Facts) : InvAutGen J (MulAut.conj (eta uJ 11 1)) := by
  obtain ⟨hA, hB⟩ := j4_comm_eta_orders hF
  exact j4_invAutGen_of_seeds (Or.inl hA) (Or.inl hB) (Or.inl hA)

theorem j4_invAutGen_a (hF : J4Facts) :
    InvAutGen J (MulAut.conj a) := by
  have hAB := j4_comm_ab_orders hF
  exact j4_invAutGen_of_seeds (Or.inr rfl) (Or.inl hAB) (Or.inr hAB)

theorem j4_mem_inner_of_odd_outer {G : Type*} [Group G] (hodd : Odd (Nat.card (Outer G)))
    {α : MulAut G} (h2 : α * α = 1) : α ∈ inner G := by
  have hdvd : orderOf (α : Outer G) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [sq, ← QuotientGroup.mk_mul, h2, QuotientGroup.mk_one]
  have hodd' : ¬ 2 ∣ Nat.card (Outer G) := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hodd
  have h1 : orderOf (α : Outer G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exact absurd (h ▸ orderOf_dvd_natCard (α : Outer G)) hodd'
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem invAutGen_J4_J :
    ∀ φ : @MulAut J (Subgroup.toGroup J).toMul, φ * φ = 1 → φ ≠ 1 → InvAutGen J φ := by
  intro φ hφ2 hφ1
  have hF := j4Facts
  have hodd : Odd (Nat.card (Outer J)) :=
    CFSG.Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  obtain ⟨x, rfl⟩ := j4_mem_inner_of_odd_outer hodd hφ2
  have hxx : x * x = 1 := mul_self_eq_one_of_conj_mul_self CFSG.Sporadic.J4Schreier.center_J hφ2
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hφ1 (map_one _)
  rcases inv_conj_root hF hxx hx1 with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact invAutGen_conj_of_conj c hc.symm (j4_invAutGen_eta hF)
  · obtain ⟨c, hc⟩ := isConj_iff.1 ((isConj_eta_three_a hF).symm.trans h)
    exact invAutGen_conj_of_conj c hc.symm (j4_invAutGen_a hF)

theorem invAutGen_carrier_J4 :
    ∀ φ : MulAut (NativeSporadic.Carrier .J4), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .J4) φ :=
  @invAutGen_of_mulEquiv_forall (NativeSporadic.Carrier .J4) J _ (Subgroup.toGroup J)
    (seedEquiv j4Facts.mat) invAutGen_J4_J

end CFSG.Quasithin.F7Two
