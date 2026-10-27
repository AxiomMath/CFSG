
module

public import CFSG.Sporadic.Schreier.J4SKernelBase1

public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import Certificates.Certificate2173
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.LocalAnalysis.ComponentInitial MulAction

theorem H_eq_Hj : H = Hj := by
  have hle : H ≤ Hj := by
    rw [← stabilizer_v_eq_Hj]
    exact H_le_stabilizer_v
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_H, card_Hj j4Facts])

theorem stabilizer_root : stabilizer J vO = H := by
  ext g
  rw [mem_stabilizer_iff, H_eq_Hj, ← stabilizer_v_eq_Hj, mem_stabilizer_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [orbit.coe_smul] at this
  · intro h
    exact Subtype.ext (by rw [orbit.coe_smul]; exact h)

theorem H_isCoatom : IsCoatom H := by
  rw [H_eq_Hj]
  exact j4Facts.coatom

theorem orbit_H_eq_Hj
    (x : Row) : orbit H x = orbit Hj x := by
  rw [H_eq_Hj]

theorem mem_orbit_H_subRep
    {x : Row}
    (hx : x ∈ orbit J v) : ∃ l < 7, x ∈ orbit H (subRep l) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨l, hl, h, hh, h', hh', e⟩ := j4Facts.cosets g
  refine ⟨l, hl, ?_⟩
  rw [orbit_H_eq_Hj]
  refine ⟨⟨h, hh⟩, ?_⟩
  change h • subRep l = g • v
  have hfix : h' • v = v := by rw [v_eq_rootV]; exact Hj_fix_root j4Facts.mat h' hh'
  rw [subRep, e, mul_smul, mul_smul, hfix]

theorem ncard_orbit_H_subRep
    {l : ℕ} (hl : l < 7) :
    (orbit H (subRep l)).ncard = subSizeL l := by
  rw [orbit_H_eq_Hj, subRep, v_eq_rootV]
  exact j4Facts.sizes l hl

theorem orbit_H_eq_of_ncard_row
    {x y : Row}
    (hx : x ∈ orbit J v) (hy : y ∈ orbit J v)
    (h : (orbit H x).ncard = (orbit H y).ncard) : orbit H x = orbit H y := by
  obtain ⟨l, hl, hxl⟩ := mem_orbit_H_subRep hx
  obtain ⟨m, hm, hym⟩ := mem_orbit_H_subRep hy
  rw [orbit_eq_iff.2 hxl, orbit_eq_iff.2 hym] at h ⊢
  rw [ncard_orbit_H_subRep hl, ncard_orbit_H_subRep hm] at h
  have hlm : l = m := by
    interval_cases l <;> interval_cases m <;> first | rfl | (exfalso; simp [subSizeL] at h)
  rw [hlm]

theorem horb_J
    : ∀ d ∈ ({28336, 15180, 82575360} : Set ℕ), ∃ x₀ : Xv,
    (orbit H x₀).ncard = d ∧ ∀ x : Xv, (orbit H x).ncard = d → orbit H x = orbit H x₀ := by
  intro d hd
  obtain ⟨l, hl, rfl⟩ : ∃ l < 7, subSizeL l = d := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨6, by norm_num, rfl⟩
    · exact ⟨5, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  have hq : subRep l ∈ orbit J v := ⟨_, rfl⟩
  refine ⟨⟨subRep l, hq⟩, ?_, fun x hx => ?_⟩
  · rw [ncard_orbit_Xv]
    exact ncard_orbit_H_subRep hl
  · rw [ncard_orbit_Xv] at hx
    refine orbit_Xv_eq H (orbit_H_eq_of_ncard_row x.2 hq ?_)
    rw [hx, ncard_orbit_H_subRep hl]

theorem R3E_J4_pointwise_local_automorphism_kernel_no_large_primes :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ A : Subgroup (pointwiseFixingAut H), IsPGroup p A → A = ⊥) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (pointwiseFixingAut H) → p = 2 ∨ p = 3 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have h := pointwise_kernel_no_large_primes stabilizer_root H_isCoatom N_le_H K_le_H
    conj_mem_N_of_mem_H N_comm (by rw [inf_comm, K_inf_N]) (fun _ hh => exists_mul_of_mem_H hh)
    isPGroup_N (by rw [card_N]; norm_num) card_H horb_J
    (fun k hk ok => (R3E_J4_local_five_elements_fixed_rank_three.2.2.2.2 k hk ok).1)
    (fun k hk ok => card_centralizer_seven hk ok)
    (fun e he f hf oe of hc => not_commute_eleven_twentythree he hf oe of hc)
  exact h

end CFSG.Sporadic.J4Schreier
