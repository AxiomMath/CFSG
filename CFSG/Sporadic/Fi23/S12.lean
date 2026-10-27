module

public import CFSG.Sporadic.Fi23.S12Cert
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_of_rep_eq
    {T : Table} {g h : J} (hg : Rep 31671 T g) (hh : Rep 31671 T h) : g = h := by
  have key : h⁻¹ * g = 1 := by
    apply eq_one_of_fix_all
    intro i
    have e1 := hg i.val i.isLt
    have e2 := hh i.val i.isLt
    rw [idx_of_lt _ i.isLt] at e1 e2
    have e3 : g • i = h • i := Fin.ext (e1.symm.trans e2)
    rw [mul_smul, e3, inv_smul_smul]
  exact (inv_mul_eq_one.1 key).symm

theorem sq_eq_one_of_invoOK {T : Table} {u : J} (hT : Rep 31671 T u)
    (h : invoOK 31671 T = true) : u ^ 2 = 1 := by
  apply eq_one_of_fix_all
  intro i
  apply Fin.ext
  have := idx_sq_of_invoOK hT h i.val i.isLt
  rw [idx_of_lt _ i.isLt] at this
  exact this

theorem isConj_t2_of_fixCount
    {T : Table} {u : J} (hT : Rep 31671 T u) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (h : fixCount T = 183) : IsConj t2 u := by
  have hfix : Nat.card {z : D23 // u * z * u⁻¹ = z} = 183 := by rw [card_fixed_eq hT, h]
  rcases involution_cover u hu2 hu1 with h2 | h2 | h2
  · have := card_fixed_conj h2
    rw [card_fixed_d, hfix] at this
    exact absurd this (by norm_num)
  · have := card_fixed_conj h2
    rw [card_fixed_d_mul_d1, hfix] at this
    exact absurd this (by norm_num)
  · exact h2

theorem isConj_d_mul_d1_of_fixCount
    {T : Table} {u : J} (hT : Rep 31671 T u) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (h : fixCount T = 695) : IsConj (d * d1) u := by
  have hfix : Nat.card {z : D23 // u * z * u⁻¹ = z} = 695 := by rw [card_fixed_eq hT, h]
  rcases involution_cover u hu2 hu1 with h2 | h2 | h2
  · have := card_fixed_conj h2
    rw [card_fixed_d, hfix] at this
    exact absurd this (by norm_num)
  · exact h2
  · have := card_fixed_conj h2
    rw [card_fixed_t2, hfix] at this
    exact absurd this (by norm_num)

@[expose] noncomputable def sEl (i : ℕ) : J := conjPt s12Pts[i]!

theorem rep_sEl
    (i : ℕ) : Rep 31671 (s12Tab orb i) (sEl i) := rep_ptT s12Pts[i]!

theorem s12_parts :
    (∀ i < 11, s12Pts[i]! < 31671) ∧ (∀ i < 10, s12Braid orb i = true) ∧
      (∀ i < 11, ∀ j < 11, i + 2 ≤ j → s12Comm orb i j = true) ∧
      (invoOK 31671 (s12P4 orb) = true ∧ isIdT (s12P4 orb) = false ∧
        fixCount (s12P4 orb) = 183) ∧
      (invoOK 31671 (s12P6 orb) = true ∧ isIdT (s12P6 orb) = false ∧
        fixCount (s12P6 orb) = 695) := by
  have h : s12Checks orb = true := s12_certificate
  unfold s12Checks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩⟩
  · simpa using (allIn_eq_true.1 h1) i (Nat.zero_le _) hi
  · exact (allIn_eq_true.1 h2) i (Nat.zero_le _) hi
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h3) i (Nat.zero_le _) hi)) j (Nat.zero_le _) hj
    simpa [Nat.not_lt.2 hij] using this

theorem s12Pts_lt
    {i : ℕ} (hi : i < 11) : s12Pts[i]! < 31671 := s12_parts.1 i hi

theorem sEl_mem
    {i : ℕ} (hi : i < 11) : sEl i ∈ D23 :=
  (isConj_d_iff _).2 ⟨⟨s12Pts[i]!, s12Pts_lt hi⟩, rfl⟩

theorem sEl_sq
    {i : ℕ} (hi : i < 11) : sEl i * sEl i = 1 := by
  rw [← pow_two]
  exact conjPt_sq (s12Pts_lt hi)

theorem sEl_braid
    {i : ℕ} (hi : i + 1 < 11) :
    sEl i * sEl (i + 1) * sEl i = sEl (i + 1) * sEl i * sEl (i + 1) := by
  have h := s12_parts.2.1 i (by omega)
  unfold s12Braid at h
  rw [beq_iff_eq] at h
  have h2 : Rep 31671 (compT 31671 (compT 31671 (s12Tab orb i) (s12Tab orb (i + 1)))
      (s12Tab orb i)) (sEl (i + 1) * sEl i * sEl (i + 1)) := by
    rw [h]
    exact Rep.compT (Rep.compT (rep_sEl _) (rep_sEl _)) (rep_sEl _)
  exact eq_of_rep_eq (Rep.compT (Rep.compT (rep_sEl _) (rep_sEl _)) (rep_sEl _)) h2

theorem sEl_comm
    {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < 11) : sEl i * sEl j = sEl j * sEl i := by
  have h := s12_parts.2.2.1 i (by omega) j hj hij
  unfold s12Comm at h
  rw [beq_iff_eq] at h
  have h2 : Rep 31671 (compT 31671 (s12Tab orb i) (s12Tab orb j)) (sEl j * sEl i) := by
    rw [h]
    exact Rep.compT (rep_sEl _) (rep_sEl _)
  exact eq_of_rep_eq (Rep.compT (rep_sEl _) (rep_sEl _)) h2

theorem sEl_zero_ne_two :
    sEl 0 ≠ sEl 2 := by
  intro h
  have := conjPt_inj (by rw [orb_size]; exact s12Pts_lt (by norm_num))
    (by rw [orb_size]; exact s12Pts_lt (by norm_num)) h
  revert this
  decide

theorem sEl_zero_mul_two_ne_one :
    sEl 0 * sEl 2 ≠ 1 := by
  intro h
  apply sEl_zero_ne_two
  have h2 : sEl 2 * sEl 2 = 1 := sEl_sq (by norm_num)
  exact mul_right_cancel (h.trans h2.symm)

theorem isCoxeterA_sEl :
    CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 11 sEl :=
  ⟨fun _ hi => sEl_sq hi, fun _ hi => sEl_braid hi, fun _ _ hij hj => sEl_comm hij hj⟩

theorem exists_hom_s12 :
    ∃ ψ : Equiv.Perm (Fin 12) →* J,
    ∀ i, i < 11 → ψ (CFSG.Permutation.SymmetricCoxeter.adjSwap 11 i) = sEl i :=
  CFSG.Permutation.SymmetricCoxeter.exists_hom_perm 11 sEl isCoxeterA_sEl

theorem isConj_d_mul_d1_s2 :
    IsConj (d * d1) (sEl 0 * sEl 2) :=
  isConj_d_mul_d1_of_mem (sEl_mem (by norm_num))
    ⟨sEl_mem (by norm_num), sEl_zero_ne_two.symm, (sEl_comm (by norm_num) (by norm_num)).symm⟩

theorem rep_P4 :
    Rep 31671 (s12P4 orb) (sEl 0 * sEl 2 * sEl 4 * sEl 6) :=
  Rep.compT (Rep.compT (Rep.compT (rep_sEl 0) (rep_sEl 2)) (rep_sEl 4)) (rep_sEl 6)

theorem rep_P6 :
    Rep 31671 (s12P6 orb) (sEl 0 * sEl 2 * sEl 4 * sEl 6 * sEl 8 * sEl 10) :=
  Rep.compT (Rep.compT rep_P4 (rep_sEl 8)) (rep_sEl 10)

theorem isConj_t2_s4 :
    IsConj t2 (sEl 0 * sEl 2 * sEl 4 * sEl 6) :=
  isConj_t2_of_fixCount rep_P4 (sq_eq_one_of_invoOK rep_P4 s12_parts.2.2.2.1.1)
    (ne_one_of_isIdT rep_P4 s12_parts.2.2.2.1.2.1) s12_parts.2.2.2.1.2.2

theorem isConj_d_mul_d1_s6 :
    IsConj (d * d1) (sEl 0 * sEl 2 * sEl 4 * sEl 6 * sEl 8 * sEl 10) :=
  isConj_d_mul_d1_of_fixCount rep_P6 (sq_eq_one_of_invoOK rep_P6 s12_parts.2.2.2.2.1)
    (ne_one_of_isIdT rep_P6 s12_parts.2.2.2.2.2.1) s12_parts.2.2.2.2.2.2

theorem exists_two_of_isConj_d_mul_d1
    {u : J} (h : IsConj (d * d1) u) :
    ∃ x ∈ D23, ∃ y ∈ D23, x ≠ y ∧ x * y = y * x ∧ u = x * y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hd1 := d1_mem_localClass
  refine ⟨c * d * c⁻¹, conj_mem_D23 c d (IsConj.refl d), c * d1 * c⁻¹,
    conj_mem_D23 c d1 hd1.1, ?_, ?_, ?_⟩
  · intro hxy
    exact hd1.2.1 (mul_left_cancel (mul_right_cancel hxy)).symm
  · have e : d * d1 = d1 * d := hd1.2.2.symm
    calc c * d * c⁻¹ * (c * d1 * c⁻¹) = c * (d * d1) * c⁻¹ := by group
      _ = c * (d1 * d) * c⁻¹ := by rw [e]
      _ = c * d1 * c⁻¹ * (c * d * c⁻¹) := by group
  · rw [← hc]
    group

end CFSG.Sporadic.Fi23
