module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.LieType.Chevalley.BorelStructure

public noncomputable section

namespace CFSG.Quasithin.F112R.St84.G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

@[expose] def dT (s t : Kˣ) : ModGL Tag.G2 K :=
  torusElt Tag.G2 K g2ia (s ^ 2 * t ^ 3) * torusElt Tag.G2 K g2ir (s * t ^ 2)

private theorem univ_eq_pair : (Finset.univ : Finset (Fin Tag.G2.rank)) = {g2ia, g2ir} := by
  decide

private theorem sum_cartan_ia (γ : Fin Tag.G2.rank → ℤ) :
    ∑ j, Tag.G2.cartan g2ia j * γ j = 2 * γ g2ia - γ g2ir := by
  rw [univ_eq_pair, Finset.sum_pair (by decide)]
  rw [show Tag.G2.cartan g2ia g2ia = 2 by decide, show Tag.G2.cartan g2ia g2ir = -1 by decide]
  ring

private theorem sum_cartan_ir (γ : Fin Tag.G2.rank → ℤ) :
    ∑ j, Tag.G2.cartan g2ir j * γ j = -3 * γ g2ia + 2 * γ g2ir := by
  rw [univ_eq_pair, Finset.sum_pair (by decide)]
  rw [show Tag.G2.cartan g2ir g2ia = -3 by decide, show Tag.G2.cartan g2ir g2ir = 2 by decide]

private theorem units_char (s t : Kˣ) (m n : ℤ) :
    (s ^ 2 * t ^ 3) ^ (2 * m - n) * (s * t ^ 2) ^ (-3 * m + 2 * n) = s ^ m * t ^ n := by
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 2 <;> push_cast <;> ring

theorem dT_conj_pinnedX {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (s t : Kˣ) (c : K) :
    dT s t * X γ c * (dT s t)⁻¹ = X γ (((s ^ γ g2ia * t ^ γ g2ir : Kˣ) : K) * c) := by
  have h1 := root_torus_conjugation (τ := Tag.G2) (R := K) g2ir hγ (s * t ^ 2) c
  have h2 := root_torus_conjugation (τ := Tag.G2) (R := K) g2ia hγ (s ^ 2 * t ^ 3)
    ((((s * t ^ 2) ^ (∑ j, Tag.G2.cartan g2ir j * γ j) : Kˣ) : K) * c)
  rw [sum_cartan_ir] at h1 h2
  rw [sum_cartan_ia] at h2
  calc dT s t * X γ c * (dT s t)⁻¹
      = torusElt Tag.G2 K g2ia (s ^ 2 * t ^ 3) *
          (torusElt Tag.G2 K g2ir (s * t ^ 2) * X γ c * (torusElt Tag.G2 K g2ir (s * t ^ 2))⁻¹) *
          (torusElt Tag.G2 K g2ia (s ^ 2 * t ^ 3))⁻¹ := by
        simp only [dT, mul_inv_rev, mul_assoc]
    _ = X γ (((s ^ γ g2ia * t ^ γ g2ir : Kˣ) : K) * c) := by
        rw [h1, h2, ← mul_assoc, ← Units.val_mul, units_char]

theorem dT_conj_r (s t : Kˣ) (c : K) :
    dT s t * X g2r c * (dT s t)⁻¹ = X g2r ((t : K) * c) := by
  rw [dT_conj_pinnedX isRoot_g2r, show g2r g2ia = 0 by decide, show g2r g2ir = 1 by decide, zpow_zero, zpow_one, one_mul]

theorem dT_conj_a (s t : Kˣ) (c : K) :
    dT s t * X g2a c * (dT s t)⁻¹ = X g2a ((s : K) * c) := by
  rw [dT_conj_pinnedX isRoot_g2a, show g2a g2ia = 1 by decide, show g2a g2ir = 0 by decide, zpow_zero, zpow_one, mul_one]

theorem dT_conj_u (s t : Kˣ) (c : K) :
    dT s t * X g2u c * (dT s t)⁻¹ = X g2u ((s : K) * t * c) := by
  rw [dT_conj_pinnedX isRoot_g2u, show g2u g2ia = 1 by decide, show g2u g2ir = 1 by decide, zpow_one, zpow_one,
    Units.val_mul]

theorem dT_conj_v (s t : Kˣ) (c : K) :
    dT s t * X g2v c * (dT s t)⁻¹ = X g2v ((s : K) * t ^ 2 * c) := by
  rw [dT_conj_pinnedX isRoot_g2v, show g2v g2ia = 1 by decide, show g2v g2ir = 2 by decide, zpow_one,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]

theorem dT_conj_b (s t : Kˣ) (c : K) :
    dT s t * X g2b c * (dT s t)⁻¹ = X g2b ((s : K) * t ^ 3 * c) := by
  rw [dT_conj_pinnedX isRoot_g2b, show g2b g2ia = 1 by decide, show g2b g2ir = 3 by decide, zpow_one,
    show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]

theorem dT_conj_c (s t : Kˣ) (c : K) :
    dT s t * X g2c c * (dT s t)⁻¹ = X g2c ((s : K) ^ 2 * t ^ 3 * c) := by
  rw [dT_conj_pinnedX isRoot_g2c, show g2c g2ia = 2 by decide, show g2c g2ir = 3 by decide,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
    zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

theorem dT_mul (s t s' t' : Kˣ) : dT s t * dT s' t' = dT (s * s') (t * t') := by
  simp only [dT]
  rw [mul_assoc, ← mul_assoc (torusElt Tag.G2 K g2ir (s * t ^ 2)),
    torusElt_mul_comm g2ir g2ia, mul_assoc, ← mul_assoc, ← torusElt_mul, ← torusElt_mul]
  congr 2
  · rw [mul_pow, mul_pow, mul_mul_mul_comm]
  · rw [mul_pow, mul_mul_mul_comm]

theorem dT_one : dT (1 : Kˣ) 1 = 1 := by
  simp only [dT, one_pow, mul_one, torusElt_one]

theorem dT_inv (s t : Kˣ) : (dT s t)⁻¹ = dT s⁻¹ t⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, dT_mul, inv_mul_cancel, inv_mul_cancel, dT_one]

theorem dT_mem_adjointGroup (s t : Kˣ) : dT s t ∈ adjointGroup Tag.G2 K :=
  mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)

theorem dT_mem_torusGroup (s t : Kˣ) : dT s t ∈ torusGroup Tag.G2 K :=
  mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem torusElt_ia_eq_dT (x : Kˣ) : torusElt Tag.G2 K g2ia x = dT (x ^ 2) x⁻¹ := by
  simp only [dT]
  rw [show (x ^ 2) ^ 2 * x⁻¹ ^ 3 = x by group, show x ^ 2 * x⁻¹ ^ 2 = 1 by group, torusElt_one,
    mul_one]

theorem torusElt_ir_eq_dT (y : Kˣ) : torusElt Tag.G2 K g2ir y = dT (y⁻¹ ^ 3) (y ^ 2) := by
  simp only [dT]
  rw [show (y⁻¹ ^ 3) ^ 2 * (y ^ 2) ^ 3 = 1 by group, show y⁻¹ ^ 3 * (y ^ 2) ^ 2 = y by group,
    torusElt_one, one_mul]

theorem mem_torusGroup_iff {h : ModGL Tag.G2 K} :
    h ∈ torusGroup Tag.G2 K ↔ ∃ s t : Kˣ, dT s t = h := by
  constructor
  · intro hh
    rw [torusGroup] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨i, y⟩, rfl⟩ := hx
      have hi : i = g2ia ∨ i = g2ir := by
        revert i
        decide
      rcases hi with rfl | rfl
      · exact ⟨y ^ 2, y⁻¹, (torusElt_ia_eq_dT y).symm⟩
      · exact ⟨y⁻¹ ^ 3, y ^ 2, (torusElt_ir_eq_dT y).symm⟩
    | one => exact ⟨1, 1, dT_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, t, rfl⟩ := hx
      obtain ⟨s', t', rfl⟩ := hy
      exact ⟨s * s', t * t', (dT_mul s t s' t').symm⟩
    | inv x _ hx =>
      obtain ⟨s, t, rfl⟩ := hx
      exact ⟨s⁻¹, t⁻¹, (dT_inv s t).symm⟩
  · rintro ⟨s, t, rfl⟩
    exact dT_mem_torusGroup s t

theorem dT_conj_g2N (s t : Kˣ) (A B C D E F : K) :
    dT s t * g2N A B C D E F * (dT s t)⁻¹ =
      g2N ((t : K) * A) ((s : K) * B) ((s : K) * t * C) ((s : K) * t ^ 2 * D)
        ((s : K) * t ^ 3 * E) ((s : K) ^ 2 * t ^ 3 * F) := by
  change MulAut.conj (dT s t) (g2N A B C D E F) = _
  simp only [g2N, map_mul]
  simp only [MulAut.conj_apply, dT_conj_r, dT_conj_a, dT_conj_u, dT_conj_v, dT_conj_b,
    dT_conj_c]

theorem dT_injective {s t s' t' : Kˣ} (h : dT s t = dT s' t') : s = s' ∧ t = t' := by
  have hr := dT_conj_r s t 1
  have ha := dT_conj_a s t 1
  rw [h, dT_conj_r, pinnedX_r_eq_g2N, pinnedX_r_eq_g2N] at hr
  rw [h, dT_conj_a, pinnedX_a_eq_g2N, pinnedX_a_eq_g2N] at ha
  have e1 := (g2N_injective ha).2.1
  have e2 := (g2N_injective hr).1
  rw [mul_one, mul_one] at e1 e2
  exact ⟨(Units.ext e1).symm, (Units.ext e2).symm⟩

theorem dT_eq_one_iff {s t : Kˣ} : dT s t = 1 ↔ s = 1 ∧ t = 1 := by
  constructor
  · intro h
    rw [← dT_one] at h
    exact dT_injective h
  · rintro ⟨rfl, rfl⟩
    exact dT_one

theorem dT_comm_g2N_iff (s t : Kˣ) (A B C D E F : K) :
    dT s t * g2N A B C D E F = g2N A B C D E F * dT s t ↔
      (t : K) * A = A ∧ (s : K) * B = B ∧ (s : K) * t * C = C ∧ (s : K) * t ^ 2 * D = D ∧
        (s : K) * t ^ 3 * E = E ∧ (s : K) ^ 2 * t ^ 3 * F = F := by
  rw [← mul_inv_eq_iff_eq_mul, dT_conj_g2N]
  constructor
  · exact g2N_injective
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [h1, h2, h3, h4, h5, h6]

end CFSG.Quasithin.F112R.St84.G2q

end
