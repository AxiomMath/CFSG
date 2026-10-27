module

public import CFSG.Timmesfeld.Transvection.ModelSURadical
public import CFSG.LinearAlgebra.UnipotentRadicalComm
import CFSG.Timmesfeld.Transvection.ModelSUTransMul
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LinearAlgebra

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

variable (F m) in
@[expose] def lowSpan : Submodule F (Fin m → F) where
  carrier := {x | ∀ j : Fin m, m / 2 ≤ j.val → x j = 0}
  add_mem' := fun hx hy j hj => by rw [Pi.add_apply, hx j hj, hy j hj, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c x hx j hj => by rw [Pi.smul_apply, hx j hj, smul_zero]

theorem mem_lowSpan {x : Fin m → F} :
    x ∈ lowSpan F m ↔ ∀ j : Fin m, m / 2 ≤ j.val → x j = 0 :=
  Iff.rfl

theorem single_lowIdx_mem_lowSpan (a : Fin (m / 2)) :
    (Pi.single (lowIdx a) 1 : Fin m → F) ∈ lowSpan F m := by
  rw [mem_lowSpan]
  intro j hj
  rw [Pi.single_apply, if_neg]
  intro h
  have := congrArg Fin.val h
  simp only [lowIdx, Fin.val_mk] at this
  omega

theorem eq_sum_of_mem_lowSpan {x : Fin m → F} (hx : x ∈ lowSpan F m) :
    x = ∑ a : Fin (m / 2), x (lowIdx a) • Pi.single (lowIdx a) 1 := by
  funext j
  rw [Fintype.sum_apply]
  symm
  by_cases hj : j.val < m / 2
  · refine (Finset.sum_eq_single
      (f := fun a : Fin (m / 2) => (x (lowIdx a) • Pi.single (lowIdx a) 1 : Fin m → F) j)
      ⟨j.val, hj⟩ ?_ ?_).trans ?_
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
      intro h
      have hval : b.val = j.val := by
        have := congrArg Fin.val h
        simp only [lowIdx, Fin.val_mk] at this
        omega
      exact hb (Fin.ext hval)
    · intro h
      exact absurd (Finset.mem_univ _) h
    · rw [Pi.smul_apply, Pi.single_apply,
        if_pos (show j = lowIdx (⟨j.val, hj⟩ : Fin (m / 2)) from Fin.ext rfl)]
      rw [smul_eq_mul, mul_one,
        show lowIdx (⟨j.val, hj⟩ : Fin (m / 2)) = j from Fin.ext rfl]
  · rw [mem_lowSpan.1 hx j (by omega)]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [lowIdx, Fin.val_mk] at this
    omega

theorem uForm_eq_zero_of_mem_lowSpan {x y : Fin m → F} (hx : x ∈ lowSpan F m)
    (hy : y ∈ lowSpan F m) : uForm σ x y = 0 := by
  rw [uForm_eq]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m / 2 ≤ j.val
  · rw [hx j hj, map_zero, zero_mul]
  · rw [hy (Fin.rev j) (by simp only [Fin.val_rev]; omega), mul_zero]

private theorem eq_zero_of_uForm_self_eq_zero_of_rev_eq {x : Fin m → F}
    (hxx : uForm σ x x = 0) (h : ∀ a : Fin (m / 2), x (Fin.rev (lowIdx a)) = 0)
    {j : Fin m} (hjj : j = Fin.rev j) : x j = 0 := by
  have hterm : ∀ i : Fin m, i ≠ j → σ (x i) * x (Fin.rev i) = 0 := by
    intro i hi
    rcases eq_or_ne i (Fin.rev i) with hii | hii
    · have hi2 : i.val = m / 2 := by
        have := congrArg Fin.val hii
        simp only [Fin.val_rev] at this
        omega
      have hj2 : j.val = m / 2 := by
        have := congrArg Fin.val hjj
        simp only [Fin.val_rev] at this
        omega
      exact absurd (Fin.ext (by omega)) hi
    · obtain ⟨a, ha | ha⟩ := exists_lowIdx hii
      · rw [ha, h a, mul_zero]
      · rw [ha, h a, map_zero, zero_mul]
  rw [uForm_eq, Finset.sum_eq_single j (fun i _ hi => hterm i hi)
    (fun hc => absurd (Finset.mem_univ _) hc)] at hxx
  rcases mul_eq_zero.mp hxx with h1 | h1
  · exact (map_eq_zero σ).1 h1
  · rw [hjj]
    exact h1

theorem mem_lowSpan_of_apply_rev_eq_zero {x : Fin m → F} (hxx : uForm σ x x = 0)
    (h : ∀ a : Fin (m / 2), x (Fin.rev (lowIdx a)) = 0) : x ∈ lowSpan F m := by
  rw [mem_lowSpan]
  intro j hj
  by_cases hjj : j = Fin.rev j
  · exact eq_zero_of_uForm_self_eq_zero_of_rev_eq hxx h hjj
  · obtain ⟨a, ha | ha⟩ := exists_lowIdx hjj
    · rw [ha] at hj
      simp only [lowIdx, Fin.val_mk] at hj
      omega
    · rw [ha, h a]

theorem mem_lowSpan_of_forall_uForm_single_eq_zero {x : Fin m → F}
    (hxx : uForm σ x x = 0)
    (h : ∀ a : Fin (m / 2), uForm σ x (Pi.single (lowIdx a) 1) = 0) :
    x ∈ lowSpan F m := by
  refine mem_lowSpan_of_apply_rev_eq_zero hxx fun a => ?_
  have := h a
  rw [uForm_single_right] at this
  exact (map_eq_zero σ).1 this

variable (σ m) in
@[expose] def lowRad : Subgroup (SU σ m) := (unipotentRadical (lowSpan F m)).subgroupOf (SU σ m)

theorem mem_lowRad {g : SU σ m} : g ∈ lowRad σ m ↔
    (∀ x, suMat σ m g *ᵥ x - x ∈ lowSpan F m) ∧ ∀ x ∈ lowSpan F m, suMat σ m g *ᵥ x = x :=
  Iff.rfl

theorem commute_of_mem_lowRad {g h : SU σ m} (hg : g ∈ lowRad σ m) (hh : h ∈ lowRad σ m) :
    g * h = h * g :=
  Subtype.ext (commute_of_mem_unipotentRadical hg hh)

instance instIsMulCommutativeLowRad : IsMulCommutative (lowRad σ m) :=
  ⟨⟨fun g h => Subtype.ext (commute_of_mem_lowRad g.2 h.2)⟩⟩

theorem mul_self_eq_one_of_mem_lowRad [CharP F 2] {g : SU σ m} (hg : g ∈ lowRad σ m) :
    g * g = 1 :=
  Subtype.ext (mul_self_eq_one_of_mem_unipotentRadical hg)

theorem isPGroup_lowRad [CharP F 2] : IsPGroup 2 (lowRad σ m) :=
  (isPGroup_unipotentRadical (lowSpan F m)).comap_subtype

theorem le_lowRad_of_isUTransGroup {v : Fin m → F} (hv : v ∈ lowSpan F m)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ v T) : T ≤ lowRad σ m := by
  intro x hx
  obtain ⟨c, -, hx⟩ := (hT.1 x).1 hx
  rw [mem_lowRad]
  constructor
  · intro y
    rw [hx, uTrans_mulVec]
    have : y + (c * uForm σ v y) • v - y = (c * uForm σ v y) • v := by abel
    rw [this]
    exact (lowSpan F m).smul_mem _ hv
  · intro y hy
    rw [hx, uTrans_mulVec, uForm_eq_zero_of_mem_lowSpan hv hy, mul_zero, zero_smul, add_zero]

theorem mem_lowRad_of_forall_sub_mem {g : SU σ m}
    (h : ∀ x, suMat σ m g *ᵥ x - x ∈ lowSpan F m) : g ∈ lowRad σ m := by
  rw [mem_lowRad]
  refine ⟨h, fun u hu => ?_⟩
  have hzero : ∀ z, uForm σ z (suMat σ m g *ᵥ u - u) = 0 := by
    intro z
    obtain ⟨y, rfl⟩ : ∃ y, suMat σ m g *ᵥ y = z :=
      ⟨suMat σ m g⁻¹ *ᵥ z, suMat_mulVec_suMat_inv_mulVec g z⟩
    have h1 : uForm σ (suMat σ m g *ᵥ y) (suMat σ m g *ᵥ u - u) =
        -uForm σ (suMat σ m g *ᵥ y - y) u := by
      rw [uForm_sub_right, uForm_mulVec, uForm_sub_left]
      ring
    rw [h1, uForm_eq_zero_of_mem_lowSpan (h y) hu, neg_zero]
  have hz : suMat σ m g *ᵥ u - u = 0 := by
    funext i
    obtain ⟨z, rfl⟩ := Fin.rev_surjective i
    have hzi := hzero (Pi.single z 1)
    rwa [uForm_single_left] at hzi
  exact sub_eq_zero.mp hz

theorem suMat_mulVec_mem_lowSpan_of_mem_normalizer [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {g : SU σ m} (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    {x : Fin m → F} (hx : x ∈ lowSpan F m) : suMat σ m g *ᵥ x ∈ lowSpan F m := by
  have hsingle : ∀ a : Fin (m / 2),
      suMat σ m g *ᵥ (Pi.single (lowIdx a) 1 : Fin m → F) ∈ lowSpan F m := by
    intro a
    set e : Fin m → F := Pi.single (lowIdx a) 1 with he
    have hee : uForm σ e e = 0 := uForm_single_self (lowIdx_ne_rev a a)
    obtain ⟨T, hT⟩ := exists_isUTransGroup hσ hee
    obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans (σ := σ) hσ hee
      (by rw [map_one, CharTwo.add_self_eq_zero])
    have htT : t ∈ T := (hT.1 t).2 ⟨1, by rw [map_one, CharTwo.add_self_eq_zero], ht⟩
    have htQ : t ∈ lowRad σ m :=
      le_lowRad_of_isUTransGroup (single_lowIdx_mem_lowSpan a) hT htT
    have hconj : g * t * g⁻¹ ∈ lowRad σ m := (Subgroup.mem_normalizer_iff.mp hg t).1 htQ
    set y : Fin m → F := Pi.single (Fin.rev (lowIdx a)) 1 with hy
    have hty : suMat σ m t *ᵥ y = y + e := by
      rw [ht, uTrans_mulVec, he, hy, uForm_single_left, Pi.single_eq_same]
      rw [one_mul, one_smul, add_comm]
    have heq : e = suMat σ m t *ᵥ y - y := by rw [hty]; abel
    have hsub := (mem_lowRad.mp hconj).1 (suMat σ m g *ᵥ y)
    convert hsub using 1
    rw [heq, Matrix.mulVec_sub]
    rw [show suMat σ m g *ᵥ (suMat σ m t *ᵥ y) = suMat σ m (g * t) *ᵥ y by
      rw [map_mul, Matrix.mulVec_mulVec]]
    have hkey : suMat σ m (g * t * g⁻¹) *ᵥ (suMat σ m g *ᵥ y) = suMat σ m (g * t) *ᵥ y := by
      conv_lhs => rw [map_mul, map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← map_mul,
        ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]
    rw [hkey]
  rw [eq_sum_of_mem_lowSpan hx, Matrix.mulVec_sum]
  refine (lowSpan F m).sum_mem fun a _ => ?_
  rw [Matrix.mulVec_smul]
  exact (lowSpan F m).smul_mem _ (hsingle a)

theorem mem_lowSpan_of_isPGroup_of_lowRad_le [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {P : Subgroup (SU σ m)} (hP : IsPGroup 2 P) (hRP : lowRad σ m ≤ P) {v : Fin m → F}
    (hvv : uForm σ v v = 0) {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ v T) (hTP : T ≤ P) :
    v ∈ lowSpan F m := by
  by_contra hv
  obtain ⟨a, ha⟩ : ∃ a : Fin (m / 2), v (Fin.rev (lowIdx a)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (mem_lowSpan_of_apply_rev_eq_zero hvv h)
  have hee : uForm σ (Pi.single (lowIdx a) 1 : Fin m → F) (Pi.single (lowIdx a) 1) = 0 :=
    uForm_single_self (lowIdx_ne_rev a a)
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨Te, hTe⟩ := exists_isUTransGroup hσ hee
  obtain ⟨te, hte⟩ := exists_suMat_eq_uTrans (σ := σ) hσ hee h1
  obtain ⟨tv, htv⟩ := exists_suMat_eq_uTrans (σ := σ) hσ hvv h1
  have hteP : te ∈ P := hRP (le_lowRad_of_isUTransGroup (single_lowIdx_mem_lowSpan a) hTe
    ((hTe.1 te).2 ⟨1, h1, hte⟩))
  have htvP : tv ∈ P := hTP ((hT.1 tv).2 ⟨1, h1, htv⟩)
  obtain ⟨k, hk⟩ := hP ⟨te * tv, P.mul_mem hteP htvP⟩
  have hk' : (te * tv) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hne : uForm σ (Pi.single (lowIdx a) 1 : Fin m → F) v ≠ 0 := by
    rwa [uForm_single_left]
  have hmat : suMat σ m (te * tv) =
      uTrans σ (Pi.single (lowIdx a) 1 : Fin m → F) 1 * uTrans σ v 1 := by
    rw [map_mul, hte, htv]
  exact (ne_one_pow_two_pow_of_uTrans_mul hσ hee hvv hne one_ne_zero one_ne_zero hmat k) hk'

end ModelRank

end CFSG.Timmesfeld.Transvection
