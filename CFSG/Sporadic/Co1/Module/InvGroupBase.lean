
module

public import CFSG.Sporadic.Co1.Module.InvSpec
public import CFSG.Sporadic.Co1.Module.InvPermChar

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint Matrix

theorem co1Act_mul (g h : NativeSporadic.Co1) (v : Vec24) :
    co1Act (g * h) v = co1Act g (co1Act h v) := by
  simp only [co1Act_eq_mulVec, map_mul, Matrix.mulVec_mulVec]

theorem co1Act_one (v : Vec24) : co1Act 1 v = v := by
  simp [co1Act_eq_mulVec]

@[instance_reducible] noncomputable def vecMulAction :
    MulAction NativeSporadic.Co1 Vec24 where
  smul g v := co1Act g v
  one_smul v := co1Act_one v
  mul_smul g h v := co1Act_mul g h v

attribute [local instance] vecMulAction

theorem smul_eq_co1Act (g : NativeSporadic.Co1) (v : Vec24) : g • v = co1Act g v := rfl

theorem finite_co1 : Finite NativeSporadic.Co1 := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [CFSG.Sporadic.Co1.card_Co1]
  norm_num

theorem card_stabilizer_mul_ncard_orbit (v : Vec24) :
    Nat.card (MulAction.stabilizer NativeSporadic.Co1 v) *
      (MulAction.orbit NativeSporadic.Co1 v).ncard = Nat.card NativeSporadic.Co1 := by
  have h3 := Subgroup.card_mul_index (MulAction.stabilizer NativeSporadic.Co1 v)
  rw [MulAction.index_stabilizer NativeSporadic.Co1 v] at h3
  exact h3

theorem orbit_eq_range (v : Vec24) :
    MulAction.orbit NativeSporadic.Co1 v = Set.range fun g : NativeSporadic.Co1 => co1Act g v :=
  rfl

@[expose] def stabOf (v : Vec24) : Subgroup NativeSporadic.Co1 where
  carrier := {g | co1Act g v = v}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [co1Act_mul, hh, hg]
  one_mem' := co1Act_one v
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    rw [← co1Act_mul, inv_mul_cancel, co1Act_one]

theorem mem_stabOf {g : NativeSporadic.Co1} {v : Vec24} : g ∈ stabOf v ↔ co1Act g v = v := Iff.rfl

theorem card_centralizer_bound {v : Vec24} {N n F : ℕ}
    (hN : (Set.range fun g : NativeSporadic.Co1 => co1Act g v).ncard = N)
    {s : NativeSporadic.Co1} (hs : co1Act s v = v) (f : ℕ → NativeSporadic.Co1)
    (hfinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hf : ∀ i < n, ∃ x : NativeSporadic.Co1, co1Act x v = v ∧ f i = x * s * x⁻¹)
    (hF : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v) | co1Act s w = w}.ncard ≤ F) :
    Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) * n * N ≤
      Nat.card NativeSporadic.Co1 * F := by
  have := finite_co1
  let _ : MulAction NativeSporadic.Co1 Vec24 := vecMulAction
  have hinj : Set.InjOn f (Set.Iio n) := fun i hi j hj e => hfinj i hi j hj e
  set S : Set NativeSporadic.Co1 := f '' Set.Iio n with hS
  have hSn : S.ncard = n := by
    rw [hS, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]
  have hS₁ : ∀ t ∈ S, t ∈ MulAction.stabilizer NativeSporadic.Co1 v := by
    rintro t ⟨i, hi, rfl⟩
    obtain ⟨x, hx, hfx⟩ := hf i hi
    rw [hfx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (MulAction.mem_stabilizer_iff.2 hx)
      (MulAction.mem_stabilizer_iff.2 hs)) (Subgroup.inv_mem _ (MulAction.mem_stabilizer_iff.2 hx))
  have hS₂ : ∀ t ∈ S, IsConj s t := by
    rintro t ⟨i, hi, rfl⟩
    obtain ⟨x, hx, hfx⟩ := hf i hi
    exact isConj_iff.2 ⟨x, hfx.symm⟩
  have h1 := card_centralizer_mul_ncard_le hS₁ hS₂
  rw [hSn] at h1
  have h2 := card_stabilizer_mul_ncard_orbit v
  rw [orbit_eq_range, hN] at h2
  calc Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) * n * N
      ≤ (Nat.card (MulAction.stabilizer NativeSporadic.Co1 v) *
        {w ∈ MulAction.orbit NativeSporadic.Co1 v | s • w = w}.ncard) * N :=
        Nat.mul_le_mul_right _ h1
    _ ≤ (Nat.card (MulAction.stabilizer NativeSporadic.Co1 v) * F) * N :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hF)
    _ = Nat.card NativeSporadic.Co1 * F := by
        rw [← h2]
        ring

theorem co1Act_inv_apply (g : NativeSporadic.Co1) (v : Vec24) : co1Act g⁻¹ (co1Act g v) = v := by
  rw [← co1Act_mul, inv_mul_cancel, co1Act_one]

theorem co1Act_apply_inv (g : NativeSporadic.Co1) (v : Vec24) : co1Act g (co1Act g⁻¹ v) = v := by
  rw [← co1Act_mul, mul_inv_cancel, co1Act_one]

theorem fixSet_conj (x s : NativeSporadic.Co1) :
    {v : Vec24 | co1Act (x * s * x⁻¹) v = v} = (co1Act x) '' {v | co1Act s v = v} := by
  ext v
  constructor
  · intro hv
    refine ⟨co1Act x⁻¹ v, ?_, co1Act_apply_inv x v⟩
    have : co1Act (x * s * x⁻¹) v = co1Act x (co1Act s (co1Act x⁻¹ v)) := by
      rw [co1Act_mul, co1Act_mul]
    have h2 : co1Act x (co1Act s (co1Act x⁻¹ v)) = v := this.symm.trans hv
    have h3 := congrArg (co1Act x⁻¹) h2
    rwa [co1Act_inv_apply] at h3
  · rintro ⟨w, hw, rfl⟩
    show co1Act (x * s * x⁻¹) (co1Act x w) = co1Act x w
    rw [co1Act_mul, co1Act_mul, co1Act_inv_apply]
    have : co1Act s w = w := hw
    rw [this]

theorem co1Act_injective (g : NativeSporadic.Co1) : Function.Injective (co1Act g) := by
  intro a b h
  have := congrArg (co1Act g⁻¹) h
  rwa [co1Act_inv_apply, co1Act_inv_apply] at this

theorem ncard_fix_conj (x s : NativeSporadic.Co1) :
    {v : Vec24 | co1Act (x * s * x⁻¹) v = v}.ncard = {v : Vec24 | co1Act s v = v}.ncard := by
  rw [fixSet_conj, Set.ncard_image_of_injective _ (co1Act_injective x)]

theorem card_centralizer_conj (x s : NativeSporadic.Co1) :
    Nat.card (Subgroup.centralizer ({x * s * x⁻¹} : Set NativeSporadic.Co1)) =
      Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj x).toEquiv (fun c => ?_))).symm
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  show s * c = c * s ↔ x * s * x⁻¹ * (x * c * x⁻¹) = x * c * x⁻¹ * (x * s * x⁻¹)
  constructor
  · intro h
    calc x * s * x⁻¹ * (x * c * x⁻¹) = x * (s * c) * x⁻¹ := by group
      _ = x * (c * s) * x⁻¹ := by rw [h]
      _ = x * c * x⁻¹ * (x * s * x⁻¹) := by group
  · intro h
    have h2 : x * (s * c) * x⁻¹ = x * (c * s) * x⁻¹ := by
      calc x * (s * c) * x⁻¹ = x * s * x⁻¹ * (x * c * x⁻¹) := by group
        _ = x * c * x⁻¹ * (x * s * x⁻¹) := h
        _ = x * (c * s) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

end CFSG.Sporadic.Co1.Module
