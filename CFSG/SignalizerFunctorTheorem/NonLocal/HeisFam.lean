module

public import CFSG.SignalizerFunctorTheorem.NonLocal.PermHeis

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

structure HeisFam (Γ : Type*) [Group Γ] (S : Type*) (P : S → Type*) [∀ s, AddCommGroup (P s)]
    (Zp : Type*) [AddCommGroup Zp] where
  xa : ∀ s, P s → Γ
  xb : ∀ s, P s → Γ
  z : Zp → Γ
  e : ∀ s, P s → P s → Zp
  Rg : AddSubgroup Zp
  z_add : ∀ w w', z (w + w') = z w * z w'
  e_add_left : ∀ s c c' d, e s (c + c') d = e s c d + e s c' d
  e_mem : ∀ s c d, e s c d ∈ Rg
  e_surj : ∀ s (c : P s), c ≠ 0 → ∀ w ∈ Rg, ∃ d, e s c d = w
  xa_comm : ∀ s t c d, xa s c * xa t d = xa t d * xa s c
  xb_comm : ∀ s t c d, xb s c * xb t d = xb t d * xb s c
  z_comm_a : ∀ w s d, z w * xa s d = xa s d * z w
  z_comm_b : ∀ w s d, z w * xb s d = xb s d * z w
  xab_comm : ∀ s t, s ≠ t → ∀ c d, xb s c * xa t d = xa t d * xb s c
  comm_ss : ∀ s c d, ⁅(xb s c)⁻¹, xa s d⁆ = z (e s c d)

namespace HeisFam

variable {Γ : Type*} [Group Γ] {S : Type*} {P : S → Type*} [∀ s, AddCommGroup (P s)]
  {Zp : Type*} [AddCommGroup Zp] (H : HeisFam Γ S P Zp)

theorem z_zero : H.z 0 = 1 := by
  have h := H.z_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem z_neg (w : Zp) : H.z (-w) = (H.z w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← H.z_add, neg_add_cancel, H.z_zero]

theorem z_comm (w w' : Zp) : H.z w * H.z w' = H.z w' * H.z w := by
  rw [← H.z_add, ← H.z_add, add_comm]

@[expose] def Z : Subgroup Γ where
  carrier := {g | ∃ w ∈ H.Rg, H.z w = g}
  mul_mem' := by
    rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
    exact ⟨w + w', add_mem hw hw', H.z_add w w'⟩
  one_mem' := ⟨0, zero_mem _, H.z_zero⟩
  inv_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨-w, neg_mem hw, H.z_neg w⟩

theorem mem_Z {g : Γ} : g ∈ H.Z ↔ ∃ w ∈ H.Rg, H.z w = g := Iff.rfl

theorem z_mem_Z {w : Zp} (hw : w ∈ H.Rg) : H.z w ∈ H.Z := ⟨w, hw, rfl⟩

@[expose] def genA : Set Γ :=
  {g | ∃ w ∈ H.Rg, H.z w = g} ∪ Set.range (fun p : (s : S) × P s => H.xa p.1 p.2)

@[expose] def A : Subgroup Γ := Subgroup.closure H.genA

theorem genA_comm : ∀ x ∈ H.genA, ∀ y ∈ H.genA, x * y = y * x := by
  rintro x (⟨w, hw, rfl⟩ | ⟨⟨s, c⟩, rfl⟩) y (⟨w', hw', rfl⟩ | ⟨⟨t, d⟩, rfl⟩)
  · exact H.z_comm w w'
  · exact H.z_comm_a w t d
  · exact (H.z_comm_a w' s c).symm
  · exact H.xa_comm s t c d

theorem isMulCommutative_A : IsMulCommutative H.A :=
  Subgroup.isMulCommutative_closure fun x hx y hy _ => H.genA_comm x hx y hy

theorem A_comm : ∀ a ∈ H.A, ∀ b ∈ H.A, a * b = b * a := by
  have := H.isMulCommutative_A
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : H.A) ⟨b, hb⟩)

theorem Z_le_A : H.Z ≤ H.A := by
  rintro _ ⟨w, hw, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨w, hw, rfl⟩)

theorem xa_mem_A (s : S) (c : P s) : H.xa s c ∈ H.A :=
  Subgroup.subset_closure (Or.inr ⟨⟨s, c⟩, rfl⟩)

variable [Fintype S] [DecidableEq S]

@[expose] def yElt (c : ∀ s, P s) : Γ :=
  (Finset.univ : Finset S).noncommProd (fun s => H.xb s (c s))
    (fun _ _ _ _ _ => H.xb_comm _ _ _ _)

omit [DecidableEq S] in
theorem yElt_comm_z (c : ∀ s, P s) (w : Zp) : H.yElt c * H.z w = H.z w * H.yElt c := by
  have := Finset.noncommProd_commute (Finset.univ : Finset S) (fun s => H.xb s (c s))
    (fun _ _ _ _ _ => H.xb_comm _ _ _ _) (H.z w) (fun s _ => (H.z_comm_b w s (c s)))
  exact this.symm

theorem comm_yElt_xa (c : ∀ s, P s) (t : S) (d : P t) :
    ⁅(H.yElt c)⁻¹, H.xa t d⁆ = H.z (H.e t (c t) d) := by
  set f : S → Γ := fun s => H.xb s (c s) with hf
  have hcomm : ((Finset.univ : Finset S) : Set S).Pairwise (fun a b => Commute (f a) (f b)) :=
    fun _ _ _ _ _ => H.xb_comm _ _ _ _
  have hcomm' : (((Finset.univ : Finset S).erase t : Finset S) : Set S).Pairwise
      (fun a b => Commute (f a) (f b)) := fun _ _ _ _ _ => H.xb_comm _ _ _ _
  have hy : H.yElt c = f t * (((Finset.univ : Finset S).erase t).noncommProd f hcomm') := by
    rw [HeisFam.yElt]
    exact (Finset.mul_noncommProd_erase _ (Finset.mem_univ t) f hcomm hcomm').symm
  set p := ((Finset.univ : Finset S).erase t).noncommProd f hcomm' with hp
  set u := f t with hu
  set a := H.xa t d with ha
  set zc := H.z (H.e t (c t) d) with hzc
  have hpa : p * a = a * p := by
    have := Finset.noncommProd_commute ((Finset.univ : Finset S).erase t) f hcomm' a
      (fun s hs => (H.xab_comm s t (Finset.ne_of_mem_erase hs) (c s) d).symm)
    exact this.symm
  have hpz : p * zc = zc * p := by
    have := Finset.noncommProd_commute ((Finset.univ : Finset S).erase t) f hcomm' zc
      (fun s _ => H.z_comm_b _ s (c s))
    exact this.symm
  have hcss := H.comm_ss t (c t) d
  rw [commutatorElement_def, inv_inv] at hcss
  have hua : u⁻¹ * a * u = zc * a := by
    have h1 : u⁻¹ * a * u * a⁻¹ = zc := hcss
    calc u⁻¹ * a * u = (u⁻¹ * a * u * a⁻¹) * a := by group
      _ = zc * a := by rw [h1]
  rw [hy, commutatorElement_def, inv_inv]
  calc (u * p)⁻¹ * a * (u * p) * a⁻¹ = p⁻¹ * (u⁻¹ * a * u) * p * a⁻¹ := by group
    _ = p⁻¹ * (zc * a) * p * a⁻¹ := by rw [hua]
    _ = p⁻¹ * zc * (a * p) * a⁻¹ := by group
    _ = p⁻¹ * zc * (p * a) * a⁻¹ := by rw [hpa]
    _ = p⁻¹ * (zc * p) := by group
    _ = p⁻¹ * (p * zc) := by rw [hpz]
    _ = zc := by group

theorem comm_yElt_mem_Z (c : ∀ s, P s) : ∀ a ∈ H.A, ⁅(H.yElt c)⁻¹, a⁆ ∈ H.Z := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨w, hw, rfl⟩ | ⟨⟨s, d⟩, rfl⟩
    · have h1 := H.yElt_comm_z c w
      have : ⁅(H.yElt c)⁻¹, H.z w⁆ = 1 := by
        rw [commutatorElement_def, inv_inv]
        calc (H.yElt c)⁻¹ * H.z w * H.yElt c * (H.z w)⁻¹
            = (H.yElt c)⁻¹ * (H.z w * H.yElt c) * (H.z w)⁻¹ := by group
          _ = 1 := by rw [← h1]; group
      rw [this]
      exact one_mem _
    · simp only
      rw [H.comm_yElt_xa c s d]
      exact H.z_mem_Z (H.e_mem s _ d)
  | one => rw [commutatorElement_one_right]; exact one_mem _
  | mul x y hx hy ih₁ ih₂ =>
    have h1 : ⁅(H.yElt c)⁻¹, x * y⁆ = ⁅(H.yElt c)⁻¹, x⁆ * (x * ⁅(H.yElt c)⁻¹, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    have h2 : x * ⁅(H.yElt c)⁻¹, y⁆ * x⁻¹ = ⁅(H.yElt c)⁻¹, y⁆ := by
      have := H.A_comm x hx _ (H.Z_le_A ih₂)
      rw [this]; group
    rw [h1, h2]
    exact mul_mem ih₁ ih₂
  | inv x hx ih =>
    have h1 : ⁅(H.yElt c)⁻¹, x⁻¹⁆ = x⁻¹ * (⁅(H.yElt c)⁻¹, x⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    have h2 : x⁻¹ * (⁅(H.yElt c)⁻¹, x⁆)⁻¹ * x = (⁅(H.yElt c)⁻¹, x⁆)⁻¹ := by
      have := H.A_comm x⁻¹ (inv_mem hx) _ (H.Z_le_A (inv_mem ih))
      rw [this]; group
    rw [h1, h2]
    exact inv_mem ih

theorem exists_dist (c c' : ∀ s, P s) (hne : c ≠ c') (u : Γ) (hu : u ∈ H.Z) :
    ∃ a ∈ H.A, ⁅(H.yElt c)⁻¹, a⁆ = u * ⁅(H.yElt c')⁻¹, a⁆ := by
  obtain ⟨w, hw, rfl⟩ := hu
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
  have hδ : c t - c' t ≠ 0 := sub_ne_zero.mpr ht
  obtain ⟨d, hd⟩ := H.e_surj t (c t - c' t) hδ w hw
  refine ⟨H.xa t d, H.xa_mem_A _ _, ?_⟩
  rw [H.comm_yElt_xa, H.comm_yElt_xa, ← H.z_add]
  congr 1
  have h1 : H.e t (c t) d = H.e t (c t - c' t) d + H.e t (c' t) d := by
    rw [← H.e_add_left, sub_add_cancel]
  rw [h1, hd]

theorem card_le_perm [Finite S] [∀ s, Finite (P s)] [Finite Γ] {Λ : Type*} [Finite Λ]
    (π : Γ →* Equiv.Perm Λ) (hnt : ∃ w ∈ H.Rg, π (H.z w) ≠ 1) :
    Nat.card (∀ s, P s) ≤ Nat.card Λ := by
  have hA := H.isMulCommutative_A
  obtain ⟨w, hw, hπ⟩ := hnt
  exact card_le_card_of_heisenberg_perm π H.A H.Z hA H.Z_le_A (fun c => H.yElt c)
    (fun c a ha => H.comm_yElt_mem_Z c a ha)
    (fun c c' hne u hu => H.exists_dist c c' hne u hu) ⟨H.z w, H.z_mem_Z hw, hπ⟩

theorem two_mul_card_le_perm [Finite S] [∀ s, Finite (P s)] [Finite Γ] {Λ : Type*} [Finite Λ]
    (π : Γ →* Equiv.Perm Λ) (hnt : ∃ w ∈ H.Rg, H.z w * H.z w = 1 ∧ π (H.z w) ≠ 1) :
    2 * Nat.card (∀ s, P s) ≤ Nat.card Λ := by
  have hA := H.isMulCommutative_A
  obtain ⟨w, hw, hsq, hπ⟩ := hnt
  exact two_mul_card_le_card_of_heisenberg_perm π H.A H.Z hA H.Z_le_A (fun c => H.yElt c)
    (fun c a ha => H.comm_yElt_mem_Z c a ha)
    (fun c c' hne u hu => H.exists_dist c c' hne u hu) (H.z_mem_Z hw) hsq hπ
    (fun c => H.yElt_comm_z c w)

end HeisFam

end CFSG.SignalizerFunctorTheorem.NonLocal
