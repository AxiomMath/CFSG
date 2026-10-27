module

public import CFSG.SignalizerFunctorTheorem.NonLocal.LowerBound
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.SignalizerFunctorTheorem.NonLocal

structure HeisSystem (Γ : Type*) [Group Γ] (k : Type*) [Field k] (S : Type*) where
  xa : S → k → Γ
  xb : S → k → Γ
  z : k → Γ
  ε : S → k
  xa_add : ∀ s c d, xa s (c + d) = xa s c * xa s d
  xb_add : ∀ s c d, xb s (c + d) = xb s c * xb s d
  z_add : ∀ c d, z (c + d) = z c * z d
  z_injective : Function.Injective z
  ε_ne : ∀ s, ε s ≠ 0
  xa_comm : ∀ s t c d, xa s c * xa t d = xa t d * xa s c
  xb_comm : ∀ s t c d, xb s c * xb t d = xb t d * xb s c
  z_comm_a : ∀ c s d, z c * xa s d = xa s d * z c
  z_comm_b : ∀ c s d, z c * xb s d = xb s d * z c
  xab_comm : ∀ s t, s ≠ t → ∀ c d, xb s c * xa t d = xa t d * xb s c
  comm_ss : ∀ s c d, ⁅(xb s c)⁻¹, xa s d⁆ = z (ε s * c * d)

namespace HeisSystem

variable {Γ : Type*} [Group Γ] {k : Type*} [Field k] {S : Type*} (H : HeisSystem Γ k S)

theorem z_zero : H.z 0 = 1 := by
  have h := H.z_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem z_neg (c : k) : H.z (-c) = (H.z c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← H.z_add, neg_add_cancel, H.z_zero]

theorem xa_zero (s : S) : H.xa s 0 = 1 := by
  have h := H.xa_add s 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem z_pow (c : k) (n : ℕ) : H.z c ^ n = H.z (n • c) := by
  induction n with
  | zero => simp [H.z_zero]
  | succ n ih => rw [pow_succ, ih, ← H.z_add, succ_nsmul]

theorem xa_pow (s : S) (c : k) (n : ℕ) : H.xa s c ^ n = H.xa s (n • c) := by
  induction n with
  | zero => simp [H.xa_zero]
  | succ n ih => rw [pow_succ, ih, ← H.xa_add, succ_nsmul]

@[expose] def Z : Subgroup Γ where
  carrier := Set.range H.z
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, H.z_add c d⟩
  one_mem' := ⟨0, H.z_zero⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨-c, H.z_neg c⟩

theorem mem_Z {g : Γ} : g ∈ H.Z ↔ ∃ c, H.z c = g := Iff.rfl

theorem z_mem_Z (c : k) : H.z c ∈ H.Z := ⟨c, rfl⟩

@[expose] def genA : Set Γ := Set.range H.z ∪ Set.range (fun p : S × k => H.xa p.1 p.2)

@[expose] def A : Subgroup Γ := Subgroup.closure H.genA

theorem genA_comm : ∀ x ∈ H.genA, ∀ y ∈ H.genA, x * y = y * x := by
  rintro x (⟨c, rfl⟩ | ⟨⟨s, c⟩, rfl⟩) y (⟨d, rfl⟩ | ⟨⟨t, d⟩, rfl⟩)
  · rw [← H.z_add, ← H.z_add, add_comm]
  · exact H.z_comm_a c t d
  · exact (H.z_comm_a d s c).symm
  · exact H.xa_comm s t c d

theorem isMulCommutative_A : IsMulCommutative H.A :=
  Subgroup.isMulCommutative_closure fun x hx y hy _ => H.genA_comm x hx y hy

theorem A_comm : ∀ a ∈ H.A, ∀ b ∈ H.A, a * b = b * a := by
  have := H.isMulCommutative_A
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : H.A) ⟨b, hb⟩)

theorem Z_le_A : H.Z ≤ H.A := by
  rintro _ ⟨c, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem z_mem_A (c : k) : H.z c ∈ H.A := H.Z_le_A (H.z_mem_Z c)

theorem xa_mem_A (s : S) (c : k) : H.xa s c ∈ H.A :=
  Subgroup.subset_closure (Or.inr ⟨(s, c), rfl⟩)

theorem A_pow_prime (r : ℕ) [CharP k r] : ∀ a ∈ H.A, a ^ r = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨c, rfl⟩ | ⟨⟨s, c⟩, rfl⟩
    · rw [H.z_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, H.z_zero]
    · simp only
      rw [H.xa_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, H.xa_zero]
  | one => exact one_pow r
  | mul x y hx hy ih₁ ih₂ =>
    rw [(show Commute x y from H.A_comm x hx y hy).mul_pow, ih₁, ih₂, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem A_isPGroup (r : ℕ) [Fact r.Prime] [CharP k r] : IsPGroup r H.A := by
  refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
  have h1 : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one (Subtype.ext (H.A_pow_prime r g g.2))
  rcases (Nat.dvd_prime Fact.out).mp h1 with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

variable [Fintype S] [DecidableEq S]

@[expose] def yElt (c : S → k) : Γ :=
  (Finset.univ : Finset S).noncommProd (fun s => H.xb s (c s)) (fun _ _ _ _ _ => H.xb_comm _ _ _ _)

omit [DecidableEq S] in
theorem yElt_comm_z (c : S → k) (c' : k) : H.yElt c * H.z c' = H.z c' * H.yElt c := by
  have := Finset.noncommProd_commute (Finset.univ : Finset S) (fun s => H.xb s (c s))
    (fun _ _ _ _ _ => H.xb_comm _ _ _ _) (H.z c') (fun s _ => (H.z_comm_b c' s (c s)))
  exact this.symm

theorem comm_yElt_xa (c : S → k) (t : S) (d : k) :
    ⁅(H.yElt c)⁻¹, H.xa t d⁆ = H.z (H.ε t * c t * d) := by
  set f : S → Γ := fun s => H.xb s (c s) with hf
  have hcomm : ((Finset.univ : Finset S) : Set S).Pairwise (fun a b => Commute (f a) (f b)) :=
    fun _ _ _ _ _ => H.xb_comm _ _ _ _
  have hcomm' : (((Finset.univ : Finset S).erase t : Finset S) : Set S).Pairwise
      (fun a b => Commute (f a) (f b)) := fun _ _ _ _ _ => H.xb_comm _ _ _ _
  have hy : H.yElt c = f t * (((Finset.univ : Finset S).erase t).noncommProd f hcomm') := by
    rw [HeisSystem.yElt]
    exact (Finset.mul_noncommProd_erase _ (Finset.mem_univ t) f hcomm hcomm').symm
  set p := ((Finset.univ : Finset S).erase t).noncommProd f hcomm' with hp
  set u := f t with hu
  set a := H.xa t d with ha
  set zc := H.z (H.ε t * c t * d) with hzc
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

theorem comm_yElt_mem_Z (c : S → k) : ∀ a ∈ H.A, ⁅(H.yElt c)⁻¹, a⁆ ∈ H.Z := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨c', rfl⟩ | ⟨⟨s, d⟩, rfl⟩
    · have h1 := H.yElt_comm_z c c'
      have : ⁅(H.yElt c)⁻¹, H.z c'⁆ = 1 := by
        rw [commutatorElement_def, inv_inv]
        calc (H.yElt c)⁻¹ * H.z c' * H.yElt c * (H.z c')⁻¹
            = (H.yElt c)⁻¹ * (H.z c' * H.yElt c) * (H.z c')⁻¹ := by group
          _ = 1 := by rw [← h1]; group
      rw [this]
      exact one_mem _
    · simp only
      rw [H.comm_yElt_xa c s d]
      exact H.z_mem_Z _
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

theorem exists_dist {F : Type*} [Field F] (ξ : Γ → F)
    (h1 : ∀ z ∈ H.Z, ∀ z' ∈ H.Z, ξ (z * z') = ξ z * ξ z') (h2 : ∀ z ∈ H.Z, ξ z ≠ 0)
    (h3 : ∃ z ∈ H.Z, ξ z ≠ 1) (c c' : S → k) (hne : c ≠ c') :
    ∃ a ∈ H.A, ξ ⁅(H.yElt c)⁻¹, a⁆ ≠ ξ ⁅(H.yElt c')⁻¹, a⁆ := by
  obtain ⟨_, ⟨e, rfl⟩, he⟩ := h3
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
  have hδ : c t - c' t ≠ 0 := sub_ne_zero.mpr ht
  have hε := H.ε_ne t
  have hεδ : H.ε t * (c t - c' t) ≠ 0 := mul_ne_zero hε hδ
  refine ⟨H.xa t (e / (H.ε t * (c t - c' t))), H.xa_mem_A _ _, ?_⟩
  rw [H.comm_yElt_xa, H.comm_yElt_xa]
  have hsum : H.ε t * c t * (e / (H.ε t * (c t - c' t))) =
      H.ε t * c' t * (e / (H.ε t * (c t - c' t))) + e := by
    field_simp
    ring
  rw [hsum, H.z_add, h1 _ (H.z_mem_Z _) _ (H.z_mem_Z _)]
  intro h
  have h0 := h2 _ (H.z_mem_Z (H.ε t * c' t * (e / (H.ε t * (c t - c' t)))))
  apply he
  have : ξ (H.z (H.ε t * c' t * (e / (H.ε t * (c t - c' t))))) * ξ (H.z e) =
      ξ (H.z (H.ε t * c' t * (e / (H.ε t * (c t - c' t))))) * 1 := by rw [h, mul_one]
  exact mul_left_cancel₀ h0 this

include H in
theorem heis_lower_bound [Finite Γ] [Finite k] {X : Type*} [Group X] (φ : Γ →* X)
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) [CharP k r] (hexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (hfaith : ∀ g : Γ, (∀ v ∈ V, φ g * v * (φ g)⁻¹ = v) → g = 1) :
    s ^ (Nat.card k ^ Nat.card S) ≤ Nat.card V := by
  have : Fact r.Prime := ⟨hr⟩
  have hA := H.isMulCommutative_A
  have : Finite H.A := Subtype.finite
  have hlow := pow_le_card_of_heisenberg φ V hr hs hrs hexp hnorm H.A H.Z hA
    (H.A_isPGroup r) H.Z_le_A (ι := S → k) H.yElt
    (fun c a ha => H.comm_yElt_mem_Z c a ha)
    (by
      by_contra hcon
      push Not at hcon
      have h1 : H.z 1 = 1 := hfaith _ (hcon _ (H.z_mem_Z 1))
      have : H.z 1 = H.z 0 := h1.trans H.z_zero.symm
      exact one_ne_zero (H.z_injective this))
    (fun F _ _ ξ h1 h2 h3 i j hij => H.exists_dist ξ h1 h2 h3 i j hij)
  rwa [Nat.card_fun] at hlow

end HeisSystem

end CFSG.SignalizerFunctorTheorem.NonLocalExc
