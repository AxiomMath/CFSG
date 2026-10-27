module

public import CFSG.Sporadic.Co1Patterson.TwistModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Sporadic.Co1Patterson

theorem card_preimage_mk {F : Type*} [Group F] (N : Subgroup F) (P : F ⧸ N → Prop) :
    Nat.card {f : F // P (QuotientGroup.mk f)} = Nat.card {x : F ⧸ N // P x} * Nat.card N := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeEquiv (Subgroup.groupEquivQuotientProdSubgroup (s := N))
    (q := fun p : (F ⧸ N) × N => P p.1) fun f => ?_).trans Equiv.prodSubtypeFstEquivSubtypeProd)
  rfl

theorem card_fibreProd_fst {H E L : Type*} [Group H] [Group E] [Group L] (φ : H →* L)
    (π : E →* L) (hπ : Function.Surjective π) (P : H → Prop) :
    Nat.card {f : fibreProd φ π // P (f : H × E).1} = Nat.card {h : H // P h} * Nat.card π.ker := by
  rw [← Nat.card_prod]
  set s : L → E := Function.surjInv hπ with hs
  have hs' : ∀ l, π (s l) = l := Function.surjInv_eq hπ
  refine Nat.card_congr
    { toFun := fun f => (⟨(f.1 : H × E).1, f.2⟩, ⟨(s (φ (f.1 : H × E).1))⁻¹ * (f.1 : H × E).2,
        by rw [MonoidHom.mem_ker, map_mul, map_inv, hs', mem_fibreProd.1 f.1.2, inv_mul_cancel]⟩)
      invFun := fun p => ⟨⟨((p.1 : H), s (φ p.1) * p.2), by
        rw [mem_fibreProd, map_mul, hs', MonoidHom.mem_ker.1 p.2.2, mul_one]⟩, p.1.2⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun p => by
        ext
        · rfl
        · simp }

theorem card_subtype_mono {α : Type*} [Finite α] {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, h x.1 x.2⟩) fun _ _ hab =>
    Subtype.ext (Subtype.mk.inj hab)

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H₀ : Type} [Group H₀] [Finite H₀] (S₀ : ExtraspecialTypeSystem n L act qf bil H₀) {E : Type}
  [Group E] [Finite E] {π : E →* L} {ζ : E} (hζ : π ζ = 1)

@[expose] def twMk (h : H₀) (e : E) (he : S₀.φ h = π e) : Twist S₀ π ζ hζ :=
  QuotientGroup.mk ⟨(h, e), he⟩

@[expose] def twW {w₀ : H₀} (hw₀ : S₀.φ w₀ = 1) : Twist S₀ π ζ hζ :=
  twMk S₀ hζ w₀ 1 (by rw [hw₀, map_one])

@[expose] def twZ : Twist S₀ π ζ hζ := twMk S₀ hζ S₀.z 1 (by rw [S₀.φ_z, map_one])

variable (hζc : ∀ e, ζ * e = e * ζ) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
include hζc hζ2 hζ1

omit [Finite H₀] [Finite E] in
theorem card_normalClosure_zζ : Nat.card (normalClosure {zζ S₀ π ζ hζ}) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨zζ S₀ π ζ hζ, subset_normalClosure rfl⟩, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun x : normalClosure {zζ S₀ π ζ hζ} => ((x : fibreProd S₀.φ π) :
      H₀ × E).2) h
    exact hζ1 h1.symm
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_normalClosure_zζ_iff S₀ hζ hζc hζ2).1 hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem card_twist_sq_z_ge (hπ : Function.Surjective π)
    (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) {w₀ : H₀} (hw₀ : S₀.φ w₀ = 1) :
    Nat.card {h : H₀ // h * w₀ = w₀ * h ∧ h * h = 1 ∧ ∀ e, π e = S₀.φ h → e * e = ζ} ≤
      Nat.card {x : Twist S₀ π ζ hζ // x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧
        x * x = twZ S₀ hζ} := by
  have hk2 : Nat.card π.ker = 2 := card_ker_eq_two π hker hζ1
  have h1 : Nat.card {f : fibreProd S₀.φ π //
        (QuotientGroup.mk f : Twist S₀ π ζ hζ) * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ *
          QuotientGroup.mk f ∧ (QuotientGroup.mk f : Twist S₀ π ζ hζ) *
            QuotientGroup.mk f = twZ S₀ hζ} =
      Nat.card {x : Twist S₀ π ζ hζ // x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧
        x * x = twZ S₀ hζ} * 2 := by
    have h := card_preimage_mk (normalClosure {zζ S₀ π ζ hζ}) fun x : Twist S₀ π ζ hζ =>
      x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧ x * x = twZ S₀ hζ
    rwa [card_normalClosure_zζ S₀ hζ hζc hζ2 hζ1] at h
  have h2 : Nat.card {f : fibreProd S₀.φ π // (f : H₀ × E).1 * w₀ = w₀ * (f : H₀ × E).1 ∧
      (f : H₀ × E).1 * (f : H₀ × E).1 = 1 ∧ ∀ e, π e = S₀.φ (f : H₀ × E).1 → e * e = ζ} =
      Nat.card {h : H₀ // h * w₀ = w₀ * h ∧ h * h = 1 ∧ ∀ e, π e = S₀.φ h → e * e = ζ} * 2 := by
    have h := card_fibreProd_fst S₀.φ π hπ fun h =>
      h * w₀ = w₀ * h ∧ h * h = 1 ∧ ∀ e, π e = S₀.φ h → e * e = ζ
    rwa [hk2] at h
  have hle : Nat.card {f : fibreProd S₀.φ π // (f : H₀ × E).1 * w₀ = w₀ * (f : H₀ × E).1 ∧
      (f : H₀ × E).1 * (f : H₀ × E).1 = 1 ∧ ∀ e, π e = S₀.φ (f : H₀ × E).1 → e * e = ζ} ≤
      Nat.card {f : fibreProd S₀.φ π //
        (QuotientGroup.mk f : Twist S₀ π ζ hζ) * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ *
          QuotientGroup.mk f ∧ (QuotientGroup.mk f : Twist S₀ π ζ hζ) *
            QuotientGroup.mk f = twZ S₀ hζ} := by
    refine card_subtype_mono fun f hf => ?_
    obtain ⟨hcomm, hsq, hlift⟩ := hf
    obtain ⟨⟨h, e⟩, he⟩ := f
    simp only at hcomm hsq hlift
    have hee : e * e = ζ := hlift e (mem_fibreProd.1 he).symm
    refine ⟨?_, ?_⟩
    · rw [twW, twMk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp [hcomm]
    · rw [twZ, twMk, ← QuotientGroup.mk_mul, mk_eq_mk_iff_twist S₀ hζ hζc hζ2]
      right
      apply Subtype.ext
      simp [zζ, hsq, hee, hζ2]
  omega

theorem card_twist_sq_w_le (hπ : Function.Surjective π)
    (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) {w₀ : H₀} (hw₀ : S₀.φ w₀ = 1) :
    Nat.card {x : Twist S₀ π ζ hζ // x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧
        x * x = twW S₀ hζ hw₀} ≤
      Nat.card {h : H₀ // h * w₀ = w₀ * h ∧ (h * h = w₀ ∨ h * h = w₀ * S₀.z)} := by
  have hk2 : Nat.card π.ker = 2 := card_ker_eq_two π hker hζ1
  have h1 : Nat.card {f : fibreProd S₀.φ π //
        (QuotientGroup.mk f : Twist S₀ π ζ hζ) * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ *
          QuotientGroup.mk f ∧ (QuotientGroup.mk f : Twist S₀ π ζ hζ) *
            QuotientGroup.mk f = twW S₀ hζ hw₀} =
      Nat.card {x : Twist S₀ π ζ hζ // x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧
        x * x = twW S₀ hζ hw₀} * 2 := by
    have h := card_preimage_mk (normalClosure {zζ S₀ π ζ hζ}) fun x : Twist S₀ π ζ hζ =>
      x * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ * x ∧ x * x = twW S₀ hζ hw₀
    rwa [card_normalClosure_zζ S₀ hζ hζc hζ2 hζ1] at h
  have h2 : Nat.card {f : fibreProd S₀.φ π // (f : H₀ × E).1 * w₀ = w₀ * (f : H₀ × E).1 ∧
        ((f : H₀ × E).1 * (f : H₀ × E).1 = w₀ ∨
          (f : H₀ × E).1 * (f : H₀ × E).1 = w₀ * S₀.z)} =
      Nat.card {h : H₀ // h * w₀ = w₀ * h ∧ (h * h = w₀ ∨ h * h = w₀ * S₀.z)} * 2 := by
    have h := card_fibreProd_fst S₀.φ π hπ fun h =>
      h * w₀ = w₀ * h ∧ (h * h = w₀ ∨ h * h = w₀ * S₀.z)
    rwa [hk2] at h
  have hle : Nat.card {f : fibreProd S₀.φ π //
        (QuotientGroup.mk f : Twist S₀ π ζ hζ) * twW S₀ hζ hw₀ = twW S₀ hζ hw₀ *
          QuotientGroup.mk f ∧ (QuotientGroup.mk f : Twist S₀ π ζ hζ) *
            QuotientGroup.mk f = twW S₀ hζ hw₀} ≤
      Nat.card {f : fibreProd S₀.φ π // (f : H₀ × E).1 * w₀ = w₀ * (f : H₀ × E).1 ∧
        ((f : H₀ × E).1 * (f : H₀ × E).1 = w₀ ∨
          (f : H₀ × E).1 * (f : H₀ × E).1 = w₀ * S₀.z)} := by
    refine card_subtype_mono fun f hf => ?_
    obtain ⟨hcomm, hsq⟩ := hf
    obtain ⟨⟨h, e⟩, he⟩ := f
    rw [twW, twMk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mk_eq_mk_iff_twist S₀ hζ hζc hζ2] at hcomm
    rw [twW, twMk, ← QuotientGroup.mk_mul, mk_eq_mk_iff_twist S₀ hζ hζc hζ2] at hsq
    simp only
    refine ⟨?_, ?_⟩
    · rcases hcomm with hc | hc
      · have := congrArg (fun x : fibreProd S₀.φ π => (x : H₀ × E).1) hc
        simpa using this.symm
      · exfalso
        have := congrArg (fun x : fibreProd S₀.φ π => (x : H₀ × E).2) hc
        simp only [Subgroup.coe_mul, Prod.snd_mul, zζ, one_mul, mul_one] at this
        exact hζ1 (by simpa using this)
    · rcases hsq with hs | hs
      · left
        have := congrArg (fun x : fibreProd S₀.φ π => (x : H₀ × E).1) hs
        simpa using this.symm
      · right
        have := congrArg (fun x : fibreProd S₀.φ π => (x : H₀ × E).1) hs
        simp only [Subgroup.coe_mul, Prod.fst_mul, zζ] at this
        rw [this, mul_assoc, S₀.z_mul_self, mul_one]
  omega

end CFSG.Sporadic.SuzRecog
