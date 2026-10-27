module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem card_le_mul_card_inf_of_le_sup {H : Type*} [Group H] {B L₁ L₂ : Subgroup H}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hdisj : L₁ ⊓ L₂ = ⊥) (hB : B ≤ L₁ ⊔ L₂)
    {n : ℕ} (hn : ∀ f : B →* H, f.range ≤ L₁ → Nat.card f.range ≤ n) :
    Nat.card B ≤ n * Nat.card ↥(B ⊓ L₂) := by
  classical
  have hcomm' : ∀ a : ↥L₁, ∀ b : ↥L₂, Commute (L₁.subtype a) (L₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let ψ : ↥L₁ × ↥L₂ →* H := MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm'
  have hψ_apply : ∀ p : ↥L₁ × ↥L₂, ψ p = (p.1 : H) * (p.2 : H) :=
    fun p => MonoidHom.noncommCoprod_apply _ _ _ p
  have hψ_range : ψ.range = L₁ ⊔ L₂ := by
    show (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm').range = L₁ ⊔ L₂
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hdisj' : Disjoint L₁.subtype.range L₂.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact _root_.disjoint_iff.mpr hdisj
  have hψ_inj : Function.Injective ψ := by
    show Function.Injective (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm')
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subgroup.subtype_injective L₁, Subgroup.subtype_injective L₂, hdisj'⟩
  let β : B →* ↥L₁ × ↥L₂ :=
    (MonoidHom.ofInjective hψ_inj).symm.toMonoidHom.comp
      (B.subtype.codRestrict ψ.range fun x => by
        rw [hψ_range]
        exact hB x.2)
  have hβ_apply : ∀ b : B, ψ (β b) = (b : H) := fun b =>
    MonoidHom.apply_ofInjective_symm hψ_inj _
  let θ : B →* H := L₁.subtype.comp ((MonoidHom.fst ↥L₁ ↥L₂).comp β)
  have hθ_apply : ∀ b : B, θ b = ((β b).1 : H) := fun _ => rfl
  have hθ_range : θ.range ≤ L₁ := by
    rintro x ⟨b, rfl⟩
    exact (β b).1.2
  have hker : θ.ker = (B ⊓ L₂).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hb
      have h1 : ((β b).1 : H) = 1 := by
        rw [hθ_apply b] at hb
        exact hb
      have h1' : (β b).1 = 1 := Subtype.ext h1
      have hβeq : β b = (1, (β b).2) := Prod.ext h1' rfl
      refine ⟨b.2, ?_⟩
      have hb_eq : (b : H) = ((β b).2 : H) := by
        calc (b : H) = ψ (β b) := (hβ_apply b).symm
          _ = ψ (1, (β b).2) := by rw [hβeq]
          _ = ((β b).2 : H) := by rw [hψ_apply]; simp
      simpa [hb_eq] using (β b).2.2
    · rintro ⟨_, hbL₂⟩
      let c : ↥L₂ := ⟨(b : H), hbL₂⟩
      have hc : ψ (β b) = ψ (1, c) := by
        rw [hβ_apply b, hψ_apply]
        simp [c]
      have hβeq : β b = (1, c) := hψ_inj hc
      rw [hθ_apply b, hβeq]
      rfl
  have hcard_ker : Nat.card θ.ker = Nat.card ↥(B ⊓ L₂) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker_range := Subgroup.card_ker_mul_card_range θ
  rw [hcard_ker] at hker_range
  have hrange_le : Nat.card θ.range ≤ n := hn θ hθ_range
  calc Nat.card B = Nat.card ↥(B ⊓ L₂) * Nat.card θ.range := hker_range.symm
    _ ≤ Nat.card ↥(B ⊓ L₂) * n := Nat.mul_le_mul_left _ hrange_le
    _ = n * Nat.card ↥(B ⊓ L₂) := Nat.mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
