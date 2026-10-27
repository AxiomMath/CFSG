module

public import CFSG.Walter.J1.A5Sub

public section

namespace CFSG.Walter.J1

namespace A5

private instance instDecEqPermFin5' : DecidableEq (Equiv.Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

private instance instDecMemA5' :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Equiv.Perm.sign.decidableMemKer

set_option maxHeartbeats 0 in
theorem card_inv_three : ∀ x : A, (x ^ 3 = 1 ∧ x ≠ 1) →
    (Finset.univ.filter (fun f : A => f ^ 2 = 1 ∧ f ≠ 1 ∧ f * x * f⁻¹ = x⁻¹)).card = 3 := by
  decide +kernel

end A5

namespace A5Sub

variable {G : Type*} [Group G] {F : Subgroup G} (e : F ≃* alternatingGroup (Fin 5))
include e

theorem ncard_inv_three {x : G} (hxF : x ∈ F) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    {f : G | f ∈ F ∧ f ^ 2 = 1 ∧ f ≠ 1 ∧ f * x * f⁻¹ = x⁻¹}.ncard = 3 := by
  classical
  obtain ⟨a, rfl⟩ := exists_ι e hxF
  have ha3 : a ^ 3 = 1 := by rwa [← map_pow, ι_eq_one_iff] at hx3
  have ha1 : a ≠ 1 := by rwa [Ne, ι_eq_one_iff] at hx1
  have h := A5.card_inv_three a ⟨ha3, ha1⟩
  have himage : {f : G | f ∈ F ∧ f ^ 2 = 1 ∧ f ≠ 1 ∧ f * ι e a * f⁻¹ = (ι e a)⁻¹} =
      ι e '' {b : alternatingGroup (Fin 5) | b ^ 2 = 1 ∧ b ≠ 1 ∧ b * a * b⁻¹ = a⁻¹} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hf, hf2, hf1, hfa⟩
      obtain ⟨b, rfl⟩ := exists_ι e hf
      refine ⟨b, ⟨?_, ?_, ?_⟩, rfl⟩
      · rwa [← map_pow, ι_eq_one_iff] at hf2
      · rwa [Ne, ι_eq_one_iff] at hf1
      · rwa [← map_inv, ← map_mul, ← map_mul, ← map_inv, ι_eq_iff] at hfa
    · rintro ⟨b, ⟨hb2, hb1, hba⟩, rfl⟩
      refine ⟨ι_mem e b, ?_, ?_, ?_⟩
      · rw [← map_pow, hb2, map_one]
      · rwa [Ne, ι_eq_one_iff]
      · rw [← map_inv, ← map_mul, ← map_mul, hba, map_inv]
  rw [himage, Set.ncard_image_of_injective _ (ι_injective e)]
  rw [Set.ncard_eq_toFinset_card']
  convert h using 2
  ext b
  simp

end A5Sub

end CFSG.Walter.J1
