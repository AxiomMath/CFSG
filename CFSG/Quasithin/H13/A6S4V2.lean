module

public import CFSG.Quasithin.H13.A6S4Defs
public import CFSG.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def DAgens : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 4 5]

@[expose] def BadWit (y : P6) : Prop :=
  ∃ σ ∈ DAgens, ([1, e0123, y, y * e0123, act4f σ y] : List P6).Nodup

instance (y : P6) : Decidable (BadWit y) := by unfold BadWit; infer_instance

theorem v2_cert : ∀ y : P6, InW4 y → y ≠ 1 → y ≠ e0123 → ¬ InW2 y → BadWit y := by
  decide +kernel

theorem DAgens_mem : ∀ σ ∈ DAgens, InD6 σ ∧ σ ∈ alternatingGroup (Fin 6) := by
  intro σ hσ
  simp only [DAgens, List.mem_cons, List.not_mem_nil, or_false] at hσ
  obtain ⟨h1, h2, h3⟩ := gens_DA
  rcases hσ with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V2_unique {W : Subgroup G} (hW : IsV2 T V W) : W = S.V2 := by
  classical
  obtain ⟨h1, hWV, hTW, hcard⟩ := hW
  have hzW : S.z ∈ W := h1 (S.mem_V1_iff.2 (Or.inr rfl))
  have key : ∀ x ∈ W, x ∉ fsuV1 T V → x ∈ S.V2 := by
    intro x hxW hxV1
    have hxV : x ∈ V := hWV hxW
    refine S.mem_pre.2 ⟨hxV, ?_⟩
    show InW2 (S.frame.ψ ⟨x, hxV⟩ : P6)
    by_contra hy
    set y : P6 := (S.frame.ψ ⟨x, hxV⟩ : P6) with hydef
    have hy1 : y ≠ 1 := fun h => hxV1 (by
      have : (⟨x, hxV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
      exact S.mem_V1_iff.2 (Or.inl (congrArg Subtype.val this)))
    have hyz : y ≠ e0123 := fun h => hxV1 (by
      have : (⟨x, hxV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
        S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
      exact S.mem_V1_iff.2 (Or.inr (congrArg Subtype.val this)))
    obtain ⟨σ, hσ, hnd⟩ := v2_cert y (S.frame.ψ ⟨x, hxV⟩).2 hy1 hyz hy
    obtain ⟨hσD, hσA⟩ := DAgens_mem σ hσ
    obtain ⟨t, htT, rfl⟩ := S.frame.DA_T σ hσD hσA
    have htx : (t : G) * x * (t : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hTW htT) x).mp hxW
    let f : ↥W → P6 := fun w => (S.frame.ψ ⟨w, hWV w.2⟩ : P6)
    have hf : Function.Injective f := by
      intro u w h
      have := S.frame.ψ.injective (Subtype.ext h)
      exact Subtype.ext (congrArg (fun v : ↥V => (v : G)) this)
    have : Fintype ↥W := Fintype.ofFinite _
    have hsub : ([1, e0123, y, y * e0123, act4f (S.frame.ρ t) y] : List P6).toFinset ⊆
        Finset.univ.image f := by
      intro u hu
      rw [List.mem_toFinset] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [Finset.mem_image]
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, Finset.mem_univ _, by simp [f]⟩
      · refine ⟨⟨S.z, hzW⟩, Finset.mem_univ _, ?_⟩
        show (S.frame.ψ ⟨S.z, _⟩ : P6) = e0123
        rw [S.psi_z]
      · exact ⟨⟨x, hxW⟩, Finset.mem_univ _, rfl⟩
      · refine ⟨⟨x * S.z, W.mul_mem hxW hzW⟩, Finset.mem_univ _, ?_⟩
        show (S.frame.ψ (⟨x, hxV⟩ * ⟨S.z, S.z_mem_V⟩) : P6) = _
        rw [map_mul, S.psi_z]
        rfl
      · refine ⟨⟨(t : G) * x * (t : G)⁻¹, htx⟩, Finset.mem_univ _, ?_⟩
        show (S.frame.ψ ⟨(t : G) * x * (t : G)⁻¹, _⟩ : P6) = _
        rw [S.psi_conj t ⟨x, hxV⟩, act4_coe]
        rfl
    have h5 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_image_of_injective _ hf, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard] at h5
    simp at h5
  have hle : W ≤ S.V2 := fun x hx => by
    by_cases hxV1 : x ∈ fsuV1 T V
    · exact S.V1_le_V2 hxV1
    · exact key x hx hxV1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [S.card_V2, hcard])

end Setting4

end CFSG.Quasithin.H13.A6
