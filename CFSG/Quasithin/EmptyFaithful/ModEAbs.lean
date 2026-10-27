module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.ModE

open CFSG.Open

theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] {A : Subgroup X} (h : IsElemAbelian 2 A)
    (f : X →* Y) : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map h _

theorem card_eq_ker_mul {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (B : Subgroup X) :
    Nat.card B = Nat.card (B ⊓ φ.ker : Subgroup X) * Nat.card (B.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.domRestrict B)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
  rw [← h]
  congr 1
  have e1 : (B ⊓ φ.ker).subgroupOf B = φ.ker.subgroupOf B := Subgroup.inf_subgroupOf_left φ.ker B
  rw [← e1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ φ.ker ≤ B)).toEquiv

theorem card_ker_part {K Y X : Type*} [Group K] [Group Y] [Group X] [Finite X] (φ : K →* Y)
    (e : ↥φ.ker ≃* X) (B : Subgroup K) (hB : ∀ b ∈ B, b * b = 1) :
    Nat.card (B ⊓ φ.ker : Subgroup K) ≤ Nat.card {x : X // x * x = 1} := by
  let f : ↥(B ⊓ φ.ker) → {x : X // x * x = 1} := fun b =>
    ⟨e ⟨b.1, b.2.2⟩, by
      have h1 : (⟨b.1, b.2.2⟩ : ↥φ.ker) * ⟨b.1, b.2.2⟩ = 1 := Subtype.ext (hB b.1 b.2.1)
      rw [← map_mul, h1, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : e ⟨a.1, a.2.2⟩ = e ⟨b.1, b.2.2⟩ := congrArg Subtype.val hab
    have h2 := e.injective h1
    have h3 : (a.1 : K) = b.1 := congrArg (fun x : ↥φ.ker => (x : K)) h2
    exact Subtype.ext h3
  exact Nat.card_le_card_of_injective f hf

theorem card_le_of_TB {D : Type*} [Group D] [Finite D] {T : Subgroup D}
    (hT : ∃ P : Sylow 2 D, (P : Subgroup D) = T)
    (hb : ∀ B : Subgroup D, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 8) {A : Subgroup D}
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ 8 := by
  obtain ⟨P, rfl⟩ := hT
  have hA2 : IsPGroup 2 A := fun x => ⟨1, by
    have h1 := hA.2 x x.2
    apply Subtype.ext
    simpa using h1⟩
  obtain ⟨Q, hAQ⟩ := hA2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P Q
  let φ : D →* D :=
    { toFun := fun x => g⁻¹ * x * g
      map_one' := by group
      map_mul' := fun x y => by group }
  have hφinj : Function.Injective φ := by
    intro x y h
    have h' : g⁻¹ * x * g = g⁻¹ * y * g := h
    exact mul_left_cancel (mul_right_cancel h')
  have hBle : A.map φ ≤ (P : Subgroup D) := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ (Q : Subgroup D) := hAQ ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    exact h1
  have h2 := hb _ hBle (isElemAbelian_map hA φ)
  rwa [Subgroup.card_map_of_injective hφinj] at h2

end CFSG.Quasithin.ModE
