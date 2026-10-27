module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Chain

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF79

section Norm


theorem exists_normalization {Y S : Subgroup H6} (e : Nonempty (↥Y ≃* G3)) (hS : S ≤ Y)
    (hS6 : Nat.card S = 6) (hC : Nat.card ↥(Subgroup.centralizer (S : Set H6)) = 36)
    {v₁ v₂ : H6} (h1 : v₁ * v₁ = 1) (h2 : v₂ * v₂ = 1) (hne1 : v₁ ≠ 1) (hne2 : v₂ ≠ 1)
    (hne : v₁ ≠ v₂) (h3 : (v₁ * v₂) ^ 3 = 1)
    (hcomm : ∀ s ∈ S, s * v₁ = v₁ * s ∧ s * v₂ = v₂ * s)
    (hC2 : Nat.card ↥(Subgroup.centralizer
      ((Subgroup.closure ({v₁, v₂} : Set H6) : Subgroup H6) : Set H6)) = 36) :
    ∃ g : H6, Y.map (MulAut.conj g).toMonoidHom = Xstar ∧
      S.map (MulAut.conj g).toMonoidHom = K4s ∧
      (g * v₁ * g⁻¹ = pH ∨ g * v₁ * g⁻¹ = qH ∨ g * v₁ * g⁻¹ = rH) ∧
      (g * v₂ * g⁻¹ = pH ∨ g * v₂ * g⁻¹ = qH ∨ g * v₂ * g⁻¹ = rH) := by
  obtain ⟨g, hY, hSK⟩ := classify_L32 e hS hS6 hC
  refine ⟨g, hY, hSK, ?_⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u : H6, u = g * v₁ * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : H6, u = g * v₂ * g⁻¹ := ⟨_, rfl⟩
  rw [← hu₁, ← hu₂]
  have hconj : ∀ x y : H6, g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := fun x y => by
    group
  have hu₁sq : u₁ * u₁ = 1 := by rw [hu₁, hconj, h1]; group
  have hu₂sq : u₂ * u₂ = 1 := by rw [hu₂, hconj, h2]; group
  have hu₁ne : u₁ ≠ 1 := by
    intro h
    apply hne1
    have : g * v₁ * g⁻¹ = g * 1 * g⁻¹ := by rw [← hu₁, h]; group
    simpa using this
  have hu₂ne : u₂ ≠ 1 := by
    intro h
    apply hne2
    have : g * v₂ * g⁻¹ = g * 1 * g⁻¹ := by rw [← hu₂, h]; group
    simpa using this
  have hu₁inv : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁sq
  have hu₂inv : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right hu₂sq
  obtain ⟨a, ha⟩ : ∃ a : H6, a = u₁ * u₂ := ⟨_, rfl⟩
  have ha3 : a ^ 3 = 1 := by
    have : a = (MulAut.conj g) (v₁ * v₂) := by
      rw [ha, hu₁, hu₂, hconj, MulAut.conj_apply]
    rw [this, ← map_pow, h3, map_one]
  have haa : a * (u₂ * u₁) = 1 := by
    calc a * (u₂ * u₁) = u₁ * (u₂ * u₂) * u₁ := by rw [ha]; group
      _ = 1 := by rw [hu₂sq]; simpa using hu₁sq
  have ha2 : a ^ 2 = u₂ * u₁ := by
    have h' : a ^ 2 * a = 1 := by rw [← pow_succ, ha3]
    exact (eq_inv_of_mul_eq_one_left h').trans (inv_eq_of_mul_eq_one_right haa)
  have ha1 : a ≠ 1 := by
    intro h
    apply hne
    have h' : u₂ = u₁ := by
      calc u₂ = u₁ * (u₁ * u₂) := by rw [← mul_assoc, hu₁sq, one_mul]
        _ = u₁ := by rw [← ha, h, mul_one]
    have : g * v₂ * g⁻¹ = g * v₁ * g⁻¹ := by rw [← hu₂, ← hu₁, h']
    simpa using this.symm
  have hta : u₁ * a * u₁ = a ^ 2 := by
    rw [ha2, ha]
    calc u₁ * (u₁ * u₂) * u₁ = (u₁ * u₁) * u₂ * u₁ := by group
      _ = u₂ * u₁ := by rw [hu₁sq, one_mul]
  have hD : ∀ u : H6, (∀ s ∈ S, s * u = u * s) → g * u * g⁻¹ ∈ Dsub := fun u hu => by
    rw [Dsub_eq, ← hSK, Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * s * g⁻¹ * (g * u * g⁻¹) = g * (s * u) * g⁻¹ := by group
      _ = g * (u * s) * g⁻¹ := by rw [hu s hs]
      _ = g * u * g⁻¹ * (g * s * g⁻¹) := by group
  have hu₁D : u₁ ∈ Dsub := by rw [hu₁]; exact hD v₁ fun s hs => (hcomm s hs).1
  have hu₂D : u₂ ∈ Dsub := by rw [hu₂]; exact hD v₂ fun s hs => (hcomm s hs).2
  have haD : a ∈ Dsub := by rw [ha]; exact Dsub.mul_mem hu₁D hu₂D
  have hcl1 : Subgroup.closure ({a, u₁} : Set H6) = Subgroup.closure ({u₁, u₂} : Set H6) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · rw [ha]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · rw [Set.mem_singleton_iff.1 hx]
        exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff.1 hx]
        have : u₂ = u₁ * a := by rw [ha, ← mul_assoc, hu₁sq, one_mul]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  have hcl2 : Subgroup.closure ({u₁, u₂} : Set H6) =
      (Subgroup.closure ({v₁, v₂} : Set H6)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair, hu₁, hu₂]
    rfl
  have hCa : Nat.card ↥(Subgroup.centralizer
      ((Subgroup.closure ({a, u₁} : Set H6) : Subgroup H6) : Set H6)) = 36 := by
    rw [hcl1, hcl2, card_centralizer_map_conj, hC2]
  obtain ⟨hKa, hKt⟩ := classify_K2 ha3 ha1 hu₁sq hu₁ne hta haD hu₁D hCa
  have hKu₂ : u₂ ∈ K2star := by
    have : u₂ = u₁ * a := by rw [ha, ← mul_assoc, hu₁sq, one_mul]
    rw [this]
    exact K2star.mul_mem hKt hKa
  exact ⟨K2star_involutions hKt hu₁sq hu₁ne, K2star_involutions hKu₂ hu₂sq hu₂ne⟩

end Norm

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
