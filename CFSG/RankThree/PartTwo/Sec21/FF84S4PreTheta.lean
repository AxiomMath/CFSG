module

public import CFSG.RankThree.PartTwo.Sec21.FF84A8
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

theorem std_conj (x y : Perm (Fin 8))
    (hmix : ((x = a8c ∨ x = a8c ^ 2) ∧ (y = a8d ∨ y = a8d ^ 2)) ∨
      ((x = a8d ∨ x = a8d ^ 2) ∧ (y = a8c ∨ y = a8c ^ 2))) :
    ∃ τ : Perm (Fin 8), τ * x * τ⁻¹ = a8c ∧ τ * y * τ⁻¹ = a8d := by
  let W : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5
  rcases hmix with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨swap 4 5, by decide, by decide⟩
    · exact ⟨swap 0 1, by decide, by decide⟩
    · exact ⟨swap 0 1 * swap 4 5, by decide, by decide⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨W, by decide, by decide⟩
    · exact ⟨swap 4 5 * W, by decide, by decide⟩
    · exact ⟨swap 0 1 * W, by decide, by decide⟩
    · exact ⟨swap 0 1 * swap 4 5 * W, by decide, by decide⟩

private theorem cd2_cube : (a8c8 * a8d8 ^ 2) ^ 3 = 1 := Subtype.ext (Equiv.ext (by decide))
private theorem cd_cube : (a8c8 * a8d8) ^ 3 = 1 := Subtype.ext (Equiv.ext (by decide))
private theorem c2d_eq : a8c8 ^ 2 * a8d8 = (a8c8 * a8d8 ^ 2) ^ 2 :=
  Subtype.ext (Equiv.ext (by decide))
private theorem c2d2_eq : a8c8 ^ 2 * a8d8 ^ 2 = (a8c8 * a8d8) ^ 2 :=
  Subtype.ext (Equiv.ext (by decide))

private theorem card_type3sq {z : A8}
    (h : z = a8c8 * a8d8 ∨ z = a8c8 * a8d8 ^ 2 ∨ z = a8c8 ^ 2 * a8d8 ∨ z = a8c8 ^ 2 * a8d8 ^ 2) :
    Nat.card (Subgroup.centralizer ({z} : Set A8)) = 18 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact card_cent_cd
  · exact card_cent_cd2
  · rw [c2d_eq, centralizer_sq_eq cd2_cube]; exact card_cent_cd2
  · rw [c2d2_eq, centralizer_sq_eq cd_cube]; exact card_cent_cd

theorem P0_cycle_of_card {z : A8} (hz : z ∈ a8P0)
    (hz1 : z ≠ 1) (hc : Nat.card (Subgroup.centralizer ({z} : Set A8)) ≠ 18) :
    (z = a8c8 ∨ z = a8c8 ^ 2) ∨ (z = a8d8 ∨ z = a8d8 ^ 2) := by
  rcases P0_cases hz with h | h | h | h | h | h | h | h | h
  · exact absurd h hz1
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have := card_type3sq (z := z) (Or.inl h); omega
  · have := card_type3sq (z := z) (Or.inr (Or.inl h)); omega
  · have := card_type3sq (z := z) (Or.inr (Or.inr (Or.inl h))); omega
  · have := card_type3sq (z := z) (Or.inr (Or.inr (Or.inr h))); omega

theorem pair_conj {x y : A8} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hc : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    (hcx : Nat.card (Subgroup.centralizer ({x} : Set A8)) ≠ 18)
    (hcy : Nat.card (Subgroup.centralizer ({y} : Set A8)) ≠ 18) :
    ∃ τ : Perm (Fin 8), τ * (x : Perm (Fin 8)) * τ⁻¹ = a8c ∧
      τ * (y : Perm (Fin 8)) * τ⁻¹ = a8d := by
  have hP : IsPGroup 3 (Subgroup.closure ({x, y} : Set A8)) := by
    refine isPGroup_closure_three _ ?_ ?_
    · intro s hs
      rcases hs with h | h
      · rw [h]; exact hx3
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hy3
    · intro s hs u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
      rcases hs with h | h <;> rcases hu with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hc | exact hc.symm
  obtain ⟨g, hg⟩ := exists_conj_into_P0 hP
  have hxP : g * x * g⁻¹ ∈ a8P0 := hg x (Subgroup.subset_closure (by simp))
  have hyP : g * y * g⁻¹ ∈ a8P0 := hg y (Subgroup.subset_closure (by simp))
  have hx1' : g * x * g⁻¹ ≠ 1 := fun e => hx1 (by
    have e' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e', e]; group)
  have hy1' : g * y * g⁻¹ ≠ 1 := fun e => hy1 (by
    have e' : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [e', e]; group)
  have hxc : Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set A8)) ≠ 18 := by
    rw [card_centralizer_conj]; exact hcx
  have hyc : Nat.card (Subgroup.centralizer ({g * y * g⁻¹} : Set A8)) ≠ 18 := by
    rw [card_centralizer_conj]; exact hcy
  have hyx' : g * y * g⁻¹ ∉ Subgroup.zpowers (g * x * g⁻¹) := by
    intro hm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hyx
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [conj_zpow] at hn
    exact mul_left_cancel (mul_right_cancel hn)
  have hzp : ∀ {w : A8}, w ^ 3 = 1 → ∀ {u v : A8}, (u = w ∨ u = w ^ 2) → (v = w ∨ v = w ^ 2) →
      v ∈ Subgroup.zpowers u := by
    intro w hw3 u v hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
      have h4 : (w ^ 2) ^ 2 = w := by
        rw [← pow_mul]
        calc w ^ (2 * 2) = w ^ 3 * w := by rw [← pow_succ]
          _ = w := by rw [hw3, one_mul]
      simpa using h4
    · exact Subgroup.mem_zpowers _
  have cX := P0_cycle_of_card hxP hx1' hxc
  have cY := P0_cycle_of_card hyP hy1' hyc
  have coeC : ∀ {z : A8}, (z = a8c8 ∨ z = a8c8 ^ 2) → ((z : A8) : Perm (Fin 8)) = a8c ∨
      ((z : A8) : Perm (Fin 8)) = a8c ^ 2 := by
    rintro z (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have coeD : ∀ {z : A8}, (z = a8d8 ∨ z = a8d8 ^ 2) → ((z : A8) : Perm (Fin 8)) = a8d ∨
      ((z : A8) : Perm (Fin 8)) = a8d ^ 2 := by
    rintro z (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmix : (((g * x * g⁻¹ : A8) : Perm (Fin 8)) = a8c ∨ ((g * x * g⁻¹ : A8) : Perm (Fin 8)) = a8c ^ 2) ∧
        (((g * y * g⁻¹ : A8) : Perm (Fin 8)) = a8d ∨ ((g * y * g⁻¹ : A8) : Perm (Fin 8)) = a8d ^ 2) ∨
      (((g * x * g⁻¹ : A8) : Perm (Fin 8)) = a8d ∨ ((g * x * g⁻¹ : A8) : Perm (Fin 8)) = a8d ^ 2) ∧
        (((g * y * g⁻¹ : A8) : Perm (Fin 8)) = a8c ∨ ((g * y * g⁻¹ : A8) : Perm (Fin 8)) = a8c ^ 2) := by
    rcases cX with cX | cX <;> rcases cY with cY | cY
    · exact absurd (hzp a8c8_cube cX cY) hyx'
    · exact Or.inl ⟨coeC cX, coeD cY⟩
    · exact Or.inr ⟨coeD cX, coeC cY⟩
    · exact absurd (hzp a8d8_cube cX cY) hyx'
  obtain ⟨τ, h1, h2⟩ := std_conj _ _ hmix
  refine ⟨τ * (g : Perm (Fin 8)), ?_, ?_⟩
  · rw [← h1]; simp [mul_assoc]
  · rw [← h2]; simp [mul_assoc]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
