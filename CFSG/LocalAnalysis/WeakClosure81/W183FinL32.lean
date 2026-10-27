module

public import CFSG.LocalAnalysis.WeakClosure81.W183Fin2
public import CFSG.GH74.KGroups.L27
import CFSG.GH74.KGroups.AutModelIndexTwo
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Quasithin.Background.P4InspEndAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

private abbrev w183Pm (n : ℕ) := Equiv.Perm (Fin n)

private def w183V4 {G : Type*} [Group G] (a b : G) : List G := [1, a, b, a * b]

private def w183TiB {n : ℕ} (Y : List (w183Pm n)) (a b : w183Pm n) : Bool :=
  [a, b, a * b].all fun t => Y.all fun g =>
    !(decide (g * t = t * g)) ||
      ((w183V4 a b).contains (g * a * g⁻¹) && (w183V4 a b).contains (g * b * g⁻¹))

private def w183KleinB {n : ℕ} (a b : w183Pm n) : Bool :=
  decide (a * b = b * a) && !(decide (a = b))

private def w183FinL32B {n : ℕ} (Y : List (w183Pm n)) : Bool :=
  let I := Y.filter fun g => decide (g * g = 1 ∧ g ≠ 1)
  I.all fun a => I.all fun b => !(w183KleinB a b) || !(w183TiB Y a b)

private theorem w183L27FinL32B : w183FinL32B (elemsT L27.QA) = true := by decide +kernel

private theorem w183FinL32B_sound {n : ℕ} {Y : List (w183Pm n)} (h : w183FinL32B Y = true)
    {a b : w183Pm n} (ha : a ∈ Y) (hb : b ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    ¬ (∀ t ∈ [a, b, a * b], ∀ g ∈ Y, g * t = t * g →
        g * a * g⁻¹ ∈ w183V4 a b ∧ g * b * g⁻¹ ∈ w183V4 a b) := by
  intro hTI
  simp only [w183FinL32B, List.all_eq_true, List.mem_filter, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_true] at h
  have h1 := h a ⟨ha, ha2, ha1⟩ b ⟨hb, hb2, hb1⟩
  have hk : w183KleinB a b = true := by simp [w183KleinB, hc, hab]
  have ht : w183TiB Y a b = true := by
    simp only [w183TiB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      decide_eq_false_iff_not, decide_eq_true_eq, List.contains_iff_mem]
    intro t ht g hg
    by_cases hgt : g * t = t * g
    · exact Or.inr (hTI t ht g hg hgt)
    · exact Or.inl hgt
  rcases h1 with h1 | h1
  · rw [hk] at h1; simp at h1
  · rw [ht] at h1; simp at h1

private theorem w183L32Model {Y : Type} [Group Y]
    (L : Subgroup Y) (hL : IsL3 ↥L 1) :
    ∃ M : AutModel ↥L (Equiv.Perm (Fin 8)), M.P = L27.QP.originalSubgroup ∧
      M.A = L27.QA.originalSubgroup ∧ Nat.card M.A = 2 * Nat.card M.P := by
  obtain ⟨e⟩ := L27.equiv_of_lieModel3 hL
  obtain ⟨M, hP, hA⟩ := L27.autModel e
  refine ⟨M, hP, hA, ?_⟩
  rw [hP, hA, card_group _ L27.QA_ok, card_group _ L27.QP_ok, L27.QA_valid.2, L27.QP_valid.2]

private theorem w183KleinData {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y}
    (h4 : Nat.card A = 4) (hel : IsElemAbelian 2 A) :
    ∃ a b : Y, a ∈ A ∧ b ∈ A ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a ∧ ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  obtain ⟨x, y, hx1, hy1, hxy⟩ :=
    CFSG.Quasithin.G11.P4InspEnd.p4inspend_two_ne_one (P := A) (by omega)
  have ha1 : (x : Y) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hb1 : (y : Y) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hab : (x : Y) ≠ y := fun h => hxy (Subtype.ext h)
  exact ⟨x, y, x.2, y.2, ha1, hb1, hab, CFSG.Goldschmidt.Sec8.mul_self_eq_one hel x.2,
    CFSG.Goldschmidt.Sec8.mul_self_eq_one hel y.2, CFSG.Goldschmidt.Sec8.comm hel x.2 y.2,
    fun z hz => CFSG.Goldschmidt.Sec8.mem_four hel h4 x.2 y.2 hz ha1 hb1 hab⟩

private theorem w183MemV4OfMap {Y G : Type*} [Group Y] [Group G] (ψ : Y →* G) {a b x : Y}
    (h : x = 1 ∨ x = a ∨ x = b ∨ x = a * b) : ψ x ∈ w183V4 (ψ a) (ψ b) := by
  simp only [w183V4, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one ψ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul ψ _ _)))

theorem finL32_holds : FinL32 := by
  intro Y _ _ L hLn hL hC hτ A hA4 hAel hTI
  haveI := hLn
  obtain ⟨M, hP, hA, h2⟩ := w183L32Model L hL
  obtain ⟨τ, hτ⟩ := hτ
  have hτL : τ ∉ L := by
    intro hτL
    obtain ⟨-, P, -, hPd⟩ := hτ
    exact hPd τ hτL (by rw [inv_mul_cancel]; exact CFSG.Quasithin.conjSubgroup_one P)
  have hLtop : L ≠ ⊤ := fun h => hτL (h ▸ Subgroup.mem_top τ)
  rcases M.nonempty_mulEquiv_or_eq_top L hC h2 with ⟨⟨eYA⟩⟩ | h
  swap
  · exact absurd h hLtop
  let ψ := M.actHom L
  have hψinj : Function.Injective ψ := M.actHom_injective L hC
  have hψmem : ∀ y, ψ y ∈ M.A := M.actHom_mem L
  have hcardYA : Nat.card Y = Nat.card M.A := Nat.card_congr eYA.toEquiv
  have hsurj : ∀ g ∈ M.A, ∃ y, ψ y = g := by
    let f : Y →* M.A := ψ.codRestrict M.A hψmem
    have hf : Function.Injective f := fun a b hab => hψinj (congrArg Subtype.val hab)
    haveI : Finite M.A := Nat.finite_of_card_ne_zero (by
      rw [← hcardYA]; exact Nat.card_pos.ne')
    have hfb : Function.Bijective f := hf.bijective_of_nat_card_le (le_of_eq hcardYA.symm)
    intro g hg
    obtain ⟨y, hy⟩ := hfb.2 ⟨g, hg⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨a, b, haA, hbA, ha1, hb1, hab, ha2, hb2, hcomm, hmem⟩ := w183KleinData hA4 hAel
  have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hψb2 : ψ b * ψ b = 1 := by rw [← map_mul, hb2, map_one]
  have hψa1 : ψ a ≠ 1 := fun h => ha1 (hψinj (by rw [h, map_one]))
  have hψb1 : ψ b ≠ 1 := fun h => hb1 (hψinj (by rw [h, map_one]))
  have hψab : ψ a ≠ ψ b := fun h => hab (hψinj h)
  have hψc : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hcomm]
  refine w183FinL32B_sound w183L27FinL32B (a := ψ a) (b := ψ b) ?_ ?_
    hψa2 hψa1 hψb2 hψb1 hψab hψc ?_
  · rw [mem_elemsT _ L27.QA_ok, ← hA]; exact hψmem a
  · rw [mem_elemsT _ L27.QA_ok, ← hA]; exact hψmem b
  intro t ht g hg hgt
  rw [mem_elemsT _ L27.QA_ok, ← hA] at hg
  obtain ⟨y, rfl⟩ := hsurj g hg
  have key : ∀ t₀ ∈ A, t₀ ≠ 1 → ψ y * ψ t₀ = ψ t₀ * ψ y →
      ψ y * ψ a * (ψ y)⁻¹ ∈ w183V4 (ψ a) (ψ b) ∧
        ψ y * ψ b * (ψ y)⁻¹ ∈ w183V4 (ψ a) (ψ b) := by
    intro t₀ ht₀A ht₀1 hc
    have hyt : y * t₀ = t₀ * y := hψinj (by rw [map_mul, map_mul]; exact hc)
    have hN := hTI t₀ ht₀A ht₀1 y hyt
    have hya : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN a).mp haA
    have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN b).mp hbA
    have h1 := w183MemV4OfMap ψ (hmem _ hya)
    have h2 := w183MemV4OfMap ψ (hmem _ hyb)
    rw [map_mul, map_mul, map_inv] at h1 h2
    exact ⟨h1, h2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact key a haA ha1 hgt
  · exact key b hbA hb1 hgt
  · refine key (a * b) (A.mul_mem haA hbA) ?_ (by rw [map_mul]; exact hgt)
    intro h
    exact hab (by
      have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact inv_eq_of_mul_eq_one_right hb2)

end CFSG.LocalAnalysis.WeakClosure81

end
