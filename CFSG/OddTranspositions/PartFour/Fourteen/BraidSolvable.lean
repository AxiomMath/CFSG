module

public import Mathlib.GroupTheory.Solvable
import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo

public section

namespace CFSG.OddTranspositions.PartFour

variable {X : Type} [Group X]

theorem mem_normalizer_closure_of_mul_self {S : Set X} {g : X} (hg : g * g = 1)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set X) := by
  have key : ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ ∈ Subgroup.closure S := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key y, fun hy => ?_⟩
  have h2 := key _ hy
  have e : g * (g * y * g⁻¹) * g⁻¹ = y := by
    rw [hginv]
    calc g * (g * y * g) * g = (g * g) * y * (g * g) := by group
      _ = y := by rw [hg, one_mul, mul_one]
  rwa [e] at h2

theorem isSolvable_closure_of_braid [Finite X] {a b c : X} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hac : Commute a c) (hab : a * b * a = b * a * b)
    (hbc : b * c * b = c * b * c) :
    Group.IsSolvable (Subgroup.closure ({a, b, c} : Set X)) := by
  set Y := Subgroup.closure ({a, b, c} : Set X) with hY
  let a' : Y := ⟨a, Subgroup.subset_closure (by simp)⟩
  let b' : Y := ⟨b, Subgroup.subset_closure (by simp)⟩
  let c' : Y := ⟨c, Subgroup.subset_closure (by simp)⟩
  have ha' : a' * a' = 1 := Subtype.ext ha
  have hb' : b' * b' = 1 := Subtype.ext hb
  have hc' : c' * c' = 1 := Subtype.ext hc
  have hac' : a' * c' = c' * a' := Subtype.ext hac.eq
  have hab' : a' * b' * a' = b' * a' * b' := Subtype.ext hab
  have hbc' : b' * c' * b' = c' * b' * c' := Subtype.ext hbc
  have hai : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'
  have hbi : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'
  have hci : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right hc'
  set w : Y := b' * (a' * c') * b' with hw
  have key1 : w * a' = c' * w := by
    simp only [hw]
    calc b' * (a' * c') * b' * a' = b' * (c' * a') * b' * a' := by rw [hac']
      _ = b' * c' * (a' * b' * a') := by group
      _ = b' * c' * (b' * a' * b') := by rw [hab']
      _ = (b' * c' * b') * a' * b' := by group
      _ = (c' * b' * c') * a' * b' := by rw [hbc']
      _ = c' * (b' * (c' * a') * b') := by group
      _ = c' * (b' * (a' * c') * b') := by rw [hac']
  have key2 : w * c' = a' * w := by
    simp only [hw]
    calc b' * (a' * c') * b' * c' = b' * a' * (c' * b' * c') := by group
      _ = b' * a' * (b' * c' * b') := by rw [hbc']
      _ = (b' * a' * b') * c' * b' := by group
      _ = (a' * b' * a') * c' * b' := by rw [hab']
      _ = a' * (b' * (a' * c') * b') := by group
  have hcomm : (a' * c') * w = w * (a' * c') := by
    calc (a' * c') * w = c' * (a' * w) := by rw [hac']; group
      _ = c' * (w * c') := by rw [key2]
      _ = (c' * w) * c' := by group
      _ = (w * a') * c' := by rw [key1]
      _ = w * (a' * c') := by group
  set V : Subgroup Y := Subgroup.closure {a' * c', w} with hV
  have hacV : a' * c' ∈ V := Subgroup.subset_closure (by simp)
  have hwV : w ∈ V := Subgroup.subset_closure (by simp)
  have hnorm : ∀ g ∈ ({a', b', c'} : Set Y), g ∈ Subgroup.normalizer (V : Set Y) := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · refine mem_normalizer_closure_of_mul_self ha' fun x hx => ?_
      rcases hx with rfl | rfl
      · rw [hai, show a' * (a' * c') * a' = (a' * a') * c' * a' by group, ha', one_mul, ← hac']
        exact hacV
      · rw [hai, mul_assoc, key1, ← mul_assoc]
        exact Subgroup.mul_mem _ hacV hwV
    · refine mem_normalizer_closure_of_mul_self hb' fun x hx => ?_
      rcases hx with rfl | rfl
      · rw [hbi]
        exact hwV
      · rw [hbi, hw, show b' * (b' * (a' * c') * b') * b' = (b' * b') * (a' * c') * (b' * b') by
          group, hb', one_mul, mul_one]
        exact hacV
    · refine mem_normalizer_closure_of_mul_self hc' fun x hx => ?_
      rcases hx with rfl | rfl
      · rw [hci, hac', show c' * (c' * a') * c' = (c' * c') * a' * c' by group, hc', one_mul,
          ← hac']
        exact hacV
      · rw [hci, mul_assoc, key2, ← mul_assoc, ← hac']
        exact Subgroup.mul_mem _ hacV hwV
  have hYtop : Subgroup.closure (((↑) : Y → X) ⁻¹' ({a, b, c} : Set X)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hpre : ((↑) : Y → X) ⁻¹' ({a, b, c} : Set X) = ({a', b', c'} : Set Y) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · rintro (h | h | h) <;> rw [h] <;> simp [a', b', c']
  have hgen : Subgroup.closure ({a', b', c'} : Set Y) = ⊤ := by rw [← hpre, hYtop]
  have hVn : V.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hnorm
  have hVsolv : Group.IsSolvable V := by
    let : CommGroup V := Subgroup.closureCommGroupOfComm (k := {a' * c', w}) (by
      intro x hx y hy hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hcomm
      · exact hcomm.symm
      · exact absurd rfl hxy)
    exact isSolvable_of_comm mul_comm
  have hQsolv : Group.IsSolvable (Y ⧸ V) := by
    set π := QuotientGroup.mk' V
    have hA : π a' * π a' = 1 := by rw [← map_mul, ha', map_one]
    have hB : π b' * π b' = 1 := by rw [← map_mul, hb', map_one]
    have hC : π c' = π a' := by
      have h1 : π a' * π c' = 1 := by
        rw [← map_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hacV
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hA]
    have htop : Subgroup.zpowers (π a') ⊔ Subgroup.zpowers (π b') = ⊤ := by
      have hmap : (⊤ : Subgroup Y).map π = ⊤ :=
        Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective V)
      rw [← hmap, ← hgen, MonoidHom.map_closure]
      have himg : π '' ({a', b', c'} : Set Y) = ({π a', π b'} : Set (Y ⧸ V)) := by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hC]
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [himg, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    have h := CFSG.LocalAnalysis.WeakClosure81.isSolvable_sup_zpowers_of_mul_self_eq_one hA hB
    rw [htop] at h
    exact solvable_of_surjective (f := (⊤ : Subgroup (Y ⧸ V)).subtype)
      (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  exact solvable_of_ker_le_range V.subtype (QuotientGroup.mk' V) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])


theorem braid_of_cube {a b : X} (ha : a * a = 1) (hb : b * b = 1) (h3 : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h : a * b * a * (b * a * b) = 1 := by
    rw [← h3, pow_three]
    group
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hai, hbi, mul_assoc]

end CFSG.OddTranspositions.PartFour
