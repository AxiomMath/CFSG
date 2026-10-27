module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem card_le_mul_of_comm_mem {X P : Subgroup D} {y : D}
    (hP : ∀ w ∈ X, w * y * w⁻¹ * y⁻¹ ∈ P) :
    Nat.card X ≤ Nat.card P *
      Nat.card (X ⊓ Subgroup.centralizer ({y} : Set D) : Subgroup D) := by
  set C : Subgroup D := X ⊓ Subgroup.centralizer ({y} : Set D) with hC
  have hCX : C ≤ X := inf_le_left
  have h1 : (C.subgroupOf X).index * Nat.card (C.subgroupOf X) = Nat.card X :=
    Subgroup.index_mul_card _
  have h2 : Nat.card (C.subgroupOf X) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  have h3 : (C.subgroupOf X).index ≤ Nat.card P := by
    rw [Subgroup.index]
    let F : (↥X ⧸ C.subgroupOf X) → P := Quotient.lift
      (fun w : ↥X => (⟨(w : D) * y * (w : D)⁻¹ * y⁻¹, hP w w.2⟩ : P)) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ C.subgroupOf X := QuotientGroup.leftRel_apply.mp hab
        have hc : ((a⁻¹ * b : ↥X) : D) ∈ C := hab'
        have hcy : ((a : D))⁻¹ * (b : D) ∈ Subgroup.centralizer ({y} : Set D) := hc.2
        have hy : ((a : D))⁻¹ * (b : D) * y = y * (((a : D))⁻¹ * (b : D)) :=
          Subgroup.mem_centralizer_singleton_iff.mp hcy
        apply Subtype.ext
        show (a : D) * y * (a : D)⁻¹ * y⁻¹ = (b : D) * y * (b : D)⁻¹ * y⁻¹
        have : (a : D) * y * (a : D)⁻¹ = (b : D) * y * (b : D)⁻¹ := by
          calc (a : D) * y * (a : D)⁻¹
              = (b : D) * (((b : D)⁻¹ * (a : D)) * y * ((b : D)⁻¹ * (a : D))⁻¹) * (b : D)⁻¹ := by
                group
            _ = (b : D) * y * (b : D)⁻¹ := by
                have hinv : ((b : D)⁻¹ * (a : D)) = (((a : D))⁻¹ * (b : D))⁻¹ := by group
                rw [hinv]
                have : (((a : D))⁻¹ * (b : D))⁻¹ * y * ((((a : D))⁻¹ * (b : D))⁻¹)⁻¹ = y := by
                  rw [inv_inv, mul_assoc, ← hy]
                  group
                rw [this]
        rw [this])
    have hinj : Function.Injective F := by
      intro a b hab
      induction a using Quotient.inductionOn with
      | h a =>
        induction b using Quotient.inductionOn with
        | h b =>
          apply Quotient.sound
          have hab' : (a : D) * y * (a : D)⁻¹ * y⁻¹ = (b : D) * y * (b : D)⁻¹ * y⁻¹ :=
            congrArg Subtype.val hab
          have e : (a : D) * y * (a : D)⁻¹ = (b : D) * y * (b : D)⁻¹ := mul_right_cancel hab'
          refine QuotientGroup.leftRel_apply.mpr ?_
          show ((a : D))⁻¹ * (b : D) ∈ C
          refine ⟨X.mul_mem (X.inv_mem a.2) b.2, ?_⟩
          show ((a : D))⁻¹ * (b : D) ∈ Subgroup.centralizer ({y} : Set D)
          rw [Subgroup.mem_centralizer_singleton_iff]
          symm
          calc y * (((a : D))⁻¹ * (b : D))
              = ((a : D))⁻¹ * ((a : D) * y * (a : D)⁻¹) * (b : D) := by group
            _ = ((a : D))⁻¹ * ((b : D) * y * (b : D)⁻¹) * (b : D) := by rw [e]
            _ = ((a : D))⁻¹ * (b : D) * y := by group
    exact Nat.card_le_card_of_injective F hinj
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

omit [Finite D] in
theorem Vv_B_le_Vn_two {u β : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hβ : (graph (A ⊔ B) A B).Adj u β) : Vv V β ≤ Vn V 2 u := by
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hu
  refine (Vv_B_le_iff hβt).mpr fun l hl => ?_
  have hlt : vtype l = false := vtype_eq_false_of_adj hl hβt
  refine Vv_le_Vn hlt ?_
  have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl u β l
  have h2 : CosetGeom.dist u β = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hβ
  have h3 : CosetGeom.dist β l = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hl
  omega

omit [Finite D] in
theorem inv_mul_mul_of_mul_mul_inv {g c : D} (hgc : g * c * g⁻¹ = c) : g⁻¹ * c * g = c := by
  calc g⁻¹ * c * g = g⁻¹ * (g * c * g⁻¹) * g := by rw [hgc]
    _ = c := by group

omit [Finite D] in
@[expose] def I2aProp (A B V : Subgroup D) : Prop :=
  ∀ β a a' t t' : CosetGeom (A ⊔ B) A B, vtype β = true → (graph (A ⊔ B) A B).Adj β a →
    (graph (A ⊔ B) A B).Adj β a' → a ≠ a' → (graph (A ⊔ B) A B).Adj a t →
    (graph (A ⊔ B) A B).Adj a' t' → t ≠ β → t' ≠ β → Vv V t ⊓ Vv V t' ≤ Vv V β

end GoldAmL3

end F6

end CFSG.Quasithin
