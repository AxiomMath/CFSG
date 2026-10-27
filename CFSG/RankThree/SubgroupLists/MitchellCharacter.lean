module

public import CFSG.RankThree.SubgroupLists.MitchellQOne

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K] [Finite K]

theorem false_of_forall_conj_anticommute (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) {q : Matrix V₄ V₄ K}
    (hq0 : q ≠ 0)
    (hantiF : ∀ g : G, (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q =
      -(q * (((g * t * g⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K))) : False := by
  set T : Matrix V₄ V₄ K := ((t : GL V₄ K) : Matrix V₄ V₄ K) with hT
  have hsign : ∀ x : G, ∃ ε : K, ε * ε = 1 ∧
      ((x : GL V₄ K) : Matrix V₄ V₄ K) * q = ε •
          (q * ((x : GL V₄ K) : Matrix V₄ V₄ K)) := by
    intro x
    have hx : x ∈ Subgroup.closure ({y | ∃ g : G, y = g * t * g⁻¹} ∪ {⟨-1, hneg⟩}) := by
      rw [closure_conj_neg_eq_top hq hZ hneg ht]; trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨g, rfl⟩ | hy
      · exact ⟨-1, by ring, by rw [neg_one_smul]; exact hantiF g⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨1, by ring, by simp⟩
    | one => exact ⟨1, by ring, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨ε₁, h₁, hy⟩ := hy
      obtain ⟨ε₂, h₂, hz⟩ := hz
      refine ⟨ε₁ * ε₂, by linear_combination ε₁ * ε₁ * h₂ + h₁, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [Matrix.mul_assoc, hz, Matrix.mul_smul, ← Matrix.mul_assoc, hy, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc, mul_comm]
    | inv y _ hy =>
      obtain ⟨ε, hε, hy⟩ := hy
      refine ⟨ε, hε, ?_⟩
      have hyy : (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
          ((y : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      have hyy' : ((y : GL V₄ K) : Matrix V₄ V₄ K) *
          (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      calc (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q
          = (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q *
              (((y : GL V₄ K) : Matrix V₄ V₄ K) *
              (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                  by rw [hyy', Matrix.mul_one]
        _ = (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
            (ε • (((y : GL V₄ K) : Matrix V₄ V₄ K) * q)) *
              (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
            have : q * ((y : GL V₄ K) : Matrix V₄ V₄ K) = ε •
                (((y : GL V₄ K) : Matrix V₄ V₄ K) * q) := by
              rw [hy, smul_smul, hε, one_smul]
            rw [← this]; simp only [Matrix.mul_assoc]
        _ = ε • (q * (((y⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  set Splus : Subgroup G :=
    { carrier := {x | ((x : GL V₄ K) : Matrix V₄ V₄ K) * q = q *
        ((x : GL V₄ K) : Matrix V₄ V₄ K)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul] at ha hb ⊢
        rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have haa : (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
            ((a : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
        have haa' : ((a : GL V₄ K) : Matrix V₄ V₄ K) *
            (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
          rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
        calc (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q
            = (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q *
                (((a : GL V₄ K) : Matrix V₄ V₄ K) *
                (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                    by rw [haa', Matrix.mul_one]
          _ = (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) *
              (((a : GL V₄ K) : Matrix V₄ V₄ K) * q) *
                (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
              rw [ha]; simp only [Matrix.mul_assoc]
          _ = q * (((a⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) := by
              simp only [← Matrix.mul_assoc, haa, Matrix.one_mul] }
  have hcommS : ∀ x y : G, ⁅x, y⁆ ∈ Splus := by
    intro x y
    obtain ⟨εx, hεx, hx⟩ := hsign x
    obtain ⟨εy, hεy, hy⟩ := hsign y
    show (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K) * q = q *
        (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K)
    set C : Matrix V₄ V₄ K := (((⁅x, y⁆ : G) : GL V₄ K) : Matrix V₄ V₄ K)
    set X : Matrix V₄ V₄ K := ((x : GL V₄ K) : Matrix V₄ V₄ K)
    set Y : Matrix V₄ V₄ K := ((y : GL V₄ K) : Matrix V₄ V₄ K)
    have hCYX : C * (Y * X) = X * Y := by
      have : ⁅x, y⁆ * (y * x) = x * y := by rw [commutatorElement_def]; group
      have := congrArg (fun z : G => ((z : GL V₄ K) : Matrix V₄ V₄ K)) this
      simpa [C, X, Y] using this
    have hXYq : X * Y * q = (εx * εy) • (q * (X * Y)) := by
      rw [Matrix.mul_assoc, hy, Matrix.mul_smul, ← Matrix.mul_assoc, hx, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc, mul_comm]
    have hYXq : Y * X * q = (εx * εy) • (q * (Y * X)) := by
      rw [Matrix.mul_assoc, hx, Matrix.mul_smul, ← Matrix.mul_assoc, hy, Matrix.smul_mul,
        smul_smul, Matrix.mul_assoc]
    have hε0 : εx * εy ≠ 0 := by
      intro h0
      have : εx * εy * (εx * εy) = 1 := by linear_combination εx * εx * hεy + hεx
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have hkey : (εx * εy) • ((C * q - q * C) * (Y * X)) = 0 := by
      have e1 : C * q * (Y * X) = (εx * εy)⁻¹ • (C * (Y * X) * q) := by
        rw [Matrix.mul_assoc C (Y * X) q, hYXq, Matrix.mul_smul, smul_smul,
          inv_mul_cancel₀ hε0, one_smul, Matrix.mul_assoc]
      have e2 : q * C * (Y * X) = (εx * εy)⁻¹ • (X * Y * q) := by
        rw [hXYq, smul_smul, inv_mul_cancel₀ hε0, one_smul, Matrix.mul_assoc, hCYX]
      rw [Matrix.sub_mul, e1, e2, hCYX, sub_self, smul_zero]
    rcases smul_eq_zero.mp hkey with h | h
    · exact absurd h hε0
    · have hW : (((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) = Y * X := by
        simp [X, Y]
      have hWW : (((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) *
          ((((y * x)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have : C * q - q * C = 0 := by
        calc C * q - q * C = (C * q - q * C) *
            ((((y * x : G) : GL V₄ K) : Matrix V₄ V₄ K) *
              ((((y * x)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K)) :=
                  by rw [hWW, Matrix.mul_one]
          _ = 0 := by rw [← Matrix.mul_assoc, hW, h, Matrix.zero_mul]
      exact sub_eq_zero.mp this
  have hle : commutator G ≤ Splus := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcommS x y
  have : Group.IsPerfect G := hq.1
  have htS : t ∈ Splus := hle (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have htq : T * q = q * T := htS
  have hanti1 : T * q = -(q * T) := by
    have := hantiF 1
    simpa [hT] using this
  have hqT : q * T = 0 := by
    have : (2 : K) • (q * T) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← htq]
      rw [hanti1, neg_add_cancel]
    exact (smul_eq_zero.mp this).resolve_left h2
  apply hq0
  have hTT : T * T = 1 := by rw [hT, ← Units.val_mul, ht.2.1, Units.val_one]
  calc q = q * T * T := by rw [Matrix.mul_assoc, hTT, Matrix.mul_one]
    _ = 0 := by rw [hqT, Matrix.zero_mul]

end CFSG.RankThree.SubgroupLists
