module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def calLp (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {L | L ∈ calC D.M ∧ p ∈ piSet L}

@[expose] def calLpStar (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | ∃ L ∈ calLp D p, X = conjClosure D.M L}

@[expose] def IsA5xA5 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))

@[expose] def calL1Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | X ∈ calLpStar D p ∧
    ((∃ f : ℕ, IsG2 (Bar2 X) f ∨ IsSp4 (Bar2 X) f ∨ IsU4 (Bar2 X) f) ∨ IsU5 (Bar2 X) 2)}

@[expose] def calL2Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | X ∈ calLpStar D p ∧ X ∉ calLp D p ∧ ¬ IsA5xA5 (Bar2 X)}

@[expose] def calL3Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | X ∈ calLpStar D p ∧ IsA5xA5 (Bar2 X)}

@[expose] def calL4Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | X ∈ calLpStar D p ∧
    (∃ n : ℕ, IsL2 (Bar2 X) (2 ^ n) ∨ IsU3 (Bar2 X) (2 ^ n)) ∧ ¬ IsAlt (Bar2 X) 5}

@[expose] def calL5Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  {X | X ∈ calLpStar D p ∧ IsAlt (Bar2 X) 5}

@[expose] def calLjStar (D : Data G) (p : ℕ) : ℕ → Set (Subgroup G) := fun j =>
  if j = 1 then calL1Star D p
  else if j = 2 then calL2Star D p
  else if j = 3 then calL3Star D p
  else if j = 4 then calL4Star D p
  else if j = 5 then calL5Star D p
  else ∅

@[expose] noncomputable def jM (D : Data G) (p : ℕ) : ℕ :=
  sInf {j | 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty}

@[expose] noncomputable def calL0Star (D : Data G) (p : ℕ) : Set (Subgroup G) :=
  calLjStar D p (jM D p)

@[expose] def centSection (M A B : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ M ∧ m ∈ normalizer (A : Set G) ∧ m ∈ normalizer (B : Set G) ∧
    ∀ a ∈ A, m * a * m⁻¹ * a⁻¹ ∈ B}
  one_mem' := ⟨one_mem _, one_mem _, one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁M, hm₁A, hm₁B, h₁⟩ ⟨hm₂M, hm₂A, hm₂B, h₂⟩
    refine ⟨M.mul_mem hm₁M hm₂M, Subgroup.mul_mem _ hm₁A hm₂A,
      Subgroup.mul_mem _ hm₁B hm₂B, fun a ha => ?_⟩
    have hb : m₂ * a * m₂⁻¹ * a⁻¹ ∈ B := h₂ a ha
    have hba : m₂ * a * m₂⁻¹ = (m₂ * a * m₂⁻¹ * a⁻¹) * a := by group
    have hm₁b : m₁ * (m₂ * a * m₂⁻¹ * a⁻¹) * m₁⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hm₁B _).mp hb
    have hEq : m₁ * m₂ * a * (m₁ * m₂)⁻¹ * a⁻¹ =
        (m₁ * (m₂ * a * m₂⁻¹ * a⁻¹) * m₁⁻¹) * (m₁ * a * m₁⁻¹ * a⁻¹) := by
      rw [hba]
      group
    rw [hEq]
    exact B.mul_mem hm₁b (h₁ a ha)
  inv_mem' := by
    rintro m ⟨hmM, hmA, hmB, h⟩
    refine ⟨M.inv_mem hmM, Subgroup.inv_mem _ hmA, Subgroup.inv_mem _ hmB, fun a ha => ?_⟩
    have ha' : m⁻¹ * a * m ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmA) a).mp ha
    have h' : m * (m⁻¹ * a * m) * m⁻¹ * (m⁻¹ * a * m)⁻¹ ∈ B := h _ ha'
    have hinv : (m⁻¹ * a * m * a⁻¹)⁻¹ =
        m * (m⁻¹ * a * m) * m⁻¹ * (m⁻¹ * a * m)⁻¹ := by group
    have hx : (m⁻¹ * a * m * a⁻¹)⁻¹ ∈ B := hinv.symm ▸ h'
    simpa using B.inv_mem hx

@[expose] def Lp (D : Data G) (p : ℕ) : Subgroup G :=
  Opp p (oTwoEOf D.M)

@[expose] def Sp (D : Data G) (p : ℕ) : Subgroup G :=
  Opp p (centSection D.M (Lp D p) (CFSG.Open.pCoreOf 2 (Lp D p)))

@[expose] def Hyp1754 (D : Data G) (p : ℕ) : Prop :=
  p ∈ D.sig ∧ ∀ L ∈ calC D.M,
    (L.subgroupOf D.M).Normal ∧
      (F08.Thin8 L ∨ (∃ f : ℕ, IsU3 (Bar2 L) f) ∨ IsL3 (Bar2 L) 2)

@[expose] noncomputable def eM (M : Subgroup G) : ℕ :=
  sSup {n | ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = CFSG.Open.pRank p M}

@[expose] def oUpperTwo (H : Subgroup G) : Subgroup G :=
  CFSG.ComponentClassification.AS76b.oUpperTwo H

theorem oUpperTwo_le (H : Subgroup G) : oUpperTwo H ≤ H := by
  unfold oUpperTwo CFSG.ComponentClassification.AS76b.oUpperTwo
  exact (Subgroup.closure_le H).mpr fun x hx => hx.1

theorem oUpperTwo_eq_closure (H : Subgroup G) :
    oUpperTwo H = Subgroup.closure {h : G | h ∈ H ∧ Odd (orderOf h)} := by
  unfold oUpperTwo CFSG.ComponentClassification.AS76b.oUpperTwo
  rfl

@[expose] noncomputable def nOf (L : Subgroup G) : ℕ :=
  sInf {f | 0 < f ∧ ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
    CFSG.Blueprint.LieModel (Bar2 L) t m 2 f}

@[expose] def IsMaxParabolicOver (X S P : Subgroup G) : Prop :=
  P ≤ X ∧ X ⊓ normalizer (S : Set G) ≤ P ∧ P ≠ X ∧
    ∀ Q : Subgroup G, P ≤ Q → Q ≤ X → Q = P ∨ Q = X

@[expose] def SwapsParabolics (T X : Subgroup G) : Prop :=
  ∃ t ∈ T, ∃ P : Subgroup G,
    IsMaxParabolicOver X (T ⊓ X) P ∧ P.map (MulAut.conj t).toMonoidHom ≠ P

@[simp] theorem mem_calLp {D : Data G} {p : ℕ} {L : Subgroup G} :
    L ∈ calLp D p ↔ L ∈ calC D.M ∧ p ∈ piSet L := Iff.rfl

@[simp] theorem mem_calLpStar {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calLpStar D p ↔ ∃ L ∈ calLp D p, X = conjClosure D.M L := Iff.rfl

@[simp] theorem mem_calL1Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL1Star D p ↔ X ∈ calLpStar D p ∧
      ((∃ f : ℕ, IsG2 (Bar2 X) f ∨ IsSp4 (Bar2 X) f ∨ IsU4 (Bar2 X) f) ∨
        IsU5 (Bar2 X) 2) := Iff.rfl

@[simp] theorem mem_calL2Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL2Star D p ↔ X ∈ calLpStar D p ∧ X ∉ calLp D p ∧ ¬ IsA5xA5 (Bar2 X) := Iff.rfl

@[simp] theorem mem_calL3Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL3Star D p ↔ X ∈ calLpStar D p ∧ IsA5xA5 (Bar2 X) := Iff.rfl

@[simp] theorem mem_calL4Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL4Star D p ↔ X ∈ calLpStar D p ∧
      (∃ n : ℕ, IsL2 (Bar2 X) (2 ^ n) ∨ IsU3 (Bar2 X) (2 ^ n)) ∧
        ¬ IsAlt (Bar2 X) 5 := Iff.rfl

@[simp] theorem mem_calL5Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL5Star D p ↔ X ∈ calLpStar D p ∧ IsAlt (Bar2 X) 5 := Iff.rfl

@[simp] theorem mem_calL0Star {D : Data G} {p : ℕ} {X : Subgroup G} :
    X ∈ calL0Star D p ↔ X ∈ calLjStar D p (jM D p) := Iff.rfl

theorem calLp_subset_calC (D : Data G) (p : ℕ) : calLp D p ⊆ calC D.M :=
  fun _ hx => hx.1

theorem calLjStar_subset (D : Data G) (p j : ℕ) : calLjStar D p j ⊆ calLpStar D p := by
  intro X hX
  simp only [calLjStar] at hX ⊢
  split_ifs at hX ⊢ <;>
    simp_all [mem_calL1Star, mem_calL2Star, mem_calL3Star, mem_calL4Star, mem_calL5Star]

theorem calL0Star_subset (D : Data G) (p : ℕ) : calL0Star D p ⊆ calLpStar D p :=
  calLjStar_subset D p (jM D p)

theorem centSection_le (M A B : Subgroup G) : centSection M A B ≤ M := by
  rintro m ⟨hmM, -, -, -⟩
  exact hmM

theorem Lp_le_oTwoEOf (D : Data G) (p : ℕ) : Lp D p ≤ oTwoEOf D.M := by
  unfold Lp Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le _).mpr fun x hx => hx.1

theorem Lp_le_M (D : Data G) (p : ℕ) : Lp D p ≤ D.M :=
  (Lp_le_oTwoEOf D p).trans (Subgroup.map_subtype_le _)

theorem Sp_le_centSection (D : Data G) (p : ℕ) :
    Sp D p ≤ centSection D.M (Lp D p) (CFSG.Open.pCoreOf 2 (Lp D p)) := by
  unfold Sp Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le _).mpr fun x hx => hx.1

theorem Sp_le (D : Data G) (p : ℕ) : Sp D p ≤ D.M :=
  (Sp_le_centSection D p).trans (centSection_le _ _ _)

@[expose] def IsL2U3Product (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), Nonempty (X ≃* A × B) ∧ IsL2 A n ∧ IsU3 B n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
