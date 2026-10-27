module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSingularPlaneRoots

public section

namespace CFSG.RankThree.PartTwo.Sec7

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)

variable {G : Type*} [Group G]

@[expose] def localSet (D : Set G) (d : G) : Set G :=
  {a | a ∈ D ∧ a * d = d * a ∧ a ≠ d}

@[expose] def centralizerIn (D : Set G) (a : G) : Set G :=
  {x | x ∈ D ∧ x * a = a * x}

@[expose] def vSet (D : Set G) (d : G) : Set G :=
  {a | a ∈ D ∧ centralizerIn D a = centralizerIn D d}

@[expose] def wSet (D : Set G) (d : G) : Set G :=
  {a | a ∈ D ∧ localSet D a = localSet D d}

@[expose] def conjOrbit (X : Subgroup G) (d : G) : Set G :=
  {a | ∃ x ∈ X, a = x * d * x⁻¹}

theorem mul_self_eq_one_of_orderOf_eq_two {a : G} (h : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem conj_eq_of_orderOf_mul_eq_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h3 : (a * b) ^ 3 = 1) : (a * b) * a * (a * b)⁻¹ = b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h6 : a * b * a * b * a * b = 1 := by
    rw [← h3]
    simp [pow_succ, mul_assoc]
  rw [mul_inv_rev, hai, hbi]
  calc a * b * a * (b * a) = (a * b * a * b * a * b) * b := by
        simp only [mul_assoc, hb, mul_one]
    _ = b := by rw [h6, one_mul]

theorem rank3II_7_1 [Finite G] {D A B : Set G} (hD : IsThreeTranspositions D) (hAB : D = A ∪ B)
    (hdisj : Disjoint A B) (hA : ∀ g : G, ∀ x ∈ A, g * x * g⁻¹ ∈ A) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have haD : a ∈ D := hAB ▸ Or.inl ha
  have hbD : b ∈ D := hAB ▸ Or.inr hb
  have ha2 := mul_self_eq_one_of_orderOf_eq_two (hD.1.2.1 a haD)
  have hb2 := mul_self_eq_one_of_orderOf_eq_two (hD.1.2.1 b hbD)
  have hnot : b ∉ A := fun hbA => Set.disjoint_left.mp hdisj hbA hb
  have hpos : 0 < orderOf (a * b) := orderOf_pos _
  have hle : orderOf (a * b) ≤ 3 := hD.2 a haD b hbD
  have h123 : orderOf (a * b) = 1 ∨ orderOf (a * b) = 2 ∨ orderOf (a * b) = 3 := by omega
  rcases h123 with h | h | h
  ·
    have h1 : a * b = 1 := orderOf_eq_one_iff.mp h
    have hba : b = a := by
      rw [← inv_eq_of_mul_eq_one_left ha2]
      exact eq_inv_of_mul_eq_one_right h1
    exact absurd (hba ▸ ha) hnot
  ·
    have h2 : a * b * (a * b) = 1 := by
      rw [← pow_two, ← h, pow_orderOf_eq_one]
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
    have := eq_inv_of_mul_eq_one_left h2
    rw [mul_inv_rev, hai, hbi] at this
    exact this
  ·
    have h3 : (a * b) ^ 3 = 1 := by rw [← h, pow_orderOf_eq_one]
    exact absurd (conj_eq_of_orderOf_mul_eq_three ha2 hb2 h3 ▸ hA (a * b) a ha) hnot

@[expose] def Item72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), IsThreeTranspositions D →
    (∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) → ∀ d ∈ D,
      vSet D d = conjOrbit (CFSG.pCore 2 G) d ∧ wSet D d = conjOrbit (CFSG.pCore 3 G) d ∧
      (IsPGroup 2 (Subgroup.closure (localSet D d)) →
        (CFSG.pCore 3 (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G)) ⊔
          Subgroup.zpowers d = ⊤)

@[expose] def Item73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), IsThreeTranspositions D →
    (∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) → ∀ d ∈ D, ∀ n : ℕ, (n = 3 ∨ n = 4) →
      Nonempty (Subgroup.closure (localSet D d) ≃* Equiv.Perm (Fin n)) →
        Nonempty (G ≃* Equiv.Perm (Fin (n + 2))) ∨
          n = 3 ∧ ¬ CFSG.pCore 3 G ≤ Subgroup.center G

end CFSG.RankThree.PartTwo.Sec7
