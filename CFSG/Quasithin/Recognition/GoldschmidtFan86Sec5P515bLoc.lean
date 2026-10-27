module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Rev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Seven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Rev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513bAux
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Prod
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P53b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57Mech
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Dih

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

theorem four_prods {H : Type*} [Group H] {a b d x y : H} (hab : a * b = b * a)
    (had : a * d = d * a) (hbd : b * d = d * b) (hdd : d * d = 1) (hx : x = a ∨ x = a * d)
    (hy : y = b ∨ y = b * d) :
    (x * y = a * b ∨ x * y = a * b * d) ∧ (y * x = a * b ∨ y * x = a * b * d) := by
  have h1 : b * d * a = a * b * d := by
    calc b * d * a = b * (d * a) := by rw [mul_assoc]
      _ = b * (a * d) := by rw [had]
      _ = b * a * d := by rw [mul_assoc]
      _ = a * b * d := by rw [hab]
  have h2 : a * d * b = a * b * d := by
    calc a * d * b = a * (d * b) := by rw [mul_assoc]
      _ = a * (b * d) := by rw [hbd]
      _ = a * b * d := by rw [mul_assoc]
  have h3 : a * d * (b * d) = a * b := by
    calc a * d * (b * d) = a * d * b * d := by rw [mul_assoc (a * d) b d]
      _ = a * b * d * d := by rw [h2]
      _ = a * b := by rw [mul_assoc, hdd, mul_one]
  have h4 : b * d * (a * d) = a * b := by
    calc b * d * (a * d) = b * d * a * d := by rw [mul_assoc (b * d) a d]
      _ = a * b * d * d := by rw [h1]
      _ = a * b := by rw [mul_assoc, hdd, mul_one]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨Or.inl rfl, Or.inl hab.symm⟩
  · exact ⟨Or.inr (by rw [mul_assoc]), Or.inr h1⟩
  · exact ⟨Or.inr h2, Or.inr (by rw [← mul_assoc, ← hab])⟩
  · exact ⟨Or.inl h3, Or.inl h4⟩

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mul_mem_nbrStab_of_sq_mem (F : FanTree Γ G) {v a : V} (hva : Γ.Adj v a) {z g : G}
    (hz : z ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)
    (hg : g ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) (hz2 : z * z = 1)
    (hg2 : g * g ∈ nbrStab Γ G v) (hn : z ∉ nbrStab Γ G v) (hn' : g ∉ nbrStab Γ G v) :
    z * g ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hva
  have hp : pval Γ v = 3 ∨ pval Γ v = 5 := F.valence v
  let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨z, hz⟩
  let e' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨g, hg⟩
  have he2 : e * e = 1 := Subtype.ext hz2
  have h1 : φ e ≠ 1 := fun h => hn ((hφ e).2 h)
  have h1' : φ e' ≠ 1 := fun h => hn' ((hφ e').2 h)
  have h2 : φ e * φ e = 1 := by rw [← map_mul, he2, map_one]
  have h2' : φ e' * φ e' = 1 := by
    rw [← map_mul]
    exact (hφ (e' * e')).1 hg2
  have h3 := units_sq_eq_one_unique hp (φ e) (φ e') h1 h2 h1' h2'
  have h4 : φ (e * e') = 1 := by rw [map_mul, ← h3]; exact h2
  exact (hφ (e * e')).2 h4

end P515

end CFSG.Quasithin.Fan86
