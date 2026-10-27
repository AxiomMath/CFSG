module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public noncomputable section

namespace CFSG.StandardType.F4SplitTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem exists_unitValue_equiv [Finite K] :
    Nonempty (Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1))) := by
  have he : Kˣ ≃* Multiplicative (ZMod (Nat.card Kˣ)) :=
    (zmodCyclicMulEquiv (inferInstance : IsCyclic Kˣ)).symm
  rw [Nat.card_units] at he
  exact ⟨he⟩

@[expose] def coordHom : (Fin Tag.F4.rank → Kˣ) →* adjointGroup .F4 K :=
  (rootDiagUnitHom .F4 K).codRestrict (adjointGroup .F4 K)
    (fun a => torusGroup_le_adjointGroup_F4 (F4_rootDiagUnit_mem_torusGroup a))

theorem coe_coordHom (a : Fin Tag.F4.rank → Kˣ) :
    (coordHom a : ModGL .F4 K) = rootDiagUnit .F4 a := rfl

theorem coordHom_injective : Function.Injective (coordHom (K := K)) := by
  intro a b h
  exact rootDiagUnit_injective (congrArg Subtype.val h)

@[expose] def corootTupleHom (j : Fin Tag.F4.rank) : Kˣ →* (Fin Tag.F4.rank → Kˣ) where
  toFun u i := u ^ CartanMatrix.F₄ i j
  map_one' := by ext i; simp
  map_mul' u v := by ext i; simp [mul_zpow]

@[expose] def corootHom (j : Fin Tag.F4.rank) : Kˣ →* adjointGroup .F4 K :=
  coordHom.comp (corootTupleHom j)

theorem coe_corootHom (j : Fin Tag.F4.rank) (u : Kˣ) :
    (corootHom j u : ModGL .F4 K) = torusElt .F4 K j u := by
  rw [corootHom, MonoidHom.comp_apply, coe_coordHom, torusElt_eq_rootDiagUnit]
  congr 1
  funext i
  have hC : Tag.F4.cartan j i = CartanMatrix.F₄ i j := by
    fin_cases i <;> fin_cases j <;> rfl
  simp only [corootTupleHom, MonoidHom.coe_mk, OneHom.coe_mk, hC]

theorem mem_range_coordHom_iff (g : adjointGroup .F4 K) :
    g ∈ (coordHom (K := K)).range ↔ (g : ModGL .F4 K) ∈ torusGroup .F4 K := by
  constructor
  · rintro ⟨a, rfl⟩
    exact F4_rootDiagUnit_mem_torusGroup a
  · intro hg
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    exact ⟨a, Subtype.ext ha.symm⟩

theorem mem_torusPow_iff (g : adjointGroup .F4 K) (p : ℕ) :
    g ∈ TableBF4.torusPow K p ↔ g ∈ (coordHom (K := K)).range ∧ g ^ p = 1 := by
  rw [TableBF4.mem_torusPow, mem_range_coordHom_iff]

theorem simple_conj_coordHom (j : Fin Tag.F4.rank) (a : Fin Tag.F4.rank → Kˣ) :
    weylElt .F4 K j 1 * (coordHom a : ModGL .F4 K) * (weylElt .F4 K j 1)⁻¹ =
      (coordHom a : ModGL .F4 K) * (corootHom j (a j) : ModGL .F4 K)⁻¹ := by
  rw [coe_coordHom, coe_corootHom, weylElt_conj_rootDiagUnit, torusElt_eq_rootDiagUnit,
    rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]

end CFSG.StandardType.F4SplitTorus
