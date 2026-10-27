module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6

namespace S126

theorem permAct_allOnes (σ : Equiv.Perm (Fin 8)) : permAct 8 σ (allOnes 8) = allOnes 8 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply]
  rfl

abbrev D8 : Type := ↥(coreMod 8) ⧸ natKer 8

@[expose] noncomputable def dAct (σ : Equiv.Perm (Fin 8)) : D8 →* D8 :=
  QuotientGroup.map (natKer 8) (natKer 8) (coreAct 8 σ).toMonoidHom (by
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hx : (x : PermMod 8) ∈ Subgroup.zpowers
      (allOnes 8))
    show ((coreAct 8 σ x : coreMod 8) : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
    have hk' : (x : PermMod 8) = allOnes 8 ^ k := hk.symm
    rw [coreAct_coe, hk', map_zpow, permAct_allOnes]
    exact Subgroup.zpow_mem_zpowers _ k)

@[expose] def wt (x : PermMod 8) : ℕ :=
  (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0).card

@[expose] def HasWt (k : ℕ) (y : D8) : Prop :=
  ∃ m : ↥(coreMod 8), (QuotientGroup.mk m : D8) = y ∧ wt (m : PermMod 8) = k

@[expose] def IsNonsing (y : D8) : Prop := HasWt 2 y

@[expose] def partner (i : Fin 8) : Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6] i

@[expose] def PresPart (σ : Equiv.Perm (Fin 8)) : Prop :=
  (∀ i, σ (partner i) = partner (σ i)) ∧
    ((∀ i : Fin 8, i.val < 4 → (σ i).val < 4) ∨ (∀ i : Fin 8, i.val < 4 → 4 ≤ (σ i).val))

@[expose] def eset (S : Finset (Fin 8)) : PermMod 8 :=
  Multiplicative.ofAdd fun i => if i ∈ S then 1 else 0

@[expose] def X5 : Subgroup ↥(coreMod 8) where
  carrier := {m | Multiplicative.toAdd (m : PermMod 8) 0 + Multiplicative.toAdd (m : PermMod 8) 1 +
    Multiplicative.toAdd (m : PermMod 8) 2 + Multiplicative.toAdd (m : PermMod 8) 3 = 0}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, toAdd_mul, Pi.add_apply] at ha hb ⊢
    calc _ = (Multiplicative.toAdd (a : PermMod 8) 0 + Multiplicative.toAdd (a : PermMod 8) 1 +
          Multiplicative.toAdd (a : PermMod 8) 2 + Multiplicative.toAdd (a : PermMod 8) 3) +
          (Multiplicative.toAdd (b : PermMod 8) 0 + Multiplicative.toAdd (b : PermMod 8) 1 +
          Multiplicative.toAdd (b : PermMod 8) 2 + Multiplicative.toAdd (b : PermMod 8) 3) := by
          ring
      _ = 0 := by rw [ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv, toAdd_inv, Pi.neg_apply] at ha ⊢
    calc _ = -(Multiplicative.toAdd (a : PermMod 8) 0 + Multiplicative.toAdd (a : PermMod 8) 1 +
          Multiplicative.toAdd (a : PermMod 8) 2 + Multiplicative.toAdd (a : PermMod 8) 3) := by
          ring
      _ = 0 := by rw [ha, neg_zero]

@[expose] def X2 : Subgroup ↥(coreMod 8) :=
  Subgroup.closure {m | (m : PermMod 8) = eset {0, 1, 2, 3} ∨ (m : PermMod 8) = eset {0, 1, 4, 5}}

@[expose] def X1 : Subgroup ↥(coreMod 8) :=
  Subgroup.closure {m | (m : PermMod 8) = eset {0, 1, 2, 3}}

@[expose] noncomputable def W1 : Subgroup D8 := X1.map (QuotientGroup.mk' (natKer 8))

@[expose] noncomputable def W2 : Subgroup D8 := X2.map (QuotientGroup.mk' (natKer 8))

@[expose] noncomputable def W5 : Subgroup D8 := X5.map (QuotientGroup.mk' (natKer 8))

variable {G : Type} [Group G]

structure Frame126 (T L V : Subgroup G) [IsMulCommutative ↥V] where
  π : ↥(alternatingGroup (Fin 8)) →* ↥(autOn L V)
  π_surj : Function.Surjective π
  β : ↥V →* D8
  β_surj : Function.Surjective β
  β_ker : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Subgroup.centralizer (L : Set G)
  equi : ∀ (σ : ↥(alternatingGroup (Fin 8))) (v : ↥V),
    β (((π σ : ↥(autOn L V)) : MulAut ↥V) v) = dAct σ (β v)
  tAct : ∀ t ∈ T, ∃ σ : Equiv.Perm (Fin 8), PresPart σ ∧
    ∀ v w : ↥V, (w : G) = t * v * t⁻¹ → β w = dAct σ (β v)

namespace Frame126

variable {T L V : Subgroup G} [IsMulCommutative ↥V] (F : Frame126 T L V)

@[expose] def Nonsing (v : G) : Prop := ∃ hv : v ∈ V, IsNonsing (F.β ⟨v, hv⟩)

@[expose] def Wt4 (v : G) : Prop := ∃ hv : v ∈ V, HasWt 4 (F.β ⟨v, hv⟩)

@[expose] noncomputable def V1 : Subgroup G := (W1.comap F.β).map V.subtype

@[expose] noncomputable def V2 : Subgroup G := (W2.comap F.β).map V.subtype

@[expose] noncomputable def V5 : Subgroup G := (W5.comap F.β).map V.subtype

end Frame126

abbrev Li (L W : Subgroup G) : Subgroup G := L₁Of L W

abbrev Ri (T L W : Subgroup G) : Subgroup G := pCoreOf 2 (Li L W ⊔ T)

end S126

end CFSG.Quasithin.H13
