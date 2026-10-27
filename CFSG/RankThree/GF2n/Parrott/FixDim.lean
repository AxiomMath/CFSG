module

public import CFSG.RankThree.GF2n.Parrott.CentralizerV
public import CFSG.RankThree.GF2n.Parrott.LinearV
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

section ParrottHyp

variable (h : Tim79a.ParrottHyp z)

@[expose] noncomputable def fixedAddSubgroup (x : H z) :
    AddSubgroup (Additive (QuotientV.V z)) :=
  Subgroup.toAddSubgroup (autFixedSubgroup (conjV h x))

@[simp] theorem mem_fixedAddSubgroup_iff (x : H z) (v : Additive (QuotientV.V z)) :
    v ∈ fixedAddSubgroup h x ↔
      Additive.toMul v ∈ autFixedSubgroup (conjV h x) :=
  Additive.mem_toAddSubgroup _ _

@[expose] noncomputable def fixSubmodule (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup (autFixedSubgroup (conjV h x)))

@[simp] theorem mem_fixSubmodule_iff (x : H z) (v : Additive (QuotientV.V z)) :
    v ∈ fixSubmodule h x ↔ Additive.toMul v ∈ autFixedSubgroup (conjV h x) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [fixSubmodule, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem card_fixSubmodule (x : H z) :
    Nat.card ↥(fixSubmodule h x) = Nat.card ↥(autFixedSubgroup (conjV h x)) := by
  apply Nat.card_congr
  refine
    { toFun := fun v => ⟨Additive.toMul v.1, (mem_fixSubmodule_iff h x v.1).mp v.2⟩
      invFun := fun w =>
        ⟨Additive.ofMul w.1, (mem_fixSubmodule_iff h x (Additive.ofMul w.1)).mpr (by simp)⟩
      left_inv := by
        intro v
        ext
        simp
      right_inv := by
        intro w
        ext
        simp }

@[expose] noncomputable def fixDimV (x : H z) : ℕ :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  Module.finrank (ZMod 2) (fixSubmodule h x)

theorem card_fix (x : H z) :
    Nat.card ↥(autFixedSubgroup (conjV h x)) = 2 ^ fixDimV h x := by
  rw [← card_fixSubmodule h x]
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixSubmodule h x)),
    Nat.card_zmod]
  rfl

theorem card_centralizerJ_eq_card_inf_mul_card_pow_fixDim {x : H z}
    (hcopx : Nat.Coprime (orderOf x) (Nat.card (J z))) :
    Nat.card (centralizerJ x) =
      Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) * 2 ^ fixDimV h x := by
  rw [card_centralizerJ_eq_card_inf_mul_card_autFixed h hcopx, card_fix h x]

theorem card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
    {x : H z} (hx : orderOf x = 3) :
    Nat.card (centralizerJ x) =
      Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) * 2 ^ fixDimV h x := by
  refine card_centralizerJ_eq_card_inf_mul_card_pow_fixDim h ?_
  rw [hx, card_J h]
  norm_num

end ParrottHyp

end CFSG.RankThree.GF2n.Parrott
