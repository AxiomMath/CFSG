module

public import CFSG.RankThree.GF2n.Smith81.S81QBridge
public import CFSG.RankThree.GF2n.Smith81.S81XE7Pf
public import CFSG.RankThree.GF2n.Smith81.S81QStepD6

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X


@[expose] def Psi0 : Finset Rt := Rn fA2 Rd6

theorem mem_Psi0 {γ : Rt} : γ ∈ Psi0 ↔ γ ∈ Perp ∧ γ nodeA2 = 1 := mem_Rn_iff (Or.inl rfl)

theorem Psi0_subset_Rd6 : Psi0 ⊆ Rd6 := Rn_subset _

theorem card_Psi0 : Psi0.card = 15 := card_Rn_fA2

theorem Psi0_subset_Phi : Psi0 ⊆ Phi (a0 : Fin e7Data.d) := by
  intro γ hγ
  obtain ⟨hP, h1⟩ := mem_Psi0.1 hγ
  exact mem_Phi.2 ⟨(perp_iff.1 hP).1, by rw [pr_a0_eq hP]; exact h1⟩

abbrev ND (K : Type) [Field K] : Type := ↥Psi0 → K

variable {K : Type} [Field K]

open _root_.Classical in
@[expose] def extD (n : ND K) : Rt → K := fun γ => if h : γ ∈ Psi0 then n ⟨γ, h⟩ else 0

theorem extD_of_mem {γ : Rt} (h : γ ∈ Psi0) (n : ND K) : extD n γ = n ⟨γ, h⟩ := by
  simp [extD, h]

theorem extD_of_not_mem {γ : Rt} (h : γ ∉ Psi0) (n : ND K) : extD n γ = 0 := by
  simp [extD, h]

theorem extD_add (n m : ND K) : extD (n + m) = extD n + extD m := by
  funext γ
  by_cases h : γ ∈ Psi0
  · simp [extD_of_mem h]
  · simp [extD_of_not_mem h]

@[expose] def uD (n : ND K) : Gp K := prodX (Phi (a0 : Fin e7Data.d)).toList (extD n)

theorem uD_add (n m : ND K) : uD (n + m) = uD n * uD m := by
  unfold uD
  rw [extD_add, prodX_mul (fun γ hγ => Finset.mem_toList.1 hγ)]

theorem uD_zero : uD (0 : ND K) = 1 := by
  have : extD (0 : ND K) = 0 := by
    funext γ
    by_cases h : γ ∈ Psi0
    · simp [extD_of_mem h]
    · simp [extD_of_not_mem h]
  unfold uD
  rw [this, prodX_zero]

theorem uD_single (β : ↥Psi0) (b : K) : uD (Pi.single β b) = xE β.1 b := by
  classical
  unfold uD
  have hβ : β.1 ∈ Phi (a0 : Fin e7Data.d) := Psi0_subset_Phi β.2
  have h := prodX_eq_single (L := (Phi (a0 : Fin e7Data.d)).toList) (Finset.nodup_toList _)
    (δ₀ := β.1) (Finset.mem_toList.2 hβ) (c := extD (Pi.single β b)) (fun γ hγ hne => by
      by_cases hγ' : γ ∈ Psi0
      · rw [extD_of_mem hγ']
        have : (⟨γ, hγ'⟩ : ↥Psi0) ≠ β := fun e => hne (congrArg Subtype.val e)
        simp [Pi.single_apply, this]
      · exact extD_of_not_mem hγ' _)
  rw [h, extD_of_mem β.2]
  simp

theorem uD_mem_URge (n : ND K) : uD n ∈ URge K Rd6 1 := by
  unfold uD prodX
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  by_cases hγ' : γ ∈ Psi0
  · exact xE_mem_URge (Psi0_subset_Rd6 hγ') (by
      have := (mem_Rd6.1 (Psi0_subset_Rd6 hγ')).2
      exact_mod_cast this) _
  · rw [extD_of_not_mem hγ']
    have : xE γ (0 : K) = 1 := e7Data_valid.xm_zero K γ
    rw [this]
    exact one_mem _

variable [CharP K 2]

theorem coef_uD (n : ND K) {δ : Rt} (hδ : IsRoot .E7 δ) (hδa : δ ∈ Psi0) {b : Fin e7Data.d}
    (hb : pr b δ = -1) :
    endoE (uD n) (Finsupp.single b 1) (shift δ b) = n ⟨δ, hδa⟩ := by
  unfold uD
  rw [coef_prodX (a0 : Fin e7Data.d) (extD n) b hδ hb, if_pos (Psi0_subset_Phi hδa),
    extD_of_mem hδa]

theorem uD_injective : Function.Injective (uD : ND K → Gp K) := by
  intro n m h
  funext δ
  have hδr : IsRoot .E7 δ.1 := (perp_iff.1 (mem_Psi0.1 δ.2).1).1
  obtain ⟨b, hb⟩ := exists_pr_eq_neg_one hδr
  have h1 := coef_uD n hδr δ.2 hb
  have h2 := coef_uD m hδr δ.2 hb
  rw [h] at h1
  exact h1.symm.trans h2

end CFSG.RankThree.GF2n.Smith81.D6Spin
