module

public import CFSG.RankThree.GF2n.Smith81.S81ZUnip
public import CFSG.RankThree.GF2n.Smith81.S81XE7Pf
public import CFSG.RankThree.GF2n.Smith81.S81XE7Fin

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X


abbrev NU (K : Type) [Field K] : Type := ↥(Phi a7) → K

variable {K : Type} [Field K]

open _root_.Classical in
@[expose] def extN (n : NU K) : Rt → K := fun γ => if h : γ ∈ Phi a7 then n ⟨γ, h⟩ else 0

theorem extN_of_mem {γ : Rt} (h : γ ∈ Phi a7) (n : NU K) : extN n γ = n ⟨γ, h⟩ := by
  simp [extN, h]

theorem extN_of_not_mem {γ : Rt} (h : γ ∉ Phi a7) (n : NU K) : extN n γ = 0 := by
  simp [extN, h]

theorem extN_add (n m : NU K) : extN (n + m) = extN n + extN m := by
  funext γ
  by_cases h : γ ∈ Phi a7
  · simp [extN_of_mem h]
  · simp [extN_of_not_mem h]

@[expose] def uN (n : NU K) : Gp K := prodX (Phi a7).toList (extN n)

theorem uN_add (n m : NU K) : uN (n + m) = uN n * uN m := by
  unfold uN
  rw [extN_add, prodX_mul (fun γ hγ => Finset.mem_toList.1 hγ)]

theorem uN_zero : uN (0 : NU K) = 1 := by
  have : extN (0 : NU K) = 0 := by
    funext γ
    by_cases h : γ ∈ Phi a7
    · simp [extN_of_mem h]
    · simp [extN_of_not_mem h]
  unfold uN
  rw [this, prodX_zero]

theorem uN_mem (n : NU K) : uN n ∈ UA K a7 := mem_UA_iff.2 ⟨_, rfl⟩

theorem prodX_congr {L : List Rt} {c c' : Rt → K} (h : ∀ γ ∈ L, c γ = c' γ) :
    prodX L c = prodX L c' := by
  unfold prodX
  congr 1
  exact List.map_congr_left fun γ hγ => by rw [h γ hγ]

theorem exists_uN {h : Gp K} (hh : h ∈ UA K a7) : ∃ n : NU K, uN n = h := by
  obtain ⟨c, rfl⟩ := mem_UA_iff.1 hh
  refine ⟨fun γ => c γ.1, ?_⟩
  unfold uN
  exact prodX_congr fun γ hγ => by
    have := Finset.mem_toList.1 hγ
    rw [extN_of_mem this]

theorem uN_single (β : ↥(Phi a7)) (b : K) : uN (Pi.single β b) = xE β.1 b := by
  classical
  unfold uN
  have h := prodX_eq_single (L := (Phi a7).toList) (Finset.nodup_toList _)
    (δ₀ := β.1) (Finset.mem_toList.2 β.2) (c := extN (Pi.single β b)) (fun γ hγ hne => by
      have hγ' : γ ∈ Phi a7 := Finset.mem_toList.1 hγ
      rw [extN_of_mem hγ']
      have : (⟨γ, hγ'⟩ : ↥(Phi a7)) ≠ β := fun e => hne (congrArg Subtype.val e)
      simp [Pi.single_apply, this])
  rw [h, extN_of_mem β.2]
  simp

variable [CharP K 2]

theorem coef_uN (n : NU K) {δ : Rt} (hδ : IsRoot .E7 δ) (hδa : δ ∈ Phi a7) {b : Fin e7Data.d}
    (hb : pr b δ = -1) :
    endoE (uN n) (Finsupp.single b 1) (shift δ b) = n ⟨δ, hδa⟩ := by
  unfold uN
  rw [coef_prodX a7 (extN n) b hδ hb, if_pos hδa, extN_of_mem hδa]

theorem uN_injective : Function.Injective (uN : NU K → Gp K) := by
  intro n m h
  funext δ
  obtain ⟨b, hb⟩ := exists_pr_eq_neg_one (mem_Phi.1 δ.2).1
  have h1 := coef_uN n (mem_Phi.1 δ.2).1 δ.2 hb
  have h2 := coef_uN m (mem_Phi.1 δ.2).1 δ.2 hb
  rw [h] at h1
  exact h1.symm.trans h2

end CFSG.RankThree.GF2n.Smith81.S81Z
