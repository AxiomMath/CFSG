module

public import CFSG.Quasithin.H13.A7Nat1238YCoord
public import CFSG.Quasithin.H13.A7IrrPlus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise

theorem permAct7_eq_iff_smul_supp7 (σ : Perm (Fin 7)) (w : Fin 7 → ZMod 2) :
    permAct7 σ w = w ↔ σ • ((supp7 w : Finset (Fin 7)) : Set (Fin 7)) = supp7 w := by
  rw [← Finset.coe_smul_finset, Finset.coe_inj, ← supp7_permAct7]
  exact ⟨fun h => by rw [h], eq_of_supp7_eq⟩

theorem isCoatom_stab_supp7 {w : Fin 7 → ZMod 2} (hw : w ∈ evenWeight 7) (hw0 : w ≠ 0) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 7))
      ((supp7 w : Finset (Fin 7)) : Set (Fin 7))) := by
  classical
  refine alternatingGroup.isCoatom_stabilizer (α := Fin 7) ?_ ?_ ?_
  · by_contra hne
    apply hw0
    funext i
    rcases zmodTwo_eq_zero_or_one (w i) with h0 | h1
    · exact h0
    · exact absurd ⟨i, Finset.mem_coe.2 (mem_supp7.2 h1)⟩ hne
  · by_contra hne
    have hall : ∀ i, w i = 1 := fun i => by
      by_contra hi
      exact hne ⟨i, fun h => hi (mem_supp7.1 (Finset.mem_coe.1 h))⟩
    have hsum := mem_evenWeight.1 hw
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
    exact absurd hsum (by decide)
  · intro h7
    have : Nat.card (Fin 7) = 7 := Nat.card_fin 7
    omega

variable {G : Type} [Group G] {T K I : Subgroup G} {ψ₁ : I ≃* Multiplicative (evenWeight 7)}

theorem le_closure_of_not_centralizes (h₁ : A7NatPre T K I ψ₁) {B : Subgroup G} (hBK : B ≤ K)
    {v : I} (hv1 : v ≠ 1) (hBv : ¬ ∀ b ∈ B, b * (v : G) * b⁻¹ = v) :
    K ≤ closure ((B : Set G) ∪ (K ⊓ centralizer ({(v : G)} : Set G))) := by
  classical
  set W := closure ((B : Set G) ∪ (K ⊓ centralizer ({(v : G)} : Set G))) with hWdef
  set lam := natLam h₁.L_le h₁.Lact with hlam
  have hlams := natLam_surjective h₁.L_le h₁.Lact h₁.Lonto
  set w := vec ψ₁ v with hwdef
  have hw : w ∈ evenWeight 7 := vec_mem ψ₁ v
  have hw0 : w ≠ 0 := fun h0 => hv1 ((vec_eq_zero_iff ψ₁ v).1 h0)
  have hWK : W ≤ K := (closure_le _).2 (Set.union_subset hBK fun x hx => (mem_inf.1 hx).1)
  set H : Subgroup (alternatingGroup (Fin 7)) := (W.subgroupOf K).map lam with hH
  set S := MulAction.stabilizer (alternatingGroup (Fin 7))
    ((supp7 w : Finset (Fin 7)) : Set (Fin 7)) with hS
  have hfix : ∀ k : K, permAct7 (lam k : Perm (Fin 7)) w = w →
      (k : G) ∈ K ⊓ centralizer ({(v : G)} : Set G) := by
    intro k hk
    refine ⟨k.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := conj_eq_of_permAct7 h₁ (l := k) (x := v) hk
    calc (k : G) * v = (k * v * (k : G)⁻¹) * k := by group
      _ = v * k := by rw [h1]
  have hSH : S ≤ H := by
    intro σ hσ
    obtain ⟨k, rfl⟩ := hlams σ
    have hk : permAct7 (lam k : Perm (Fin 7)) w = w :=
      (permAct7_eq_iff_smul_supp7 _ w).2 hσ
    exact ⟨k, subset_closure (Or.inr (hfix k hk)), rfl⟩
  have hHS : ¬ H ≤ S := by
    intro hle
    apply hBv
    intro b hb
    have hbW : b ∈ W := subset_closure (Or.inl hb)
    have h1 : lam ⟨b, hBK hb⟩ ∈ S := hle ⟨⟨b, hBK hb⟩, hbW, rfl⟩
    have h2 : permAct7 (lam ⟨b, hBK hb⟩ : Perm (Fin 7)) w = w :=
      (permAct7_eq_iff_smul_supp7 _ w).2 h1
    exact conj_eq_of_permAct7 h₁ (l := ⟨b, hBK hb⟩) (x := v) h2
  have hHtop : H = ⊤ :=
    (isCoatom_stab_supp7 hw hw0).2 H (lt_of_le_of_ne hSH fun h => hHS (h ▸ le_rfl))
  intro k hk
  obtain ⟨x, hxW, hx⟩ : lam ⟨k, hk⟩ ∈ H := by rw [hHtop]; exact mem_top _
  have hxk : lam (x⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
  have hc : ((x⁻¹ * ⟨k, hk⟩ : K) : G) ∈ centralizer (I : Set G) :=
    (natLam_eq_one_iff h₁.L_le h₁.Lact _).1 hxk
  have hcv : ((x⁻¹ * ⟨k, hk⟩ : K) : G) ∈ K ⊓ centralizer ({(v : G)} : Set G) :=
    ⟨(x⁻¹ * ⟨k, hk⟩ : K).2, mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hc (v : G) v.2).symm⟩
  have h1 : ((x : K) : G) * ((x⁻¹ * ⟨k, hk⟩ : K) : G) = k := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [← h1]
  exact mul_mem (mem_subgroupOf.1 hxW) (subset_closure (Or.inr hcv))

end CFSG.Quasithin.H13.A7
