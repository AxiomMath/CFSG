module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Lie
public import Certificates.Certificate7773
public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.Milestones.ASVolI.F48.Rest.EngQE

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr burnsideF48t_u52eF

@[expose] noncomputable def burnsideF48t_u52eσ (i : ℕ) : Equiv.Perm (Fin 462) :=
  CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[i]!

@[expose] noncomputable def burnsideF48t_u52f : Equiv.Perm (Fin 462) := burnsideF48t_u52eσ 4

@[expose] noncomputable def burnsideF48t_u52Xh : Subgroup (Equiv.Perm (Fin 462)) :=
  burnsideF48t_u52X ⊔ Subgroup.zpowers burnsideF48t_u52f

@[expose] noncomputable def burnsideF48t_u52eXs : Subgroup ↥burnsideF48t_u52Xh :=
  burnsideF48t_u52X.subgroupOf burnsideF48t_u52Xh

section Letters


theorem burnsideF48t_u52e_cert : burnsideF48t_u52eInvOK () = true ∧ burnsideF48t_u52eFOK () = true ∧
    burnsideF48t_u52eRelOK () = true ∧ burnsideF48t_u52eKhOK () = true ∧
    burnsideF48t_u52eCandOK () = true :=
  Certificates.certificate7773

theorem burnsideF48t_u52e_inv : (burnsideF48t_u52eLArr ()).size = 5 ∧
    (burnsideF48t_u52eLInv ()).size = 5 ∧
    ∀ i < 5, pisInv 462 (burnsideF48t_u52eLArr ())[i]! (burnsideF48t_u52eLInv ())[i]! = true := by
  have h := burnsideF48t_u52e_cert.1
  simp only [burnsideF48t_u52eInvOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, fun i hi => allBelowN_spec h.2 hi⟩

theorem burnsideF48t_u52e_prep_σ {i : ℕ} (hi : i < 5) :
    PRep 462 (burnsideF48t_u52eLArr ())[i]! (burnsideF48t_u52eσ i) ∧
      PRep 462 (burnsideF48t_u52eLInv ())[i]! (burnsideF48t_u52eσ i)⁻¹ :=
  prep_permOfArr (burnsideF48t_u52e_inv.2.2 i hi)

theorem burnsideF48t_u52e_recL :
    burnsideF48t_RecL 462 (burnsideF48t_u52eLArr ()) (burnsideF48t_u52eLInv ())
      (fun i : Fin 5 => burnsideF48t_u52eσ i) :=
  fun i => burnsideF48t_u52e_prep_σ i.2


theorem burnsideF48t_u52e_LArr_lt {i : ℕ} (hi : i < 4) :
    (burnsideF48t_u52eLArr ())[i]! = burnsideF48t_u52LArr[i]! := by
  have hs : burnsideF48t_u52LArr.size = 4 := burnsideF48t_u52_inv.1
  unfold burnsideF48t_u52eLArr
  rw [getElem!_pos _ i (by rw [Array.size_push, hs]; omega), getElem!_pos _ i (by rw [hs]; exact hi),
    Array.getElem_push_lt]

theorem burnsideF48t_u52e_LArr_four : (burnsideF48t_u52eLArr ())[4]! = burnsideF48t_u52eF := by
  have hs : burnsideF48t_u52LArr.size = 4 := burnsideF48t_u52_inv.1
  unfold burnsideF48t_u52eLArr
  rw [getElem!_pos _ 4 (by rw [Array.size_push, hs]; omega)]
  have e : (4 : ℕ) = burnsideF48t_u52LArr.size := hs.symm
  simp only [e, Array.getElem_push_eq]

theorem burnsideF48t_u52e_σ_lt {i : ℕ} (hi : i < 4) : burnsideF48t_u52eσ i = burnsideF48t_u52σ i := by
  have h := (burnsideF48t_u52e_prep_σ (show i < 5 by omega)).1
  rw [burnsideF48t_u52e_LArr_lt hi] at h
  exact h.unique (burnsideF48t_u52_prep_σ hi).1

theorem burnsideF48t_u52e_prep_f : PRep 462 burnsideF48t_u52eF burnsideF48t_u52f := by
  have h := (burnsideF48t_u52e_prep_σ (show 4 < 5 by norm_num)).1
  rwa [burnsideF48t_u52e_LArr_four] at h

theorem burnsideF48t_u52e_fok : pisInv 462 burnsideF48t_u52eF burnsideF48t_u52eF = true ∧
    burnsideF48t_u52eF[0]! = 0 ∧ burnsideF48t_u52eF[165]! = 165 ∧
    (∀ g ∈ burnsideF48t_u52Gens (), burnsideF48t_sift 462 (burnsideF48t_u52LevX ())
      burnsideF48t_u52BaseX (pcomp 462 (pcomp 462 burnsideF48t_u52eF g) burnsideF48t_u52eF) = true) ∧
    burnsideF48t_sift 462 (burnsideF48t_u52LevX ()) burnsideF48t_u52BaseX burnsideF48t_u52eF =
      false := by
  have h := burnsideF48t_u52e_cert.2.1
  simp only [burnsideF48t_u52eFOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun g hg => Array.all_eq_true_iff_forall_mem.1 h4 g hg, h5⟩

theorem burnsideF48t_u52e_f_inv : burnsideF48t_u52f⁻¹ = burnsideF48t_u52f :=
  (prep_inv_of_pisInv burnsideF48t_u52e_prep_f burnsideF48t_u52e_fok.1).unique
    burnsideF48t_u52e_prep_f

theorem burnsideF48t_u52e_f_mul_self : burnsideF48t_u52f * burnsideF48t_u52f = 1 := by
  calc burnsideF48t_u52f * burnsideF48t_u52f = burnsideF48t_u52f * burnsideF48t_u52f⁻¹ := by
        rw [burnsideF48t_u52e_f_inv]
    _ = 1 := mul_inv_cancel _

theorem burnsideF48t_u52e_f_pA : burnsideF48t_u52f burnsideF48t_u52pA = burnsideF48t_u52pA :=
  Fin.ext ((burnsideF48t_u52e_prep_f burnsideF48t_u52pA).symm.trans burnsideF48t_u52e_fok.2.1)

theorem burnsideF48t_u52e_f_pB : burnsideF48t_u52f burnsideF48t_u52pB = burnsideF48t_u52pB :=
  Fin.ext ((burnsideF48t_u52e_prep_f burnsideF48t_u52pB).symm.trans burnsideF48t_u52e_fok.2.2.1)


theorem burnsideF48t_u52e_f_conj {g : Equiv.Perm (Fin 462)} (hg : g ∈ burnsideF48t_u52X) :
    burnsideF48t_u52f * g * burnsideF48t_u52f⁻¹ ∈ burnsideF48t_u52X := by
  have hle : burnsideF48t_u52X ≤ burnsideF48t_u52X.comap (MulAut.conj burnsideF48t_u52f).toMonoidHom := by
    rw [burnsideF48t_u52_X_eq, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < 6 := lt_of_lt_of_eq k.2 burnsideF48t_u52_inv.2.2.1
    rw [← burnsideF48t_u52_X_eq, SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, burnsideF48t_u52e_f_inv]
    have hgk : (burnsideF48t_u52Gens ())[(k : ℕ)]! ∈ burnsideF48t_u52Gens () := by
      rw [getElem!_pos _ (k : ℕ) k.2]
      exact Array.getElem_mem _
    exact burnsideF48t_u52_mem_X_of_sift (prep_pcomp (prep_pcomp burnsideF48t_u52e_prep_f
      (burnsideF48t_u52_prep_γ hk).1) burnsideF48t_u52e_prep_f) (burnsideF48t_u52e_fok.2.2.2.1 _ hgk)
  have := hle hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem burnsideF48t_u52e_f_not_mem : burnsideF48t_u52f ∉ burnsideF48t_u52X := fun h => by
  have := burnsideF48t_sift_of_mem (by norm_num) burnsideF48t_u52_nodupX burnsideF48t_u52_chains.1
    burnsideF48t_u52e_prep_f h
  exact absurd (burnsideF48t_u52e_fok.2.2.2.2.symm.trans this) (by decide)

end Letters

section Model


private theorem burnsideF48t_u52e_mul_mem {z₁ z₂ : Equiv.Perm (Fin 462)}
    (h₁ : z₁ ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z₁ ∈ burnsideF48t_u52X)
    (h₂ : z₂ ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z₂ ∈ burnsideF48t_u52X) :
    z₁ * z₂ ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * (z₁ * z₂) ∈ burnsideF48t_u52X := by
  have hf := burnsideF48t_u52e_f_inv
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (burnsideF48t_u52X.mul_mem h₁ h₂)
  · refine Or.inr ?_
    have e : burnsideF48t_u52f * (z₁ * z₂) =
        (burnsideF48t_u52f * z₁ * burnsideF48t_u52f⁻¹) * (burnsideF48t_u52f * z₂) := by group
    rw [e]
    exact burnsideF48t_u52X.mul_mem (burnsideF48t_u52e_f_conj h₁) h₂
  · refine Or.inr ?_
    rw [← mul_assoc]
    exact burnsideF48t_u52X.mul_mem h₁ h₂
  · refine Or.inl ?_
    have e : z₁ * z₂ = (burnsideF48t_u52f * (burnsideF48t_u52f * z₁) * burnsideF48t_u52f⁻¹) *
        (burnsideF48t_u52f * z₂) := by
      rw [hf]
      calc z₁ * z₂ = (burnsideF48t_u52f * burnsideF48t_u52f) * z₁ *
            (burnsideF48t_u52f * burnsideF48t_u52f) * z₂ := by
            rw [burnsideF48t_u52e_f_mul_self, one_mul, mul_one]
        _ = _ := by group
    rw [e]
    exact burnsideF48t_u52X.mul_mem (burnsideF48t_u52e_f_conj h₁) h₂

private theorem burnsideF48t_u52e_inv_mem {z : Equiv.Perm (Fin 462)}
    (h : z ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z ∈ burnsideF48t_u52X) :
    z⁻¹ ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z⁻¹ ∈ burnsideF48t_u52X := by
  rcases h with h | h
  · exact Or.inl (burnsideF48t_u52X.inv_mem h)
  · refine Or.inr ?_
    have e : burnsideF48t_u52f * z⁻¹ =
        burnsideF48t_u52f * (burnsideF48t_u52f * z)⁻¹ * burnsideF48t_u52f⁻¹ := by
      rw [mul_inv_rev, burnsideF48t_u52e_f_inv, mul_assoc burnsideF48t_u52f (z⁻¹ * burnsideF48t_u52f),
        mul_assoc z⁻¹, burnsideF48t_u52e_f_mul_self, mul_one]
    rw [e]
    exact burnsideF48t_u52e_f_conj (burnsideF48t_u52X.inv_mem h)

theorem burnsideF48t_u52e_mem_Xh (z : Equiv.Perm (Fin 462)) :
    z ∈ burnsideF48t_u52Xh ↔ z ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z ∈ burnsideF48t_u52X := by
  let T : Subgroup (Equiv.Perm (Fin 462)) :=
    { carrier := {z | z ∈ burnsideF48t_u52X ∨ burnsideF48t_u52f * z ∈ burnsideF48t_u52X}
      mul_mem' := fun h₁ h₂ => burnsideF48t_u52e_mul_mem h₁ h₂
      one_mem' := Or.inl burnsideF48t_u52X.one_mem
      inv_mem' := fun h => burnsideF48t_u52e_inv_mem h }
  constructor
  · intro hz
    have hle : burnsideF48t_u52Xh ≤ T := by
      refine sup_le (fun g hg => Or.inl hg) ?_
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [burnsideF48t_u52e_f_mul_self]; exact burnsideF48t_u52X.one_mem)
    exact hle hz
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have e : z = burnsideF48t_u52f * (burnsideF48t_u52f * z) := by
        rw [← mul_assoc, burnsideF48t_u52e_f_mul_self, one_mul]
      rw [e]
      exact burnsideF48t_u52Xh.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left h)

theorem burnsideF48t_u52e_X_le : burnsideF48t_u52X ≤ burnsideF48t_u52Xh := le_sup_left

theorem burnsideF48t_u52e_f_mem : burnsideF48t_u52f ∈ burnsideF48t_u52Xh :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem burnsideF48t_u52e_index : burnsideF48t_u52eXs.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨burnsideF48t_u52f, burnsideF48t_u52e_f_mem⟩, fun b => ?_⟩
  simp only [burnsideF48t_u52eXs, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X
  · refine Or.inr ⟨hb, fun h => burnsideF48t_u52e_f_not_mem ?_⟩
    have := burnsideF48t_u52X.mul_mem (burnsideF48t_u52X.inv_mem hb) h
    simpa using this
  · refine Or.inl ⟨?_, hb⟩
    have hfb := ((burnsideF48t_u52e_mem_Xh b).1 b.2).resolve_left hb
    have e : (b : Equiv.Perm (Fin 462)) * burnsideF48t_u52f =
        burnsideF48t_u52f * (burnsideF48t_u52f * b) * burnsideF48t_u52f⁻¹ := by
      rw [burnsideF48t_u52e_f_inv, ← mul_assoc, burnsideF48t_u52e_f_mul_self, one_mul]
    rw [e]
    exact burnsideF48t_u52e_f_conj hfb

theorem burnsideF48t_u52e_normal : burnsideF48t_u52eXs.Normal :=
  Subgroup.normal_of_index_eq_two burnsideF48t_u52e_index

theorem burnsideF48t_u52e_card_Xs : Nat.card ↥burnsideF48t_u52eXs = 13685760 := by
  rw [burnsideF48t_u52eXs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_u52e_X_le).toEquiv, burnsideF48t_u52_card_X]

theorem burnsideF48t_u52e_card_Xh : Nat.card ↥burnsideF48t_u52Xh = 27371520 := by
  have h := Subgroup.card_mul_index burnsideF48t_u52eXs
  rw [burnsideF48t_u52e_card_Xs, burnsideF48t_u52e_index] at h
  omega

end Model

section Cent


theorem burnsideF48t_u52e_stab_pA :
    MulAction.stabilizer ↥burnsideF48t_u52X burnsideF48t_u52pA = burnsideF48t_u52P1 := by
  ext z
  rw [MulAction.mem_stabilizer_iff, burnsideF48t_u52_mem_P1_iff]
  rfl

theorem burnsideF48t_u52e_stab_pB :
    MulAction.stabilizer ↥burnsideF48t_u52X burnsideF48t_u52pB = burnsideF48t_u52P2 := by
  ext z
  rw [MulAction.mem_stabilizer_iff, burnsideF48t_u52_mem_P2_iff]
  rfl

theorem burnsideF48t_u52e_card_P1 : Nat.card ↥burnsideF48t_u52P1 = 82944 := by
  rw [← Subgroup.card_map_of_injective burnsideF48t_u52X.subtype_injective, burnsideF48t_u52_map_P1,
    burnsideF48t_u52_card_P1']

theorem burnsideF48t_u52e_card_P2 : Nat.card ↥burnsideF48t_u52P2 = 46080 := by
  rw [← Subgroup.card_map_of_injective burnsideF48t_u52X.subtype_injective, burnsideF48t_u52_map_P2,
    burnsideF48t_u52_card_P2']

theorem burnsideF48t_u52e_card_pts : Nat.card {x : Fin 462 | (x : ℕ) < 165} = 165 := by
  rw [Nat.card_congr (Equiv.mk (fun x : {x : Fin 462 | (x : ℕ) < 165} => (⟨(x.1 : ℕ), x.2⟩ : Fin 165))
    (fun i => ⟨⟨i.1, by have := i.2; omega⟩, i.2⟩) (fun x => Subtype.ext (Fin.ext rfl))
    (fun i => Fin.ext rfl)), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem burnsideF48t_u52e_card_lns : Nat.card {x : Fin 462 | 165 ≤ (x : ℕ)} = 297 := by
  rw [Nat.card_congr (Equiv.mk (fun x : {x : Fin 462 | 165 ≤ (x : ℕ)} =>
      (⟨(x.1 : ℕ) - 165, by have := x.1.2; omega⟩ : Fin 297))
    (fun i => ⟨⟨i.1 + 165, by have := i.2; omega⟩, show 165 ≤ i.1 + 165 by omega⟩)
    (fun x => Subtype.ext (Fin.ext (by have : 165 ≤ (x.1 : ℕ) := x.2; simp only; omega)))
    (fun i => Fin.ext (by simp only; omega))), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem burnsideF48t_u52e_reach_pt {p : Fin 462} (hp : (p : ℕ) < 165) :
    ∃ g ∈ burnsideF48t_u52X, g burnsideF48t_u52pA = p := by
  have h1 := MulAction.index_stabilizer (↥burnsideF48t_u52X) burnsideF48t_u52pA
  rw [burnsideF48t_u52e_stab_pA] at h1
  have h2 := Subgroup.card_mul_index burnsideF48t_u52P1
  rw [burnsideF48t_u52e_card_P1, burnsideF48t_u52_card_X] at h2
  have horb : (MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pA).ncard = 165 := by omega
  have hS : ({x : Fin 462 | (x : ℕ) < 165} : Set (Fin 462)).ncard = 165 := by
    rw [← Nat.card_coe_set_eq]
    exact burnsideF48t_u52e_card_pts
  have hsub : MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pA ⊆
      {x : Fin 462 | (x : ℕ) < 165} := by
    rintro _ ⟨g, rfl⟩
    exact burnsideF48t_u52_X_lt g.2 (show ((burnsideF48t_u52pA : Fin 462) : ℕ) < 165 by decide)
  have he := Set.eq_of_subset_of_ncard_le hsub (by rw [hS, horb]) (Set.toFinite _)
  have hmem : p ∈ MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pA := by
    rw [he]
    exact hp
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, g.2, hg⟩

theorem burnsideF48t_u52e_reach_ln {p : Fin 462} (hp : 165 ≤ (p : ℕ)) :
    ∃ g ∈ burnsideF48t_u52X, g burnsideF48t_u52pB = p := by
  have h1 := MulAction.index_stabilizer (↥burnsideF48t_u52X) burnsideF48t_u52pB
  rw [burnsideF48t_u52e_stab_pB] at h1
  have h2 := Subgroup.card_mul_index burnsideF48t_u52P2
  rw [burnsideF48t_u52e_card_P2, burnsideF48t_u52_card_X] at h2
  have horb : (MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pB).ncard = 297 := by omega
  have hS : ({x : Fin 462 | 165 ≤ (x : ℕ)} : Set (Fin 462)).ncard = 297 := by
    rw [← Nat.card_coe_set_eq]
    exact burnsideF48t_u52e_card_lns
  have hsub : MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pB ⊆
      {x : Fin 462 | 165 ≤ (x : ℕ)} := by
    rintro _ ⟨g, rfl⟩
    exact burnsideF48t_u52_X_ge g.2 (show 165 ≤ ((burnsideF48t_u52pB : Fin 462) : ℕ) by decide)
  have he := Set.eq_of_subset_of_ncard_le hsub (by rw [hS, horb]) (Set.toFinite _)
  have hmem : p ∈ MulAction.orbit ↥burnsideF48t_u52X burnsideF48t_u52pB := by
    rw [he]
    exact hp
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, g.2, hg⟩

theorem burnsideF48t_u52e_comm_fix {c : Equiv.Perm (Fin 462)}
    (hc : ∀ g ∈ burnsideF48t_u52X, c * g = g * c) :
    c burnsideF48t_u52pA = burnsideF48t_u52pA ∧ c burnsideF48t_u52pB = burnsideF48t_u52pB := by
  have hfix : ∀ {g : Equiv.Perm (Fin 462)} {o : Fin 462}, g ∈ burnsideF48t_u52X → g o = o →
      g (c o) = c o := by
    intro g o hg ho
    have := congrArg (fun h : Equiv.Perm (Fin 462) => h o) (hc g hg)
    simp only [Equiv.Perm.mul_apply, ho] at this
    exact this.symm
  have hS : ∀ o : Fin 462, (∀ s ∈ burnsideF48t_u52S0', s o = o) →
      o = burnsideF48t_u52pA ∨ o = burnsideF48t_u52pB := by
    intro o ho
    by_contra hne
    rw [not_or] at hne
    obtain ⟨s, hs, hso⟩ := burnsideF48t_u52_S0'_moves hne.1 hne.2
    exact hso (ho s hs)
  have hσ := burnsideF48t_u52_σ_fix
  have hA := hS (c burnsideF48t_u52pA) fun s hs =>
    hfix (burnsideF48t_u52_S0'_le_X hs) (burnsideF48t_u52_S0'_fix hs).1
  have hB := hS (c burnsideF48t_u52pB) fun s hs =>
    hfix (burnsideF48t_u52_S0'_le_X hs) (burnsideF48t_u52_S0'_fix hs).2
  refine ⟨hA.resolve_right fun h => ?_, hB.resolve_left fun h => ?_⟩
  · have := hfix (burnsideF48t_u52_σ_mem (i := 2) (by norm_num)) hσ.2.2.2.2.1
    rw [h] at this
    exact hσ.2.2.2.2.2.2.2 this
  · have := hfix (burnsideF48t_u52_σ_mem (i := 3) (by norm_num)) hσ.2.2.2.2.2.1
    rw [h] at this
    exact hσ.2.2.2.2.2.2.1 this

theorem burnsideF48t_u52e_comm_eq_one {c : Equiv.Perm (Fin 462)}
    (hc : ∀ g ∈ burnsideF48t_u52X, c * g = g * c) : c = 1 := by
  obtain ⟨hA, hB⟩ := burnsideF48t_u52e_comm_fix hc
  ext o
  have key : ∀ {o₀ : Fin 462}, c o₀ = o₀ → ∀ g ∈ burnsideF48t_u52X, c (g o₀) = g o₀ := by
    intro o₀ ho₀ g hg
    have := congrArg (fun h : Equiv.Perm (Fin 462) => h o₀) (hc g hg)
    simp only [Equiv.Perm.mul_apply, ho₀] at this
    exact this
  by_cases ho : (o : ℕ) < 165
  · obtain ⟨g, hg, rfl⟩ := burnsideF48t_u52e_reach_pt ho
    rw [key hA g hg]
    rfl
  · obtain ⟨g, hg, rfl⟩ := burnsideF48t_u52e_reach_ln (not_lt.1 ho)
    rw [key hB g hg]
    rfl

end Cent

abbrev burnsideF48t_u52eS1 : Set (Fin 5) := {i | i ≠ 3}

abbrev burnsideF48t_u52eS2 : Set (Fin 5) := {i | i ≠ 2}

@[expose] noncomputable def burnsideF48t_u52eP1' : Subgroup (Equiv.Perm (Fin 462)) :=
  Subgroup.closure ((fun i : Fin 5 => burnsideF48t_u52eσ i) '' burnsideF48t_u52eS1)

@[expose] noncomputable def burnsideF48t_u52eP2' : Subgroup (Equiv.Perm (Fin 462)) :=
  Subgroup.closure ((fun i : Fin 5 => burnsideF48t_u52eσ i) '' burnsideF48t_u52eS2)

section Par


theorem burnsideF48t_u52e_σ_mem {i : ℕ} (hi : i < 5) : burnsideF48t_u52eσ i ∈ burnsideF48t_u52Xh := by
  by_cases h4 : i < 4
  · rw [burnsideF48t_u52e_σ_lt h4]
    exact burnsideF48t_u52e_X_le (burnsideF48t_u52_σ_mem h4)
  · obtain rfl : i = 4 := by omega
    exact burnsideF48t_u52e_f_mem

@[expose] noncomputable def burnsideF48t_u52eL (i : Fin 5) : ↥burnsideF48t_u52Xh :=
  ⟨burnsideF48t_u52eσ i, burnsideF48t_u52e_σ_mem i.2⟩

theorem burnsideF48t_u52e_coe_L (i : Fin 5) :
    ((burnsideF48t_u52eL i : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) = burnsideF48t_u52eσ i :=
  rfl

theorem burnsideF48t_u52e_coe_ev (w : List (Fin 5 × Bool)) :
    ((burnsideF48s_ev burnsideF48t_u52eL w : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) =
      burnsideF48s_ev (fun i : Fin 5 => burnsideF48t_u52eσ i) w :=
  (burnsideF48s_ev_map burnsideF48t_u52Xh.subtype burnsideF48t_u52eL w).symm

@[expose] noncomputable def burnsideF48t_u52eP1 : Subgroup ↥burnsideF48t_u52Xh :=
  Subgroup.closure (burnsideF48t_u52eL '' burnsideF48t_u52eS1)

@[expose] noncomputable def burnsideF48t_u52eP2 : Subgroup ↥burnsideF48t_u52Xh :=
  Subgroup.closure (burnsideF48t_u52eL '' burnsideF48t_u52eS2)

theorem burnsideF48t_u52e_σ4 : burnsideF48t_u52eσ 4 = burnsideF48t_u52f := rfl

theorem burnsideF48t_u52e_σ_pA {i : ℕ} (hi : i < 5) (h3 : i ≠ 3) :
    burnsideF48t_u52eσ i burnsideF48t_u52pA = burnsideF48t_u52pA := by
  have hσ := burnsideF48t_u52_σ_fix
  by_cases h4 : i < 4
  · rw [burnsideF48t_u52e_σ_lt h4]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    exacts [hσ.1, hσ.2.2.1, hσ.2.2.2.2.1]
  · obtain rfl : i = 4 := by omega
    rw [burnsideF48t_u52e_σ4]
    exact burnsideF48t_u52e_f_pA

theorem burnsideF48t_u52e_σ_pB {i : ℕ} (hi : i < 5) (h2 : i ≠ 2) :
    burnsideF48t_u52eσ i burnsideF48t_u52pB = burnsideF48t_u52pB := by
  have hσ := burnsideF48t_u52_σ_fix
  by_cases h4 : i < 4
  · rw [burnsideF48t_u52e_σ_lt h4]
    rcases (show i = 0 ∨ i = 1 ∨ i = 3 by omega) with rfl | rfl | rfl
    exacts [hσ.2.1, hσ.2.2.2.1, hσ.2.2.2.2.2.1]
  · obtain rfl : i = 4 := by omega
    rw [burnsideF48t_u52e_σ4]
    exact burnsideF48t_u52e_f_pB

theorem burnsideF48t_u52e_map_P1 :
    burnsideF48t_u52eP1.map burnsideF48t_u52Xh.subtype = burnsideF48t_u52eP1' := by
  rewrite [burnsideF48t_u52eP1, MonoidHom.map_closure, Set.image_image, burnsideF48t_u52eP1']
  exact congrArg Subgroup.closure (Set.image_congr fun i _ => burnsideF48t_u52e_coe_L i)

theorem burnsideF48t_u52e_map_P2 :
    burnsideF48t_u52eP2.map burnsideF48t_u52Xh.subtype = burnsideF48t_u52eP2' := by
  rewrite [burnsideF48t_u52eP2, MonoidHom.map_closure, Set.image_image, burnsideF48t_u52eP2']
  exact congrArg Subgroup.closure (Set.image_congr fun i _ => burnsideF48t_u52e_coe_L i)

theorem burnsideF48t_u52e_f_mem_P1' : burnsideF48t_u52f ∈ burnsideF48t_u52eP1' :=
  Subgroup.subset_closure ⟨4, show (4 : Fin 5) ≠ 3 by decide, rfl⟩

theorem burnsideF48t_u52e_f_mem_P2' : burnsideF48t_u52f ∈ burnsideF48t_u52eP2' :=
  Subgroup.subset_closure ⟨4, show (4 : Fin 5) ≠ 2 by decide, rfl⟩

theorem burnsideF48t_u52e_P1'_le : burnsideF48t_u52P1' ≤ burnsideF48t_u52eP1' := by
  rw [burnsideF48t_u52_P1'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hk : (k : ℕ) < 3 := burnsideF48t_u52_P1Arr.1 ▸ k.2
  refine Subgroup.subset_closure ⟨⟨k, by omega⟩, fun h => ?_, ?_⟩
  · have := congrArg Fin.val h
    simp only at this
    omega
  · show burnsideF48t_u52eσ k = burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)
    rw [burnsideF48t_u52e_σ_lt (by omega)]
    rfl

theorem burnsideF48t_u52e_P2'_le : burnsideF48t_u52P2' ≤ burnsideF48t_u52eP2' := by
  rw [burnsideF48t_u52_P2'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hk := burnsideF48t_u52_P2Idx_cases k
  have hk4 : burnsideF48t_u52P2Idx k < 5 := by omega
  refine Subgroup.subset_closure ⟨⟨burnsideF48t_u52P2Idx k, hk4⟩, fun h => ?_, ?_⟩
  · have := congrArg Fin.val h
    simp only at this
    omega
  · show burnsideF48t_u52eσ (burnsideF48t_u52P2Idx k) = burnsideF48t_u52σ (burnsideF48t_u52P2Idx k)
    exact burnsideF48t_u52e_σ_lt (by omega)

theorem burnsideF48t_u52e_P1'_eq : burnsideF48t_u52eP1' =
    burnsideF48t_u52Xh ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA := by
  apply le_antisymm
  · rw [burnsideF48t_u52eP1', Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨burnsideF48t_u52e_σ_mem i.2, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def]
    exact burnsideF48t_u52e_σ_pA i.2 fun h => hi (Fin.ext h)
  · intro z hz'
    obtain ⟨hz, hz0⟩ := Subgroup.mem_inf.1 hz'
    rw [MulAction.mem_stabilizer_iff] at hz0
    rcases (burnsideF48t_u52e_mem_Xh z).1 hz with h | h
    · refine burnsideF48t_u52e_P1'_le ?_
      rw [burnsideF48t_u52_P1'_eq]
      exact ⟨h, MulAction.mem_stabilizer_iff.2 hz0⟩
    · have hfz : burnsideF48t_u52f * z ∈ burnsideF48t_u52eP1' := by
        refine burnsideF48t_u52e_P1'_le ?_
        rw [burnsideF48t_u52_P1'_eq]
        refine ⟨h, MulAction.mem_stabilizer_iff.2 ?_⟩
        rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
          show z burnsideF48t_u52pA = burnsideF48t_u52pA from hz0, burnsideF48t_u52e_f_pA]
      have e : z = burnsideF48t_u52f * (burnsideF48t_u52f * z) := by
        rw [← mul_assoc, burnsideF48t_u52e_f_mul_self, one_mul]
      rw [e]
      exact burnsideF48t_u52eP1'.mul_mem burnsideF48t_u52e_f_mem_P1' hfz

theorem burnsideF48t_u52e_P2'_eq : burnsideF48t_u52eP2' =
    burnsideF48t_u52Xh ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB := by
  apply le_antisymm
  · rw [burnsideF48t_u52eP2', Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨burnsideF48t_u52e_σ_mem i.2, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [Equiv.Perm.smul_def]
    exact burnsideF48t_u52e_σ_pB i.2 fun h => hi (Fin.ext h)
  · intro z hz'
    obtain ⟨hz, hz0⟩ := Subgroup.mem_inf.1 hz'
    rw [MulAction.mem_stabilizer_iff] at hz0
    rcases (burnsideF48t_u52e_mem_Xh z).1 hz with h | h
    · refine burnsideF48t_u52e_P2'_le ?_
      rw [burnsideF48t_u52_P2'_eq]
      exact ⟨h, MulAction.mem_stabilizer_iff.2 hz0⟩
    · have hfz : burnsideF48t_u52f * z ∈ burnsideF48t_u52eP2' := by
        refine burnsideF48t_u52e_P2'_le ?_
        rw [burnsideF48t_u52_P2'_eq]
        refine ⟨h, MulAction.mem_stabilizer_iff.2 ?_⟩
        rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
          show z burnsideF48t_u52pB = burnsideF48t_u52pB from hz0, burnsideF48t_u52e_f_pB]
      have e : z = burnsideF48t_u52f * (burnsideF48t_u52f * z) := by
        rw [← mul_assoc, burnsideF48t_u52e_f_mul_self, one_mul]
      rw [e]
      exact burnsideF48t_u52eP2'.mul_mem burnsideF48t_u52e_f_mem_P2' hfz

theorem burnsideF48t_u52e_mem_P1 (z : ↥burnsideF48t_u52Xh) :
    z ∈ burnsideF48t_u52eP1 ↔ (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pA = burnsideF48t_u52pA := by
  rw [← Subgroup.mem_map_iff_mem burnsideF48t_u52Xh.subtype_injective, burnsideF48t_u52e_map_P1,
    burnsideF48t_u52e_P1'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

theorem burnsideF48t_u52e_mem_P2 (z : ↥burnsideF48t_u52Xh) :
    z ∈ burnsideF48t_u52eP2 ↔ (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pB = burnsideF48t_u52pB := by
  rw [← Subgroup.mem_map_iff_mem burnsideF48t_u52Xh.subtype_injective, burnsideF48t_u52e_map_P2,
    burnsideF48t_u52e_P2'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

end Par

end CFSG.ASVolI
