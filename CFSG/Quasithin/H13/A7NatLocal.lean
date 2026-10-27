module

public import CFSG.Quasithin.H13.A7NatFusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

section Lam

variable {G : Type*} [Group G] {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

@[expose] def stabA7 (w : Fin 7 → ZMod 2) : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {σ | permAct7 (σ : Perm (Fin 7)) w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul] at ha hb ⊢
    rw [permAct7_mul, hb, ha]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_one, permAct7_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
    conv_lhs => rw [← ha]
    exact permAct7_inv_apply _ _

theorem mem_stabA7 {w : Fin 7 → ZMod 2} {σ : alternatingGroup (Fin 7)} :
    σ ∈ stabA7 w ↔ permAct7 (σ : Perm (Fin 7)) w = w := Iff.rfl

@[expose] noncomputable def natLam (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) :
    L →* alternatingGroup (Fin 7) :=
  (coordRep ψ hLV (fun a ha => (hLact a ha).imp fun _ hσ => hσ.2)).codRestrict _ fun l => by
    obtain ⟨σ, hσA, hσ⟩ := hLact l l.2
    rw [IsCoordAct.unique ψ (hLV l.2) (coordRep_spec ψ hLV _ l) hσ]
    exact hσA

variable (hLV : L ≤ normalizer (V : Set G))
  (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)

include hLV hLact in
theorem natLam_spec (l : L) : IsCoordAct ψ l (natLam hLV hLact l : Perm (Fin 7)) :=
  coordRep_spec ψ hLV _ l

include hLV hLact in
theorem natLam_eq (l : L) {σ : Perm (Fin 7)} (hσ : IsCoordAct ψ l σ) :
    (natLam hLV hLact l : Perm (Fin 7)) = σ :=
  IsCoordAct.unique ψ (hLV l.2) (natLam_spec hLV hLact l) hσ

include hLV hLact in
theorem natLam_surjective (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) :
    Function.Surjective (natLam hLV hLact) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, hact⟩ := hLonto σ hσ
  exact ⟨⟨l, hl⟩, Subtype.ext (natLam_eq hLV hLact ⟨l, hl⟩ hact)⟩

include hLV hLact in
theorem natLam_eq_one_iff (l : L) :
    natLam hLV hLact l = 1 ↔ (l : G) ∈ centralizer (V : Set G) := by
  rw [← coordRep_eq_one_iff ψ hLV (fun a ha => (hLact a ha).imp fun _ hσ => hσ.2) l]
  constructor
  · intro h1
    exact congrArg Subtype.val h1
  · intro h1
    exact Subtype.ext h1

include hLV hLact in
theorem mem_centralizer_iff_natLam (v : V) (l : L) :
    (l : G) ∈ centralizer ({(v : G)} : Set G) ↔
      permAct7 (natLam hLV hLact l : Perm (Fin 7)) (vec ψ v) = vec ψ v := by
  have hspec := natLam_spec hLV hLact l
  let y : V := ⟨(l : G) * v * (l : G)⁻¹, (mem_normalizer_iff.1 (hLV l.2) v).1 v.2⟩
  have hy := hspec v y rfl
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have hyv : y = v := Subtype.ext (show (l : G) * v * (l : G)⁻¹ = v by
      rw [hc, mul_inv_cancel_right])
    rw [← hy, hyv]
  · intro hf
    rw [hf] at hy
    have h1 : (l : G) * v * (l : G)⁻¹ = v := congrArg Subtype.val (vec_injective ψ hy)
    calc (l : G) * v = (l : G) * v * (l : G)⁻¹ * l := by group
      _ = v * l := by rw [h1]

include hLV hLact in
theorem natLam_map_inf_centralizer
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) (v : V) :
    ((L ⊓ centralizer ({(v : G)} : Set G)).subgroupOf L).map (natLam hLV hLact) =
      stabA7 (vec ψ v) := by
  ext σ
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_inf] at hl
    exact (mem_centralizer_iff_natLam hLV hLact v l).1 hl.2
  · intro hσ
    obtain ⟨l, rfl⟩ := natLam_surjective hLV hLact hLonto σ
    refine ⟨l, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_inf]
    exact ⟨l.2, (mem_centralizer_iff_natLam hLV hLact v l).2 hσ⟩

end Lam

theorem zmod_two_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

theorem zmod_two_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by
  decide

theorem eq_one_of_weight_six {w : Fin 7 → ZMod 2} {j : Fin 7} (hw : hammingNorm w = 6)
    (hj : w j = 0) : ∀ i, i ≠ j → w i = 1 := by
  classical
  intro i hij
  by_contra hne
  have hi0 : w i = 0 := zmod_two_eq_zero_of_ne_one _ hne
  have hsub : (Finset.univ.filter fun k => w k ≠ 0) ⊆ (Finset.univ.erase i).erase j := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hk (h ▸ hj), fun h => hk (h ▸ hi0)⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simpa using hij.symm),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have h2 : hammingNorm w = (Finset.univ.filter fun k => w k ≠ 0).card := rfl
  omega

theorem permAct7_fix_iff_of_weight_six {w : Fin 7 → ZMod 2} {j : Fin 7}
    (hw : hammingNorm w = 6) (hj : w j = 0) (σ : Perm (Fin 7)) :
    permAct7 σ w = w ↔ σ j = j := by
  have h1 := eq_one_of_weight_six hw hj
  constructor
  · intro h
    by_contra hσj
    have h2 := congrFun h (σ j)
    rw [permAct7_apply, show σ⁻¹ (σ j) = j from Perm.inv_eq_iff_eq.2 rfl, hj, h1 _ hσj] at h2
    exact zero_ne_one h2
  · intro h
    funext i
    rw [permAct7_apply]
    by_cases hi : i = j
    · subst hi
      rw [show σ⁻¹ i = i from Perm.inv_eq_iff_eq.2 h.symm]
    · have hi' : σ⁻¹ i ≠ j := fun h' => hi ((Perm.inv_eq_iff_eq.1 h').trans h)
      rw [h1 _ hi', h1 _ hi]

theorem eq_zero_of_weight_two {w : Fin 7 → ZMod 2} {i j : Fin 7} (hij : i ≠ j)
    (hw : hammingNorm w = 2) (hi : w i = 1) (hj : w j = 1) : ∀ k, k ≠ i → k ≠ j → w k = 0 := by
  classical
  intro k hki hkj
  by_contra hne
  have hsub : ({i, j, k} : Finset (Fin 7)) ⊆ Finset.univ.filter fun l => w l ≠ 0 := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hl with rfl | rfl | rfl
    · rw [hi]; exact one_ne_zero
    · rw [hj]; exact one_ne_zero
    · exact hne
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hij, Ne.symm hki]),
    Finset.card_insert_of_notMem (by simp [Ne.symm hkj]), Finset.card_singleton] at h1
  have h2 : hammingNorm w = (Finset.univ.filter fun l => w l ≠ 0).card := rfl
  omega

theorem permAct7_fix_iff_of_weight_two {w : Fin 7 → ZMod 2} {i j : Fin 7} (hij : i ≠ j)
    (hw : hammingNorm w = 2) (hi : w i = 1) (hj : w j = 1) (σ : Perm (Fin 7)) :
    permAct7 σ w = w ↔ (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
  have h0 := eq_zero_of_weight_two hij hw hi hj
  have hone : ∀ k, w k = 1 ↔ k = i ∨ k = j := by
    intro k
    constructor
    · intro hk
      by_contra hne
      push Not at hne
      rw [h0 k hne.1 hne.2] at hk
      exact zero_ne_one hk
    · rintro (rfl | rfl)
      · exact hi
      · exact hj
  have key : permAct7 σ w = w ↔ ∀ k, (σ⁻¹ k = i ∨ σ⁻¹ k = j) ↔ (k = i ∨ k = j) := by
    constructor
    · intro h k
      rw [← hone, ← hone]
      have := congrFun h k
      rw [permAct7_apply] at this
      rw [this]
    · intro h
      funext k
      rw [permAct7_apply]
      apply zmod_two_eq_of_ne_zero_iff
      have hk := h k
      rw [← hone, ← hone] at hk
      constructor
      · intro h1
        have h2 : w (σ⁻¹ k) = 1 := zmod_two_eq_one_of_ne_zero _ h1
        rw [hk.1 h2]
        exact one_ne_zero
      · intro h1
        have h2 : w k = 1 := zmod_two_eq_one_of_ne_zero _ h1
        rw [hk.2 h2]
        exact one_ne_zero
  rw [key]
  constructor
  · intro h
    have hσi : σ i = i ∨ σ i = j := by
      have := (h (σ i)).1 (Or.inl (Perm.inv_eq_iff_eq.2 rfl))
      exact this
    have hσj : σ j = i ∨ σ j = j := (h (σ j)).1 (Or.inr (Perm.inv_eq_iff_eq.2 rfl))
    rcases hσi with h1 | h1 <;> rcases hσj with h2 | h2
    · exact absurd (σ.injective (h1.trans h2.symm)) hij
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (σ.injective (h1.trans h2.symm)) hij
  · intro h k
    have hk1 : σ⁻¹ k = i ↔ k = σ i := Perm.inv_eq_iff_eq
    have hk2 : σ⁻¹ k = j ↔ k = σ j := Perm.inv_eq_iff_eq
    rw [hk1, hk2]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      exact Or.comm

end CFSG.Quasithin.H13.A7
