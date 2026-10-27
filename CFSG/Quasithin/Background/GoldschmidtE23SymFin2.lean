module

public import CFSG.Quasithin.Background.GoldschmidtE23SymFin
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open Equiv G6 CFSG.QuasithinUnique

namespace GE23

theorem isSylowTwoOf_d8 : IsSylowTwoOf d8 (⊤ : Subgroup (Perm (Fin 5))) := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_d8]; norm_num), ?_⟩
  have hm := Subgroup.card_mul_index d8
  rw [card_d8, Nat.card_perm, Nat.card_fin] at hm
  have h120 : Nat.factorial 5 = 120 := by decide
  have : d8.index = 15 := by omega
  show ¬ 2 ∣ d8.relIndex ⊤
  rw [Subgroup.relIndex_top_right, this]
  decide

theorem exists_finset_of_le {R : Subgroup (Perm (Fin 5))} (hR : R ≤ d8) :
    ∃ S : Finset (Perm (Fin 5)), S ∈ d8list.toFinset.powerset ∧ (∀ σ, σ ∈ S ↔ σ ∈ R) ∧
      S.card = Nat.card ↥R := by
  classical
  refine ⟨d8list.toFinset.filter (· ∈ R), ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · intro σ
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨mem_d8_iff.1 (hR h), h⟩⟩
  · have h1 : (R : Set (Perm (Fin 5))) = ↑(d8list.toFinset.filter (· ∈ R)) := by
      ext σ
      simp only [SetLike.mem_coe, Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨mem_d8_iff.1 (hR h), h⟩, fun h => h.2⟩
    have h2 : Nat.card ↥R = (R : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
    rw [h2, h1, Set.ncard_coe_finset]

theorem classify_sub {R : Subgroup (Perm (Fin 5))} (hR : R ≤ d8)
    (hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hsq : ∀ a ∈ R, a * a = 1) :
    Nat.card ↥R * Nat.card ↥(fixΔ R) ≤ 16 ∧
      (Nat.card ↥R * Nat.card ↥(fixΔ R) = 16 → R ≤ e4) := by
  obtain ⟨S, hSmem, hS, hcard⟩ := exists_finset_of_le hR
  have hfix : Nat.card ↥(fixΔ R) = (fixVec S).card := card_fixΔ hS
  have key := fixVec_classify S hSmem
    (fun a ha b hb => ⟨(hS _).2 (R.mul_mem ((hS a).1 ha) ((hS b).1 hb)),
      hab a ((hS a).1 ha) b ((hS b).1 hb), hsq a ((hS a).1 ha)⟩)
    ((hS 1).2 R.one_mem)
  rw [hfix, ← hcard]
  refine ⟨key.1, fun h σ hσ => ?_⟩
  have h1 : σ ∈ e4list.toFinset := key.2 h ((hS σ).2 hσ)
  exact mem_e4_iff.2 (List.mem_toFinset.1 h1)

@[expose] def MulClosed (S : Finset (Perm (Fin 5))) : Prop := ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S

instance (S : Finset (Perm (Fin 5))) : Decidable (MulClosed S) := by
  unfold MulClosed
  infer_instance

theorem e4_nontrivial_gen : ∀ S ∈ e4list.toFinset.powerset,
    MulClosed S → 1 < S.card → S.card * (fixVec S).card = 16 → sa ∈ S ∨ sb ∈ S := by
  decide +kernel

theorem gen_of_sub {R : Subgroup (Perm (Fin 5))} (hR : R ≤ e4) (hne : R ≠ ⊥)
    (h16 : Nat.card ↥R * Nat.card ↥(fixΔ R) = 16) : sa ∈ R ∨ sb ∈ R := by
  classical
  have hR' : R ≤ d8 := hR.trans e4_le_d8
  obtain ⟨S, -, hS, hcard⟩ := exists_finset_of_le hR'
  have hfix : Nat.card ↥(fixΔ R) = (fixVec S).card := card_fixΔ hS
  rw [hfix, ← hcard] at h16
  have hSe4 : S ∈ e4list.toFinset.powerset := by
    refine Finset.mem_powerset.2 fun σ hσ => ?_
    exact List.mem_toFinset.2 (mem_e4_iff.1 (hR ((hS σ).1 hσ)))
  have hne' : 1 < S.card := by
    rw [hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot R).2 hne
  have := e4_nontrivial_gen S hSe4
    (fun a ha b hb => (hS _).2 (R.mul_mem ((hS a).1 ha) ((hS b).1 hb))) hne' h16
  rcases this with h | h
  · exact Or.inl ((hS sa).1 h)
  · exact Or.inr ((hS sb).1 h)

theorem centre_d8 : ∀ σ ∈ d8list, (∀ τ ∈ d8list, σ * τ = τ * σ) → σ = 1 ∨ σ = sa * sb := by
  decide +kernel

theorem eps_central : ∀ τ ∈ d8list, (sa * sb) * τ = τ * (sa * sb) := by decide +kernel

theorem eps_ne_one : sa * sb ≠ 1 := by decide +kernel

@[expose] def esa : Subgroup (Perm (Fin 5)) := Subgroup.closure {sa}

@[expose] def esb : Subgroup (Perm (Fin 5)) := Subgroup.closure {sb}

@[expose] def esalist : List (Perm (Fin 5)) := [1, sa]

@[expose] def esblist : List (Perm (Fin 5)) := [1, sb]

theorem mem_esa_iff {x : Perm (Fin 5)} : x ∈ esa ↔ x ∈ esalist := by
  have hcl : ∀ y ∈ esalist, ∀ z ∈ esalist, y * z ∈ esalist := by decide +kernel
  have hinv : ∀ y ∈ esalist, y⁻¹ ∈ esalist := by decide +kernel
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ esalist) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      decide +kernel
    · decide +kernel
    · intro y z _ _ hy hz
      exact hcl y hy z hz
    · intro y _ hy
      exact hinv y hy
  · intro hx
    have hsa : sa ∈ esa := Subgroup.subset_closure rfl
    simp only [esalist, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact esa.one_mem
    · exact hsa

theorem mem_esb_iff {x : Perm (Fin 5)} : x ∈ esb ↔ x ∈ esblist := by
  have hcl : ∀ y ∈ esblist, ∀ z ∈ esblist, y * z ∈ esblist := by decide +kernel
  have hinv : ∀ y ∈ esblist, y⁻¹ ∈ esblist := by decide +kernel
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ esblist) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl
      decide +kernel
    · decide +kernel
    · intro y z _ _ hy hz
      exact hcl y hy z hz
    · intro y _ hy
      exact hinv y hy
  · intro hx
    have hsb : sb ∈ esb := Subgroup.subset_closure rfl
    simp only [esblist, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact esb.one_mem
    · exact hsb

theorem card_esa : Nat.card ↥esa = 2 := by
  have h1 : (esa : Set (Perm (Fin 5))) = ↑esalist.toFinset := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset]
    exact mem_esa_iff
  have h2 : Nat.card ↥esa = (esa : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
  rw [h2, h1, Set.ncard_coe_finset]
  decide +kernel

theorem card_esb : Nat.card ↥esb = 2 := by
  have h1 : (esb : Set (Perm (Fin 5))) = ↑esblist.toFinset := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset]
    exact mem_esb_iff
  have h2 : Nat.card ↥esb = (esb : Set (Perm (Fin 5))).ncard := Nat.card_coe_set_eq _
  rw [h2, h1, Set.ncard_coe_finset]
  decide +kernel

theorem card_fixΔ_esa : Nat.card ↥(fixΔ esa) = 8 := by
  rw [card_fixΔ (S := esalist.toFinset)
    (fun σ => by rw [List.mem_toFinset]; exact mem_esa_iff.symm)]
  decide +kernel

theorem card_fixΔ_esb : Nat.card ↥(fixΔ esb) = 8 := by
  rw [card_fixΔ (S := esblist.toFinset)
    (fun σ => by rw [List.mem_toFinset]; exact mem_esb_iff.symm)]
  decide +kernel

theorem card_fixΔ_e4 : Nat.card ↥(fixΔ e4) = 4 := by
  rw [card_fixΔ (S := e4list.toFinset) (fun σ => by rw [List.mem_toFinset]; exact mem_e4_iff.symm)]
  exact card_fixVec_e4

theorem esa_le_e4 : esa ≤ e4 := by
  intro x hx
  rcases (by simpa [esalist] using mem_esa_iff.1 hx : x = 1 ∨ x = sa) with rfl | rfl
  · exact e4.one_mem
  · exact sa_mem_e4

theorem esb_le_e4 : esb ≤ e4 := by
  intro x hx
  rcases (by simpa [esblist] using mem_esb_iff.1 hx : x = 1 ∨ x = sb) with rfl | rfl
  · exact e4.one_mem
  · exact sb_mem_e4

theorem sa_mem_esa : sa ∈ esa := Subgroup.subset_closure rfl

theorem sb_mem_esb : sb ∈ esb := Subgroup.subset_closure rfl

theorem e4_eq_sup : e4 = esa ⊔ esb := by
  refine le_antisymm ?_ (sup_le esa_le_e4 esb_le_e4)
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_sup_left sa_mem_esa
  · exact Subgroup.mem_sup_right sb_mem_esb

theorem sr_conj_esa : ∀ x ∈ esalist, sr * x * sr⁻¹ ∈ esblist := by decide +kernel

theorem sr_conj_esb : ∀ x ∈ esblist, sr * x * sr⁻¹ ∈ esalist := by decide +kernel

@[expose] def y0 : ↥(coreMod 5) := ofVec ![1, 1, 1, 1, 0] (by decide)

theorem y0_ne_one : y0 ≠ 1 := by
  intro h
  have h1 : vecOf y0 0 = vecOf (1 : ↥(coreMod 5)) 0 := by rw [h]
  revert h1
  decide +kernel

theorem y0_fixed_sa : coreAct 5 sa y0 = y0 := by
  rw [coreAct_eq_iff]
  decide +kernel

theorem y0_fixed_sb : coreAct 5 sb y0 = y0 := by
  rw [coreAct_eq_iff]
  decide +kernel

end GE23

end CFSG.Quasithin
