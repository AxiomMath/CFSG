module

public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMLine
public import Certificates.Data.S1277Cand

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277MLine
open scoped IsMulCommutative

section Census

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [IsMulCommutative ↥V]

theorem census_real (C : Coding ↥V) (hCV : Subgroup.centralizer (V : Set G) = V)
    {E : Subgroup G} (hE : IsElemAbelian 2 E) (hE64 : Nat.card E = 64)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) {bs : List B6}
    (hbs : ∀ e (he : e ∈ E), C.cB (conjAct V ⟨e, hEV he⟩) ∈ bs) (hlen : bs.length ≤ 8)
    (hfix : ∀ B ∈ bs, isInvB B = true → (fixCode B).length ≤ 16)
    (hpair : ∀ B₁ ∈ bs, ∀ B₂ ∈ bs, B₁ ≠ B₂ → isInvB B₁ = true → isInvB B₂ = true →
      B₁.comp B₂ = B₂.comp B₁ → (fixInterL B₁ B₂).length < 8) : E ≤ V := by
  classical
  by_contra hnot
  set A : Subgroup (MulAut ↥V) := autOn E V with hA
  have hAcard : Nat.card A = (E ⊓ V).relIndex E := by
    rw [hA, card_autOn_eq_relIndex hEV, hCV]
  have hDcard : (E ⊓ V).relIndex E * Nat.card ↥(E ⊓ V) = 64 := by
    have h := Subgroup.relIndex_mul_card (H := E ⊓ V) (K := E)
    rw [inf_eq_left.2 (inf_le_left : E ⊓ V ≤ E)] at h
    rw [h, hE64]
  have hAfin : (A : Set (MulAut ↥V)).Finite := Set.toFinite _
  have hAmem : ∀ a ∈ A, C.cB a ∈ bs := by
    intro a ha
    obtain ⟨⟨e, he⟩, rfl⟩ := (A4.mem_autOn_iff hEV).1 ha
    exact hbs e he
  have hA8 : Nat.card A ≤ 8 := by
    have h1 : (C.cB '' (A : Set (MulAut ↥V))).ncard ≤ bs.length :=
      ncard_le_length' (hAfin.image _) (by rintro _ ⟨a, ha, rfl⟩; exact hAmem a ha)
    rw [Set.ncard_image_of_injective _ C.cB_injective] at h1
    have h2 : (A : Set (MulAut ↥V)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
    omega
  have hD8 : 8 ≤ Nat.card ↥(E ⊓ V) := by
    by_contra hlt
    push Not at hlt
    have : (E ⊓ V).relIndex E * Nat.card ↥(E ⊓ V) ≤ 8 * 7 :=
      Nat.mul_le_mul (hAcard ▸ hA8) (by omega)
    omega
  obtain ⟨e₁, he₁E, he₁V⟩ : ∃ e ∈ E, e ∉ V := by
    by_contra hno
    push Not at hno
    exact hnot fun x hx => hno x hx
  have he₁sq : e₁ * e₁ = 1 := by rw [← pow_two]; exact hE.2 e₁ he₁E
  set a₁ : MulAut ↥V := conjAct V ⟨e₁, hEV he₁E⟩ with ha₁
  have ha₁A : a₁ ∈ A := (A4.mem_autOn_iff hEV).2 ⟨⟨e₁, he₁E⟩, rfl⟩
  have ha₁ne : a₁ ≠ 1 := conjAct_ne_one (hEV he₁E) he₁V hCV
  have ha₁sq : a₁ * a₁ = 1 := conjAct_sq_one (hEV he₁E) he₁sq
  have hB₁ : isInvB (C.cB a₁) = true := isInv_cB C ha₁sq ha₁ne
  have hfixA : ∀ a ∈ A, ∀ d ∈ (E ⊓ V).subgroupOf V, a d = d := by
    intro a ha d hd
    obtain ⟨⟨e, he⟩, rfl⟩ := (A4.mem_autOn_iff hEV).1 ha
    change conjAct V ⟨e, hEV he⟩ d = d
    apply Subtype.ext
    rw [conjAct_val]
    have hdE : (d : G) ∈ E := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hd)).1
    have hc : e * (d : G) = (d : G) * e := comm_of_isElemAbelian hE he hdE
    rw [hc]; group
  have hDcodes : ∀ (S : Set ℕ), (∀ d ∈ (E ⊓ V).subgroupOf V, C.cd d ∈ S) → S.Finite →
      Nat.card ↥(E ⊓ V) ≤ S.ncard := by
    intro S hS hSfin
    have h1 : (C.cd '' (((E ⊓ V).subgroupOf V : Subgroup ↥V) : Set ↥V)).ncard =
        Nat.card ↥(E ⊓ V) := by
      rw [Set.ncard_image_of_injective _ C.cd_injective, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ V ≤ V)).toEquiv
    rw [← h1]
    exact Set.ncard_le_ncard (by rintro _ ⟨d, hd, rfl⟩; exact hS d hd) hSfin
  have hfixc : ∀ a ∈ A, ∀ d ∈ (E ⊓ V).subgroupOf V,
      (C.cB a).app (C.cd d) = C.cd d := by
    intro a ha d hd
    rw [← C.cd_apply, hfixA a ha d hd]
  have hD16 : Nat.card ↥(E ⊓ V) ≤ 16 := by
    have h := hDcodes ↑(fixCode (C.cB a₁)).toFinset (fun d hd => by
      rw [Finset.mem_coe, List.mem_toFinset]
      unfold fixCode
      rw [List.mem_filter]
      refine ⟨List.mem_range.2 (C.cd_lt d), ?_⟩
      simpa using hfixc a₁ ha₁A d hd) (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    exact h.trans ((List.toFinset_card_le _).trans (hfix _ (hAmem a₁ ha₁A) hB₁))
  have hA4 : 4 ≤ Nat.card A := by
    by_contra hlt
    push Not at hlt
    rw [hAcard] at hlt
    have : (E ⊓ V).relIndex E * Nat.card ↥(E ⊓ V) ≤ 3 * 16 :=
      Nat.mul_le_mul (by omega) hD16
    omega
  obtain ⟨a₂, ha₂A, ha₂1, ha₂ne⟩ : ∃ a₂ ∈ A, a₂ ≠ 1 ∧ a₂ ≠ a₁ := by
    by_contra hno
    push Not at hno
    have hsub : (A : Set (MulAut ↥V)) ⊆ {1, a₁} := by
      intro a ha
      by_cases h1 : a = 1
      · exact Or.inl h1
      · exact Or.inr (hno a ha h1)
    have h2 : ({1, a₁} : Set (MulAut ↥V)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    have h3 : (A : Set (MulAut ↥V)).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h2
    have h4 : (A : Set (MulAut ↥V)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨⟨e₂, he₂E⟩, he₂⟩ := (A4.mem_autOn_iff hEV).1 ha₂A
  have he₂' : conjAct V ⟨e₂, hEV he₂E⟩ = a₂ := he₂
  have he₂sq : e₂ * e₂ = 1 := by rw [← pow_two]; exact hE.2 e₂ he₂E
  have ha₂sq : a₂ * a₂ = 1 := by
    rw [← he₂']; exact conjAct_sq_one (hEV he₂E) he₂sq
  have hB₂ : isInvB (C.cB a₂) = true := isInv_cB C ha₂sq ha₂1
  have hBne : C.cB a₁ ≠ C.cB a₂ := fun h => ha₂ne (C.cB_injective h).symm
  have hcomm12 : a₁ * a₂ = a₂ * a₁ := by
    rw [ha₁, ← he₂', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact comm_of_isElemAbelian hE he₁E he₂E
  have hBcomm : (C.cB a₁).comp (C.cB a₂) = (C.cB a₂).comp (C.cB a₁) := by
    rw [← C.cB_mul, ← C.cB_mul, hcomm12]
  have hlt8 := hpair _ (hAmem a₁ ha₁A) _ (hAmem a₂ ha₂A) hBne hB₁ hB₂ hBcomm
  have h := hDcodes ↑(fixInterL (C.cB a₁) (C.cB a₂)).toFinset (fun d hd => by
    rw [Finset.mem_coe, List.mem_toFinset]
    unfold fixInterL
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 (C.cd_lt d), ?_⟩
    simp [hfixc a₁ ha₁A d hd, hfixc a₂ ha₂A d hd]) (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h
  have := h.trans (List.toFinset_card_le _)
  omega

end Census

end CFSG.Quasithin.H13.I1277

end
