module

public import CFSG.LocalAnalysis.StandardType.GGKSmall7Defs
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat6
public import CFSG.LocalAnalysis.StandardType.GGDepED4Up7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private instance lr6rd_decPredIn : DecidablePred GGDepED4In :=
  fun c => by unfold GGDepED4In; infer_instance

private instance lr6rd_decLeaf : DecidablePred GGDepED4Leaf :=
  fun c => by unfold GGDepED4Leaf; infer_instance

private lemma lr6rd_coxE6_diag (i : Fin 6) : CoxeterMatrix.E₆ i i = 1 :=
  (CoxeterMatrix.E₆).diagonal i

private lemma lr6rd_coxE6_leaf_leaf (x y : Fin 6) (hx : GGDepED4Leaf x) (hy : GGDepED4Leaf y)
    (hxy : x ≠ y) : CoxeterMatrix.E₆ x y = 2 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | decide

private lemma lr6rd_coxE6_leaf_center (x : Fin 6) (hx : GGDepED4Leaf x) :
    CoxeterMatrix.E₆ x 3 = 3 := by
  rcases hx with rfl | rfl | rfl <;> decide

private lemma lr6rd_coxE6_center_leaf (x : Fin 6) (hx : GGDepED4Leaf x) :
    CoxeterMatrix.E₆ 3 x = 3 := by
  rcases hx with rfl | rfl | rfl <;> decide

private def lr6rd_embJ : Fin 4 → {c : Fin 6 // GGDepED4In c} :=
  ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]

private lemma lr6rd_embJ_inj : Function.Injective lr6rd_embJ := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lr6rd_embJ]

private lemma lr6rd_J_val (j : {c : Fin 6 // GGDepED4In c}) :
    j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 4 := by
  obtain ⟨v, hv⟩ := j
  fin_cases v
  · exact (hv.1 rfl).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact (hv.2 rfl).elim

private lemma lr6rd_J_exists (j : {c : Fin 6 // GGDepED4In c}) :
    ∃ i : Fin 4, lr6rd_embJ i = j := by
  obtain ⟨v, hv⟩ := j
  rcases lr6rd_J_val ⟨v, hv⟩ with h | h | h | h
  · exact ⟨0, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨1, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨2, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨3, Subtype.ext (by rw [h]; rfl)⟩

private lemma lr6rd_cardJ : Fintype.card {c : Fin 6 // GGDepED4In c} = 4 := by
  have hbij : Function.Bijective lr6rd_embJ := ⟨lr6rd_embJ_inj, lr6rd_J_exists⟩
  have h := Fintype.card_congr (Equiv.ofBijective lr6rd_embJ hbij)
  rw [Fintype.card_fin] at h
  exact h.symm

theorem ggDepED4_E6_of_pat6 {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)}
    {CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3))
    (hP : GGDepED4PatE6 CK) :
    ∃ eK : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa),
      MK = CoxeterMatrix.E₆.reindex eK ∧ ∀ i j, CK (eK i) (eK j) = CartanMatrix.E 6 i j := by
  classical
  obtain ⟨a₁, a₂, c, c', hane, hleafc, hleafc', hcc', hpairJ, h12, h21, h11, h22⟩ := hP
  have hc : GGDepED4In c := by
    rcases hleafc with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have hc' : GGDepED4In c' := by
    rcases hleafc' with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have hc3 : c ≠ 3 := by rcases hleafc with rfl | rfl | rfl <;> decide
  have hc'3 : c' ≠ 3 := by rcases hleafc' with rfl | rfl | rfl <;> decide
  have hd : ∃ d : Fin 6, GGDepED4Leaf d ∧ d ≠ c ∧ d ≠ c' := by
    rcases hleafc with rfl | rfl | rfl <;> rcases hleafc' with rfl | rfl | rfl
    · exact absurd rfl hcc'
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact absurd rfl hcc'
    · exact ⟨1, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨1, by decide, by decide, by decide⟩
    · exact absurd rfl hcc'
  obtain ⟨d, hdleaf, hdc, hdc'⟩ := hd
  have hd3 : d ≠ 3 := by rcases hdleaf with rfl | rfl | rfl <;> decide
  have hdi : GGDepED4In d := by
    rcases hdleaf with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have h3i : GGDepED4In (3 : Fin 6) := by unfold GGDepED4In; decide
  let eKf : Fin 6 → ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := fun i =>
    if i = 0 then Sum.inr a₁
    else if i = 1 then Sum.inl ⟨d, hdi⟩
    else if i = 2 then Sum.inl ⟨c, hc⟩
    else if i = 3 then Sum.inl ⟨3, h3i⟩
    else if i = 4 then Sum.inl ⟨c', hc'⟩
    else Sum.inr a₂
  have hinj : Function.Injective eKf := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eKf]
  have hcardJ : Fintype.card {c : Fin 6 // GGDepED4In c} = 4 := lr6rd_cardJ
  have hcardLa : Fintype.card Λa = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hΛa
  have hcardsum : Fintype.card (Fin 6) = Fintype.card ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := by
    rw [Fintype.card_fin, Fintype.card_sum, hcardJ, hcardLa]
  have hbij : Function.Bijective eKf :=
    (Fintype.bijective_iff_injective_and_card eKf).mpr ⟨hinj, hcardsum⟩
  let eK : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := Equiv.ofBijective eKf hbij
  have hMKJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl i) (Sum.inl j) = CoxeterMatrix.E₆ i.1 j.1 :=
    lr6p6_MJ hCK (emb := Sum.inl) (fun _ _ h => Sum.inl.inj h) hJ
  have hCa1 : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).1
  have hCa1' : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).2.1
  have hCa2 : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inr a₂) (Sum.inl j) = (if j.1 = c' then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).2.2.1
  have hCa2' : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inl j) (Sum.inr a₂) = (if j.1 = c' then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).2.2.2
  have hM_of_zero : ∀ u v : ({c : Fin 6 // GGDepED4In c} ⊕ Λa), u ≠ v →
      CK u v = 0 → MK u v = 2 := by
    intro u v huv h0
    rcases hCK.entries huv with h | h | h | h
    · exact h.1
    · rw [h.2.1] at h0; norm_num at h0
    · rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> (rw [h1] at h0; norm_num at h0)
    · rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> (rw [h1] at h0; norm_num at h0)
  have hM_of_neg : ∀ u v : ({c : Fin 6 // GGDepED4In c} ⊕ Λa), u ≠ v →
      CK u v = -1 → CK v u = -1 → MK u v = 3 := by
    intro u v huv h1 h2
    rcases hCK.entries huv with h | h | h | h
    · rw [h.2.1] at h1; norm_num at h1
    · exact h.1
    · rcases h.2 with ⟨-, hb⟩ | ⟨ha, -⟩
      · rw [hb] at h2; norm_num at h2
      · rw [ha] at h1; norm_num at h1
    · rcases h.2 with ⟨-, hb⟩ | ⟨ha, -⟩
      · rw [hb] at h2; norm_num at h2
      · rw [ha] at h1; norm_num at h1
  have hMKa1 : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c
    · have h1 : CK (Sum.inr a₁) (Sum.inl j) = -1 := by rw [hCa1 j, if_pos hjc]
      have h2 : CK (Sum.inl j) (Sum.inr a₁) = -1 := by rw [hCa1' j, if_pos hjc]
      rw [hM_of_neg _ _ Sum.inr_ne_inl h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inr a₁) (Sum.inl j) = 0 := by rw [hCa1 j, if_neg hjc]
      rw [hM_of_zero _ _ Sum.inr_ne_inl h0, if_neg hjc]
  have hMKa1' : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c
    · have h1 : CK (Sum.inl j) (Sum.inr a₁) = -1 := by rw [hCa1' j, if_pos hjc]
      have h2 : CK (Sum.inr a₁) (Sum.inl j) = -1 := by rw [hCa1 j, if_pos hjc]
      rw [hM_of_neg _ _ Sum.inl_ne_inr h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inl j) (Sum.inr a₁) = 0 := by rw [hCa1' j, if_neg hjc]
      rw [hM_of_zero _ _ Sum.inl_ne_inr h0, if_neg hjc]
  have hMKa2 : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inr a₂) (Sum.inl j) = (if j.1 = c' then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c'
    · have h1 : CK (Sum.inr a₂) (Sum.inl j) = -1 := by rw [hCa2 j, if_pos hjc]
      have h2 : CK (Sum.inl j) (Sum.inr a₂) = -1 := by rw [hCa2' j, if_pos hjc]
      rw [hM_of_neg _ _ Sum.inr_ne_inl h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inr a₂) (Sum.inl j) = 0 := by rw [hCa2 j, if_neg hjc]
      rw [hM_of_zero _ _ Sum.inr_ne_inl h0, if_neg hjc]
  have hMKa2' : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl j) (Sum.inr a₂) = (if j.1 = c' then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c'
    · have h1 : CK (Sum.inl j) (Sum.inr a₂) = -1 := by rw [hCa2' j, if_pos hjc]
      have h2 : CK (Sum.inr a₂) (Sum.inl j) = -1 := by rw [hCa2 j, if_pos hjc]
      rw [hM_of_neg _ _ Sum.inl_ne_inr h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inl j) (Sum.inr a₂) = 0 := by rw [hCa2' j, if_neg hjc]
      rw [hM_of_zero _ _ Sum.inl_ne_inr h0, if_neg hjc]
  have hMK11 : MK (Sum.inr a₁) (Sum.inr a₁) = 1 := MK.diagonal _
  have hMK22 : MK (Sum.inr a₂) (Sum.inr a₂) = 1 := MK.diagonal _
  have hMK12 : MK (Sum.inr a₁) (Sum.inr a₂) = 2 :=
    hM_of_zero _ _ (fun h => hane (Sum.inr.inj h)) h12
  have hMK21 : MK (Sum.inr a₂) (Sum.inr a₁) = 2 :=
    hM_of_zero _ _ (fun h => hane (Sum.inr.inj h).symm) h21
  have eK_apply : ∀ i : Fin 6, eK i = eKf i := fun i => Equiv.ofBijective_apply eKf hbij i
  have hc3' : (3 : Fin 6) ≠ c := fun h => hc3 h.symm
  have hc'3' : (3 : Fin 6) ≠ c' := fun h => hc'3 h.symm
  have hd3' : (3 : Fin 6) ≠ d := fun h => hd3 h.symm
  have hcd : c ≠ d := fun h => hdc h.symm
  have hc'd : c' ≠ d := fun h => hdc' h.symm
  have hc'c : c' ≠ c := fun h => hcc' h.symm
  have hMKtot : ∀ i j : Fin 6, MK (eK i) (eK j) = CoxeterMatrix.E₆ i j := by
    intro i j
    rw [eK_apply i, eK_apply j]
    fin_cases i <;> fin_cases j <;>
      simp [eKf, hMKJ, hMKa1, hMKa1', hMKa2, hMKa2',
        hMK11, hMK12, hMK21, hMK22, hdc, hdc', hcc', hd3, hc3, hc'3, hc3', hc'3', hd3',
        hcd, hc'd, hc'c, hleafc, hleafc', hdleaf, lr6rd_coxE6_diag, lr6rd_coxE6_leaf_leaf,
        lr6rd_coxE6_leaf_center, lr6rd_coxE6_center_leaf] <;> decide
  have hMKeq : MK = CoxeterMatrix.E₆.reindex eK := by
    apply CoxeterMatrix.ext
    funext x y
    rw [CoxeterMatrix.reindex_apply]
    simpa using hMKtot (eK.symm x) (eK.symm y)
  have hCKtot : ∀ i j : Fin 6, CK (eK i) (eK j) = CartanMatrix.E 6 i j :=
    l05nEU_cartan_of_reindex eK hCK hMKeq
  exact ⟨eK, hMKeq, hCKtot⟩

private lemma lr6rd_M_of_zero {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h0 : C u v = 0) : M u v = 2 := by
  rcases hC.entries huv with h | h | h | h
  · exact h.1
  · rw [h.2.1] at h0; norm_num at h0
  · rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> (rw [h1] at h0; norm_num at h0)
  · rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> (rw [h1] at h0; norm_num at h0)

private lemma lr6rd_M_of_neg {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h1 : C u v = -1) (h2 : C v u = -1) :
    M u v = 3 := by
  rcases hC.entries huv with h | h | h | h
  · rw [h.2.1] at h1; norm_num at h1
  · exact h.1
  · rcases h.2 with ⟨-, hb⟩ | ⟨ha, -⟩
    · rw [hb] at h2; norm_num at h2
    · rw [ha] at h1; norm_num at h1
  · rcases h.2 with ⟨-, hb⟩ | ⟨ha, -⟩
    · rw [hb] at h2; norm_num at h2
    · rw [ha] at h1; norm_num at h1

private lemma lr6rd_D6_diag (i : Fin 6) : CartanMatrix.D 6 i i = 2 := by
  fin_cases i <;> decide

private lemma lr6rd_cartan_of_D6_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (hCK : GGIntCartan MK CK) (e : Fin 6 ≃ Λ) (he : MK = (ggCoxeterMatrixD 6).reindex e) :
    ∀ i j, CK (e i) (e j) = CartanMatrix.D 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCK.1]
    exact (lr6rd_D6_diag i).symm
  · have hC₂ : GGIntCartan MK (Matrix.reindex e e (CartanMatrix.D 6)) := by
      rw [he]
      exact GGIntCartan.reindex e (ggIntCartan_D 6)
    have hle : MK (e i) (e j) ≤ 3 := by
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        ggCoxeterMatrixD_apply, if_neg hij]
      split_ifs <;> omega
    have hpair := (hCK.pair hC₂ (e.injective.ne hij)).2 hle
    rw [hpair.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem ggDepED4_D6_of_pat6 {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)}
    {CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3))
    (hP : GGDepED4PatD6 CK) :
    ∃ eD : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa),
      MK = (ggCoxeterMatrixD 6).reindex eD ∧ ∀ i j, CK (eD i) (eD j) = CartanMatrix.D 6 i j := by
  classical
  obtain ⟨a₁, a₂, c, hane, hleafc, hpairJ, h12, h21, h11, h22⟩ := hP
  have hc : GGDepED4In c := by
    rcases hleafc with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have hc3 : c ≠ 3 := by rcases hleafc with rfl | rfl | rfl <;> decide
  have he12 : ∃ e1 e2 : Fin 6,
      GGDepED4Leaf e1 ∧ GGDepED4Leaf e2 ∧ e1 ≠ e2 ∧ e1 ≠ c ∧ e2 ≠ c := by
    rcases hleafc with rfl | rfl | rfl
    · exact ⟨2, 4, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 4, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨e1, e2, he1, he2, he12', he1c, he2c⟩ := he12
  have he13 : e1 ≠ 3 := by rcases he1 with rfl | rfl | rfl <;> decide
  have he23 : e2 ≠ 3 := by rcases he2 with rfl | rfl | rfl <;> decide
  have he1i : GGDepED4In e1 := by
    rcases he1 with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have he2i : GGDepED4In e2 := by
    rcases he2 with rfl | rfl | rfl <;> unfold GGDepED4In <;> decide
  have h3i : GGDepED4In (3 : Fin 6) := by unfold GGDepED4In; decide
  let eDf : Fin 6 → ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := fun i =>
    if i = 0 then Sum.inr a₂
    else if i = 1 then Sum.inr a₁
    else if i = 2 then Sum.inl ⟨c, hc⟩
    else if i = 3 then Sum.inl ⟨3, h3i⟩
    else if i = 4 then Sum.inl ⟨e1, he1i⟩
    else Sum.inl ⟨e2, he2i⟩
  have hinj : Function.Injective eDf := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eDf]
  have hcardLa : Fintype.card Λa = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hΛa
  have hcardsum : Fintype.card (Fin 6) = Fintype.card ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := by
    rw [Fintype.card_fin, Fintype.card_sum, lr6rd_cardJ, hcardLa]
  have hbij : Function.Bijective eDf :=
    (Fintype.bijective_iff_injective_and_card eDf).mpr ⟨hinj, hcardsum⟩
  let eD : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := Equiv.ofBijective eDf hbij
  have hMKJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl i) (Sum.inl j) = CoxeterMatrix.E₆ i.1 j.1 :=
    lr6p6_MJ hCK (emb := Sum.inl) (fun _ _ h => Sum.inl.inj h) hJ
  have hCa1 : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).1
  have hCa1' : ∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then (-1 : ℤ) else 0) :=
    fun j => (hpairJ j).2.1
  have hCa2 : ∀ j : {c : Fin 6 // GGDepED4In c}, CK (Sum.inr a₂) (Sum.inl j) = 0 :=
    fun j => (hpairJ j).2.2.1
  have hCa2' : ∀ j : {c : Fin 6 // GGDepED4In c}, CK (Sum.inl j) (Sum.inr a₂) = 0 :=
    fun j => (hpairJ j).2.2.2
  have hMKa1 : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c
    · have h1 : CK (Sum.inr a₁) (Sum.inl j) = -1 := by rw [hCa1 j, if_pos hjc]
      have h2 : CK (Sum.inl j) (Sum.inr a₁) = -1 := by rw [hCa1' j, if_pos hjc]
      rw [lr6rd_M_of_neg hCK Sum.inr_ne_inl h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inr a₁) (Sum.inl j) = 0 := by rw [hCa1 j, if_neg hjc]
      rw [lr6rd_M_of_zero hCK Sum.inr_ne_inl h0, if_neg hjc]
  have hMKa1' : ∀ j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then 3 else 2) := by
    intro j
    by_cases hjc : j.1 = c
    · have h1 : CK (Sum.inl j) (Sum.inr a₁) = -1 := by rw [hCa1' j, if_pos hjc]
      have h2 : CK (Sum.inr a₁) (Sum.inl j) = -1 := by rw [hCa1 j, if_pos hjc]
      rw [lr6rd_M_of_neg hCK Sum.inl_ne_inr h1 h2, if_pos hjc]
    · have h0 : CK (Sum.inl j) (Sum.inr a₁) = 0 := by rw [hCa1' j, if_neg hjc]
      rw [lr6rd_M_of_zero hCK Sum.inl_ne_inr h0, if_neg hjc]
  have hMKa2 : ∀ j : {c : Fin 6 // GGDepED4In c}, MK (Sum.inr a₂) (Sum.inl j) = 2 :=
    fun j => lr6rd_M_of_zero hCK Sum.inr_ne_inl (hCa2 j)
  have hMKa2' : ∀ j : {c : Fin 6 // GGDepED4In c}, MK (Sum.inl j) (Sum.inr a₂) = 2 :=
    fun j => lr6rd_M_of_zero hCK Sum.inl_ne_inr (hCa2' j)
  have hMK11 : MK (Sum.inr a₁) (Sum.inr a₁) = 1 := MK.diagonal _
  have hMK22 : MK (Sum.inr a₂) (Sum.inr a₂) = 1 := MK.diagonal _
  have hMK12 : MK (Sum.inr a₁) (Sum.inr a₂) = 3 :=
    lr6rd_M_of_neg hCK (fun h => hane (Sum.inr.inj h)) h12 h21
  have hMK21 : MK (Sum.inr a₂) (Sum.inr a₁) = 3 :=
    lr6rd_M_of_neg hCK (fun h => hane (Sum.inr.inj h).symm) h21 h12
  have eD_apply : ∀ i : Fin 6, eD i = eDf i := fun i => Equiv.ofBijective_apply eDf hbij i
  have hc3' : (3 : Fin 6) ≠ c := fun h => hc3 h.symm
  have he13' : (3 : Fin 6) ≠ e1 := fun h => he13 h.symm
  have he23' : (3 : Fin 6) ≠ e2 := fun h => he23 h.symm
  have he1c' : c ≠ e1 := fun h => he1c h.symm
  have he2c' : c ≠ e2 := fun h => he2c h.symm
  have he21' : e2 ≠ e1 := fun h => he12' h.symm
  have hMKtot : ∀ i j : Fin 6, MK (eD i) (eD j) = ggCoxeterMatrixD 6 i j := by
    intro i j
    rw [eD_apply i, eD_apply j]
    fin_cases i <;> fin_cases j <;>
      simp [eDf, hMKJ, hMKa1, hMKa1', hMKa2, hMKa2',
        hMK11, hMK12, hMK21, hMK22, hc3, hc3', he1c, he2c, he12', he13, he23, he13', he23',
        he1c', he2c', he21', he1, he2, hleafc, lr6rd_coxE6_diag, lr6rd_coxE6_leaf_leaf,
        lr6rd_coxE6_leaf_center, lr6rd_coxE6_center_leaf, ggCoxeterMatrixD_apply] <;> decide
  have hMKeq : MK = (ggCoxeterMatrixD 6).reindex eD := by
    apply CoxeterMatrix.ext
    funext x y
    rw [CoxeterMatrix.reindex_apply]
    simpa using hMKtot (eD.symm x) (eD.symm y)
  have hCKtot : ∀ i j : Fin 6, CK (eD i) (eD j) = CartanMatrix.D 6 i j :=
    lr6rd_cartan_of_D6_reindex hCK eD hMKeq
  exact ⟨eD, hMKeq, hCKtot⟩

theorem ggKSmall7_cases_of_alignedW {G : Type} [Group G] [Finite G] {Bs F J O : Subgroup G}
    (hA : GGDepED4AlignedW 3 2 Bs F J O) :
    GGResXDatumE6Core 3 Bs O ∨ GGKSmall7D6Data Bs O F := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hform, hrefl, hpairL, hpairK, ⟨fK, hfK⟩, hAL, hAK, hAJ⟩ := hA
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  let eJ := l05nEC_eJ b₁ b₂ e hb1 hb2
  let ee : ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) :=
    Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) := MK.reindex ee.symm
  let CK' : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)
      ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hMKweyl ee.symm
  have hCK' : GGIntCartan MK' CK' := by
    have hh := GGIntCartan.reindex (e := ee.symm) hCKcartan
    simpa [MK', CK', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using hh
  have hJ' : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK' (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at hpk
    have hck : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp only [CK', Matrix.submatrix_apply, ee, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.refl_apply]
    have hgoal : α (Sum.inl (eJ i).1) (h (Sum.inl (eJ j).1)) =
        (CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) : ZMod 3) := hpk
    rw [hck, ← hgoal]
    show α (Sum.inl (e i.1)) (h (Sum.inl (e j.1))) = CartanMatrix.E 6 i.1 j.1
    rw [hpairL (e i.1) (e j.1), l05nEU_cartan_of_reindex e hCLcartan hML i.1 j.1]
  have hAKrange : Set.range (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa =>
      φ (o.map Subtype.val id)) =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  rcases ggDepED4_pattern6 hcardΛa hWMK' hCK' hJ' with hPE6 | hPD6
  · obtain ⟨eK, hMK'e, -⟩ := ggDepED4_E6_of_pat6 hcardΛa hWMK' hCK' hJ' hPE6
    left
    have hM : MK = CoxeterMatrix.E₆.reindex (eK.trans ee) := by
      apply CoxeterMatrix.ext
      funext x y
      rw [CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply]
      have hh := congrFun (congrFun (congrArg CoxeterMatrix.M hMK'e) (ee.symm x)) (ee.symm y)
      simpa [MK', CoxeterMatrix.reindex_apply] using hh
    refine ⟨{i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa, inferInstance, inferInstance, MK, CK, V,
      inferInstance, inferInstance, ι, (fun o => φ (o.map Subtype.val id)),
      (fun o => h (o.map Subtype.val id)), (fun o => α (o.map Subtype.val id)),
      eK.trans ee, hM, hMKweyl, hCKcartan, ?_, ?_, ?_, ⟨fK, hfK⟩, ?_⟩
    · intro o w; exact hform (o.map Subtype.val id) w
    · intro o; exact hrefl (o.map Subtype.val id)
    · intro o o'; exact hpairK o o'
    · rw [hAK, ← hAKrange]
  · obtain ⟨eD, hMK'e, hCK'e⟩ := ggDepED4_D6_of_pat6 hcardΛa hWMK' hCK' hJ' hPD6
    right
    have hM : MK = (ggCoxeterMatrixD 6).reindex (eD.trans ee) := by
      apply CoxeterMatrix.ext
      funext x y
      rw [CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply]
      have hh := congrFun (congrFun (congrArg CoxeterMatrix.M hMK'e) (ee.symm x)) (ee.symm y)
      simpa [MK', CoxeterMatrix.reindex_apply] using hh
    have hrangeD : Set.range (fun i : Fin 6 =>
        φ (((eD.trans ee) i).map Subtype.val id)) =
        Set.range (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => φ (o.map Subtype.val id)) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨(eD.trans ee) i, rfl⟩
      · rintro ⟨o, rfl⟩; exact ⟨(eD.trans ee).symm o, by simp⟩
    have hrangeE : Set.range (fun i : Fin 6 => φ (Sum.inl (e i))) =
        Set.range (fun i : Λ => φ (Sum.inl i)) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    have hAK' : ggAutomizer O Bs = Subgroup.closure
        (Set.range (fun i : Fin 6 => φ (((eD.trans ee) i).map Subtype.val id))) := by
      rw [hAK, ← hAKrange, ← hrangeD]
    have hAL' : ggAutomizer F Bs = Subgroup.closure
        (Set.range (fun i : Fin 6 => φ (Sum.inl (e i)))) := by
      rw [hAL, hrangeE]
    have hpairD : ∀ i j : Fin 6, α (((eD.trans ee) i).map Subtype.val id)
        (h (((eD.trans ee) j).map Subtype.val id)) = (CartanMatrix.D 6 i j : ZMod 3) := by
      intro i j
      have hp := hpairK ((eD.trans ee) i) ((eD.trans ee) j)
      rw [hp]
      have hsub : CK ((eD.trans ee) i) ((eD.trans ee) j) = CK' (eD i) (eD j) := by
        simp [CK', Matrix.submatrix_apply, ee, Equiv.trans_apply]
      rw [hsub, hCK'e i j]
    have hpairE : ∀ i j : Fin 6, α (Sum.inl (e i)) (h (Sum.inl (e j))) =
        (CartanMatrix.E₆ i j : ZMod 3) := by
      intro i j
      rw [hpairL (e i) (e j), l05nEU_cartan_of_reindex e hCLcartan hML i j]
    have hcardMK : Nat.card ↥(ggAutomizer O Bs) = Nat.card MK.Group :=
      (Nat.card_congr fK.toEquiv).symm
    have hcardD : Nat.card MK.Group = Nat.card (ggCoxeterMatrixD 6).Group := by
      rw [hM]
      exact Nat.card_congr
        (CoxeterMatrix.reindexGroupEquiv (ggCoxeterMatrixD 6) (eD.trans ee)).toEquiv
    have hcard23040 : Nat.card (ggCoxeterMatrixD 6).Group = 23040 := by
      rw [OrthF3.card_coxeterD_eq 6 (by norm_num)]
      norm_num
    refine ⟨V, inferInstance, inferInstance, ι,
      (fun i => φ (((eD.trans ee) i).map Subtype.val id)),
      (fun i => φ (Sum.inl (e i))),
      (fun i => h (((eD.trans ee) i).map Subtype.val id)),
      (fun i => h (Sum.inl (e i))),
      (fun i => α (((eD.trans ee) i).map Subtype.val id)),
      (fun i => α (Sum.inl (e i))), ?_, ?_, ?_, ?_, hpairD, hpairE, hAK', hAL',
      hcardMK.trans (hcardD.trans hcard23040)⟩
    · intro i w; exact hform (((eD.trans ee) i).map Subtype.val id) w
    · intro i w; exact hform (Sum.inl (e i)) w
    · intro i; exact hrefl (((eD.trans ee) i).map Subtype.val id)
    · intro i; exact hrefl (Sum.inl (e i))

end CFSG.StandardType

end
