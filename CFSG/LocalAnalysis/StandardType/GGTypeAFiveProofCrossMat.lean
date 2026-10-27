module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputsBlock
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestLevi

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.ComponentClassification

section IdOutside

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

@[expose] def GGIdOutside (S : Finset ι) (X : Matrix ι ι F) : Prop :=
  ∀ i j, (i ∉ S ∨ j ∉ S) → X i j = if i = j then 1 else 0

omit [Fintype ι] in
theorem GGIdOutside.mono {S S' : Finset ι} {X : Matrix ι ι F} (h : GGIdOutside S X)
    (hS : S ⊆ S') : GGIdOutside S' X := fun i j hij =>
  h i j (hij.imp (fun hi hS' => hi (hS hS')) (fun hj hS' => hj (hS hS')))

omit [Fintype ι] in
theorem ggIdOutside_one (S : Finset ι) : GGIdOutside S (1 : Matrix ι ι F) := fun _ _ _ =>
  Matrix.one_apply

theorem GGIdOutside.mul {S : Finset ι} {X Y : Matrix ι ι F} (hX : GGIdOutside S X)
    (hY : GGIdOutside S Y) : GGIdOutside S (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  rcases hij with hi | hj
  · rw [Finset.sum_eq_single i (fun k _ hk => by rw [hX i k (Or.inl hi), ite_eq_right (Ne.symm hk),
      zero_mul]) (by simp), hX i i (Or.inl hi), ite_eq_left rfl, one_mul, hY i j (Or.inl hi)]
  · rw [Finset.sum_eq_single j (fun k _ hk => by rw [hY k j (Or.inr hj), ite_eq_right hk, mul_zero])
      (by simp), hY j j (Or.inr hj), ite_eq_left rfl, mul_one, hX i j (Or.inr hj)]

theorem GGIdOutside.sub_one_mul_sub_one {S S' : Finset ι} (h : Disjoint S S')
    {X Y : Matrix ι ι F} (hX : GGIdOutside S X) (hY : GGIdOutside S' Y) :
    (X - 1) * (Y - 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ S
  · have hk' : k ∉ S' := Finset.disjoint_left.mp h hk
    rw [Matrix.sub_apply Y 1 k j, hY k j (Or.inl hk'), Matrix.one_apply, sub_self, mul_zero]
  · rw [Matrix.sub_apply X 1 i k, hX i k (Or.inr hk), Matrix.one_apply, sub_self, zero_mul]

theorem GGIdOutside.commute {S S' : Finset ι} (h : Disjoint S S') {X Y : Matrix ι ι F}
    (hX : GGIdOutside S X) (hY : GGIdOutside S' Y) : X * Y = Y * X := by
  have h1 := hX.sub_one_mul_sub_one h hY
  have h2 := hY.sub_one_mul_sub_one h.symm hX
  calc X * Y = (X - 1) * (Y - 1) + X + Y - 1 := by noncomm_ring
    _ = (Y - 1) * (X - 1) + Y + X - 1 := by rw [h1, h2]; abel
    _ = Y * X := by noncomm_ring

theorem ggIdOutside_iff_mem_coordBlockSL {N : ℕ} {S : Finset (Fin N)}
    {g : SpecialLinearGroup (Fin N) F} :
    GGIdOutside S (g : Matrix (Fin N) (Fin N) F) ↔
      g ∈ CFSG.RankThree.CALinearPlane.coordBlockSL F S :=
  CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.symm

end IdOutside

section Braid

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

theorem mul_signedPerm_one_apply (X : Matrix ι ι F) (π : Equiv.Perm ι) (i k : ι) :
    (X * signedPerm π (1 : ι → F)) i k = X i (π k) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π k)
    (fun l _ hl => by rw [signedPerm_apply, ite_eq_right hl, mul_zero]) (by simp)]
  simp [signedPerm_apply]

theorem signedPerm_one_mul_apply (X : Matrix ι ι F) (π : Equiv.Perm ι) (i k : ι) :
    (signedPerm π (1 : ι → F) * X) i k = X (π.symm i) k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm i)
    (fun l _ hl => by
      have : i ≠ π l := fun e => hl (by rw [e, Equiv.symm_apply_apply])
      rw [signedPerm_apply, ite_eq_right this, zero_mul]) (by simp)]
  simp [signedPerm_apply]

theorem GGIdOutside.braid_entries {X : Matrix ι ι F} {m a b : ι} (hma : m ≠ a) (hmb : m ≠ b)
    (hab : a ≠ b) (hX : GGIdOutside {a, b} X)
    (hbr : X * signedPerm (Equiv.swap m a) (1 : ι → F) * X =
      signedPerm (Equiv.swap m a) (1 : ι → F) * X * signedPerm (Equiv.swap m a) (1 : ι → F)) :
    X a a = 0 ∧ X b b = 0 ∧ X a b * X b a = 1 := by
  have hm : ∀ j, X m j = if m = j then 1 else 0 := fun j => hX m j (Or.inl (by simp [hma, hmb]))
  have hrow : ∀ i, (i = a ∨ i = b) → ∀ l, l ≠ a → l ≠ b → X i l = 0 := by
    intro i hi l hla hlb
    rw [hX i l (Or.inr (by simp [hla, hlb]))]
    rcases hi with rfl | rfl
    · exact ite_eq_right (Ne.symm hla)
    · exact ite_eq_right (Ne.symm hlb)
  have hma' : X m a = 0 := by rw [hm a, ite_eq_right hma]
  have L : ∀ i j, (X * signedPerm (Equiv.swap m a) (1 : ι → F) * X) i j =
      ∑ k, X i (Equiv.swap m a k) * X k j := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [mul_signedPerm_one_apply]
  have R : ∀ i j, (signedPerm (Equiv.swap m a) (1 : ι → F) * X *
      signedPerm (Equiv.swap m a) (1 : ι → F)) i j =
      X (Equiv.swap m a i) (Equiv.swap m a j) := by
    intro i j
    rw [mul_signedPerm_one_apply, signedPerm_one_mul_apply, Equiv.symm_swap]
  have hσm : Equiv.swap m a m = a := Equiv.swap_apply_left m a
  have hσa : Equiv.swap m a a = m := Equiv.swap_apply_right m a
  have hσb : Equiv.swap m a b = b := Equiv.swap_apply_of_ne_of_ne (Ne.symm hmb) (Ne.symm hab)
  have hsum : ∀ i, (i = a ∨ i = b) →
      ∑ k, X i (Equiv.swap m a k) * X k a = X i a * X m a + X i b * X b a := by
    intro i hi
    rw [Fintype.sum_eq_add m b hmb (fun k hk => ?_), hσm, hσb]
    have h1 : Equiv.swap m a k ≠ a := fun e => hk.1 ((Equiv.swap m a).injective (e.trans hσm.symm))
    have h2 : Equiv.swap m a k ≠ b := fun e => hk.2 ((Equiv.swap m a).injective (e.trans hσb.symm))
    rw [hrow i hi _ h1 h2, zero_mul]
  have e1 := congrFun (congrFun hbr m) a
  rw [L, R, hσm, hσa, Fintype.sum_eq_single a (fun k hk => by
    rw [hm, ite_eq_right (fun e => hk ((Equiv.swap m a).injective (e.symm.trans hσa.symm))),
      zero_mul])] at e1
  rw [hσa, hm, ite_eq_left rfl, one_mul] at e1
  have haa : X a a = 0 := by
    rw [e1, hX a m (Or.inr (by simp [hma, hmb])), ite_eq_right (Ne.symm hma)]
  have e2 := congrFun (congrFun hbr a) a
  rw [L, R, hσa, hsum a (Or.inl rfl), hma', mul_zero, zero_add, hm m, ite_eq_left rfl] at e2
  have e3 := congrFun (congrFun hbr b) a
  rw [L, R, hσa, hσb, hsum b (Or.inr rfl), hma', mul_zero, zero_add,
    hX b m (Or.inr (by simp [hma, hmb])), ite_eq_right (Ne.symm hmb)] at e3
  have hba : X b a ≠ 0 := fun h => by rw [h, mul_zero] at e2; exact zero_ne_one e2
  exact ⟨haa, (mul_eq_zero.mp e3).resolve_right hba, e2⟩

omit [Fintype ι] in
theorem GGIdOutside.eq_signedPerm {X : Matrix ι ι F} {a b : ι} (hab : a ≠ b)
    (hX : GGIdOutside {a, b} X) (haa : X a a = 0) (hbb : X b b = 0) :
    X = signedPerm (Equiv.swap a b)
      (fun i => if i = a then X b a else if i = b then X a b else 1) := by
  ext r s
  rw [signedPerm_apply]
  by_cases hs : s = a
  · subst hs
    rw [Equiv.swap_apply_left, ite_eq_left rfl]
    by_cases hr : r = b
    · subst hr
      rw [ite_eq_left rfl]
    · rw [ite_eq_right hr]
      by_cases hra : r = s
      · subst hra
        exact haa
      · rw [hX r s (Or.inl (by simp [hr, hra])), ite_eq_right hra]
  · by_cases hsb : s = b
    · subst hsb
      rw [Equiv.swap_apply_right, ite_eq_right hs, ite_eq_left rfl]
      by_cases hr : r = a
      · subst hr
        rw [ite_eq_left rfl]
      · rw [ite_eq_right hr]
        by_cases hrs : r = s
        · subst hrs
          exact hbb
        · rw [hX r s (Or.inl (by simp [hr, hrs])), ite_eq_right hrs]
    · rw [Equiv.swap_apply_of_ne_of_ne hs hsb, ite_eq_right hs, ite_eq_right hsb,
        hX r s (Or.inr (by simp [hs, hsb]))]

end Braid

section Cross

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

theorem ggCross_signedPerm {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {v w : ι → F}
    (hv : ∀ i, i ≠ a → i ≠ b → v i = 1) (hvab : v a * v b = 1)
    (hw : ∀ i, i ≠ a → i ≠ c → w i = 1) (hwac : w a * w c = 1) :
    (signedPerm (Equiv.swap a c) w * signedPerm (Equiv.swap a b) v) ^ 3 = 1 ∧
      GGIdOutside {b, c} (signedPerm (Equiv.swap a b) v * signedPerm (Equiv.swap a c) w *
        signedPerm (Equiv.swap a b) v) := by
  have sab_a : Equiv.swap a b a = b := Equiv.swap_apply_left a b
  have sab_b : Equiv.swap a b b = a := Equiv.swap_apply_right a b
  have sab_c : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)
  have sac_a : Equiv.swap a c a = c := Equiv.swap_apply_left a c
  have sac_c : Equiv.swap a c c = a := Equiv.swap_apply_right a c
  have sac_b : Equiv.swap a c b = b := Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc
  have vc : v c = 1 := hv c hac.symm hbc.symm
  have wb : w b = 1 := hw b hab.symm hbc
  refine ⟨?_, ?_⟩
  · rw [signedPerm_mul_signedPerm, pow_three, signedPerm_mul_signedPerm,
      signedPerm_mul_signedPerm]
    have hρ : Equiv.swap a c * Equiv.swap a b * ((Equiv.swap a c * Equiv.swap a b) *
        (Equiv.swap a c * Equiv.swap a b)) = 1 := by
      ext x
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hxa : x = a
      · simp only [hxa, sab_a, sab_b, sab_c, sac_a, sac_b, sac_c]
      by_cases hxb : x = b
      · simp only [hxb, sab_a, sab_b, sab_c, sac_a, sac_b, sac_c]
      by_cases hxc : x = c
      · simp only [hxc, sab_a, sab_b, sab_c, sac_a, sac_b, sac_c]
      simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hxa hxc]
    rw [hρ, signedPerm_one, ← Matrix.diagonal_one]
    congr 1
    funext x
    simp only [Equiv.Perm.mul_apply]
    by_cases hxa : x = a
    · simp only [hxa, sab_a, sab_b, sab_c, sac_a, sac_b, vc, wb]
      linear_combination (w a * w c) * hvab + hwac
    by_cases hxb : x = b
    · simp only [hxb, sab_a, sab_b, sab_c, sac_a, sac_c, vc, wb]
      linear_combination (w a * w c) * hvab + hwac
    by_cases hxc : x = c
    · simp only [hxc, sab_a, sab_b, sab_c, sac_b, sac_c, vc, wb]
      linear_combination (w a * w c) * hvab + hwac
    simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hxa hxc,
      hv x hxa hxb, hw x hxa hxc, mul_one]
  · rw [signedPerm_mul_signedPerm, signedPerm_mul_signedPerm]
    intro i j hij
    rw [signedPerm_apply]
    simp only [Equiv.Perm.mul_apply]
    have hbc' : j ∈ ({b, c} : Finset ι) → i ∉ ({b, c} : Finset ι) := fun hj =>
      hij.resolve_right fun h => h hj
    by_cases hja : j = a
    · simp only [hja, sab_a, sab_b, sac_b, wb]
      by_cases hia : i = a
      · rw [hia, ite_eq_left rfl, ite_eq_left rfl]
        linear_combination hvab
      · rw [ite_eq_right hia, ite_eq_right hia]
    by_cases hjb : j = b
    · have hi := hbc' (by simp [hjb])
      have hib : i ≠ b := fun h => hi (by simp [h])
      have hic : i ≠ c := fun h => hi (by simp [h])
      simp only [hjb, sab_b, sab_c, sac_a]
      rw [ite_eq_right hic, ite_eq_right hib]
    by_cases hjc : j = c
    · have hi := hbc' (by simp [hjc])
      have hib : i ≠ b := fun h => hi (by simp [h])
      have hic : i ≠ c := fun h => hi (by simp [h])
      simp only [hjc, sab_a, sab_c, sac_c]
      rw [ite_eq_right hib, ite_eq_right hic]
    simp only [Equiv.swap_apply_of_ne_of_ne hja hjb, Equiv.swap_apply_of_ne_of_ne hja hjc,
      hv j hja hjb, hw j hja hjc, mul_one]

end Cross

section Aut

variable {m : ℕ} {F : Type} [Field F]

theorem slFieldAut_transvection (σ : F ≃+* F) {i j : Fin m} (hij : i ≠ j) (c : F) :
    CatalogueBHigherLinearField.slFieldAut (Fin m) F σ (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (σ c) := by
  apply Subtype.ext
  change ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin m) F) :
    Matrix (Fin m) (Fin m) F).map σ = _
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  ext r s
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp

theorem slGraphAut_transvection {i j : Fin m} (hij : i ≠ j) (c : F) :
    CatalogueBGraphForm.slGraphAut m F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij.symm (-c) := by
  have hinv : (SpecialLinearGroup.transvection hij c)⁻¹ =
      SpecialLinearGroup.transvection hij (-c) :=
    inv_eq_of_mul_eq_one_right (SpecialLinearGroup.transvection_mul_neg hij c)
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, hinv, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem slFieldAut_weylRep (σ : F ≃+* F) (k : Fin m) :
    CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ (weylRep m F k) = weylRep m F k := by
  simp only [weylRep, map_mul, slFieldAut_transvection, map_one, map_neg]

theorem slGraphAut_weylRep_of_two (h2 : (2 : F) = 0) (k : Fin m) :
    CatalogueBGraphForm.slGraphAut (m + 1) F (weylRep m F k) = weylRep m F k := by
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, inv_eq_of_mul_eq_one_right (weylRep_mul_self m h2 k),
    coe_weylRep_of_two m h2 k]
  ext r s
  rw [Matrix.transpose_apply, signedPerm_apply, signedPerm_apply]
  by_cases h : r = Equiv.swap k.castSucc k.succ s
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Equiv.swap_apply_self])]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun e => h (by rw [e, Equiv.swap_apply_self]))]

theorem exists_slFieldGraph_transvection (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1) {i j : Fin m}
    (hij : i ≠ j) : ∃ (i' j' : Fin m) (h' : i' ≠ j') (c : F),
      ((i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i)) ∧
      (CatalogueBHigherLinearField.slFieldAut (Fin m) F σ *
        CatalogueBGraphForm.slGraphAut m F ^ ε) (SpecialLinearGroup.transvection h' c) =
          SpecialLinearGroup.transvection hij 1 := by
  interval_cases ε
  · exact ⟨i, j, hij, 1, Or.inl ⟨rfl, rfl⟩, by
      rw [pow_zero, mul_one, slFieldAut_transvection, map_one]⟩
  · refine ⟨j, i, hij.symm, -1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [pow_one, MulAut.mul_apply, slGraphAut_transvection, slFieldAut_transvection, neg_neg,
      map_one]

theorem slFieldGraph_weylRep_of_two (h2 : (2 : F) = 0) (σ : F ≃+* F) {ε : ℕ} (hε : ε ≤ 1)
    (k : Fin m) :
    (CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ *
      CatalogueBGraphForm.slGraphAut (m + 1) F ^ ε) (weylRep m F k) = weylRep m F k := by
  interval_cases ε
  · rw [pow_zero, mul_one, slFieldAut_weylRep]
  · rw [pow_one, MulAut.mul_apply, slGraphAut_weylRep_of_two h2, slFieldAut_weylRep]

end Aut

section Block

variable {n : ℕ} {F : Type} [Field F]

theorem slBlockMat_last_left (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (j : Fin (n + 1 + 1)) :
    slBlockMat n F M (Fin.last (n + 1)) j = if Fin.last (n + 1) = j then 1 else 0 := by
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  rw [last_eq_finSumFinEquiv, slBlockMat_apply]
  rcases q with q | q
  · have h : Fin.natAdd (n + 1) (0 : Fin 1) ≠ Fin.castAdd 1 q := fun h => by
      have h1 := congrArg Fin.val h
      have h2 := q.isLt
      simp at h1
      omega
    simp [h]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp

theorem slBlockMat_last_right (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (i : Fin (n + 1 + 1)) :
    slBlockMat n F M i (Fin.last (n + 1)) = if i = Fin.last (n + 1) then 1 else 0 := by
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  rw [last_eq_finSumFinEquiv, slBlockMat_apply]
  rcases p with p | p
  · have h : Fin.castAdd 1 p ≠ Fin.natAdd (n + 1) (0 : Fin 1) := fun h => by
      have h1 := congrArg Fin.val h
      have h2 := p.isLt
      simp at h1
      omega
    simp [h]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp

theorem slBlockMat_castSucc (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (i j : Fin (n + 1)) :
    slBlockMat n F M i.castSucc j.castSucc = M i j := by
  rw [castSucc_eq_finSumFinEquiv, castSucc_eq_finSumFinEquiv, slBlockMat_apply]
  rfl

@[expose] def ggLeviCoords (n : ℕ) : Finset (Fin (n + 1 + 1 + 1)) :=
  (Finset.univ.erase (Fin.last (n + 1 + 1))).erase (Fin.last (n + 1)).castSucc

theorem not_mem_ggLeviCoords_iff {k : Fin (n + 1 + 1 + 1)} :
    k ∉ ggLeviCoords n ↔ k = (Fin.last (n + 1)).castSucc ∨ k = Fin.last (n + 1 + 1) := by
  simp only [ggLeviCoords, Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not]
  tauto

theorem ggIdOutside_slBlockMat₂ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    GGIdOutside (ggLeviCoords n) (slBlockMat (n + 1) F (slBlockMat n F M)) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [slBlockMat_castSucc]
      simp only [Fin.castSucc_inj]
      have h' : i' = Fin.last (n + 1) ∨ j' = Fin.last (n + 1) := by
        rcases hij with h | h
        · rcases not_mem_ggLeviCoords_iff.mp h with h | h
          · exact Or.inl (Fin.castSucc_injective _ h)
          · exact absurd h (Fin.castSucc_ne_last _)
        · rcases not_mem_ggLeviCoords_iff.mp h with h | h
          · exact Or.inr (Fin.castSucc_injective _ h)
          · exact absurd h (Fin.castSucc_ne_last _)
      rcases h' with rfl | rfl
      · exact slBlockMat_last_left M j'
      · exact slBlockMat_last_right M i'
    · rw [slBlockMat_last_right]
  · rw [slBlockMat_last_left]

theorem coe_slBlockHom₂ (g : SpecialLinearGroup (Fin (n + 1)) F) :
    ((slBlockHom₂ n F g : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
      Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) =
      slBlockMat (n + 1) F (slBlockMat n F (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) := by
  rw [slBlockHom₂_apply, coe_slBlockHom, coe_slBlockHom]

theorem coe_slBlockHom₂_slConjugation (A : GL (Fin (n + 1)) F)
    (g : SpecialLinearGroup (Fin (n + 1)) F) :
    ((slBlockHom₂ n F (CatalogueBHigherLinearAction.slConjugation (n + 1) F A g) :
        SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
        Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) =
      slBlockMat (n + 1) F (slBlockMat n F A.val) *
        ((slBlockHom₂ n F g : SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F) :
          Matrix (Fin (n + 1 + 1 + 1)) (Fin (n + 1 + 1 + 1)) F) *
        slBlockMat (n + 1) F (slBlockMat n F (A⁻¹).val) := by
  rw [coe_slBlockHom₂, coe_slBlockHom₂, CatalogueBHigherLinearAction.slConjugation_matrix]
  simp only [slBlockMat_mul]

theorem slBlockMat₂_mul_inv (A : GL (Fin (n + 1)) F) :
    slBlockMat (n + 1) F (slBlockMat n F A.val) * slBlockMat (n + 1) F (slBlockMat n F (A⁻¹).val) =
      1 := by
  rw [← slBlockMat_mul, ← slBlockMat_mul, Units.mul_inv, slBlockMat_one, slBlockMat_one]

theorem slBlockMat₂_inv_mul (A : GL (Fin (n + 1)) F) :
    slBlockMat (n + 1) F (slBlockMat n F (A⁻¹).val) * slBlockMat (n + 1) F (slBlockMat n F A.val) =
      1 := by
  rw [← slBlockMat_mul, ← slBlockMat_mul, Units.inv_mul, slBlockMat_one, slBlockMat_one]

end Block

end CFSG.StandardType
