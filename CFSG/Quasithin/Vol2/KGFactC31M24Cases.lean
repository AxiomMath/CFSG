module

public import CFSG.Quasithin.Vol2.KGFactC31M24Nor

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 Matrix _root_.Certificates

@[expose] def x5 : G₀ := elt w5
@[expose] def x7 : G₀ := elt w7
@[expose] def x11 : G₀ := elt w11
@[expose] def x23 : G₀ := elt w23

theorem orderOf_x5 : orderOf x5 = 5 := orderOf_elt (by norm_num) a_ord5
theorem orderOf_x7 : orderOf x7 = 7 := orderOf_elt (by norm_num) a_ord7
theorem orderOf_x11 : orderOf x11 = 11 := orderOf_elt (by norm_num) a_ord11
theorem orderOf_x23 : orderOf x23 = 23 := orderOf_elt (by norm_num) a_ord23

theorem coe_pow_order {x : G₀} {q : ℕ} (hx : orderOf x = q) :
    (x : Equiv.Perm (Fin 24)) ^ q = 1 := by
  rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]

theorem perm_facts {y t : G₀} {m : ℕ} (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j < m, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (y : Equiv.Perm (Fin 24)) * t * (y : Equiv.Perm (Fin 24))⁻¹ ≠ t ∧
      ∀ j < m, (t : Equiv.Perm (Fin 24)) * ((y : Equiv.Perm (Fin 24)) ^ j * t *
        (y : Equiv.Perm (Fin 24))⁻¹ ^ j) =
        (y : Equiv.Perm (Fin 24)) ^ j * t * (y : Equiv.Perm (Fin 24))⁻¹ ^ j * t := by
  refine ⟨fun h => hmove (Subtype.ext (by simpa using h)), fun j hj => ?_⟩
  have := congrArg Subtype.val (hcomm j hj)
  simpa using this

@[expose] def cand (k : ℕ) : G₀ := elt (candW.getD k [])

theorem forall₂_cand {k : ℕ} (hk : k < 26) {l : ℕ} {v : Fin l → G₀}
    {bs : List Table}
    (hbs : List.Forall₂ (Rep 24) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 24)))) :
    List.Forall₂ (Rep 24) (conjAll (candT k) bs) (List.ofFn fun i =>
      ((cand k : G₀) : Equiv.Perm (Fin 24)) * ((v i : G₀) : Equiv.Perm (Fin 24)) *
        ((cand k : G₀) : Equiv.Perm (Fin 24))⁻¹) := by
  have hc : Rep 24 (candT k) ((cand k : G₀) : Equiv.Perm (Fin 24)) := rep_elt _
  have h := a_candInv
  rw [List.all_eq_true] at h
  have hci := Rep.inv_of_invOK hc (h k (List.mem_range.mpr hk))
  exact forall₂_conjTab hbs hc hci

theorem closure_ofFn_conj {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (c : G₀) :
    Subgroup.closure {x | x ∈ List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 24)) *
      ((v i : G₀) : Equiv.Perm (Fin 24)) * ((c : G₀) : Equiv.Perm (Fin 24))⁻¹} =
      ((eSub hv).map (MulAut.conj c).toMonoidHom).map NativeSporadic.M24.subtype := by
  rw [eSub_eq_closure, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_ofFn, MulAut.conj_apply]

theorem orbSub_eq_of_closure {x t : G₀} {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (c : G₀)
    (h : orbSub (x : Equiv.Perm (Fin 24)) (t : Equiv.Perm (Fin 24)) =
      Subgroup.closure {g | g ∈ List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 24)) *
        ((v i : G₀) : Equiv.Perm (Fin 24)) * ((c : G₀) : Equiv.Perm (Fin 24))⁻¹}) :
    orbSub x t = (eSub hv).map (MulAut.conj c).toMonoidHom := by
  apply Subgroup.map_injective (f := NativeSporadic.M24.subtype) Subtype.val_injective
  rw [orbSub_map, ← closure_ofFn_conj hv c]
  exact h

theorem orbSub_cases5
    {t : G₀} (ht : orderOf t = 2)
    (hmove : x5 * t * x5⁻¹ ≠ t)
    (hcomm : ∀ j < 5, t * (x5 ^ j * t * x5⁻¹ ^ j) = x5 ^ j * t * x5⁻¹ ^ j * t) :
    (∃ c : G₀, orbSub x5 t = (eSub basis_s32).map (MulAut.conj c).toMonoidHom) ∨
      (∃ c : G₀, orbSub x5 t = (eSub basis_s16).map (MulAut.conj c).toMonoidHom) ∨
      ∃ c : G₀, orbSub x5 t = (eSub basis_o).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hcands : List.Forall₂ (List.Forall₂ (Rep 24)) cands5
      [List.ofFn fun i => ((cand 0 : G₀) : Equiv.Perm (Fin 24)) *
          ((vS32 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 0 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 1 : G₀) : Equiv.Perm (Fin 24)) *
          ((vS32 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 1 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 2 : G₀) : Equiv.Perm (Fin 24)) *
          ((vS32 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 2 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 3 : G₀) : Equiv.Perm (Fin 24)) *
          ((vS16 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 3 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 4 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 4 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 5 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 5 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 6 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 6 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 7 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 7 : G₀) : Equiv.Perm (Fin 24))⁻¹] :=
    .cons (forall₂_cand (by norm_num) forall₂_s32) (.cons (forall₂_cand (by norm_num) forall₂_s32)
      (.cons (forall₂_cand (by norm_num) forall₂_s32) (.cons (forall₂_cand (by norm_num)
        forall₂_s16) (.cons (forall₂_cand (by norm_num) forall₂_o) (.cons (forall₂_cand
          (by norm_num) forall₂_o) (.cons (forall₂_cand (by norm_num) forall₂_o) (.cons
            (forall₂_cand (by norm_num) forall₂_o) .nil)))))))
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn24 a_orb5 hcands (List.mem_singleton_self _)
    hT (rep_elt w5) hTt (by norm_num) (coe_pow_order orderOf_x5) hmove' hcomm'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  rcases hcg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨cand 0, orbSub_eq_of_closure basis_s32 _ hcl⟩
  · exact Or.inl ⟨cand 1, orbSub_eq_of_closure basis_s32 _ hcl⟩
  · exact Or.inl ⟨cand 2, orbSub_eq_of_closure basis_s32 _ hcl⟩
  · exact Or.inr (Or.inl ⟨cand 3, orbSub_eq_of_closure basis_s16 _ hcl⟩)
  · exact Or.inr (Or.inr ⟨cand 4, orbSub_eq_of_closure basis_o _ hcl⟩)
  · exact Or.inr (Or.inr ⟨cand 5, orbSub_eq_of_closure basis_o _ hcl⟩)
  · exact Or.inr (Or.inr ⟨cand 6, orbSub_eq_of_closure basis_o _ hcl⟩)
  · exact Or.inr (Or.inr ⟨cand 7, orbSub_eq_of_closure basis_o _ hcl⟩)

theorem orbSub_cases7
    {t : G₀} (ht : orderOf t = 2)
    (hmove : x7 * t * x7⁻¹ ≠ t)
    (hcomm : ∀ j < 7, t * (x7 ^ j * t * x7⁻¹ ^ j) = x7 ^ j * t * x7⁻¹ ^ j * t) :
    (∃ c : G₀, orbSub x7 t = (eSub basis_u4).map (MulAut.conj c).toMonoidHom) ∨
      (∃ c : G₀, orbSub x7 t = (eSub basis_r2).map (MulAut.conj c).toMonoidHom) ∨
      (∃ c : G₀, orbSub x7 t = (eSub basis_o).map (MulAut.conj c).toMonoidHom) ∨
      (∃ c : G₀, orbSub x7 t = (eSub basis_u6).map (MulAut.conj c).toMonoidHom) ∨
      orbSub x7 t = (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ∨
      orbSub x7 t = (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ∨
      orbSub x7 t = (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom := by
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  have hcands : List.Forall₂ (List.Forall₂ (Rep 24)) cands7
      [List.ofFn fun i => ((cand 8 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU4 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 8 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 9 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU4 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 9 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 10 : G₀) : Equiv.Perm (Fin 24)) *
          ((vR2 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 10 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 11 : G₀) : Equiv.Perm (Fin 24)) *
          ((vR2 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 11 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 12 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 12 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 13 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 13 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 14 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU4 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 14 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 15 : G₀) : Equiv.Perm (Fin 24)) *
          ((vR2 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 15 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 16 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 16 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 17 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 17 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 18 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 18 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 19 : G₀) : Equiv.Perm (Fin 24)) *
          ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((cand 19 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 20 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 20 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 21 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 21 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 22 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 22 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 23 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 23 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 24 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 24 : G₀) : Equiv.Perm (Fin 24))⁻¹,
        List.ofFn fun i => ((cand 25 : G₀) : Equiv.Perm (Fin 24)) *
          ((vU6 i : G₀) : Equiv.Perm (Fin 24)) * ((cand 25 : G₀) : Equiv.Perm (Fin 24))⁻¹] :=
    .cons (forall₂_cand (by norm_num) forall₂_u4) <|
      .cons (forall₂_cand (by norm_num) forall₂_u4) <|
      .cons (forall₂_cand (by norm_num) forall₂_r2) <|
      .cons (forall₂_cand (by norm_num) forall₂_r2) <|
      .cons (forall₂_cand (by norm_num) forall₂_u5) <|
      .cons (forall₂_cand (by norm_num) forall₂_o) <|
      .cons (forall₂_cand (by norm_num) forall₂_u4) <|
      .cons (forall₂_cand (by norm_num) forall₂_r2) <|
      .cons (forall₂_cand (by norm_num) forall₂_o) <|
      .cons (forall₂_cand (by norm_num) forall₂_u5) <|
      .cons (forall₂_cand (by norm_num) forall₂_u5) <|
      .cons (forall₂_cand (by norm_num) forall₂_o) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .cons (forall₂_cand (by norm_num) forall₂_u6) <|
      .nil
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn24 a_orb7 hcands (List.mem_singleton_self _)
    hT (rep_elt w7) hTt (by norm_num) (coe_pow_order orderOf_x7) hmove' hcomm'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcg
  rcases hcg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨cand 8, orbSub_eq_of_closure basis_u4 _ hcl⟩
  · exact Or.inl ⟨cand 9, orbSub_eq_of_closure basis_u4 _ hcl⟩
  · exact Or.inr (Or.inl ⟨cand 10, orbSub_eq_of_closure basis_r2 _ hcl⟩)
  · exact Or.inr (Or.inl ⟨cand 11, orbSub_eq_of_closure basis_r2 _ hcl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (orbSub_eq_of_closure basis_u5 _ hcl)))))
  · exact Or.inr (Or.inr (Or.inl ⟨cand 13, orbSub_eq_of_closure basis_o _ hcl⟩))
  · exact Or.inl ⟨cand 14, orbSub_eq_of_closure basis_u4 _ hcl⟩
  · exact Or.inr (Or.inl ⟨cand 15, orbSub_eq_of_closure basis_r2 _ hcl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨cand 16, orbSub_eq_of_closure basis_o _ hcl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (orbSub_eq_of_closure basis_u5 _ hcl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (orbSub_eq_of_closure basis_u5 _ hcl))))))
  · exact Or.inr (Or.inr (Or.inl ⟨cand 19, orbSub_eq_of_closure basis_o _ hcl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 20, orbSub_eq_of_closure basis_u6 _ hcl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 21, orbSub_eq_of_closure basis_u6 _ hcl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 22, orbSub_eq_of_closure basis_u6 _ hcl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 23, orbSub_eq_of_closure basis_u6 _ hcl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 24, orbSub_eq_of_closure basis_u6 _ hcl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cand 25, orbSub_eq_of_closure basis_u6 _ hcl⟩)))

theorem not_bad11
    {t : G₀} (ht : orderOf t = 2) (hmove : x11 * t * x11⁻¹ ≠ t)
    (hcomm : ∀ j < 11, t * (x11 ^ j * t * x11⁻¹ ^ j) = x11 ^ j * t * x11⁻¹ ^ j * t) : False := by
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  exact false_of_actCheck hn24 a_act11 hT (List.mem_singleton_self _) (rep_elt w11) hTt hmove'
    hcomm'

theorem not_bad23
    {t : G₀} (ht : orderOf t = 2) (hmove : x23 * t * x23⁻¹ ≠ t)
    (hcomm : ∀ j < 23, t * (x23 ^ j * t * x23⁻¹ ^ j) = x23 ^ j * t * x23⁻¹ ^ j * t) : False := by
  obtain ⟨T, hT, hTt⟩ := exists_invTab ht
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove hcomm
  exact false_of_actCheck hn24 a_act23 hT (List.mem_singleton_self _) (rep_elt w23) hTt hmove'
    hcomm'

end CFSG.Quasithin.KGC31.M24

end
