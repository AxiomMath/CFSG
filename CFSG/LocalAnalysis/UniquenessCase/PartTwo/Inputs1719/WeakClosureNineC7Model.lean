module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC7Checks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7.C914

open CFSG.QuasithinUnique.A6Facts CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {φ : X →* Equiv.Perm (Fin 8)} {Tb : Subgroup X}

theorem exists_le_Vsub (hφ : IsF7Model φ Tb) {E : Subgroup X} (hE : E ≤ Tb)
    (hEe : IsElemAbelian 2 E) : ∃ i : Fin 4, E ≤ Vsub φ i := by
  rcases eq_or_ne E ⊥ with rfl | hne
  · exact ⟨0, bot_le⟩
  rcases elem_cases hφ hE hEe hne with ⟨i, rfl⟩ | ⟨a, ha, -, hEa⟩
  · exact ⟨i, le_rfl⟩
  · obtain ⟨i, -, hi⟩ := inv_row _ ((hφ.memT a).1 (hE ha)) (code_sq_of_sq (hEe.2 a ha))
    refine ⟨i, fun x hx => ?_⟩
    rcases hEa x hx with rfl | rfl
    · exact one_mem _
    · exact hi

theorem movWit (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {L : Subgroup X}
    (hsq : ∀ x : X, x ^ 2 ∈ L) (hcent : centralizer (L : Set X) = ⊥) {E : Subgroup X}
    (i : Fin 4) (hE : E ≤ Vsub φ i) :
    MovWit914 L Tb E (kSub φ (mrow_ok i)) (ySub φ (mrow_ok i)) 3 where
  le x hx := mem_of_sq_code hφ.toIsF7Emb hsq (m_sq i (codeN 8 (φ x)) hx)
  inf_centralizer := by rw [hcent, inf_bot_eq]
  normalizes v hv := mem_normalizer_of_code hφ.toIsF7Emb (l := (mrow i).K) (fun _ => Iff.rfl)
    (mrow_ok i).K_sub (m_nor i (codeN 8 (φ v)) (hE hv)) (m_nor' i (codeN 8 (φ v)) (hE hv))
  irr := twoPTwoIrred_kSub hφ hTb (mrow_ok i)
  elem := ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (hφ.mul_eq_mul (m_comm i (codeN 8 (φ a)) a.2 (codeN 8 (φ b)) b.2)),
    fun x hx => hφ.cube_of_code ((mrow_ok i).Y_cube (codeN 8 (φ x)) hx)⟩
  nontriv := by
    obtain ⟨y, hyK, hyT, hn1, hn2, x, hxY, hne⟩ := m_y i
    obtain ⟨y', rfl⟩ := hφ.surj y ((mrow_ok i).K_sub _ hyK)
    obtain ⟨x', rfl⟩ := hφ.surj x ((mrow_ok i).K_sub _ ((mrow_ok i).Y_sub _ hxY))
    refine ⟨y', ⟨⟨hyK, (hφ.memT y').2 hyT⟩, mem_normalizer_of_code hφ.toIsF7Emb
      (l := (mrow i).Y) (fun _ => Iff.rfl)
      (fun c hc => (mrow_ok i).K_sub _ ((mrow_ok i).Y_sub _ hc)) hn1 hn2⟩,
      x', hxY, fun h => mul_ne_mul_of_code hne (mul_inv_eq_iff_eq_mul.mp h)⟩
  three := Or.inl rfl

theorem fix914 (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {E : Subgroup X} (hE : E ≤ Tb)
    (hEe : IsElemAbelian 2 E) (hne : E ≠ ⊥) : Fix914 Tb E := by
  rcases elem_cases hφ hE hEe hne with ⟨i, rfl⟩ | ⟨a, ha, ha1, hEa⟩
  · obtain ⟨v, hv, k, hk, u, hu, hku, h3, h1⟩ := f_w i
    obtain ⟨v', rfl⟩ := hφ.surj v (row_K_sub i _ (row_V_sub i _ hv))
    obtain ⟨k', rfl⟩ := hφ.surj k (row_K_sub i _ hk)
    obtain ⟨u', rfl⟩ := hφ.surj u (row_K_sub i _ hu)
    refine ⟨Ksub φ i, Ysub φ i, 3, fun x hx => row_V_sub i (codeN 8 (φ x)) hx, fun hle => ?_,
      hφ.twoPTwoIrred hTb i, Or.inl rfl⟩
    refine not_mem_pCoreOf_two (K := Ksub φ i) hk (hφ.mul_eq_mul hku) (hφ.cube_of_code ?_)
      (fun h => h1 ?_) (hle (mem_Vsub.2 hv))
    · rw [code_mul]
      exact h3
    · rw [← code_mul, h, code_one]
  · obtain ⟨j, -, hjK, k, hk, u, hu, hku, h3, h1⟩ := s_w _ ((hφ.memT a).1 (hE ha))
      (fun h => ha1 (hφ.eq_one h)) (code_sq_of_sq (hEe.2 a ha))
    obtain ⟨k', rfl⟩ := hφ.surj k ((srow_ok j).K_sub _ hk)
    obtain ⟨u', rfl⟩ := hφ.surj u ((srow_ok j).K_sub _ hu)
    refine ⟨kSub φ (srow_ok j), ySub φ (srow_ok j), 3, fun x hx => ?_, fun hle => ?_,
      twoPTwoIrred_kSub hφ hTb (srow_ok j), Or.inl rfl⟩
    · rcases hEa x hx with rfl | rfl
      · exact one_mem _
      · exact hjK
    · refine not_mem_pCoreOf_two (K := kSub φ (srow_ok j)) hk (hφ.mul_eq_mul hku)
        (hφ.cube_of_code ?_) (fun h => h1 ?_) (hle ha)
      · rw [code_mul]
        exact h3
      · rw [← code_mul, h, code_one]

omit [Finite X] in
theorem pairProp_zC (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {L : Subgroup X}
    (hsq : ∀ x : X, x ^ 2 ∈ L) {x : X} (hx : codeN 8 (φ x) = zC) : PairProp914 L x := by
  obtain ⟨hlG, hlsq, hzG, hrel, hhG, hc1, hc2, hr1, hr2, hne⟩ := p_w
  obtain ⟨l, hl⟩ := hφ.surj pL hlG
  obtain ⟨z, hz⟩ := hφ.surj pZ hzG
  obtain ⟨h, hh⟩ := hφ.surj pH hhG
  obtain ⟨c1, hc1'⟩ := hφ.surj pC1 (t_sub _ hc1)
  obtain ⟨c2, hc2'⟩ := hφ.surj pC2 (t_sub _ hc2)
  have e1 : l * x = z * l := hφ.mul_eq_mul (by rw [hl, hx, hz]; exact hrel)
  have e2 : h * x = c1 * h := hφ.mul_eq_mul (by rw [hh, hx, hc1']; exact hr1)
  have e3 : h * z = c2 * h := hφ.mul_eq_mul (by rw [hh, hz, hc2']; exact hr2)
  have hlx : l * x * l⁻¹ = z := by rw [e1, mul_inv_cancel_right]
  refine ⟨l, mem_of_sq_code hφ.toIsF7Emb hsq (by rw [hl]; exact hlsq), ?_, ?_⟩
  · rw [hlx]
    refine (hTb.isPGroup.map (MulAut.conj h⁻¹).toMonoidHom).to_le ?_
    rw [closure_le]
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · refine ⟨c1, (hφ.memT c1).2 (by rw [hc1']; exact hc1), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, ← e2, inv_mul_cancel_left]
    · refine ⟨c2, (hφ.memT c2).2 (by rw [hc2']; exact hc2), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, ← e3, inv_mul_cancel_left]
  · rw [hlx]
    exact mul_ne_mul_of_code (by rw [hx, hz]; exact hne)

theorem normal914 (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {L : Subgroup X}
    (hsq : ∀ x : X, x ^ 2 ∈ L) {F : Subgroup X} (hF : F ≤ Tb)
    (hFn : Tb ≤ normalizer (F : Set X)) (hFe : IsElemAbelian 2 F) :
    F = ⊥ ∨ F = ⊥ ∨ (Nat.card F = 2 ∧ ∀ x ∈ F, x ≠ 1 → PairProp914 L x) := by
  rcases eq_or_ne F ⊥ with h | hne
  · exact Or.inl h
  refine Or.inr (Or.inr ?_)
  rcases elem_cases hφ hF hFe hne with ⟨i, rfl⟩ | ⟨a, ha, ha1, hFa⟩
  · obtain ⟨hnd, hlen⟩ := row_V_nd i
    have h4 : Nat.card (Vsub φ i) = 4 :=
      (hφ.card_eq (fun _ => Iff.rfl) (fun v hv => row_K_sub i _ (row_V_sub i _ hv)) hnd).trans hlen
    exact (hφ.close _ hF hFn hFe h4.ge).elim
  · have hcomm : ∀ t ∈ Tb, t * a = a * t := by
      intro t ht
      have h1 : t * a * t⁻¹ ∈ F := (mem_normalizer_iff.1 (hFn ht) a).1 ha
      rcases hFa _ h1 with h | h
      · exact absurd (conj_eq_one_iff.mp h) ha1
      · exact mul_inv_eq_iff_eq_mul.mp h
    have hz : codeN 8 (φ a) = zC := by
      refine z_cent _ ((hφ.memT a).1 (hF ha)) (fun h => ha1 (hφ.eq_one h)) fun t ht => ?_
      obtain ⟨t', rfl⟩ := hφ.surj t (t_sub _ ht)
      rw [← code_mul, ← code_mul, hcomm t' ((hφ.memT t').2 ht)]
    refine ⟨Nat.card_eq_two_iff.mpr ⟨1, ⟨a, ha⟩, fun h => ha1 (congrArg Subtype.val h).symm,
      Set.eq_univ_of_forall fun x => ?_⟩, fun x hx hx1 => ?_⟩
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hFa x x.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rw [(hFa x hx).resolve_left hx1]
      exact pairProp_zC hφ hTb hsq hz

theorem coordFacts (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) {L : Subgroup X}
    (hsq : ∀ x : X, x ^ 2 ∈ L) (h3 : 3 ∣ Nat.card L) (hcent : centralizer (L : Set X) = ⊥) :
    CoordFacts914 L Tb ⊥ where
  three_dvd := h3
  sq := by
    obtain ⟨d, hdT, hdsq, hdne⟩ := sq_w
    obtain ⟨x, rfl⟩ := hφ.surj d (t_sub _ hdT)
    refine ⟨x, ⟨(hφ.memT x).2 hdT, mem_of_sq_code hφ.toIsF7Emb hsq hdsq⟩, fun h => hdne ?_⟩
    rw [← code_mul, ← pow_two, h, code_one]
  mov E hE hEe := by
    obtain ⟨i, hi⟩ := exists_le_Vsub hφ hE hEe
    exact ⟨_, _, 3, movWit hφ hTb hsq hcent i hi⟩
  fix E hE hEe hne := Or.inl (fix914 hφ hTb hE hEe hne)
  normal F hF hFn hFe := normal914 hφ hTb hsq hF hFn hFe
  star h := absurd rfl h

end CFSG.LocalAnalysis.WeakClosure81.NFF7.C914
