module

public import CFSG.Quasithin.Background.SmithC27AltK2

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm C124 C124.YZ
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

namespace AltCtx

theorem not_sylow_of_isAltType_seven (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 3)
    (htype : IsAltType K 7) : ¬ IsSylowTwoOf R (K ⊔ R) := by
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
    rw [card_quot_of_isAltType htype, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  exact not_sylow_of_not_chi0 hC129 C.hyp (not_isChi0Block_of_card hcard)

theorem not_sixteen_dvd (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 3)
    (htype : IsAltType K 7) : ¬ 16 ∣ Nat.card (C.bar R) := fun h16 =>
  C.not_sylow_of_isAltType_seven hC129 htype
    (C.sylow_iff.2 (sylow_seven_of_sixteen_dvd C.R_pgroup h16))

theorem MK_eq_kJ_k3 (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 3)
    (htype : IsAltType K 7) : C.bar (M ⊓ K) = kJ (stdT3 7) := by
  have hstar : kJ (stdT3 7) ≤ C.bar (M ⊓ K) := by
    have h := C.star_alt
    rwa [alt_inf_normalizer_eq_kJ_stdT3 (J := swapGroupOf (stdInv 7 3) C.inv_sq)
      (fun g => Iff.rfl)] at h
  have hbad : ∀ Y : Subgroup (Perm (Fin 7)), (Y = pointStab ∨ Y = fanoStabEven ∨
      Y = fanoStabOdd) → C.bar (M ⊓ K) ≠ Y := by
    intro Y hY hMY
    apply C.not_sixteen_dvd hC129 htype
    have hcl : Subgroup.closure {x | ∃ y ∈ Y, x = y * swap 0 1 * y⁻¹} ≤
        conjClosure (C.bar R) (C.bar (M ⊓ K)) := by
      rw [Subgroup.closure_le]
      rintro x ⟨y, hy, rfl⟩
      have h01 : swap 0 1 ∈ C.bar R := C.J_le_R C.swap_mem_std
      rw [← hMY] at hy
      exact mem_conjClosure hy h01
    exact two_pow_dvd_of_isSylowTwoOf (a := 4) C.sylow_closure hcl
      (sixteen_dvd_card_closure_conj hY)
  rcases kJ_stdT3_overgroups hstar C.MK_le_alt with h | h | h | h | h
  · exact h
  · exact absurd h (hbad _ (Or.inl rfl))
  · exact absurd h (hbad _ (Or.inr (Or.inl rfl)))
  · exact absurd h (hbad _ (Or.inr (Or.inr rfl)))
  · exact absurd h C.MK_ne_alt

theorem R_eq_J_k3 (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 3)
    (htype : IsAltType K 7) : C.bar R = swapGroupOf (stdInv 7 3) C.inv_sq := by
  rcases eq_or_card_eq_sixteen_of_le_normalizer (J := swapGroupOf (stdInv 7 3) C.inv_sq)
      (fun g => Iff.rfl) C.R_pgroup C.J_le_R C.R_le_normalizer with h | h
  · exact h
  · exact absurd (by rw [h]) (C.not_sixteen_dvd hC129 htype)

theorem three_of_k3 (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 3)
    (hchi : IsChiBlock2 H K) (htype : IsAltType K 7) : C27Three H R M K (Vc R K) := by
  have hM := C.MK_eq_kJ_k3 hC129 htype
  have hRJ := C.R_eq_J_k3 hC129 htype
  obtain ⟨eR⟩ := C.nonempty_equiv_bar (A := R) le_sup_right
  obtain ⟨eJ⟩ := isE2_three_of_mem_iff (J := swapGroupOf (stdInv 7 3) C.inv_sq) (fun g => Iff.rfl)
  have hE : IsE2 3 ↥(starOf R K R) := ⟨eR.trans ((MulEquiv.subgroupCongr hRJ).trans eJ)⟩
  refine Or.inl ⟨hchi, Or.inr (Or.inr (Or.inr ⟨htype, hE,
    MulEquiv.ofBijective C.ι C.bij, part2221, isPartitionOfType_part2221, ?_⟩))⟩
  show C.bar (M ⊓ K) = _
  rw [hM, kJ_stdT3_eq_stabilizer]

end AltCtx

end CFSG.Quasithin.SmithC27
