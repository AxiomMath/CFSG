module

public import CFSG.Quasithin.H13.GoldschmidtC137SQSimp
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.Quasithin.H13.GoldschmidtC137SQKg

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.SectionRank

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)), Fintype.card_perm,
    Fintype.card_fin] at h
  have h720 : Nat.factorial 6 = 720 := by decide
  omega

theorem isKGroupCat_of_card_360 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 360) (hY : Catalog Y) : IsKGroupCat Y := by
  refine isKGroupCat_of_simple hY fun H hH N _ hs hnab => ?_
  have hdvd := card_dvd_factorial_index hH
  rw [hcard] at hdvd
  have h6 := six_le_of_dvd_factorial hdvd
  have hmul := H.card_mul_index
  rw [hcard] at hmul
  obtain ⟨h60, hle⟩ := sixty_le_card_section N hs hnab
  have hH60 : Nat.card H ≤ 60 := by
    by_contra h
    have : 61 * 6 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h6
    omega
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five
    (G := H ⧸ N) (by omega)
  exact Or.inr (Or.inl ⟨5, le_rfl, ⟨e⟩⟩)

theorem isKGroupCat_alternatingGroup_six : IsKGroupCat (alternatingGroup (Fin 6)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact isKGroupCat_of_card_360 card_alternatingGroup_six
    (Or.inr (Or.inl ⟨6, by norm_num, ⟨MulEquiv.refl _⟩⟩))

theorem isKGroupCat_of_mulEquiv_alternatingGroup_six {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 6)) : IsKGroupCat Y :=
  IsKGroupCat.of_mulEquiv isKGroupCat_alternatingGroup_six e

theorem isKGroupCat_of_hatA6 {Y : Type} [Group Y] [Finite Y]
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6)) : IsKGroupCat Y := by
  refine isKGroupCat_of_ker (QuotientGroup.mk' (Subgroup.center Y)) ?_
    (isKGroupCat_of_mulEquiv_alternatingGroup_six e)
  refine isKGroupCat_of_solvable (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
  have ha := (QuotientGroup.eq_one_iff _).1 a.2
  exact ((Subgroup.mem_center_iff.1 ha) b.1).symm

end CFSG.Quasithin.H13.U3.GC137.SQ
