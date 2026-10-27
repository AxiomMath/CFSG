module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Members
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.A312M23

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat

theorem a312For_m23
    (hq : CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M23) :
    A312For ↥CFSG.Blueprint.NativeSporadic.M23 := by
  refine CFSG.Quasithin.A312S.a312For_of_members hq m23_S_sylow
    (L := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]) (Y := m23Ctx.Y)
    m23_complete ?_
  intro j hj B hB hY
  have hj16 : j < 16 := by simpa using hj
  have hc := m23_member_card j hj16
  have hM23 : IsSporadic .M23 ↥(⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23) :=
    ⟨Subgroup.topEquiv⟩
  have hsolv : ∀ {a b : ℕ}, Nat.card (m23Ctx.Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    CFSG.Quasithin.A312S.not_isSolvable_sup hB
      (hY ▸ CFSG.Quasithin.A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three
        (by norm_num) h)
  have hS : IsPGroup 2 m23Ctx.S := m23Ctx.S_isPGroup
  interval_cases j
  · exact (hsolv (a := 7) (b := 0) (by rw [hc]; rfl)).elim
  · iterate 11 right
    left
    exact ⟨Or.inl (m23_shape_y1 hB hY), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inl (m23_shape_y2 hS hB hY)), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (m23_shape_y3 hS hB hY)))))), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (m23_shape_y4 hS hB hY)))), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inl (m23_shape_y5 hS hB hY))), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (m23_shape_y6 hS hB hY))))), hM23⟩
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (m23_shape_y7 hS hB hY)))))), hM23⟩
  · exact (m23_not_y8 hS hB hY).elim
  · iterate 11 right
    left
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (m23_shape_y9 hS hB hY)))))), hM23⟩
  · exact (hsolv (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 7) (b := 2) (by rw [hc]; rfl)).elim

theorem famM23_holds :
    FamM23 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  have hq' : CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M23 :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact @A312For.of_mulEquiv X ↥CFSG.Blueprint.NativeSporadic.M23 _ _ _ _ e (a312For_m23 hq')

end CFSG.Quasithin.A312M23
