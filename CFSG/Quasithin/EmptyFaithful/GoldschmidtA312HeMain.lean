module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeCases
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.A312He

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.K1.SporadicPerm

theorem a312For_he
    (hq : CFSG.IsQuasisimple CFSG.Sporadic.He.J) : A312For CFSG.Sporadic.He.J := by
  refine CFSG.Quasithin.A312S.a312For_of_members hq he_S_sylow
    (L := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3]) (Y := heCtx.Y) he_complete ?_
  intro j hj B hB hY
  have hj11 : j < 11 := by simpa using hj
  have hc := he_member_card j hj11
  have hHe : IsSporadic .He ↥(⊤ : Subgroup CFSG.Sporadic.He.J) :=
    ⟨Subgroup.topEquiv.trans CFSG.Sporadic.He.heEquivJ.symm⟩
  have hsolv : ∀ {a b : ℕ}, Nat.card (heCtx.Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    CFSG.Quasithin.A312S.not_isSolvable_sup hB
      (hY ▸ CFSG.Quasithin.A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three
        (by norm_num) h)
  have hS : IsPGroup 2 heCtx.S := heCtx.S_isPGroup
  interval_cases j
  · exact (hsolv (a := 10) (b := 0) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 10) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 10) (b := 2) (by rw [hc]; rfl)).elim
  · iterate 17 right
    left
    exact ⟨Or.inr (he_shape_hat3 hS hB hY), hHe⟩
  · iterate 17 right
    left
    exact ⟨Or.inr (he_shape_hat4 hS hB hY), hHe⟩
  · exact (hsolv (a := 10) (b := 2) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 10) (b := 1) (by rw [hc]; rfl)).elim
  · iterate 17 right
    left
    exact ⟨Or.inl (he_shape_ext7 hB hY), hHe⟩
  · exact (hsolv (a := 10) (b := 1) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 10) (b := 2) (by rw [hc]; rfl)).elim
  · exact (hsolv (a := 10) (b := 1) (by rw [hc]; rfl)).elim

theorem famHe_holds :
    FamHe := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  have e' : X ≃* CFSG.Sporadic.He.J := e.trans CFSG.Sporadic.He.heEquivJ
  have hq' : CFSG.IsQuasisimple CFSG.Sporadic.He.J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  exact @A312For.of_mulEquiv X CFSG.Sporadic.He.J _ _ _ _ e' (a312For_he hq')

end CFSG.Quasithin.A312He
