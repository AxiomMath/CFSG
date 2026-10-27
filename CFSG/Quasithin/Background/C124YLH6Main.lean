module

public import CFSG.Quasithin.Background.C124YLCore
public import CFSG.Quasithin.Background.C124YLH6Elim3
public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124YLH6Final

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

theorem spec4bHat6_holds : Spec4bHat6 := by
  intro G _ _ X T V L R m hV E hc
  obtain ⟨hm, htri, hhat⟩ := hc
  obtain ⟨K, iK, fK, Γ₀, hK, hdet, hHat, hcen, π, hπ⟩ := htri
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp E.comp).trans hXN
  have hLX : autI hV L ≤ autI hV X := autI_mono hV (le_of_mem_cComp E.comp)
  have hnormX : ∀ x ∈ autI hV X, x ∈ Subgroup.normalizer
      (autI hV L : Set (MulAut (IntMod V hV))) :=
    fun x hx => L2.autI_le_normalizer_of_le_normalizer hV E.normal hx
  have hstab := fun x (hx : x ∈ autI hV X) => YL.sec_stable (hnormX x hx)
  let C : YL.H6.HatCtx K Γ₀ (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) :=
    { hK := hK, hdet := hdet, hat := hHat, hcen := hcen, π := π, real := hπ }
  have hRs : autI hV R ≤ autI hV L := by
    rcases E.mcase with h | h | ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · omega
    · have h1 := autI_mono hV h
      rw [autI_sup hV hLN (inf_le_left.trans hXN),
        autI_eq_bot_of_le_centralizer hV inf_le_right, sup_bot_eq] at h1
      exact h1
    · exfalso
      obtain ⟨K1, hK1⟩ := (offenderImages_nonempty_iff_not_le hV).2 E.hJ
      obtain ⟨hw1, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
        (fixV (autI hV L) ⊓ commV (autI hV L)) hK1
      have hcardR : Nat.card ↥(autI hV R) = 2 := h
      obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ K1, r ≠ 1 := by
        obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hw1.1
        exact ⟨r, r.2, fun h => hr1 (Subtype.ext h)⟩
      have hr2 : r * r = 1 := by
        rw [← pow_two]
        exact hw1.2.1.2 r hrR
      have hrord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
      have hcardz : Nat.card (Subgroup.zpowers r) = 2 := by rw [Nat.card_zpowers, hrord]
      have hK1card : Nat.card K1 = 2 := by
        have h1 := Subgroup.card_le_of_le hBR
        have h2 : Nat.card K1 ≠ 1 := by
          intro h3
          exact hw1.1 (Subgroup.card_eq_one.1 h3)
        have h3 : 0 < Nat.card K1 := Nat.card_pos
        omega
      have hzK : Subgroup.zpowers r = K1 :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hrR) (by rw [hcardz, hK1card])
      have hoff : Nat.card (commV (autI hV L)) ≤
          2 * Nat.card (YL.liftFix (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L))
            (Subgroup.zpowers r)) := by
        rw [hzK]
        have := hw1.2.2
        rwa [hK1card] at this
      exact C.no_outer_offender hLX hnormX E.fstarX (fun x hx => (hstab x hx).1)
        (fun x hx => (hstab x hx).2) (autI_mono hV hRX (hBR hrR)) hr1 hr2 hoff
  obtain ⟨K1, hK1⟩ := (offenderImages_nonempty_iff_not_le hV).2 E.hJ
  obtain ⟨hw1, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
    (fixV (autI hV L) ⊓ commV (autI hV L)) hK1
  obtain ⟨P1, Y1, hP1, -, hunique, hpkg⟩ := C.exists_package (hBR.trans hRs) hw1
  refine YL.starL2_of_package E (Pk := autI hV L) (P0 := P1) (K0 := K1) (Y0 := Y1) hRs ?_ hP1
    hunique ?_ hpkg
  · intro l hl x hx
    exact (autI hV L).mul_mem ((autI hV L).mul_mem ((autI hV L).inv_mem hl) hx) hl
  · intro B hB
    obtain ⟨-, hBR'⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) hB
    exact hBR'.trans hRs

end CFSG.Quasithin.C124
