module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelAut
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem e8AutAt_common {G : Type} [Group G] [Finite G]
    (r : Row) (hm : r.m = 8) {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)}
    {Y : Subgroup G} (h : RootSetting r b₀ K E B Y)
    (hrec : Nat.card (ggAutomizer ⊤ B.span) = 696729600) :
    Nat.card (ggAutomizer Y E) = Nat.card (ggAutomizer ⊤ E) := by
  have hmax : IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E := h.std.2.1.2.1
  have hE : IsElemAbelian 3 E := hmax.2.1
  have hEY : E ≤ Y := h.torus_le
  have hcardE : Nat.card E = 3 ^ 8 := by rw [h.std.2.1.2.2.2.1, hm]
  obtain ⟨ι, hιinj, hιrange⟩ :=
    exists_injective_hom_range_eq_of_isEm_eight (hm ▸ h.isEm)
  have hlow : 696729600 ≤ Nat.card (ggAutomizer Y E) := by
    have h := le_natCard_ggAutomizer_range_of_card_E8 (K := GaloisField 2 1)
      natCard_galoisField_two_one ι hιinj (by rw [hιrange]; exact hEY) hE hcardE.ge
    rwa [hιrange] at h
  have hle : Nat.card (ggAutomizer Y E) ≤ Nat.card (ggAutomizer ⊤ E) :=
    Subgroup.card_le_of_le (ggAutomizer_mono E le_top)
  have htop : Nat.card (ggAutomizer ⊤ E) = 696729600 := by
    rw [← h.adapted.1, hrec]
  omega

theorem e8AutAt_E7 :
    E8AutAt Row.E7 := by
  intro G _ _ b₀ K E B Y h
  exact e8AutAt_common Row.E7 rfl h h.recOut.1

theorem e8AutAt_twD7 :
    E8AutAt Row.twD7 := by
  intro G _ _ b₀ K E B Y h
  exact e8AutAt_common Row.twD7 rfl h h.recOut.1

end CFSG.StandardType.FrameRoute.FS81

end
