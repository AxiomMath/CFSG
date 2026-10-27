module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import Certificates.Certificate3951
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem e8InvCommAt_of
    {G : Type} [Group G] [Finite G] {Y E : Subgroup G} {b : G}
    (hEm : IsEm 8 Y) (hEY : E ≤ Y) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 8 ≤ Nat.card E) (hbE : b ∈ E) (hb1 : b ≠ 1)
    (h120 : (normalizerLines Y E b).ncard = 120) :
    ∀ s ∈ Y, orderOf s = 2 → ∃ y ∈ Y, Commute s (y * b * y⁻¹) := by
  intro s hs hs2
  obtain ⟨ι, hι, hιrange⟩ := exists_injective_hom_range_eq_of_isEm_eight hEm
  have hK : Nat.card (GaloisField 2 1) = 2 := natCard_galoisField_two_one
  have h120' : (normalizerLines ι.range E b).ncard = 120 := by
    rw [hιrange]; exact h120
  have hEY' : E ≤ ι.range := by rwa [hιrange]
  obtain ⟨ι', hι'inj, hι'range, hι'θ⟩ :=
    exists_hom_range_eq_apply_rootThree_eq hK ι hι hEY' hE hcard hbE hb1 h120'
  have hsY : s ∈ ι'.range := by rw [hι'range, hιrange]; exact hs
  obtain ⟨m, rfl⟩ := hsY
  have hm2 : m ^ 2 = 1 := by
    apply hι'inj
    rw [map_pow, map_one]
    simpa [hs2] using pow_orderOf_eq_one (ι' m)
  obtain ⟨g, hg⟩ := exists_commute_conj_rootThree_highRoot (K := GaloisField 2 1) hm2
  refine ⟨ι' g, ?_, ?_⟩
  · rw [← hιrange, ← hι'range]; exact ⟨g, rfl⟩
  · simpa only [map_mul, map_inv, hι'θ] using Commute.map hg ι'

theorem e8InvCommAt_E7 :
    E8InvCommAt Row.E7 := by
  intro G _ _ b₀ K E B Y h s hs hs2
  have hEY : E ≤ Y := h.torus_le
  have hEm : IsEm 8 Y := h.isEm
  have hE : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]; exact le_rfl
  have hbE : b₀ ∈ E := h.std.2.1.2.2.1
  have hb1 : b₀ ≠ 1 := by
    have hord : orderOf b₀ = 3 := h.std.2.1.1.1
    intro hb; rw [hb, orderOf_one] at hord; omega
  have hA : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E) :=
    e8AutAt_E7 (G := G) (b₀ := b₀) (K := K) (E := E) (B := B) (Y := Y) h
  have h120 : (normalizerLines Y E b₀).ncard = 120 :=
    ncard_normalizerLines_eq_120_E7 h hA
  simpa only [rowRootElt] using e8InvCommAt_of hEm hEY hE hcard hbE hb1 h120 s hs hs2

theorem e8InvCommAt_twD7 :
    E8InvCommAt Row.twD7 := by
  intro G _ _ b₀ K E B Y h s hs hs2
  have hEY : E ≤ Y := h.torus_le
  have hEm : IsEm 8 Y := h.isEm
  have hE : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hcard : 3 ^ 8 ≤ Nat.card E := by
    rw [h.std.2.1.2.2.2.1]; exact le_rfl
  have hbE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := h.std.2.1.2.2.1
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hb1 : b₀ * B.b 1 ≠ 1 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    intro h1
    have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
      rw [hvec, h1]
    have he0 := B.indep _ h1'
    have h0 := congrFun he0 0
    simp only [Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
      Pi.zero_apply, add_zero] at h0
    exact one_ne_zero h0
  have hA : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E) :=
    e8AutAt_twD7 (G := G) (b₀ := b₀) (K := K) (E := E) (B := B) (Y := Y) h
  have h120 : (normalizerLines Y E (b₀ * B.b 1)).ncard = 120 :=
    ncard_normalizerLines_eq_120_twD7 h hA
  simpa only [rowRootElt] using e8InvCommAt_of hEm hEY hE hcard hbE hb1 h120 s hs hs2

end CFSG.StandardType.FrameRoute.FS81

end
