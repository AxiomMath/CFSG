module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Meet
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Act
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_12L2_of_r847Four {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (h847 : R847Four D) (hsig : D.sig.Nonempty) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : IsL2Odd (Bar2 L) p) :
    ⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hBN : c.B ≤ normalizer (L : Set G) := h5 hH c L hL
  have hBS := uc22s2112_le_normalizer_inf c hBN (uc22s2112_inf_eq_bot h847 hsig hH c hL hp hp2 hLp)
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (uc22p22r_fo_sylow_inf D.sylowM hL.1)
  have hOK : CFSG.Quasithin.opResidual 3 c.B ≤
      (UC6S846.rhoL L).ker.map (normalizer (L : Set G)).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, hx3⟩
    exact ⟨⟨x, hBN hx⟩, MonoidHom.mem_ker.2 (uc22s2112_rhoL_eq_one hSyl hp hp2 hLp hBN hBS
      c.hB.2.1 (uc22s13xe_odd_card_B c) hx hx3), rfl⟩
  rw [Subgroup.commutator_le]
  intro x hx l hl
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 (hOK hx)
  have h := (UC6S846.rhoL_fix_iff L n ⟨l, hl⟩).1 (by rw [MonoidHom.mem_ker.1 hn]; rfl)
  simpa [commutatorElement_def] using h

end CFSG.LocalAnalysis.UniquenessCase.UC22
