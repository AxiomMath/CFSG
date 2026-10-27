module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBAlt
public import CFSG.Quasithin.Vol2.Ch3xC58NSInputs

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

theorem minParabolicBlockSubnormal_of_c127
    (h127 : ∀ (G : Type) [Group G] [Finite G], L238.C127StatementCat (G := G)) :
    MinParabolicBlockSubnormal := by
  intro G _ _ H T N R P L hmin hH hSQ _ hRT hTR hRsyl hPX hRP hPN hminP hNC hchi hLJ hPL
  have hRH : R ≤ H := hRT.trans hmin.isSylow.1
  have hXH : oTwoUpper H ⊔ R ≤ H := sup_le (oTwoUpper_le H) hRH
  have hTX := le_normalizer_sup hmin.isSylow.1 hTR
  have hXsub : IsSubnormal (oTwoUpper H ⊔ R) H := isSubnormal_sup_oTwoUpper hRH
  have hXchar : CharTwo (oTwoUpper H ⊔ R) := L246C127.Setting.charTwo_of_isSubnormal hXsub hH
  have hXSQ : IsSQTKCat ↥(oTwoUpper H ⊔ R) := isSQTKCat_of_isSQTKTC hXH hSQ
  have hPU : P ∈ uFamHat (oTwoUpper H ⊔ R) R := mem_uFamHat hPX hRP hminP
  have hcgs : ¬ P ≤ cgsIn (oTwoUpper H ⊔ R) R := fun h =>
    hPN (h.trans (cgsIn_le_of_noCharNormal hmin hTR hNC hXH))
  obtain ⟨L', hL', hKL, -, hUV, hcase⟩ :=
    h127 G (oTwoUpper H ⊔ R) R P L hXchar hRsyl hXSQ hPU hchi hcgs hLJ hPL
  have hKeq : L = L' := by
    rcases hcase with h | ⟨m, n, hm, hn, hm3, hn3, hLm, hKn⟩
    · exact h
    · exact eq_of_alternating hmin hXsub hTX ⟨hXchar, hRsyl, hPX, hRP, hchi.1⟩ hXSQ hPN hPL hRT
        hL' hKL hUV hm hn hm3 hn3 hLm hKn
  subst hKeq
  have hLH : L ≤ H := hKL.trans (hL'.2.1.trans hXH)
  exact ⟨hchi.1.1, hLH, (isSubnormal_iff_subgroupOf hLH).1
    (A4.subnormal_trans (IsBlock2.isSubnormal hL') hXsub)⟩

end CFSG.Quasithin.C58NS.MPB
