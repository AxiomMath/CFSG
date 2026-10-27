module

public import CFSG.Quasithin.Background.C126NatClassG
public import CFSG.Quasithin.Background.C126NatDBlock
public import CFSG.Quasithin.Background.C126MinPar
public import CFSG.Quasithin.Background.C126RadFree
public import CFSG.Quasithin.Background.C1PackC126B

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2

variable {G : Type} [Group G] [Finite G]

theorem natStmt_of_e23 (hE23 : E2.E23Statement) (hRF : RadFreeStmt)
    {C₁ C₂ : Subgroup G → Subgroup G} : NatStmt C₁ C₂ := by
  intro hC H T M V hV hmin hSQ hF hred hVZ hJ hNat
  subst hVZ
  have hT := hmin.isSylow
  have hT0 : T ≠ ⊥ := C1Pack.minParabolic_ne_bot hmin
  obtain ⟨-, I, hFam, hn2⟩ := id hNat
  have hSyl : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) := by
    obtain ⟨-, -, -, -, -, -, -, -, h2, -⟩ := hFam
    exact (h2 fun L hL => (hn2 L hL).imp fun n h => h.2).2.2.1
  obtain ⟨P, hSP, hPK, hPM, hPT, hMinP, hFP, hJP⟩ :=
    C126.exists_minimal_parabolic_over_baum hmin hF hJ hSyl
  have hPH : P ≤ H := hPT ▸ le_sup_left
  have hSQP : IsSQTKTC P := C1GN.IsSQTKTC.mono hPH hSQ
  have hCls : InClassG P (baum T) :=
    inClassG_of_e23 hE23 hMinP hFP hSQP (C1GN.baum_baum T) hJP
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT.2.1 hT0
  rcases hC.dichotomy hT.2.1 hT0 hCls with h1 | h2 | h3
  · left
    have hC1T : C₁ T ≤ centerOf T := h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)
    have hHle : H ≤ Subgroup.centralizer (C₁ T : Set G) := by
      rw [← hPT]
      refine sup_le (fun p hp => ?_) (fun t ht => ?_)
      · exact Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (h1 hc).2 p hp).symm
      · exact Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (hC1T hc).2 t ht).symm
    refine le_inf (fun c hc => hT.1 (hC1T hc).1) (fun c hc => ?_)
    exact Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 (hHle hh) c hc).symm
  · right
    left
    have hTbaum : T ≤ Subgroup.normalizer (baum T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
    have hTN : T ≤ Subgroup.normalizer (C₂ T : Set G) :=
      hTbaum.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
    rw [← hPT]
    exact sup_le h2 hTN
  · right
    right
    exact oneBlock_of_block hmin hF hred hJ hNat
      (hRF G H T M (VZ T H) hV hmin hSQ hF hred rfl hJ (Or.inl hNat)) hSP hPK hPM hPT hMinP h3

end CFSG.Quasithin.C126.Nat
