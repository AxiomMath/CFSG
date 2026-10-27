module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSix
public import CFSG.Quasithin.Vol2.Ch8Sec2D5Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SAssemble

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

@[expose] def Step828SixB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → Row711M24Code T L I →
        Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
          DihedralGroup 5) →
        ¬ T ≤ Subgroup.normalizer (oTwoUpper (ch82I (fsuV T I) h) : Set G)

theorem step828Three_of (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB1 : MB1_828) (hMB2 : MB2_828) (hMB3 : MB3_828)
    (hSyl : Sylow822VB_828) (hSixB : Step828SixB) : Step828Three := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC
  have c := s828_ctx hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl hyp h731
    h821 hrow hH hh hC
  have hBt := step828Three_Bt_of hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB1 hSyl
    G T L I hyp h731 h821 hc hrow H h k hH hh hC
  refine ⟨s828_clause3 hMB2 hcard hrow c, hBt.1, hBt.2.1, hBt.2.2,
    s828_five_dprime hMB2 hcard hrow c, fun hr => ?_⟩
  have hD5 := s828_six_a hMB2 hLU hcard hyp hrow hr c
  exact ⟨hD5, hSixB G T L I hyp h731 h821 hc hrow H h k hH hh hC hr hD5⟩

end CFSG.Quasithin.H13
