module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.UniqueC0
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row13
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row17
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row20
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6Inv
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7IsHatE9
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Survivors9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S153D

namespace Stellmacher.L3YC

theorem l3YCCommNotCentral_of
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) : SzC4.L3YCCommNotCentral := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap h4 _
  have hqtfe := c.ctx.hyp.hyp.qtfe
  have hs : IsSimpleGroup G := hqtfe.simple
  have hnab := hqtfe.nonabelian
  have hQ := hqtfe.qtke
  obtain ⟨Vc, Vn, c₀, u₀, hlabel, hc₀, -, hc₀Vc, hu₀Vn, hc₀1, hu₀1, hc₀2, -, hSc, hsw, -, hZ⟩ :=
    Stellmacher.PU.L3YC.pu_f5_f6 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  obtain ⟨c₁, hc1, hc2, hcQ, hLc, hSyl, L₁, hL₁, hLL₁, hbad, h8, h9⟩ :=
    CD.L3YC.bad_case_survivors_no89 h11 h113 hQ hs hnab h37 h38 h39 h312 c hq c12 hV hYY hSL ht'T
      ht'S hswap h4
  have hc₁S : ∀ s ∈ Sgp153 T V₁, s * c₁ = c₁ * s := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.mp (hSyl.1 hs')
  have hcc : c₁ = c₀ := eq_c0_of_mem_c134CQ h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
    hlabel hc₀ hc₀Vc hc₀1 hu₀Vn hu₀1 hZ hcQ hc1 hc₁S
  subst hcc
  have hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s := fun s hs' => (hSc s hs').2
  have hnorm : (L₁.subgroupOf (Subgroup.centralizer ({c₁} : Set G))).Normal :=
    lemma_1_2_4_normal hQ hs hnab h37 h38 (CD.L3YC.pCoreOf_centralizer_ne_bot hc1 hc2) hSyl
      (CD.L3YC.lFamily_of_ctx c hSL) hLL₁ hL₁ hSL
  rcases hbad with hsurv | h21
  · rcases hsurv with ⟨h45, P, hpar, hBP⟩ | h6 | h8' | h9' | h13 | h14 | h17 | h18 | h19 | h20
    · rcases h45 with h42 | h52
      · exact row4a_false h11 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hcQ hc₀Vc
          hc1 hc2 hu₀Vn hu₀1 hu₀S hsw hLL₁ hnorm h42 hpar hBP
      · exact row4b_false h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hcQ hc1 hSyl h52 hpar
          hBP
    · exact row6_false_of h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hcQ hc₀Vc hc1
        hc2 hu₀Vn hu₀1 hu₀S hsw hSyl hQ.2.2 hL₁ hLL₁ hnorm h6
        EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6Inv.row6b_false
        fun _ _ _ hX E hE =>
          EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7IsHatE9.isHat_seven_E9_meets_centre
            hX E hE
    · exact h8 h8'
    · exact h9 h9'
    · exact Row13.row13_false h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hcQ hc₀Vc
        hc1 hu₀Vn hu₀1 hu₀S hsw hc2 rfl hSyl hLL₁ hnorm hQ.2.2 h13
    · rcases h14 with ⟨h64 | hex, hM24⟩
      · exact row14_false h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hcQ hc1 hSyl hLL₁
          hnorm ⟨h64, hM24⟩
      · exact Stellmacher.PU.L3YC.classII_row_false_of_ctx c hq hSL h4 hLc hex
    · exact row17_false h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hcQ hc1 hSyl hLL₁ hnorm
        h17
    · exact row18_false h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hcQ hc₀Vc hc1
        hu₀Vn hu₀1 hu₀S hsw hc2 rfl hSyl hLL₁ hnorm hQ.2.2 h18
    · exact Stellmacher.PU.L3YC.classII_row_false_of_ctx c hq hSL h4 hLc h19.1
    · exact row20_false c hq hSL h4 hcQ rfl hSyl hLL₁ hnorm h20
  · exact row21_false_of_a36 h36 h113 h37 h38 hQ hs hnab c hq c12 hV hYY hSL ht'T ht'S hswap h4
      hlabel hcQ hc₀Vc hc1 hu₀Vn hu₀1 hu₀S hsw hc2 rfl hSyl hL₁ hLL₁ hnorm h21

end Stellmacher.L3YC

end CFSG.Quasithin
