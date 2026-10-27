module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjChoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem nonempty_adjData_of_root {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {hV : IsElemAbelian 2 c.V} {d : S23_9_A0Data D Ch c} {b : G} {hb : b ∈ c.B0}
    {r m : ℕ} (hm2 : 2 ≤ m) (hrm : r ∣ 2 ^ m - 1)
    (hparity : (∃ k : ℕ, c.n = 2 ^ k) → ¬ S23_9_SU44 D Ch c hV → 4 ≤ m ∧ Even m)
    {Xstar : Subgroup ↥(c.H hV)}
    (ρ : Ctx23L.S23_9_AdjRootData D Ch c hV Xstar b r m)
    (hnotker : ¬ barImage D.M ρ.X ≤ d.rep.ker) :
    Nonempty (S23_9_AdjData D Ch c hV d b hb r) :=
  ⟨{ m := m
     hm2 := hm2
     hrm := hrm
     hparity := hparity
     X := ρ.X
     hXK := ρ.hXK
     hXperf := ρ.hXperf
     hXsl := ρ.hXsl
     hbX := ρ.hbX
     dRoot := ρ.dRoot
     hdX := ρ.hdX
     hdorder := ρ.hdorder
     hdb := ρ.hdb
     hinner := ρ.hinner
     hnotker := hnotker }⟩

theorem s23_9_Adj_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h52 : S23_5_2 D Ch)
    (hPS : S23_9_PointStab D Ch) (h209 : S20_9 D) (hK : KOrdNatural)
    (hA : KTab23a) (hS : KSchurL2) :
    S23_9_Adj D Ch := by
  intro hKAdj h1930 c hn hV d hnot b hb r hr hr2 hborder hbZ hcase
  obtain ⟨m, hm, X₁, X₂, hX₁, hX₂, hgen, hXprop⟩ :=
    Ctx23L.exists_KAdj_data_of c h2 h3 h4 h52 hPS h209 hK hA h1930 hn hV d
      hnot hb hr hr2 hborder hbZ hcase hKAdj
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) := by
    rcases Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c with ⟨_, h⟩
    exact h
  have hKne := c.Hinf_inf_L_ne_bot_of_not_barImage_le_rep_ker hV d hnot
  have hcn : c.n = CFSG.Open.pRank 2 D.Z := c.n_eq_pRank_of_pointStab h52 hPS h1930 hKne
  obtain ⟨hm2, hrm, hparity⟩ := Ctx23L.adjData_exponent_fields c hV hn hcn hm hcase
  obtain ⟨hXsl₁, ht₁, u₁, hu₁, huord₁, hact₁⟩ := hXprop X₁ (Or.inl rfl)
  obtain ⟨ρ₁⟩ := Ctx23L.exists_rootLift_data c hV hK hnat hS hb hr hr2 hborder ht₁ hX₁
    hm2 hXsl₁ hu₁ huord₁ hact₁
  obtain ⟨hXsl₂, ht₂, u₂, hu₂, huord₂, hact₂⟩ := hXprop X₂ (Or.inr rfl)
  obtain ⟨ρ₂⟩ := Ctx23L.exists_rootLift_data c hV hK hnat hS hb hr hr2 hborder ht₂ hX₂
    hm2 hXsl₂ hu₂ huord₂ hact₂
  have hchoice := Ctx23L.not_barImage_le_ker_or_of_generate c hV d hnot hK hnat
    hX₁ hX₂ hgen (Y₁ := ρ₁.X) (Y₂ := ρ₂.X) ρ₁.hXK ρ₂.hXK ρ₁.hmap.ge ρ₂.hmap.ge
  rcases hchoice with hnot₁ | hnot₂
  · exact nonempty_adjData_of_root (d := d) (b := b) (hb := hb) (r := r)
      hm2 hrm hparity ρ₁ hnot₁
  · exact nonempty_adjData_of_root (d := d) (b := b) (hb := hb) (r := r)
      hm2 hrm hparity ρ₂ hnot₂

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
