module

public import CFSG.Quasithin.MS93.S59Pt
public import CFSG.Quasithin.MS93.S59C2

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S59

@[expose] def Open : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → 2 ≤ k →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        (S5.bSub h.le L (baseA _)).relIndex
            (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k →
        ¬ hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          stabCenter _ (baseA (puAmalgam h.le)) →
        (Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
          ∀ t ∈ tZero h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
            (∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
              ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
            ∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
              ⁅u, t⁆ ∈ stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ∧
          ((∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
              S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≤ MSP.qLine l) →
            (∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
              S5.jOff h.le L (2 ^ k) δ (baseB _) = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) →
            ∃ h₁ ∈ hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
              stab _ (baseA (puAmalgam h.le)) ⊓
                  Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) ≤
                Subgroup.centralizer (hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) :
                  Set (puAmalgam h.le).Universal))

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_crit_gamma (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    ∃ ξ, IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
      (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le) := by
  obtain ⟨m, hm⟩ := ms21_v _ h.hyp20
  obtain ⟨ξ, hξc, hξα⟩ := S5B.exists_isCritical_iter h
    (fun _ _ hc' => vv_not_le_gp h58 h hmin hb hd hc') hc (m - 1) (by omega)
  rw [show critDist (puAmalgam h.le) - 2 * (m - 1) = 2 by omega] at hξc
  exact ⟨ξ, hξc, by omega⟩

theorem s59_at (h32 : S32) (hX2 : S33.S33X52) (h53 : S53) (h55 : S55) (h56 : S56)
    (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ' : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hcase1 : 2 ≤ k → ∀ ξ : Vtx (puAmalgam h.le),
      IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2) →
      (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le) →
      (S5.bSub h.le L (baseA _)).relIndex
          (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k →
      ¬ hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
        stabCenter _ (baseA (puAmalgam h.le)) → False) :
    2 ^ k < (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) := by
  by_contra hP
  rw [not_lt] at hP
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hdd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨ξ, hξ, hξα⟩ := exists_crit_gamma h58 h hmin hb' hd hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ'] at this
  have hγα : geo _ (baseA (puAmalgam h.le)) α' 2 ≠ baseA _ := by
    intro he
    have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _)
        (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := dist_geo _ (by omega)
    rw [he, SimpleGraph.dist_self] at hd2
    exact absurd hd2 (by norm_num)
  by_cases hZc : hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le))
  · exact case2_false h32 hX2 h55 h56 h58 h hmin hb hd hc hαβ' hξ hξα hP hZc
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1 : k = 1 := by
        have := hd.1
        omega
      obtain ⟨ha, hbb⟩ := case1_ab_of_two h hb' hd hk1 hβγ hγα hξ hξα hP hZc
      exact case1_false h32 h53 h55 h56 h hmin hb hd hc hαβ' hξ hξα hP hZc ha
        fun t ht htH => bss_of_b h hbb ht htH
    · exact hcase1 hk ξ hξ hξα hP hZc

end S59

namespace S5B

theorem s59_of (h32 : S32) (hX2 : S33.S33X52) (h53 : S53) (h54 : S54) (h55 : S55) (h56 : S56)
    (h58 : S5B.S58) (hopen : S59.Open) : S5B.S59 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hαβ'
  refine S59.s59_at h32 hX2 h53 h55 h56 h58 h hmin hb hd hc hαβ' fun hk ξ hξ hξα hP hZc => ?_
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hdd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ'] at this
  have hγα : geo _ (baseA (puAmalgam h.le)) α' 2 ≠ baseA _ := by
    intro he
    have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _)
        (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := dist_geo _ (by omega)
    rw [he, SimpleGraph.dist_self] at hd2
    exact absurd hd2 (by norm_num)
  obtain ⟨hbo, ha⟩ := hopen G M T L h hmin hb k F _ _ a hd hk α' hc hαβ' hP hZc
  have hbb : ∀ t ∈ S59.tZero h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
      (∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
        ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
      ∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
        ⁅u, t⁆ ∈ stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    by_cases hnat : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥
    · exact fun t ht htH => S59.bss_of_natural h hb' hd hnat hβγ hγα hξ hξα hP hZc ht htH
    · exact hbo hnat
  by_cases h5 : ∃ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ ∧
      (S5.jOff h.le L (2 ^ k) δ (baseB _) ≠ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ∨
        ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
          Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) →
          ¬ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
  · obtain ⟨δ, hδ, hδc⟩ := h5
    obtain ⟨g, hg, x, -, hcon⟩ := h55 G M T L h hmin hb' k F _ _ a hd α' hc hαβ' δ hδ hδc
    exact S59.case1_false_of_gen h32 h55 h56 h hmin hb hd hc hαβ' hξ hξα hP hbb hg hcon.1.1
  · have hJ : ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        S5.jOff h.le L (2 ^ k) δ (baseB _) = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) :=
      fun δ hδ => by
        by_contra hne
        exact h5 ⟨δ, hδ, Or.inl hne⟩
    have ha' : ∃ h₁ ∈ S59.hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
        stab _ (baseA (puAmalgam h.le)) ⊓
            Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) ≤
          Subgroup.centralizer (S59.hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) :
            Set (puAmalgam h.le).Universal) := by
      by_cases hlc : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≤ MSP.qLine l
      · exact ha hlc hJ
      · exact S59.exists_centralizer_le_of_fixSp h53 h hmin hb' hd hβγ hγα hξ hξα hP
          (S59.finrank_fixSp_le_one h54 h hmin hb' hd fun l hl hle => hlc ⟨l, hl, hle⟩) hZc
    exact S59.case1_false h32 h53 h55 h56 h hmin hb hd hc hαβ' hξ hξα hP hZc ha' hbb

end S5B

end CFSG.Quasithin.MS93
