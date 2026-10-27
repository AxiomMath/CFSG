module

public import CFSG.Quasithin.MS93.S510Loc
public import CFSG.Quasithin.MS93.S510Path

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

structure IsChain (h : PUHyp M T L) (q : ℕ) (a : ↥M →* ↥(StatedSp 2 F))
    (s t : Vtx (puAmalgam h.le)) (N : ℕ) : Prop where
  dist_eq : (puAmalgam h.le).treeGraph.dist s t = critDist (puAmalgam h.le) + 2 * N
  crit : ∀ j ≤ N, IsCritical _ (geo _ s t (2 * j)) (geo _ s t (2 * j + critDist (puAmalgam h.le)))
  straight : ∀ j, 1 ≤ j → j ≤ N →
    ∃ c ∈ stab _ (geo _ s t (2 * j)), c • geo _ s t (2 * j + 2) = geo _ s t (2 * j - 2)
  lam : ∀ j, 1 ≤ j → j ≤ N →
    ∃ g : (puAmalgam h.le).Universal, geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧
      geo _ s t (2 * j + 1) = g • baseB _ ∧
      g⁻¹ • geo _ s t (2 * j - 2) ∈ S5.lam h q a
        (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) (g⁻¹ • geo _ s t (2 * j + 2))

theorem exists_isChain (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56 : S56) (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') (N : ℕ) :
    ∃ s, geo _ s α' (2 * N) = α ∧ IsChain h (2 ^ k) a s α' N := by
  obtain ⟨s, hsd, hsα, hcrit, hrest⟩ :=
    exists_chain h32 hX2 h52 h54 h55 h56 h59 h hmin hb hd hc N
  exact ⟨s, hsα, hsd, hcrit, fun j h1 h2 => (hrest j h1 h2).1, fun j h1 h2 => (hrest j h1 h2).2⟩

theorem eq_geo_one_of_adj_adj {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {u ν w : Vtx X} (huν : X.treeGraph.Adj u ν)
    (hνw : X.treeGraph.Adj ν w) (huw : X.treeGraph.dist u w = 2) : ν = geo X u w 1 := by
  apply eq_geo_one X huν
  rw [dist_eq_one_of_adj X hνw, huw]

namespace IsChain

variable {h : PUHyp M T L} {q : ℕ} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem geo_eq (hch : IsChain h q a s t N) {i j m : ℕ} (hij : i ≤ j)
    (hj : j ≤ critDist (puAmalgam h.le) + 2 * N) (hm : m ≤ j - i) :
    geo _ (geo _ s t i) (geo _ s t j) m = geo _ s t (i + m) := by
  have hd := hch.dist_eq
  symm
  apply eq_geo_of_dist _ (by rw [dist_geo_geo _ (by omega) (by omega)]; omega)
  rw [dist_geo_geo _ (by omega) (by omega), dist_geo_geo _ (by omega) (by omega),
    dist_geo_geo _ (by omega) (by omega)]
  omega

theorem geo_eq' (hch : IsChain h q a s t N) {i j m : ℕ} (hij : i ≤ j)
    (hj : j ≤ critDist (puAmalgam h.le) + 2 * N) (hm : m ≤ j - i) :
    geo _ (geo _ s t j) (geo _ s t i) m = geo _ s t (j - m) := by
  have hd := hch.dist_eq
  have hdij : (puAmalgam h.le).treeGraph.dist (geo _ s t i) (geo _ s t j) = j - i :=
    dist_geo_geo _ hij (by omega)
  have := geo_symm _ (u := geo _ s t i) (w := geo _ s t j) (i := j - i - m) (by omega)
  rw [hdij, show j - i - (j - i - m) = m by omega, hch.geo_eq hij hj (by omega),
    show i + (j - i - m) = j - m by omega] at this
  exact this

theorem dist_P (hch : IsChain h q a s t N) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ critDist (puAmalgam h.le) + 2 * N) :
    (puAmalgam h.le).treeGraph.dist (geo _ s t i) (geo _ s t j) = j - i := by
  have hd := hch.dist_eq
  exact dist_geo_geo _ hij (by omega)

theorem adj_P (hch : IsChain h q a s t N) {i : ℕ}
    (hi : i < critDist (puAmalgam h.le) + 2 * N) :
    (puAmalgam h.le).treeGraph.Adj (geo _ s t i) (geo _ s t (i + 1)) := by
  have hd := hch.dist_eq
  exact adj_geo _ (by omega)

theorem isMVtx_P (hch : IsChain h q a s t N) {j : ℕ}
    (hj : 2 * j ≤ critDist (puAmalgam h.le) + 2 * N) : IsMVtx _ (geo _ s t (2 * j)) := by
  have hd := hch.dist_eq
  have hs : IsMVtx _ s := by
    have := (hch.crit 0 (Nat.zero_le _)).1
    rwa [Nat.mul_zero, geo_zero] at this
  rw [isMVtx_geo _ (by omega)]
  exact iff_of_true hs ⟨j, by ring⟩

theorem not_isMVtx_P (hch : IsChain h q a s t N) {j : ℕ}
    (hj : 2 * j + 1 ≤ critDist (puAmalgam h.le) + 2 * N) :
    ¬ IsMVtx _ (geo _ s t (2 * j + 1)) := by
  have hd := hch.dist_eq
  have hs : IsMVtx _ s := by
    have := (hch.crit 0 (Nat.zero_le _)).1
    rwa [Nat.mul_zero, geo_zero] at this
  rw [isMVtx_geo _ (by omega)]
  intro hiff
  have := hiff.1 hs
  rw [Nat.even_add_one] at this
  exact this ⟨j, by ring⟩

theorem straight_odd (hch : IsChain h q a s t N) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    {c : (puAmalgam h.le).Universal} (hc : c ∈ stab _ (geo _ s t (2 * j)))
    (hc2 : c • geo _ s t (2 * j + 2) = geo _ s t (2 * j - 2)) :
    c • geo _ s t (2 * j + 1) = geo _ s t (2 * j - 1) := by
  have hd := hch.dist_eq
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ h.hyp20 h.critDist_pos
  have e1 : geo _ s t (2 * j + 1) = geo _ (geo _ s t (2 * j)) (geo _ s t (2 * j + 2)) 1 :=
    (hch.geo_eq (by omega) (by omega) (by omega)).symm
  have e2 : geo _ s t (2 * j - 1) = geo _ (geo _ s t (2 * j)) (geo _ s t (2 * j - 2)) 1 := by
    rw [hch.geo_eq' (by omega) (by omega) (by omega)]
  rw [e1, e2, ← geo_smul, (mem_stab _).1 hc, hc2]

theorem case_prop (hch : IsChain h q a s t N)
    (hcase : S5.jOff h.le L q (geo _ s t (2 * N + 2)) (geo _ s t (2 * N + 1)) ≠
        S5.jOff h.le L q (geo _ s t (2 * N)) (geo _ s t (2 * N + 1)) ∨ ¬ LineCase h q a) :
    ∀ j ≤ N, S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨ ¬ LineCase h q a := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  intro j hj
  induction' hk : N - j with m ih generalizing j
  · obtain rfl : j = N := by omega
    exact hcase
  · have hjN : j < N := by omega
    rcases ih (j + 1) (by omega) (by omega) with hne | hnl
    · left
      obtain ⟨c, hc, hc2⟩ := hch.straight (j + 1) (by omega) (by omega)
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) = 2 * j + 2 by ring,
        show 2 * j + 2 - 2 = 2 * j by omega] at hc2
      rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hc
      have hodd := hch.straight_odd (j := j + 1) (by omega) (by omega)
        (by rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact hc)
        (by rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) = 2 * j + 2 by ring,
          show 2 * j + 2 - 2 = 2 * j by omega]; exact hc2)
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
        at hodd
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
        show 2 * (j + 1) = 2 * j + 2 by ring] at hne
      intro heq
      apply hne
      have e1 := S5B.jOff_smul h.le hLn q c (geo _ s t (2 * j + 4)) (geo _ s t (2 * j + 3))
      have e2 := S5B.jOff_smul h.le hLn q c (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 3))
      rw [hc2, hodd] at e1
      rw [(mem_stab _).1 hc, hodd] at e2
      have := e1.symm.trans (heq.symm.trans e2)
      exact Subgroup.map_injective (MulAut.conj c).injective this
    · exact Or.inr hnl

theorem facts55 (hch : IsChain h q a s t N) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hcase : S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨ ¬ LineCase h q a) :
    Qv _ (geo _ s t (2 * j - 1)) ⊔ ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) =
        stab _ (geo _ s t (2 * j)) ∧
      ZH _ (geo _ s t (2 * j + 1)) ⊓ Subgroup.centralizer
          (S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j - 1)) :
            Set (puAmalgam h.le).Universal) ≤ stabCenter _ (geo _ s t (2 * j)) ∧
      (puTrans h.le L (geo _ s t (2 * j)) ≤
          S5.jOff h.le L q (geo _ s t (2 * j - 2)) (geo _ s t (2 * j - 1)) ⊔
            S5.zHat _ (geo _ s t (2 * j)) (geo _ s t (2 * j + critDist (puAmalgam h.le))) ∨
        (Qv _ (geo _ s t (2 * j)) ≤
            S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ∧
          (Qv _ (geo _ s t (2 * j))).relIndex
              (S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ⊓
                S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j + 1))) ≤ q ^ 2 ∧
          XM _ (geo _ s t (2 * j)) ≠
            S5.uSub h.le L (geo _ s t (2 * j)) ⊔ XM _ (geo _ s t (2 * j)) ⊓
              Subgroup.centralizer
                (puTrans h.le L (geo _ s t (2 * j)) : Set (puAmalgam h.le).Universal))) := by
  have hd := hch.dist_eq
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ h.hyp20 h.critDist_pos
  obtain ⟨g, hγ, hε, hμ⟩ := hch.lam j hj1 hjN
  have hεδ : (puAmalgam h.le).treeGraph.Adj (geo _ s t (2 * j + 1)) (geo _ s t (2 * j + 2)) :=
    hch.adj_P (by omega)
  obtain ⟨ν, hγν, hνμ, -, hgen, hcen, halt⟩ := loc55 h (hch.crit j hjN) hγ hε hεδ hcase hμ
  have hd2 : (puAmalgam h.le).treeGraph.dist (geo _ s t (2 * j)) (geo _ s t (2 * j - 2)) = 2 := by
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hν : ν = geo _ s t (2 * j - 1) := by
    rw [eq_geo_one_of_adj_adj hγν hνμ hd2, hch.geo_eq' (by omega) (by omega) (by omega)]
  subst hν
  exact ⟨hgen, hcen, halt⟩

end IsChain

end S510

end CFSG.Quasithin.MS93
