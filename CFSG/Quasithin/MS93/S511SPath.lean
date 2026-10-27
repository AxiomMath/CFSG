module

public import CFSG.Quasithin.MS93.S511SStep1
public import CFSG.Quasithin.MS93.S511SX1

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem step1_gp (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    (2 ^ k) ^ 2 < (Vv _ γ ⊓ Qv _ (geo _ γ' γ 2) ⊓ Qv _ γ').relIndex (Vv _ γ) := by
  obtain ⟨g, rfl, -, hc', hβ'⟩ := S510.exists_base_crit h hc
  have key := step1_baseA h32 hX2 h52 h53 h54 h56f hZ h59 h hmin hb hd h56all hc' hβ'
  have e1 : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  rw [e1, geo_smul, show Vv _ (g • baseA (puAmalgam h.le)) =
      (Vv _ (baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom from vi_smul _ g _ 2,
    qv_smul, qv_smul, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact key

omit [Fintype F] in
theorem jOff_eq_gp (h : PUHyp M T L)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    S5.jOff h.le L (2 ^ k) (geo _ γ γ' 2) (geo _ γ γ' 1) =
      S5.jOff h.le L (2 ^ k) γ (geo _ γ γ' 1) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, hg1, hc', hβ'⟩ := S510.exists_base_crit h hc
  obtain ⟨l, hl⟩ := h56all _ hc' hβ'
  have e1 : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  have hg2 : geo _ (g • baseA (puAmalgam h.le)) γ' 2 =
      g • geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2 := by
    conv_lhs => rw [e1]
    rw [geo_smul]
  rw [hg1, hg2, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn, hl.1]

theorem commutator_zm_qv_le_zm_gp (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hJ : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hlβ : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l))
    (hlJ : S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
      S5.vPre h.le a (MSP.qLine l))
    {σ ε ρ : Vtx (puAmalgam h.le)} (hσ : IsMVtx _ σ) (hσε : (puAmalgam h.le).treeGraph.Adj σ ε)
    (hερ : (puAmalgam h.le).treeGraph.Adj ε ρ)
    (hJeq : S5.jOff h.le L (2 ^ k) ρ ε = S5.jOff h.le L (2 ^ k) σ ε) :
    ⁅ZM _ ρ, Qv _ σ⁆ ≤ ZM _ σ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hσ hσε
  have e1 : ρ = g • (g⁻¹ • ρ) := (smul_inv_smul g ρ).symm
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le)) (g⁻¹ • ρ) := by
    have := (adj_smul _ g⁻¹ _ _).2 hερ
    rwa [inv_smul_smul] at this
  have hJ₀ : S5.jOff h.le L (2 ^ k) (g⁻¹ • ρ) (baseB _) =
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
    rw [e1, S5B.jOff_smul h.le hLn, S5B.jOff_smul h.le hLn] at hJeq
    exact Subgroup.map_injective (MulAut.conj g).injective hJeq
  have hc56 : S5.Case56 h (2 ^ k) a (g⁻¹ • ρ) l := ⟨hJ₀, hl, hlβ, hlJ⟩
  have key := (Subgroup.commutator_mono le_rfl
    (S5B.qv_le_jOff h Nat.one_le_two_pow hα (adj_baseA_baseB _))).trans
    (commutator_zm_jOff_le_zm_baseA h hb hd hβδ hc56 (hJ _ _ hβδ hc56))
  have e2 : ZM _ (g • (g⁻¹ • ρ)) = (ZM _ (g⁻¹ • ρ)).map (MulAut.conj g).toMonoidHom :=
    zm_smul _ _ _
  have e3 : ZM _ (g • baseA (puAmalgam h.le)) =
      (ZM _ (baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom := zm_smul _ _ _
  have e4 : Qv _ (g • baseA (puAmalgam h.le)) =
      (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom := qv_smul _ _ _
  rw [e1, e2, e3, e4, ← Subgroup.map_commutator, map_conj_le_map_conj_iff]
  exact key

namespace IsChain

variable {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

omit [Fintype F] in
theorem frame (hch : S510.IsChain h (2 ^ k) a s t N) {j : ℕ} (hjN : j ≤ N)
    {g : (puAmalgam h.le).Universal} (hg0 : geo _ s t (2 * j) = g • baseA (puAmalgam h.le))
    (hg1 : geo _ s t (2 * j + 1) = g • baseB _) :
    IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) ∧
      geo _ (baseA (puAmalgam h.le)) (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) 1 =
        baseB _ ∧
      geo _ (baseA (puAmalgam h.le)) (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) 2 =
        g⁻¹ • geo _ s t (2 * j + 2) ∧
      (1 ≤ j → IsCritical _ (g⁻¹ • geo _ s t (2 * j - 2))
          (g⁻¹ • geo _ s t (2 * j - 2 + critDist (puAmalgam h.le))) ∧
        geo _ (g⁻¹ • geo _ s t (2 * j - 2))
          (g⁻¹ • geo _ s t (2 * j - 2 + critDist (puAmalgam h.le))) 2 = baseA _) := by
  have hdd := hch.dist_eq
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ h.hyp20 h.critDist_pos
  have hcr := hch.crit j hjN
  have hg2 := hch.geo_eq (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 2)
    (by omega) (by omega) (by omega)
  have hg1' := hch.geo_eq (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 1)
    (by omega) (by omega) (by omega)
  have e0 : baseA (puAmalgam h.le) = g⁻¹ • geo _ s t (2 * j) := by rw [hg0, inv_smul_smul]
  have hgeo : ∀ i, geo _ (baseA (puAmalgam h.le))
      (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) i =
        g⁻¹ • geo _ (geo _ s t (2 * j)) (geo _ s t (2 * j + critDist (puAmalgam h.le))) i := by
    intro i
    rw [e0, geo_smul]
  refine ⟨?_, ?_, ?_, fun hj1 => ?_⟩
  · have := (isCritical_smul _ g⁻¹ _ _).2 hcr
    rwa [← e0] at this
  · rw [hgeo, hg1', hg1, inv_smul_smul]
  · rw [hgeo, hg2]
  · have hcr0 := hch.crit (j - 1) (by omega)
    rw [show 2 * (j - 1) = 2 * j - 2 by omega] at hcr0
    refine ⟨(isCritical_smul _ g⁻¹ _ _).2 hcr0, ?_⟩
    have hg0' := hch.geo_eq (i := 2 * j - 2) (j := 2 * j - 2 + critDist (puAmalgam h.le)) (m := 2)
      (by omega) (by omega) (by omega)
    rw [geo_smul, hg0', show 2 * j - 2 + 2 = 2 * j by omega, hg0, inv_smul_smul]

theorem le_stabCenter_x1 (h32 : S32) (h53 : S53) (h59 : S5B.S59) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hch : S510.IsChain h (2 ^ k) a s t N) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hgood : ∃ g : (puAmalgam h.le).Universal, geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧
      geo _ s t (2 * j + 1) = g • baseB _ ∧
      GoodLamF h (2 ^ k) a (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le)))
        (g⁻¹ • geo _ s t (2 * j - 2)))
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (geo _ s t (2 * j + 2)))
    (hEq : 2 ^ k < (Qv _ (geo _ s t (2 * j))).relIndex E) :
    ZM _ (geo _ s t (2 * j)) ⊓ Subgroup.centralizer (Qv _ (geo _ s t (2 * j - 2)) : Set _) ⊓
        Subgroup.centralizer (E : Set _) ≤ stabCenter _ (geo _ s t (2 * j)) := by
  obtain ⟨g, hg0, hg1, hgd⟩ := hgood
  obtain ⟨hc', hβ', hδ, hμ⟩ := frame hch hjN hg0 hg1
  obtain ⟨hcμ, hμα⟩ := hμ hj1
  have hE₀ : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Qv _ (geo _ (baseA (puAmalgam h.le))
        (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) 2) := by
    rw [hδ, qv_smul]
    exact Subgroup.map_mono hE
  have hEq₀ : 2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex
      (E.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have e : baseA (puAmalgam h.le) = g⁻¹ • geo _ s t (2 * j) := by rw [hg0, inv_smul_smul]
    rw [e, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hEq
  have key := S511S.le_stabCenter_x1 h32 h53 h59 h hmin hb hd hc' hβ' hgd hcμ hμα hE₀ hEq₀
  have e1 : geo _ s t (2 * j - 2) = g • (g⁻¹ • geo _ s t (2 * j - 2)) := (smul_inv_smul g _).symm
  have e2 : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [e1, hg0, e2, zm_smul (g := g), qv_smul (g := g), S510.stabCenter_smul,
    PU.centralizer_map_mulEquiv, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff]
  exact key

theorem relIndex_x1_le (h32 : S32) (h53 : S53) (h59 : S5B.S59) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hch : S510.IsChain h (2 ^ k) a s t N) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hgood : ∃ g : (puAmalgam h.le).Universal, geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧
      geo _ s t (2 * j + 1) = g • baseB _ ∧
      GoodLamF h (2 ^ k) a (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le)))
        (g⁻¹ • geo _ s t (2 * j - 2)))
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (geo _ s t (2 * j + 2)))
    (hEQ : ¬ E ≤ Qv _ (geo _ s t (2 * j))) {H : Subgroup (puAmalgam h.le).Universal}
    (hH : H ≤ ZM _ (geo _ s t (2 * j)) ⊓
      Subgroup.centralizer (Qv _ (geo _ s t (2 * j - 2)) : Set _) ⊓
        Subgroup.centralizer (E : Set _)) :
    (stabCenter _ (geo _ s t (2 * j))).relIndex H ≤ 2 ^ k := by
  obtain ⟨g, hg0, hg1, hgd⟩ := hgood
  obtain ⟨hc', hβ', hδ, hμ⟩ := frame hch hjN hg0 hg1
  obtain ⟨hcμ, hμα⟩ := hμ hj1
  have e : baseA (puAmalgam h.le) = g⁻¹ • geo _ s t (2 * j) := by rw [hg0, inv_smul_smul]
  have hE₀ : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Qv _ (geo _ (baseA (puAmalgam h.le))
        (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) 2) := by
    rw [hδ, qv_smul]
    exact Subgroup.map_mono hE
  have hEQ₀ : ¬ E.map (MulAut.conj g⁻¹).toMonoidHom ≤ Qv _ (baseA (puAmalgam h.le)) := by
    rw [e, qv_smul, map_conj_le_map_conj_iff]
    exact hEQ
  have hH₀ : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ ZM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (Qv _ (g⁻¹ • geo _ s t (2 * j - 2)) : Set _) ⊓
        Subgroup.centralizer (E.map (MulAut.conj g⁻¹).toMonoidHom : Set _) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hH
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, ← PU.centralizer_map_mulEquiv,
      ← PU.centralizer_map_mulEquiv, ← zm_smul, ← qv_smul, ← e] at h1
    exact h1
  have key := S511S.relIndex_x1_le h32 h53 h59 h hmin hb hd hc' hβ' hgd hcμ hμα hE₀ hEQ₀ hH₀
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) _ _
      (MulAut.conj g⁻¹).injective,
    ← S510.stabCenter_smul, ← e]
  exact key

theorem le_relIndex_commutator_x1 (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) (hch : S510.IsChain h (2 ^ k) a s t N) {j : ℕ}
    (hjN : j ≤ N)
    (hgood : ∃ g : (puAmalgam h.le).Universal, geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧
      geo _ s t (2 * j + 1) = g • baseB _ ∧
      GoodLamF h (2 ^ k) a (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le)))
        (g⁻¹ • geo _ s t (2 * j - 2)))
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (geo _ s t (2 * j + 2)))
    (hEq : 2 ^ k < (Qv _ (geo _ s t (2 * j))).relIndex E) :
    (2 ^ k) ^ 2 ≤ (stabCenter _ (geo _ s t (2 * j))).relIndex
      ⁅S5.uSub h.le L (geo _ s t (2 * j)), E⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg0, hg1, hgd⟩ := hgood
  obtain ⟨hc', hβ', hδ, -⟩ := frame hch hjN hg0 hg1
  obtain ⟨l, -, hl, -⟩ := hgd.exists_conj
  have e : baseA (puAmalgam h.le) = g⁻¹ • geo _ s t (2 * j) := by rw [hg0, inv_smul_smul]
  have hE₀ : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Qv _ (geo _ (baseA (puAmalgam h.le))
        (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) 2) := by
    rw [hδ, qv_smul]
    exact Subgroup.map_mono hE
  have hEq₀ : 2 ^ k < (Qv _ (baseA (puAmalgam h.le))).relIndex
      (E.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [e, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hEq
  have key := S511S.le_relIndex_commutator_x1 h hb hd hc' hβ' hl hE₀ hEq₀
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) _ _
      (MulAut.conj g⁻¹).injective,
    ← S510.stabCenter_smul, Subgroup.map_commutator, ← S5B.uSub_smul h.le hLn, ← e]
  exact key

end IsChain

end S511S

end CFSG.Quasithin.MS93
