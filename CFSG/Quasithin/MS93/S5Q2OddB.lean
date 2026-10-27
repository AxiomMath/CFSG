module

public import CFSG.Quasithin.MS93.S5BAux
public import CFSG.Quasithin.MS93.S5Q2UC

public section

namespace CFSG.Quasithin.MS93.S5Q2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace UC

section Even

omit [Finite G] in
private theorem eq_of_relIndex_eq_two {H K N : Subgroup G} (hHK : H ≤ K) (hKN : K ≤ N)
    (hNK : ¬ N ≤ K) (h2 : H.relIndex N = 2) : H = K := by
  have e := Subgroup.relIndex_mul_relIndex H K N hHK hKN
  rw [h2] at e
  have h1 : K.relIndex N ≠ 1 := fun h1 => hNK (Subgroup.relIndex_eq_one.1 h1)
  have h3 : H.relIndex K = 1 := by
    rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | h0
    · rw [h0, zero_mul] at e; omega
    · rcases Nat.eq_zero_or_pos (K.relIndex N) with h0' | h0'
      · rw [h0', mul_zero] at e; omega
      · have : H.relIndex K * K.relIndex N = 2 := e
        have hle : H.relIndex K ≤ 2 := by
          have := Nat.le_of_dvd (by norm_num) (Dvd.intro _ this)
          exact this
        interval_cases (H.relIndex K)
        · rfl
        · omega
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.1 h3)

variable (h : PUHyp M T L)

theorem cX_le_centralizer_of_vIm_le (hd : S5.IsSp4Data M T L 1 F a)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ stab _ (baseA (puAmalgam h.le)))
    (hKe : S5.vIm h.le a K ≤ commutator (MSP.Sp4 F)) :
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (K : Set (puAmalgam h.le).Universal) := by
  rw [puAmalgam.stab_baseA] at hK
  obtain ⟨K₀, -, hK₀M, rfl⟩ := S5.exists_eq_imM h.le hK
  rw [cX_baseA h]
  have hZ : Zq M L ≤ Subgroup.centralizer (K₀ : Set G) :=
    S5Q2.le_centralizer_of_mem_commutator h hd hK₀M fun j hj => hKe (by
      rw [S5B.vIm_imM h.le]
      exact ⟨⟨j, hK₀M hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩)
  rw [← inf_of_le_left hZ, imM_inf_centralizer h.le _ hK₀M]
  exact inf_le_right

theorem not_cX_le_centralizer_qv_baseB (hd : S5.IsSp4Data M T L 1 F a)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    ¬ XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) := by
  intro hle
  rw [cX_baseA h, puAmalgam.qv_baseB] at hle
  have hZ : Zq M L ≤ Subgroup.centralizer (T : Set G) := by
    intro z hz
    have hzM : z ∈ M := Xq_le M hz.1
    have h1 := hle ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at h1 ⊢
    intro t ht
    have h2 := h1 _ ⟨⟨t, h.le ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    have h3 : (⟨t, h.le ht⟩ : ↥M) * ⟨z, hzM⟩ = ⟨z, hzM⟩ * ⟨t, h.le ht⟩ :=
      (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact h2)
    exact congrArg Subtype.val h3
  exact hC ((le_inf le_rfl hZ).trans (S5Q2.zq_inf_centralizer_T_le h hd))

theorem not_cX_le_xm_of_even (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L 1 F a) (h54 : S54)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    (hJe : S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
      commutator (MSP.Sp4 F))
    (hJ2 : (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)).relIndex
      (Qv _ (baseB (puAmalgam h.le))) = 2)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hJ : S5.jOff h.le L 2 (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ≠
      S5.jOff h.le L 2 (baseA _) (baseB _)) :
    ¬ XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ⊓
        Subgroup.centralizer (puTrans h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) :
          Set (puAmalgam h.le).Universal) ≤ XM _ (baseA (puAmalgam h.le)) := by
  intro hle
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hCH := h.centHyp
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa using hd.card_eq
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  set J := S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) with hJdef
  set Jδ := S5.jOff h.le L 2 δ (baseB (puAmalgam h.le)) with hJδdef
  set Tβ := Qv _ (baseB (puAmalgam h.le)) with hTβ
  set Cα := XM _ (baseA (puAmalgam h.le)) ⊓
    Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) with hCα
  set Cδ := XM _ δ ⊓
    Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal) with hCδ
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβadj.symm hβδ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  have hJg : Jδ = J.map (MulAut.conj g).toMonoidHom := by
    rw [hJδdef, hJdef, ← hgα, ← S5B.jOff_smul h.le hLn, hgβ]
  have hCg : Cδ = Cα.map (MulAut.conj g).toMonoidHom := by
    rw [hCδ, hCα, ← hgα, cX_smul h]
  have hTg : Tβ.map (MulAut.conj g).toMonoidHom = Tβ := by
    rw [hTβ, ← qv_smul, hgβ]
  have hTst : Tβ ≤ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hαβadj.symm
  have hT2 : IsPGroup 2 ↥Tβ := isPGroup_qv _ h20 (not_isMVtx_baseB _)
  have hJT : J ≤ Tβ := S5B.jOff_le_qv h.le L _ _ _
  have hJδT : Jδ ≤ Tβ := S5B.jOff_le_qv h.le L _ _ _
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ J := S5B.qv_le_jOff h (by norm_num) hα hαβadj
  have hQT : Qv _ (baseA (puAmalgam h.le)) ≤ Tβ := qv_le_qv _ h20 hα hαβadj
  have hTfin : Finite ↥Tβ := finite_qv _ h20 (not_isMVtx_baseB _)
  have hQfin : Finite ↥(Qv _ (baseA (puAmalgam h.le))) :=
    Finite.of_injective (Subgroup.inclusion hQT) (Subgroup.inclusion_injective hQT)
  have hJfin : Finite ↥J :=
    Finite.of_injective (Subgroup.inclusion hJT) (Subgroup.inclusion_injective hJT)
  set Kα := Tβ ⊓ Subgroup.centralizer (Cα : Set (puAmalgam h.le).Universal) with hKα
  have hJK : J ≤ Kα := le_inf hJT (Subgroup.le_centralizer_iff.1
    (cX_le_centralizer_of_vIm_le h hd (hJT.trans hTst) hJe))
  have hTK : ¬ Tβ ≤ Kα := fun hle' => not_cX_le_centralizer_qv_baseB h hd hC
    (Subgroup.le_centralizer_iff.1 (hle'.trans inf_le_right))
  have hJeq : J = Kα := eq_of_relIndex_eq_two hJK inf_le_left hTK hJ2
  have hJδ2 : Jδ.relIndex Tβ = 2 := by
    rw [hJg, ← hTg, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hJ2
  have hJδK : Jδ ≤ Tβ ⊓ Subgroup.centralizer (Cδ : Set (puAmalgam h.le).Universal) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hJK
    rw [hKα, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hTg,
      ← PU.centralizer_map_mulEquiv, ← hCg, ← hJg] at h1
    exact h1
  have hTKδ : ¬ Tβ ≤ Tβ ⊓ Subgroup.centralizer (Cδ : Set (puAmalgam h.le).Universal) := by
    intro hle'
    apply hTK
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, ← PU.centralizer_map_mulEquiv,
      hCg, map_conj_inv_map_conj] at h1
    have hTg' : Tβ.map (MulAut.conj g⁻¹).toMonoidHom = Tβ := by
      rw [hTβ, ← qv_smul, (mem_stab _).1 (inv_mem hg)]
    rw [hTg'] at h1
    exact h1
  have hJδeq := eq_of_relIndex_eq_two hJδK inf_le_left hTKδ hJδ2
  have hQJδ : Qv _ (baseA (puAmalgam h.le)) ≤ Jδ := by
    rw [hJδeq]
    refine le_inf hQT ?_
    rw [← Subgroup.le_centralizer_iff]
    exact hle.trans (xm_le_centralizer _ _)
  have hJst : J ≤ stab _ (baseA (puAmalgam h.le)) := hJT.trans hTst
  have hJ2g : IsPGroup 2 ↥J := hT2.to_le hJT
  have hJδst : Jδ ≤ stab _ (baseA (puAmalgam h.le)) := hJδT.trans hTst
  have hJδ2g : IsPGroup 2 ↥Jδ := hT2.to_le hJδT
  have hcardJ : Nat.card (S5.vIm h.le a J) = 4 := by
    rcases h54 G M T L h hmin hb 1 F _ _ a hd with ⟨-, ⟨l₁, hl₁, -, hJl₁⟩, hJq⟩ | ⟨-, -, p, hp, hTq⟩
    · have h1 : S5.vIm h.le a J ≤ MSP.qLine l₁ ⊓ commutator (MSP.Sp4 F) :=
        le_inf (S5B.vIm_le_of_le_vPre h.le hJl₁) hJe
      have h2 := Subgroup.card_le_of_le h1
      rw [MSP.card_qLine_inf_commutator hF hl₁] at h2
      rw [← S33.relIndex_qv_baseA_eq_card h hd hJst hJ2g] at h2 ⊢
      simp only [pow_one] at hJq
      rw [← hJdef] at hJq
      norm_num at hJq
      omega
    · exact absurd hTq (X52.vIm_qv_baseB_ne_qPoint h hd hC hp)
  have hcardJδ : Nat.card (S5.vIm h.le a Jδ) = 4 := by
    rw [← S33.relIndex_qv_baseA_eq_card h hd hJδst hJδ2g, ← hcardJ,
      ← S33.relIndex_qv_baseA_eq_card h hd hJst hJ2g]
    have e1 := Subgroup.relIndex_mul_card (H := Qv _ (baseA (puAmalgam h.le))) (K := Jδ)
    have e2 := Subgroup.relIndex_mul_card (H := Qv _ (baseA (puAmalgam h.le))) (K := J)
    rw [inf_of_le_left hQJδ] at e1
    rw [inf_of_le_left hQJ] at e2
    have e3 : Nat.card ↥Jδ = Nat.card ↥J := by
      rw [hJg]
      exact Nat.card_congr (J.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv.symm
    have hpos : 0 < Nat.card ↥(Qv (puAmalgam h.le) (baseA (puAmalgam h.le))) := Nat.card_pos
    rw [e3, ← e2] at e1
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  obtain ⟨-, l, hl, hX, hZ⟩ := shape_of_not_le h hd hC hc
  have hZδ : ZM _ α' ≤ Jδ := by
    refine (zm_le_qv_of_dist_lt _ (hc.isMVtx_right _ h20) ?_).trans
      (S5B.qv_le_jOff h (by norm_num) hδM hβδ.symm)
    rw [SimpleGraph.dist_comm, hδ, dist_geo_right _ (by omega), hd2]
    omega
  have hZle : S5.vIm h.le a (ZM _ α') ≤ S5.vIm h.le a Jδ :=
    Subgroup.map_mono (Subgroup.comap_mono hZδ)
  have hJδe : S5.vIm h.le a Jδ ≤ commutator (MSP.Sp4 F) := by
    have heq : S5.vIm h.le a (ZM _ α') = S5.vIm h.le a Jδ := by
      refine Subgroup.eq_of_le_of_card_ge hZle ?_
      rw [hcardJδ, hZ, hX, MSP.card_qLine_inf_commutator hF hl]
    rw [← heq, hZ, hX]
    exact inf_le_right
  have hJδJ : Jδ ≤ J := by
    rw [hJeq]
    exact le_inf hJδT (Subgroup.le_centralizer_iff.1
      (cX_le_centralizer_of_vIm_le h hd hJδst hJδe))
  refine hJ (Subgroup.eq_of_le_of_card_ge hJδJ ?_)
  rw [hJg]
  exact (Nat.card_congr (J.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).le

theorem jOff_eq_of_eq_qv {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hA : S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) = Qv _ (baseB (puAmalgam h.le))) :
    S5.jOff h.le L 2 δ (baseB _) = S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  have e := S5B.jOff_smul h.le hLn 2 g (baseA (puAmalgam h.le)) (baseB _)
  rw [hgα, hgβ, hA, ← qv_smul, hgβ] at e
  rw [e, hA]

end Even

end UC

end CFSG.Quasithin.MS93.S5Q2
