module

public import CFSG.Quasithin.MS93.S510Loc
public import CFSG.Quasithin.MS93.S510Path

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

section Eqv

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem critR_smul (g : X.Universal) (δ δ' : Vtx X) :
    critR X (g • δ) (g • δ') = (critR X δ δ').map (MulAut.conj g).toMonoidHom := by
  rw [critR, critR, zm_smul, zm_smul, Subgroup.map_commutator]

theorem critA_smul (g : X.Universal) (δ δ' : Vtx X) :
    critA X (g • δ) (g • δ') = (critA X δ δ').map (MulAut.conj g).toMonoidHom := by
  rw [critA, critA, xm_smul, qv_smul, Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

end Eqv

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section ZHat

theorem not_puTrans_le_qv (h : PUHyp M T L) {ε : Vtx (puAmalgam h.le)} (hε : ¬ IsMVtx _ ε) :
    ¬ puTrans h.le L (baseA (puAmalgam h.le)) ≤ Qv _ ε := by
  intro hle
  have h2 : IsPGroup 2 (puTrans h.le L (baseA (puAmalgam h.le))) :=
    (isPGroup_qv _ h.hyp20 hε).to_le hle
  rw [S5B.puTrans_L_baseA h] at h2
  have e1 : ↥L ≃* ↥(imM h.le L) := by
    refine (Subgroup.subgroupOfEquivOfLe h.L_le).symm.trans ?_
    exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
  have hp : IsPGroup 2 ↥L := h2.of_equiv e1.symm
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 h.L_ne_bot
  exact Group.IsPerfect.not_isNilpotent ↥L hp.isNilpotent

theorem zHat_not_le_qv_of_geo (h55 : S55) (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := by
  intro hZ
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hβ := not_isMVtx_baseB (puAmalgam h.le)
  have hgβ : ∀ g ∈ stab _ (baseA (puAmalgam h.le)),
      (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    intro g hg
    have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [(mem_stab _).1 (inv_mem hg)] at this
  have hgM : ∀ g : (puAmalgam h.le).Universal, ¬ IsMVtx _ (g⁻¹ • baseB (puAmalgam h.le)) :=
    fun g => by rw [isMVtx_smul]; exact hβ
  by_cases hl : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)
  · obtain ⟨l, hline, hTl, hJl⟩ := hl
    obtain ⟨g, hg, x, hx, -, -, hc6, -⟩ :=
      h56 G M T L h hmin hb k F _ _ a hd α' hc hαβ l hline hTl hJl
    have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
    have hQQ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) :=
      qv_le_qv _ h.hyp20 hα (hgβ g hg)
    have h1 : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
        Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
      rw [S5B.rconj_eq_map, qv_smul]
      exact Subgroup.map_mono (S5B.jOff_le_qv h.le L _ _ _)
    have h2 : S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α') ≤
        Qv _ (baseA (puAmalgam h.le)) := by
      rw [S5B.rconj_eq_map, inv_inv]
      have e : Qv _ (baseA (puAmalgam h.le)) =
          (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom := by
        rw [← qv_smul, (mem_stab _).1 hxst]
      rw [e]
      exact Subgroup.map_mono hZ
    exact not_puTrans_le_qv h (hgM g)
      (hc6.trans (sup_le (sup_le h1 (hZ.trans hQQ)) (h2.trans hQQ)))
  · push Not at hl
    obtain ⟨g, hg, x, -, ⟨ha1, -⟩, -, -⟩ := h55 G M T L h hmin hb k F _ _ a hd α' hc hαβ
      (baseA _) (adj_baseA_baseB _).symm (Or.inr fun l hline hTl hJl => hl l hline hTl hJl)
    have hQQ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) :=
      qv_le_qv _ h.hyp20 hα (hgβ g hg)
    have hst : stab _ (baseA (puAmalgam h.le)) ≤ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
      rw [← ha1]
      exact sup_le le_rfl (hZ.trans hQQ)
    exact not_puTrans_le_qv h (hgM g) ((puTrans_le_stab h.le L _).trans hst)

theorem zHat_not_le_qv_baseA (h55 : S55) (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := by
  have hb0 := h.critDist_pos
  have hadj : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by rw [hc.2.1]; exact hb0)
  obtain ⟨t, ht, htβ⟩ := exists_mem_stab_smul _ hadj (adj_baseA_baseB (puAmalgam h.le))
  have htα : t • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 ht
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (t • α') := by
    have := (isCritical_smul _ t _ _).2 hc
    rwa [htα] at this
  have hgeo : geo _ (baseA (puAmalgam h.le)) (t • α') 1 = baseB _ := by
    have := geo_smul _ t (baseA (puAmalgam h.le)) α' 1
    rw [htα] at this
    rw [this, htβ]
  have key := zHat_not_le_qv_of_geo h55 h56 h hmin hb hd hc' hgeo
  intro hZ
  apply key
  have e1 := S5B.zHat_smul _ t (baseA (puAmalgam h.le)) α'
  rw [htα] at e1
  have e2 : Qv _ (baseA (puAmalgam h.le)) =
      (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj t).toMonoidHom := by
    rw [← qv_smul, htα]
  rw [e1, e2]
  exact Subgroup.map_mono hZ

theorem zHat_not_le_qv (h55 : S55) (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ') :
    ¬ S5.zHat _ δ δ' ≤ Qv _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • δ') := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  have key := zHat_not_le_qv_baseA h55 h56 h hmin hb hd hc'
  have e : δ' = g • (g⁻¹ • δ') := (smul_inv_smul g δ').symm
  rw [e, S5B.zHat_smul, qv_smul, map_conj_le_map_conj_iff]
  exact key

theorem exists_zHat_not_mem (h55 : S55) (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ') :
    ∃ y ∈ S5.zHat _ δ δ', y ∈ stab _ δ ∧ (∃ e : ℕ, y ^ 2 ^ e = 1) ∧ y ∉ Qv _ δ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨y, hy, hyQ⟩ := Set.not_subset.1 (zHat_not_le_qv h55 h56 h hmin hb hd hc)
  have hcr := ms22_iii _ hyp hb0 h.centHyp hc
  have hZ : ZM _ δ' ≤ Qv _ (geo _ δ δ' 1) := zm_le_qv_geo_one _ hyp hb0 hc
  have hZst : ZM _ δ' ≤ stab _ δ := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hδ1 : ¬ IsMVtx _ (geo _ δ δ' 1) :=
    (isMVtx_iff_of_adj _ (adj_geo_one_of_isCritical _ hb0 hc)).1 hc.1
  have hyZ : y ∈ ZM _ δ' := (Subgroup.mem_inf.1 hy).1
  obtain ⟨e, he⟩ := isPGroup_qv _ hyp hδ1 ⟨y, hZ hyZ⟩
  exact ⟨y, hy, hZst hyZ, ⟨e, by simpa using congrArg Subtype.val he⟩, hyQ⟩

end ZHat

section S33

theorem s33_dich_baseA (hX2 : S33.S33X52) (h32 : S32) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {Y : Subgroup (puAmalgam h.le).Universal}
    (hYT : Y ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _))
    (hYX : Y ≤ Subgroup.centralizer (XM _ (baseA (puAmalgam h.le)) : Set _))
    (hAYY : ⁅⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆, Y⁆ = ⊥) :
    ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
        ⁅XM _ (baseA (puAmalgam h.le)), XM _ α'⁆ ⊔ critR _ (baseA (puAmalgam h.le)) α' ⊔
          ⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆ ∨
      (Nat.card ↥⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k ∧
        ⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
          critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α') := by
  by_cases hY : ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆
  · left
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans hY).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  · by_cases hYZ : ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
        critR _ (baseA (puAmalgam h.le)) α'
    · exact Or.inl (hYZ.trans (le_sup_right.trans le_sup_left))
    · exact Or.inr ((S5B.s33ii2_of' hX2 h hd (h32 G M T L h).2.1 hc hYT hYR hYX hY hYZ).2.2
        hAYY)

theorem s33_dich (hX2 : S33.S33X52) (h32 : S32) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ')
    {Y : Subgroup (puAmalgam h.le).Universal} (hYT : Y ≤ Qv _ (geo _ δ' δ 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ δ δ' : Set _))
    (hYX : Y ≤ Subgroup.centralizer (XM _ δ : Set _))
    (hAYY : ⁅⁅critA _ δ δ', Y⁆, Y⁆ = ⊥) :
    ⁅Y, S5.zHat _ δ δ'⁆ ≤ ⁅XM _ δ, XM _ δ'⁆ ⊔ critR _ δ δ' ⊔ ⁅critA _ δ δ', Y⁆ ∨
      (Nat.card ↥⁅Y, critA _ δ δ'⁆ = 2 ^ k ∧
        ⁅Y, critA _ δ δ'⁆ ≤ critR _ δ δ' ⊔ stabCenter _ δ') := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • δ') := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  have e : δ' = g • (g⁻¹ • δ') := (smul_inv_smul g δ').symm
  set ρ := g⁻¹ • δ' with hρ
  rw [e] at hYT hYR hAYY ⊢
  set Y₀ := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY₀
  have hYY : Y = Y₀.map (MulAut.conj g).toMonoidHom := by rw [hY₀, map_conj_map_conj_inv]
  rw [hYY] at hYT hYR hYX hAYY ⊢
  rw [geo_smul, qv_smul, map_conj_le_map_conj_iff] at hYT
  rw [critR_smul, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hYR
  rw [xm_smul, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff] at hYX
  rw [critA_smul, ← Subgroup.map_commutator, ← Subgroup.map_commutator] at hAYY
  have hAYY' : ⁅⁅critA _ (baseA (puAmalgam h.le)) ρ, Y₀⁆, Y₀⁆ = ⊥ := by
    rw [eq_bot_iff] at hAYY ⊢
    intro x hx
    have := hAYY ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact (MulAut.conj g).injective (by simpa using this)
  rcases s33_dich_baseA hX2 h32 h hd hc' hYT hYR hYX hAYY' with hl | ⟨hcard, hle⟩
  · left
    rw [S5B.zHat_smul, xm_smul, xm_smul, critR_smul, critA_smul, ← Subgroup.map_commutator,
      ← Subgroup.map_commutator, ← Subgroup.map_commutator, ← Subgroup.map_sup,
      ← Subgroup.map_sup, map_conj_le_map_conj_iff]
    exact hl
  · right
    rw [critA_smul, ← Subgroup.map_commutator, S5B.card_map_conj, critR_smul,
      S510.stabCenter_smul, ← Subgroup.map_sup, map_conj_le_map_conj_iff]
    exact ⟨hcard, hle⟩

end S33

section S58

theorem s58_gp (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ') :
    2 ^ k ≤ (S5.bSub h.le L δ).relIndex (S5.uSub h.le L (geo _ δ δ' 2)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, -, hc', hβ'⟩ := S510.exists_base_crit h hc
  have key := (h58 G M T L h hmin hb k F _ _ a hd _ hc' hβ').2.2
  have e : geo _ (g • baseA (puAmalgam h.le)) δ' 2 = g • geo _ (baseA _) (g⁻¹ • δ') 2 := by
    rw [← geo_smul, smul_inv_smul]
  rw [e, S5B.bSub_smul h.le hLn, S5B.uSub_smul h.le hLn,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact key

theorem uSub_not_le_bSub (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ') :
    ¬ S5.uSub h.le L (geo _ δ δ' 2) ≤ S5.bSub h.le L δ := by
  intro hle
  have h1 := s58_gp h58 h hmin hb hd hc
  rw [Subgroup.relIndex_eq_one.2 hle] at h1
  have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
  omega

theorem vv_not_le_gp (h58 : S5B.S58) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ δ') :
    ¬ Vv _ δ ≤ Qv _ (geo _ δ' δ 2) := by
  obtain ⟨g, rfl, -, hc', hβ'⟩ := S510.exists_base_crit h hc
  have key := (h58 G M T L h hmin hb k F _ _ a hd _ hc' hβ').2.1
  intro hle
  apply key
  have e1 : geo _ δ' (g • baseA (puAmalgam h.le)) 2 =
      g • geo _ (g⁻¹ • δ') (baseA (puAmalgam h.le)) 2 := by
    rw [← geo_smul, smul_inv_smul]
  rw [e1, Vv, vi_smul, qv_smul, map_conj_le_map_conj_iff] at hle
  exact hle

end S58

end S59

end CFSG.Quasithin.MS93
