module

public import CFSG.Quasithin.MS93.S5AGeo
public import CFSG.Quasithin.MS93.S5BJ
public import CFSG.Quasithin.MS93.S5BTv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S510

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section NatM

theorem exists_point_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k) :
    ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      MSP.commSp ((E.subgroupOf M).map a) = p ∧
      MSP.fixSp ((E.subgroupOf M).map a) = MSP.perp p ∧
      (E.subgroupOf M).map a ≤ MSP.xPoint p := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  set Ē := (E.subgroupOf M).map a
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hrel' := S5B.relIndex_centralizer_mul_card h hlift c hEM
  rw [hrel, MSP.card_V4, hFq] at hrel'
  have hk1 : 1 ≤ k := hd.1
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hfix : Nat.card (MSP.fixSp Ē) = (2 ^ k) ^ 3 := by
    have hpos : 0 < 2 ^ k := by positivity
    have : 2 ^ k * Nat.card (MSP.fixSp Ē) = 2 ^ k * (2 ^ k) ^ 3 := by rw [hrel']; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hcardfix : Nat.card (MSP.fixSp Ē) = (2 ^ k) ^ Module.finrank F (MSP.fixSp Ē) := by
    rw [← hFq]
    exact Module.natCard_eq_pow_finrank (K := F)
  have hdim : Module.finrank F (MSP.fixSp Ē) = 3 := by
    rw [hcardfix] at hfix
    exact Nat.pow_right_injective h2k hfix
  have hp : MSP.IsPoint (MSP.commSp Ē) := by
    have h4 := MSP.finrank_perp (MSP.commSp Ē)
    rw [← S5B.fixSp_eq_perp_commSp, hdim] at h4
    change Module.finrank F (MSP.commSp Ē) = 1
    omega
  refine ⟨MSP.commSp Ē, hp, rfl, S5B.fixSp_eq_perp_commSp _, ?_⟩
  rw [MSP.le_fixer_iff, S5B.fixSp_eq_perp_commSp]

theorem relIndex_eq_of_comm_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E T₀ : Subgroup G} (hT₀M : T₀ ≤ M) (hT₀ : IsPGroup 2 T₀) (hET : E ≤ T₀)
    (hEO : ¬ E ≤ pCoreOf 2 M)
    (hRE : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G))
    (hRT : ⁅Uq M T L, E⁆ ⊓ Subgroup.centralizer (T₀ : Set G) ≤
      Subgroup.centralizer (L : Set G)) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hEM : E ≤ M := hET.trans hT₀M
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L := commutator_le_left_of_le_normalizer (hEM.trans hUn)
  set Ē := (E.subgroupOf M).map a
  set Tb := (T₀.subgroupOf M).map a
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hiso : MSP.commSp Ē ≤ MSP.fixSp Ē := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hw
    exact (S5B.mem_centralizer_iff_vec h hlift c hEM u).1 (hRE hu)
  have hinf : MSP.commSp Ē ⊓ MSP.fixSp Tb = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwT⟩
    obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hw
    have huT : (u : G) ∈ Subgroup.centralizer (T₀ : Set G) :=
      (S5B.mem_centralizer_iff_vec h hlift c hT₀M u).2 hwT
    have huL : (u : G) ∈ Subgroup.centralizer (L : Set G) := hRT ⟨hu, huT⟩
    rw [Submodule.mem_bot]
    exact (c.vec_eq_zero_iff u).2 ⟨u.2, huL⟩
  have hĒ : Ē ≠ ⊥ := by
    intro hbot
    apply hEO
    intro e he
    have h1 : a ⟨e, hEM he⟩ = 1 := by
      have : a ⟨e, hEM he⟩ ∈ Ē := ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [hbot] at this
      exact this
    obtain ⟨n, hn⟩ := (hT₀.to_le hET) ⟨e, he⟩
    exact S5B.mem_pCoreOf_of_ker h hd h1 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hTb : IsPGroup 2 Tb :=
    (hT₀.comap_of_injective M.subtype (Subgroup.subtype_injective M)).map a
  have hĒTb : Ē ≤ Tb := Subgroup.map_mono fun x hx => hET hx
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hfixT : MSP.fixSp Tb ≠ ⊥ := S5.fixSp_ne_bot hTb
  have hle : MSP.commSp Ē ⊔ MSP.fixSp Tb ≤ MSP.perp (MSP.commSp Ē) := by
    rw [← S5B.fixSp_eq_perp_commSp]
    exact sup_le hiso (MSP.fixSp_antitone hĒTb)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (MSP.commSp Ē) (MSP.fixSp Tb)
  rw [hinf, finrank_bot] at h1
  have h2 := Submodule.finrank_mono hle
  have h3 := MSP.finrank_perp (MSP.commSp Ē)
  have h4 : 0 < Module.finrank F (MSP.fixSp Tb) := S5.finrank_pos_of_ne_bot hfixT
  have hd0 : Module.finrank F (MSP.commSp Ē) ≠ 0 := by
    intro h0
    apply hĒ
    rw [← MSP.fixSp_eq_top_iff, S5B.fixSp_eq_perp_commSp, Submodule.finrank_eq_zero.1 h0]
    exact LinearMap.BilinForm.orthogonal_bot
  have hp : Module.finrank F (MSP.commSp Ē) = 1 := by omega
  have hrel := S5B.relIndex_centralizer_mul_card h hlift c hEM
  have hfix : Nat.card (MSP.fixSp Ē) = (2 ^ k) ^ 3 := by
    rw [S5B.fixSp_eq_perp_commSp, ← hFq, Module.natCard_eq_pow_finrank (K := F)]
    congr 1
    omega
  rw [hfix, MSP.card_V4, hFq] at hrel
  have hpos : 0 < (2 ^ k) ^ 3 := by positivity
  have : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) * (2 ^ k) ^ 3 =
      2 ^ k * (2 ^ k) ^ 3 := by rw [hrel]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end NatM

section Vertex

theorem relIndex_eq_of_comm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε) (hEQ : ¬ E ≤ Qv _ γ)
    (hRE : ⁅S5.uSub h.le L γ, E⁆ ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    (hRT : ⁅S5.uSub h.le L γ, E⁆ ⊓
        Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal)) :
    (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L γ) =
      2 ^ k := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hEQ hRE hRT ⊢
  rw [qv_smul, map_conj_le_map_conj_iff, puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hE
  rw [hE₀] at hEQ hRE hRT ⊢
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [qv_smul, map_conj_le_map_conj_iff, S5B.qv_baseA_eq h] at hEQ
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator,
    PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
    ← imM_commutator h.le hUM hE₀M] at hRE
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator, qv_smul,
    puAmalgam.qv_baseB, puTrans_smul h.le hLn, S5B.puTrans_L_baseA h,
    PU.centralizer_map_mulEquiv, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff,
    ← imM_commutator h.le hUM hE₀M] at hRT
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hUM hE₀M]
  have hcomm : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le hUM hE₀M
  refine relIndex_eq_of_comm_M h hd h.le h.isPGroup hE₀T
    (fun hle => hEQ (imM_mono h.le hle)) ?_ ?_
  · have h1 : imM h.le ⁅Uq M T L, E₀⁆ ≤ imM h.le (⁅Uq M T L, E₀⁆ ⊓
        Subgroup.centralizer (E₀ : Set G)) := by
      rw [imM_inf_centralizer h.le _ hE₀M]
      exact le_inf le_rfl hRE
    exact ((imM_le_imM_iff h.le hcomm).1 h1).trans inf_le_right
  · intro x hx
    have hxM : x ∈ M := hcomm hx.1
    have h1 : (puAmalgam h.le).ofA ⟨x, hxM⟩ ∈ imM h.le (⁅Uq M T L, E₀⁆ ⊓
        Subgroup.centralizer (T : Set G)) := ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [imM_inf_centralizer h.le _ h.le] at h1
    have h2 := hRT h1
    have h3 : (puAmalgam h.le).ofA ⟨x, hxM⟩ ∈ imM h.le (⁅Uq M T L, E₀⁆ ⊓
        Subgroup.centralizer (L : Set G)) := by
      rw [imM_inf_centralizer h.le _ h.L_le]
      exact ⟨h1.1, h2⟩
    obtain ⟨m, hm, he⟩ := h3
    have : m = ⟨x, hxM⟩ := (puAmalgam h.le).ofA_injective he
    subst this
    exact (Subgroup.mem_subgroupOf.1 hm).2

theorem jOff_le_normalizer_of_relIndex_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (baseB (puAmalgam h.le)))
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k) :
    S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ Subgroup.normalizer
      ((S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) : Subgroup _) : Set _) := by
  rw [puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := S5B.exists_eq_imM h.le hE
  have hrel₀ : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = 2 ^ k := by
    rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at hrel
    exact hrel
  obtain ⟨p, hp, -, hfix, hxP⟩ := exists_point_of_relIndex h hd hE₀M hrel₀
  obtain ⟨g, hgE, hg1⟩ : ∃ g ∈ (E₀.subgroupOf M).map a, g ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : (E₀.subgroupOf M).map a = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    have htop : MSP.fixSp ((E₀.subgroupOf M).map a) = ⊤ := by
      rw [hbot]
      ext v
      simp [MSP.mem_fixSp, MSP.mat_one]
    rw [htop] at hfix
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    have h3 := MSP.finrank_perp p
    rw [← hfix, finrank_top, h4] at h3
    have hp1 : Module.finrank F p = 1 := hp
    omega
  have hTE : ∀ x ∈ (E₀.subgroupOf M).map a, x ∈ (T.subgroupOf M).map a := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hE₀T (Subgroup.mem_subgroupOf.1 hm)), rfl⟩
  rw [S5B.uSub_baseA h, ← imM_inf_centralizer h.le _ hE₀M]
  suffices hJ : ∃ J₀ : Subgroup G, J₀ ≤ M ∧
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le J₀ ∧
      (J₀.subgroupOf M).map a ≤ MSP.fixer p by
    obtain ⟨J₀, hJ₀M, hJJ, hJp⟩ := hJ
    refine hJJ.trans (S5B.imM_le_normalizer h.le ?_)
    refine S5B.le_normalizer_uq_inf_centralizer h hd hE₀M hJ₀M ?_
    rw [hfix]
    exact hJp.trans (S5B.fixer_le_stab_perp p)
  rcases h54 G M T L h hmin hb k F _ _ a hd with
    ⟨-, ⟨l, hl, hTl, hJl⟩, -⟩ | ⟨-, hJT, p₀, hp₀, hTq⟩
  · have hgl : g ∈ MSP.stab l := by
      obtain ⟨m, hm, rfl⟩ := hTE g hgE
      have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := by
        rw [puAmalgam.qv_baseB]
        exact ⟨m, hm, rfl⟩
      obtain ⟨m', hm', he⟩ := hTl hmT
      rw [(puAmalgam h.le).ofA_injective he] at hm'
      exact hm'
    have hpl := S5B.le_of_mem_xPoint_stab hp hl (hxP hgE) hgl hg1
    refine ⟨((MSP.qLine l).comap a).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · refine hJl.trans ?_
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.2 ⟨m, hm, rfl⟩, rfl⟩
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 hm
      rw [Subtype.ext he] at hm'
      exact MSP.fixer_antitone hpl hm'
  · have hTq' : (T.subgroupOf M).map a = MSP.qPoint p₀ := by
      rw [← hTq, S5.vIm, puAmalgam.qv_baseB]
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m, ⟨m, hm, rfl⟩, rfl⟩
      · rintro ⟨m, ⟨m', hm', he⟩, rfl⟩
        rw [(puAmalgam h.le).ofA_injective he] at hm'
        exact ⟨m, hm', rfl⟩
    have hpp : p = p₀ :=
      S5B.eq_of_mem_xPoint_qPoint hp hp₀ (hxP hgE) (hTq' ▸ hTE g hgE) hg1
    refine ⟨T, h.le, ?_, ?_⟩
    · rw [hJT, puAmalgam.qv_baseB]
    · rw [hTq', ← hpp]
      exact MSP.qPoint_le_fixer p

theorem jOff_le_normalizer_of_relIndex (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L γ) = 2 ^ k) :
    S5.jOff h.le L (2 ^ k) γ ε ≤ Subgroup.normalizer
      ((S5.uSub h.le L γ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :
        Subgroup _) : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hEE : E = E'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hrel ⊢
  rw [qv_smul, map_conj_le_map_conj_iff] at hE
  rw [S5B.uSub_smul h.le hLn, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hrel
  rw [S5B.jOff_smul h.le hLn, S5B.uSub_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, normalizer_map_conj,
    map_conj_le_map_conj_iff]
  exact jOff_le_normalizer_of_relIndex_baseA h hmin hb hd h54 hE hrel

end Vertex

end S510

end CFSG.Quasithin.MS93
