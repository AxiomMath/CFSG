module

public import CFSG.Quasithin.MS93.S5BExcl
public import CFSG.Quasithin.MS93.M15Lift
public import CFSG.Quasithin.MS93.S5BNat

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

namespace S5B

section Sp4

variable {F : Type} [Field F] [Fintype F]

theorem fixSp_eq_of_le_qLine {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    {A : Subgroup (MSP.Sp4 F)} (hA : A ≤ MSP.qLine l) (hcard : Nat.card F < Nat.card A) :
    MSP.fixSp A = l := by
  have hlA : l ≤ MSP.fixSp A := MSP.le_fixer_iff.1 hA
  have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
  have hl2 : Module.finrank F l = 2 := hl.1
  by_contra hne
  have hlt : l < MSP.fixSp A := lt_of_le_of_ne hlA (Ne.symm hne)
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have hle4 := Submodule.finrank_le (MSP.fixSp A)
  rw [h4] at hle4
  have hAfix : A ≤ MSP.fixer (MSP.fixSp A) := MSP.le_fixer_iff.2 le_rfl
  rcases (show Module.finrank F (MSP.fixSp A) = 3 ∨ Module.finrank F (MSP.fixSp A) = 4 by
    omega) with h3' | h4'
  ·
    set p := MSP.perp (MSP.fixSp A) with hp
    have hpp : MSP.IsPoint p := by
      have := MSP.finrank_perp (MSP.fixSp A)
      rw [← hp] at this
      change Module.finrank F p = 1
      omega
    have hAx : A ≤ MSP.xPoint p := by
      rw [MSP.xPoint, hp, MSP.perp_perp]
      exact hAfix
    have hle : Nat.card A ≤ Nat.card F :=
      (Subgroup.card_le_of_le hAx).trans (MSP.card_xPoint hpp).le
    omega
  ·
    have htop : MSP.fixSp A = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4']; exact h4.symm)
    have hbot : A = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
      refine MSP.ext_mulVec fun v => ?_
      rw [MSP.mat_one, Matrix.one_mulVec]
      exact (MSP.mem_fixSp.1 (htop ▸ Submodule.mem_top) g hg)
    rw [hbot, Subgroup.card_bot] at hcard
    have : 0 < Nat.card F := Nat.card_pos
    omega

end Sp4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem zm_eq_zh_sup_uSub (h : PUHyp M T L) {γ ε : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) :
    ZM _ γ = ZH _ ε ⊔ S5.uSub h.le L γ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hγ hγε
  rw [zm_smul, zh_smul, uSub_smul h.le hLn, ← Subgroup.map_sup, puAmalgam.zm_baseA,
    puAmalgam.zh_baseB, uSub_baseA h,
    show normalClosureIn M (omegaOneCenterOf T) = omegaOneCenterOf T ⊔ Uq M T L from h.Z0q_eq_sup,
    imM_sup_of_le h.le ((PU.omegaOneCenterOf_le T).trans h.le) (Uq_le h.L_le)]

omit [Finite G] [Fintype F] in
theorem jOff_le_qv (hTM : T ≤ M) (L : Subgroup G) (q : ℕ) (γ ε : Vtx (puAmalgam hTM)) :
    S5.jOff hTM L q γ ε ≤ Qv _ ε :=
  iSup₂_le fun _ hE => hE.1.1

theorem qv_le_jOff (h : PUHyp M T L) {q : ℕ} (hq : 1 ≤ q) {γ ε : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) :
    Qv _ γ ≤ S5.jOff h.le L q γ ε := by
  classical
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hε : ¬ IsMVtx _ ε := (isMVtx_iff_of_adj _ hγε).1 hγ
  have hQε : Qv _ γ ≤ Qv _ ε := qv_le_qv _ hyp hγ hγε
  have : Finite ↥(Qv (puAmalgam h.le) ε) := finite_qv _ hyp hε
  have hUQ : S5.uSub h.le L γ ≤ Subgroup.centralizer (Qv (puAmalgam h.le) γ : Set _) := by
    refine Subgroup.le_centralizer_iff.1 ((qv_le_centralizer_xm _ γ).trans
      (Subgroup.centralizer_le ?_))
    exact (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L γ).trans
      (stab_le_normalizer_zm _ _))).trans (zm_le_xm _ hyp hb0 hγ)
  set P : Subgroup (puAmalgam h.le).Universal → Prop := S5.IsOffCand h.le L q γ ε with hP
  have hPQ : P (Qv _ γ) := by
    refine ⟨hQε, ?_, ?_⟩
    · have h1 : (Subgroup.centralizer (Qv (puAmalgam h.le) γ : Set _)).relIndex
          (S5.uSub h.le L γ) = 1 := Subgroup.relIndex_eq_one.2 hUQ
      rw [h1]
      exact Nat.one_le_iff_ne_zero.2 (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    · have h1 : (Subgroup.centralizer (Qv (puAmalgam h.le) γ : Set _)).relIndex
          (S5.uSub h.le L γ) = 1 := Subgroup.relIndex_eq_one.2 hUQ
      rw [h1]
      exact Nat.one_le_pow _ _ (by omega)
  set N := Nat.card ↥(Qv (puAmalgam h.le) ε)
  have hex : ∃ n ≤ N, ∃ E, P E ∧ Nat.card E = n :=
    ⟨Nat.card ↥(Qv (puAmalgam h.le) γ), Subgroup.card_le_of_le hQε, _, hPQ, rfl⟩
  set n₀ := Nat.findGreatest (fun n => ∃ E, P E ∧ Nat.card E = n) N with hn₀
  obtain ⟨E, hE, hEn⟩ : ∃ E, P E ∧ Nat.card E = n₀ := by
    obtain ⟨n, hn, hn'⟩ := hex
    exact Nat.findGreatest_spec (P := fun n => ∃ E, P E ∧ Nat.card E = n) hn hn'
  have hmax : ∀ E', P E' → Nat.card E' ≤ Nat.card E := by
    intro E' hE'
    rw [hEn]
    exact Nat.le_findGreatest (Subgroup.card_le_of_le hE'.1) ⟨E', hE', rfl⟩
  have hEoff : E ∈ S5.offSet h.le L q γ ε := ⟨hE, hmax⟩
  have hQE : Qv _ γ ≤ E := by
    by_contra hQE
    have hlt : E < E ⊔ Qv _ γ := lt_of_le_of_ne le_sup_left fun he => hQE (he ▸ le_sup_right)
    have hEQ : E ⊔ Qv _ γ ≤ Qv _ ε := sup_le hE.1 hQε
    have : Finite ↥(E ⊔ Qv (puAmalgam h.le) γ) := Finite.of_injective
      (Subgroup.inclusion hEQ) (Subgroup.inclusion_injective hEQ)
    have hcand : P (E ⊔ Qv _ γ) := by
      have hC : S5.uSub h.le L γ ⊓ Subgroup.centralizer ((E ⊔ Qv (puAmalgam h.le) γ :
          Subgroup _) : Set _) = S5.uSub h.le L γ ⊓ Subgroup.centralizer (E : Set _) := by
        refine le_antisymm (inf_le_inf_left _
          (Subgroup.centralizer_le (le_sup_left : E ≤ E ⊔ Qv (puAmalgam h.le) γ))) ?_
        refine le_inf inf_le_left (Subgroup.le_centralizer_iff.1 (sup_le ?_ ?_))
        · exact Subgroup.le_centralizer_iff.1 inf_le_right
        · exact (Subgroup.le_centralizer_iff.1 hUQ).trans (Subgroup.centralizer_le inf_le_left)
      have hrel : (Subgroup.centralizer ((E ⊔ Qv (puAmalgam h.le) γ : Subgroup _) :
          Set _)).relIndex (S5.uSub h.le L γ) =
          (Subgroup.centralizer (E : Set _)).relIndex (S5.uSub h.le L γ) := by
        rw [← Subgroup.inf_relIndex_right, inf_comm, hC, inf_comm, Subgroup.inf_relIndex_right]
      refine ⟨hEQ, ?_, ?_⟩
      · rw [hrel]
        refine hE.2.1.trans (Subgroup.relIndex_le_of_le_right le_sup_left ?_)
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      · rw [hrel]
        exact hE.2.2
    have h1 := hmax _ hcand
    have h2 := Subgroup.card_lt_of_lt hlt
    omega
  exact hQE.trans (le_iSup₂ (f := fun E (_ : E ∈ S5.offSet h.le L q γ ε) => E) E hEoff)

theorem commutator_uq_le_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {J₀ : Subgroup G} (hJ₀M : J₀ ≤ M)
    (hJ₀ : (J₀.subgroupOf M).map a ≤ MSP.qLine l) :
    ⁅Uq M T L, J₀⁆ ≤ Subgroup.centralizer (J₀ : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  rw [Subgroup.commutator_le]
  intro u hu j hj
  have hju : j * u * j⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn (hJ₀M hj)) u).1 hu
  have hw : ⁅u, j⁆ ∈ Uq M T L := by
    have e : ⁅u, j⁆ = (j * u * j⁻¹ * u⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem (mul_mem hju (inv_mem hu))
  have hvec : c.vec ⟨⁅u, j⁆, hw⟩ ∈ l := by
    have e : (⟨⁅u, j⁆, hw⟩ : ↥(Uq M T L)) =
        (⟨j * u * j⁻¹ * u⁻¹, mul_mem hju (inv_mem hu)⟩ : ↥(Uq M T L))⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    rw [e, c.vec_inv]
    have h1 := c.vec_commutator ⟨j, hJ₀M hj⟩ ⟨u, hu⟩ hju
    rw [h1]
    refine neg_mem (MSP.commSp_qLine_le hl ?_)
    exact MSP.sub_mem_commSp (hJ₀ ⟨⟨j, hJ₀M hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩) _
  rw [Subgroup.mem_centralizer_iff]
  intro j' hj'
  have hj'w : j' * ⁅u, j⁆ * j'⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hUn (hJ₀M hj')) _).1 hw
  have hfix : MSP.mat (a ⟨j', hJ₀M hj'⟩) *ᵥ c.vec ⟨⁅u, j⁆, hw⟩ = c.vec ⟨⁅u, j⁆, hw⟩ :=
    hJ₀ ⟨⟨j', hJ₀M hj'⟩, Subgroup.mem_subgroupOf.2 hj', rfl⟩ _ hvec
  have hz : j' * ⁅u, j⁆ * j'⁻¹ * ⁅u, j⁆⁻¹ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← c.vec_eq_zero_iff ⟨_, mul_mem hj'w (inv_mem hw)⟩]
    have h1 := c.vec_commutator ⟨j', hJ₀M hj'⟩ ⟨⁅u, j⁆, hw⟩ hj'w
    rw [h1, hfix, sub_self]
  have := hlift j' (hJ₀M hj') _ hw hz.2
  calc j' * ⁅u, j⁆ = j' * ⁅u, j⁆ * j'⁻¹ * j' := by group
    _ = ⁅u, j⁆ * j' := by rw [this]

section Center

universe u v

theorem conj_eq_of_mem_stabCenter {A B : Type u} {C : Type v} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {g z : X.Universal} (hg : g ∈ stab X δ)
    (hz : z ∈ stabCenter X δ) : g * z * g⁻¹ = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  have e3 : g * (y : X.Universal) = y * g :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨g, hg⟩)
  show g * (y : X.Universal) * g⁻¹ = y
  rw [e3, mul_inv_cancel_right]

end Center

omit [Finite G] [Fintype F] in
theorem vPre_eq_imM (hTM : T ≤ M) (Y : Subgroup ↥(StatedSp 2 F)) :
    S5.vPre hTM a Y = imM hTM ((Y.comap a).map M.subtype) :=
  (imM_map_subtype hTM _).symm

omit [Finite G] [Fintype F] in
theorem map_preimage_eq (ha : Function.Surjective a) (Y : Subgroup ↥(StatedSp 2 F)) :
    ((((Y.comap a).map M.subtype).subgroupOf M).map a) = Y := by
  rw [PU.map_subtype_subgroupOf, Subgroup.map_comap_eq_self_of_surjective ha]

omit [Finite G] [Fintype F] in
theorem vIm_imM (hTM : T ≤ M) (K : Subgroup G) :
    S5.vIm hTM a (imM hTM K) = (K.subgroupOf M).map a := by
  rw [S5.vIm, imM, Subgroup.comap_map_eq_self_of_injective (puAmalgam hTM).ofA_injective]

omit [Finite G] [Fintype F] in
theorem vIm_le_of_le_vPre (hTM : T ≤ M) {Y : Subgroup ↥(StatedSp 2 F)}
    {J : Subgroup (puAmalgam hTM).Universal} (hJ : J ≤ S5.vPre hTM a Y) : S5.vIm hTM a J ≤ Y := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m', hm', he⟩ := hJ hm
  rw [(puAmalgam hTM).ofA_injective he] at hm'
  exact hm'

theorem commutator_uSub_le_centralizer_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {J : Subgroup (puAmalgam h.le).Universal}
    (hJ : J ≤ S5.vPre h.le a (MSP.qLine l)) :
    ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), J⁆ ≤ Subgroup.centralizer (J : Set _) := by
  set J₀ : Subgroup G := ((MSP.qLine l).comap a).map M.subtype with hJ₀
  have hJ₀M : J₀ ≤ M := Subgroup.map_subtype_le _
  rw [vPre_eq_imM, ← hJ₀] at hJ
  have hq := commutator_uq_le_centralizer h hd hl hJ₀M
    (map_preimage_eq hd.2.2.1 (MSP.qLine l)).le
  refine (Subgroup.commutator_mono le_rfl hJ).trans ((?_ : _ ≤ _).trans
    (Subgroup.centralizer_le hJ))
  rw [uSub_baseA h, ← imM_commutator h.le (Uq_le h.L_le) hJ₀M, ← inf_eq_left.2 hq,
    imM_inf_centralizer h.le _ hJ₀M]
  exact inf_le_right

theorem relIndex_le_card_vIm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (baseB (puAmalgam h.le))) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex E ≤ Nat.card (S5.vIm h.le a E) := by
  rw [puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := exists_eq_imM h.le hE
  rw [qv_baseA_eq h, relIndex_imM h.le hE₀M, vIm_imM, ← Subgroup.relIndex_ker,
    ← Subgroup.relIndex_subgroupOf hE₀M, ← Subgroup.inf_relIndex_right a.ker]
  refine Subgroup.relIndex_le_of_le_left ?_ ?_
  · rintro m ⟨hmk, hmE⟩
    obtain ⟨n, hn⟩ := h.isPGroup ⟨m, hE₀T (Subgroup.mem_subgroupOf.1 hmE)⟩
    exact Subgroup.mem_subgroupOf.2 (mem_pCoreOf_of_ker h hd hmk
      ⟨n, by simpa using congrArg Subtype.val hn⟩)
  · rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite

theorem uSub_inf_centralizer_le_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {J : Subgroup (puAmalgam h.le).Universal}
    (hJ : J ≤ S5.vPre h.le a (MSP.qLine l)) (hcard : 2 ^ k < Nat.card (S5.vIm h.le a J)) :
    S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (J : Set _) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hfixJ : MSP.fixSp (S5.vIm h.le a J) = l :=
    fixSp_eq_of_le_qLine hl (vIm_le_of_le_vPre h.le hJ) (hFq ▸ hcard)
  set J₀ : Subgroup G := ((MSP.qLine l).comap a).map M.subtype with hJ₀
  have hJ₀M : J₀ ≤ M := Subgroup.map_subtype_le _
  have hJst : J ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA, vPre_eq_imM, ← hJ₀] at *
    exact hJ.trans (imM_mono h.le hJ₀M |>.trans (puAmalgam.stab_baseA h.le).ge)
  obtain ⟨J₁, -, hJ₁M, rfl⟩ := exists_eq_imM h.le hJst
  rw [vIm_imM] at hfixJ
  rw [vPre_eq_imM, ← hJ₀, uSub_baseA h, ← imM_inf_centralizer h.le _ hJ₁M]
  have hsub : Uq M T L ⊓ Subgroup.centralizer (J₁ : Set G) ≤
      Uq M T L ⊓ Subgroup.centralizer (J₀ : Set G) := by
    rintro u ⟨hu, huJ⟩
    refine ⟨hu, (mem_centralizer_iff_vec h hlift c hJ₀M ⟨u, hu⟩).2 ?_⟩
    rw [map_preimage_eq hd.2.2.1, MSP.fixSp_qLine hl, ← hfixJ]
    exact (mem_centralizer_iff_vec h hlift c hJ₁M ⟨u, hu⟩).1 huJ
  refine (imM_mono h.le hsub).trans ?_
  rw [imM_inf_centralizer h.le _ hJ₀M]
  exact inf_le_right

theorem commutator_zm_qv_le_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    {l : Submodule F (MSP.V4 F)} (hc56 : S5.Case56 h (2 ^ k) a δ l)
    (hXZ : XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _)) :
    ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hJδ, hl, -, hJl⟩ := hc56
  set J := S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJ
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hk1 := hd.1
  have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ J :=
    qv_le_jOff h (Nat.one_le_two_pow) hα hαβ
  have hJT : J ≤ Qv _ (baseB (puAmalgam h.le)) := jOff_le_qv h.le L _ _ _
  obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ hαβ.symm hβδ
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
  have hJg : J.map (MulAut.conj g).toMonoidHom = J := by
    have := jOff_smul h.le hLn (2 ^ k) g (baseA (puAmalgam h.le)) (baseB _)
    rw [hgα, hgβ, hJδ] at this
    exact this.symm
  have hquadδ : ⁅S5.uSub h.le L δ, J⁆ ≤ Subgroup.centralizer (J : Set _) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (commutator_uSub_le_centralizer_baseA h hd hl hJl)
    rw [Subgroup.map_commutator, ← PU.centralizer_map_mulEquiv, ← uSub_smul h.le hLn, hgα,
      hJg] at h1
    exact h1
  have hZδ := zm_eq_zh_sup_uSub h hδ hβδ.symm
  have hδst : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hUδT : S5.uSub h.le L δ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
      (stab_le_normalizer_zm _ _))).trans ((zm_le_qv_self _ hδ hb0).trans
        (qv_le_qv _ hyp hδ hβδ.symm))
  have hZβc : ZH _ (baseB (puAmalgam h.le)) ≤
      Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) :=
    (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
  have hZJ : ⁅ZM _ δ, J⁆ ≤ ⁅S5.uSub h.le L δ, J⁆ := by
    rw [Subgroup.commutator_le]
    intro z hz j hj
    rw [hZδ] at hz
    have hn : ZH _ (baseB (puAmalgam h.le)) ≤
        Subgroup.normalizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal) :=
      ((PU.omegaOneCenterOf_le _).trans hδst).trans
        (le_normalizer_commutator (stab_le_normalizer_zm _ _)
          (stab_le_normalizer_puTrans h.le hLn δ))
    have hz' : z ∈ ((ZH _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) *
        (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hz
    obtain ⟨z₀, hz₀, u, hu, rfl⟩ := hz'
    have hc₀ : ∀ t ∈ Qv _ (baseB (puAmalgam h.le)), z₀ * t = t * z₀ := fun t ht =>
      (Subgroup.mem_centralizer_iff.1 (hZβc hz₀) t ht).symm
    have e : ⁅z₀ * u, j⁆ = ⁅u, j⁆ := by
      simp only [commutatorElement_def]
      have h1 := hc₀ (u * j * u⁻¹) (mul_mem (mul_mem (hUδT hu) (hJT hj)) (inv_mem (hUδT hu)))
      calc z₀ * u * j * (z₀ * u)⁻¹ * j⁻¹ = z₀ * (u * j * u⁻¹) * z₀⁻¹ * j⁻¹ := by group
        _ = u * j * u⁻¹ * j⁻¹ := by rw [h1]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu hj
  have hdα : (puAmalgam h.le).treeGraph.dist δ (baseA _) < critDist (puAmalgam h.le) := by
    have := dist_triangle _ δ (baseB (puAmalgam h.le)) (baseA _)
    rw [dist_eq_one_of_adj _ hβδ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    omega
  have hZQ : ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)) := zm_le_qv_of_dist_lt _ hδ hdα
  have hcomm : ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ Subgroup.centralizer (J : Set _) :=
    (Subgroup.commutator_mono le_rfl hQJ).trans (hZJ.trans hquadδ)
  have hcommZ : ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ ZM _ δ :=
    commutator_le_left_of_le_normalizer ((qv_le_qv _ hyp hα hαβ).trans
      (hδst.trans (stab_le_normalizer_zm _ _)))
  have hX : ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hZQ (hcommZ hx), ?_⟩, ?_⟩
    · exact Subgroup.centralizer_le hQJ (hcomm hx)
    · exact (isElemAbelian_zm _ hyp hb0 hδ).2 x (hcommZ hx)
  refine le_inf hX ?_
  have hcardJ : 2 ^ k < Nat.card (S5.vIm h.le a J) := by
    rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, -, hq2⟩ | ⟨-, hJT', p₀, hp₀, hTq⟩
    · rw [← hJ] at hq2
      have h1 := relIndex_le_card_vIm h hd hJT
      have h2 : 2 ^ k < (2 ^ k) ^ 2 := by
        have : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
        nlinarith
      omega
    · exfalso
      have hle : S5.vIm h.le a J ≤ MSP.qLine l := vIm_le_of_le_vPre h.le hJl
      rw [hJ, hJT', hTq] at hle
      have h1 := MSP.fixSp_antitone hle
      rw [MSP.fixSp_qLine hl, MSP.fixSp_qPoint hp₀] at h1
      have h2 := Submodule.finrank_mono h1
      rw [hl.1, show Module.finrank F p₀ = 1 from hp₀] at h2
      omega
  have hUJ := uSub_inf_centralizer_le_baseA h hd hl hJl hcardJ
  have hcen : XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := by
    rintro x ⟨-, ⟨y, hy, rfl⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwst : w ∈ stab _ (baseA (puAmalgam h.le)) := by
      rw [puAmalgam.stab_baseA, vPre_eq_imM] at *
      exact imM_mono h.le (Subgroup.map_subtype_le _) hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨w, hwst⟩)
  intro x hx
  have hxX : x ∈ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊔
      XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) := hXZ ⟨hX hx, hcomm hx⟩
  have hstC : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (stabCenter _ (baseA (puAmalgam h.le)) : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [conj_eq_of_mem_stabCenter hg hz]
      exact hz
    · intro hz
      have := conj_eq_of_mem_stabCenter (inv_mem hg) hz
      have e : z = g * z * g⁻¹ := by
        rw [← this]
        group
      rw [e]
      exact hz
  have hUst : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ stab _ (baseA _) :=
    commutator_le_of_le ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _))
      (puTrans_le_stab h.le L _) |>.trans' le_rfl
  have hn : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      ((XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) : Subgroup _) : Set _) :=
    hUst.trans ((le_inf (stab_le_normalizer_xm _ _) hstC).trans
      (Subgroup.inf_normalizer_le_normalizer_inf))
  have hx' : x ∈ ((S5.uSub h.le L (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) *
      ((XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) : Subgroup _) : Set _)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
    exact hxX
  obtain ⟨u, hu, z, hz, hxuz⟩ := hx'
  have hzJ : z ∈ Subgroup.centralizer (J : Set (puAmalgam h.le).Universal) := by
    obtain ⟨-, ⟨y, hy, rfl⟩⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwst : w ∈ stab _ (baseA (puAmalgam h.le)) :=
      qv_le_stab_of_isMVtx _ hyp hα hαβ (hJT hw)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨w, hwst⟩)
  have huJ : u ∈ Subgroup.centralizer (J : Set (puAmalgam h.le).Universal) := by
    have : u = x * z⁻¹ := by rw [← hxuz]; group
    rw [this]
    exact mul_mem (hcomm hx) (inv_mem hzJ)
  rw [← hxuz]
  exact mul_mem (hUJ ⟨hu, huJ⟩) (hcen hz)

end S5B

end CFSG.Quasithin.MS93
