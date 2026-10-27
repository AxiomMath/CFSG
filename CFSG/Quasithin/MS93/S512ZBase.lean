module

public import CFSG.Quasithin.MS93.S5B56Z
public import CFSG.Quasithin.MS93.C56Red

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S512Z

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def Large (h : PUHyp M T L) (k : ℕ) (u m : Vtx (puAmalgam h.le)) : Prop :=
  2 ^ k < (Subgroup.centralizer (Qv _ m : Set (puAmalgam h.le).Universal)).relIndex
    (S5.uSub h.le L u)

theorem large_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (u m : Vtx (puAmalgam h.le)) : Large h k (g • u) (g • m) ↔ Large h k u m := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  unfold Large
  rw [S5B.uSub_smul h.le hLn, qv_smul, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem exists_mul_of_mem_zm (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h : PUHyp M T L)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {z : (puAmalgam h.le).Universal}
    (hz : z ∈ ZM _ (baseA (puAmalgam h.le))) :
    ∃ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)),
      ∃ c ∈ stabCenter _ (baseA (puAmalgam h.le)), u * c = z := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hXα := S5B.xm_eq_uSub_sup h hXU hZc
  have hXZα := S5B.xm_eq_zm h hXU hZc
  rw [← hXZα, hXα] at hz
  have hn : XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) ≤
      Subgroup.normalizer (S5.uSub h.le L (baseA (puAmalgam h.le)) : Set _) := by
    refine inf_le_right.trans ((?_ : stabCenter _ _ ≤ stab _ _).trans
      (le_normalizer_commutator (stab_le_normalizer_zm _ _)
        (stab_le_normalizer_puTrans h.le hLn _)))
    rintro x ⟨y, -, rfl⟩
    exact y.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hz
  obtain ⟨u, hu, c, hc', rfl⟩ := hz
  exact ⟨u, hu, c, hc'.2, rfl⟩

theorem mem_centralizer_of_mem_stabCenter {A B C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {α : Vtx X} {c : X.Universal} (hc : c ∈ stabCenter X α)
    {K : Subgroup X.Universal} (hK : K ≤ stab X α) : c ∈ Subgroup.centralizer (K : Set _) :=
  Subgroup.mem_centralizer_iff.2 fun _ hy => S5C56.mul_comm_of_mem_stabCenter hc (hK hy)

theorem lt_relIndex_centralizer_qLine (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) :
    2 ^ k < (Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (baseA (puAmalgam h.le))) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  set J₀ : Subgroup G := ((MSP.qLine l).comap a).map M.subtype with hJ₀
  have hJ₀M : J₀ ≤ M := Subgroup.map_subtype_le _
  rw [S5B.vPre_eq_imM h.le, S5B.uSub_baseA h,
    S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hJ₀M]
  have hrel := S5B.relIndex_centralizer_mul_card h hlift c hJ₀M
  rw [S5B.map_preimage_eq hd.2.2.1, MSP.fixSp_qLine hl, MSP.card_V4, hFq,
    Module.natCard_eq_pow_finrank (K := F), hFq, hl.1] at hrel
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  set r := (Subgroup.centralizer (J₀ : Set G)).relIndex (Uq M T L) with hr
  have hpos : 0 < (2 ^ k) ^ 2 := by positivity
  have hr2 : r = (2 ^ k) ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hrel]
    ring
  rw [hr2]
  nlinarith

theorem zz56_of_large (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) (hlg : Large h k (baseA _) δ) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  obtain ⟨hJδ, hl', -, hJl⟩ := hl
  have hQ₁st : S5.vPre h.le a (MSP.qLine l) ≤ stab _ (baseA (puAmalgam h.le)) :=
    S5.vPre_le_stab h _
  have hQδJ : Qv _ δ ≤ S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :=
    (S5B.qv_le_jOff h Nat.one_le_two_pow hδM hβδ.symm).trans hJδ.le
  have hdδ : (puAmalgam h.le).treeGraph.dist δ (baseA _) ≤ 2 := by
    have := dist_triangle _ δ (baseB (puAmalgam h.le)) (baseA _)
    rwa [dist_eq_one_of_adj _ hβδ.symm, dist_eq_one_of_adj _ (adj_baseA_baseB _).symm] at this
  have hQδst : Qv _ δ ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_dist_le_two _ hyp hδM hdδ
  intro w hw
  by_contra hwQ
  obtain ⟨u, hu, c, hc', rfl⟩ := exists_mul_of_mem_zm hZc h hXU hw.1
  have huQ : u ∉ Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := fun hu' =>
    hwQ (mul_mem hu' (mem_centralizer_of_mem_stabCenter hc' hQ₁st))
  have huδ : u ∈ Subgroup.centralizer (Qv _ δ : Set (puAmalgam h.le).Universal) := by
    have e : u = u * c * c⁻¹ := by group
    rw [e]
    exact mul_mem (zm_le_centralizer_qv _ hyp hδM hw.2)
      (inv_mem (mem_centralizer_of_mem_stabCenter hc' hQδst))
  have hn : ¬ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (Qv _ δ : Set _) ≤
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := fun hle =>
    huQ (hle ⟨hu, huδ⟩)
  exact absurd hlg (not_lt.2 (S5C56.relIndex_centralizer_le_of_not_le h hd hl' (hQδJ.trans hJl) hn))

theorem uSub_le_zm' (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    S5.uSub h.le L δ ≤ ZM _ δ :=
  commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
    (stab_le_normalizer_zm _ _))

theorem xm_eq_zm_at (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h : PUHyp M T L)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    XM _ δ = ZM _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [xm_smul, zm_smul, S5B.xm_eq_zm h hXU hZc]

theorem exists_mem_not_centralizer (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) (hsm : ¬ Large h k (baseA _) δ) :
    ∃ w ∈ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ, w ∉ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
        Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  obtain ⟨-, hl', -, hJl⟩ := hl
  have hcardJ := S5C56.lt_card_vIm_jOff h54 h hmin hb hd hl' hJl
  have hUJ := S5B.uSub_inf_centralizer_le_baseA h hd hl' hJl hcardJ
  by_contra hcon
  push Not at hcon
  have hCδ : Qv _ (baseB (puAmalgam h.le)) ⊓
      Subgroup.centralizer (ZM _ δ : Set (puAmalgam h.le).Universal) = Qv _ δ :=
    h.centHyp δ (baseB _) hδM hβδ.symm
  have hUβ : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (uSub_le_zm' h _).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ hyp hα hαβadj))
  have hXZδ := xm_eq_zm_at hZc h hXU hδM
  have hle : S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (Qv _ δ : Set (puAmalgam h.le).Universal) ≤
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) := by
    rintro u ⟨hu, huδ⟩
    have huQδ : u ∈ Qv _ δ := by
      rw [← hCδ]
      exact ⟨hUβ hu, Subgroup.centralizer_le (zm_le_qv_self _ hδM hb0) huδ⟩
    have huX : u ∈ XM _ δ :=
      mem_omegaOneCenterOf huQδ (fun y hy => Subgroup.mem_centralizer_iff.1 huδ y hy)
        (sq_eq_one_of_mem_omegaOneCenterOf (zm_le_xm _ hyp hb0 hα (uSub_le_zm' h _ hu)))
    rw [hXZδ] at huX
    exact hUJ ⟨hu, hcon u ⟨uSub_le_zm' h _ hu, huX⟩⟩
  have hUβ' : Finite ↥(S5.uSub h.le L (baseA (puAmalgam h.le))) := by
    have : Finite ↥(Qv (puAmalgam h.le) (baseB (puAmalgam h.le))) :=
      finite_qv _ hyp (not_isMVtx_baseB _)
    exact Finite.of_injective (Subgroup.inclusion hUβ) (Subgroup.inclusion_injective hUβ)
  have h1 : (Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (baseA (puAmalgam h.le))) ≤
      (Subgroup.centralizer (Qv _ δ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (baseA (puAmalgam h.le))) := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) :
        Set (puAmalgam h.le).Universal)),
      ← Subgroup.inf_relIndex_right (Subgroup.centralizer (Qv _ δ :
        Set (puAmalgam h.le).Universal))]
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨hle ⟨hx.2, hx.1⟩, hx.2⟩) ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  exact hsm ((lt_relIndex_centralizer_qLine h hd hl').trans_le h1)

theorem not_large_of_mem (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) {w : (puAmalgam h.le).Universal}
    (hw : w ∈ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ)
    (hwJ : w ∉ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
        Set (puAmalgam h.le).Universal)) :
    ¬ Large h k (baseA _) δ := by
  intro hlg
  exact hwJ (Subgroup.centralizer_le hl.2.2.2 (zz56_of_large hZc h hd hXU hβδ hl hlg hw))

omit [Fintype F] in
theorem case56_smul (h : PUHyp M T L) {t : (puAmalgam h.le).Universal}
    (ht : t ∈ stab _ (baseB (puAmalgam h.le)))
    (htJ : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))
    {ν : Vtx (puAmalgam h.le)} {l : Submodule F (MSP.V4 F)} (hν : S5.Case56 h (2 ^ k) a ν l) :
    S5.Case56 h (2 ^ k) a (t • ν) l := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  refine ⟨?_, hν.2⟩
  have e := S5B.jOff_smul h.le hLn (2 ^ k) t ν (baseB _)
  rw [(mem_stab _).1 ht, hν.1] at e
  rw [e, htJ]

omit [Fintype F] in
theorem map_jOff_eq_of_smul (h : PUHyp M T L) {t : (puAmalgam h.le).Universal}
    (ht : t ∈ stab _ (baseB (puAmalgam h.le))) {δ : Vtx (puAmalgam h.le)}
    (hJ : S5.jOff h.le L (2 ^ k) δ (baseB _) = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))
    (htα : t • baseA (puAmalgam h.le) = δ) :
    (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have e := S5B.jOff_smul h.le hLn (2 ^ k) t (baseA (puAmalgam h.le)) (baseB _)
  rw [htα, (mem_stab _).1 ht, hJ] at e
  exact e.symm

omit [Fintype F] in
theorem map_jOff_inv_eq (h : PUHyp M T L) {t : (puAmalgam h.le).Universal}
    (htJ : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) :
    (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t⁻¹).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
  calc _ = ((S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
        (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by rw [htJ]
    _ = _ := map_conj_inv_map_conj _ t

theorem not_large_smul (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) (hsm : ¬ Large h k (baseA _) δ)
    {s : (puAmalgam h.le).Universal} (hs : s ∈ stab _ (baseB (puAmalgam h.le)))
    (hsJ : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj s).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _))
    (hsδ : s • δ = baseA _) : ¬ Large h k (baseA _) (s • baseA (puAmalgam h.le)) := by
  obtain ⟨w, hw, hwJ⟩ := exists_mem_not_centralizer hZc h54 h hmin hb hd hXU hβδ hl hsm
  have hsβ : s • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hs
  have hβδ₁ : (puAmalgam h.le).treeGraph.Adj (baseB _) (s • baseA (puAmalgam h.le)) := by
    have := (adj_smul _ s _ _).2 (adj_baseA_baseB (puAmalgam h.le)).symm
    rwa [hsβ] at this
  have hl₁ := case56_smul h hs hsJ (ν := baseA (puAmalgam h.le)) (l := l)
    ⟨rfl, hl.2⟩
  have hsJ' := map_jOff_inv_eq h hsJ
  have hCJ : (Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _)).map
        (MulAut.conj s⁻¹).toMonoidHom =
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
        Set (puAmalgam h.le).Universal) := by
    rw [← PU.centralizer_map_mulEquiv, hsJ']
  refine not_large_of_mem hZc h hd hXU hβδ₁ hl₁ (w := s * w * s⁻¹) ⟨?_, ?_⟩ ?_
  · have h1 : w ∈ ZM _ δ := hw.2
    have e : ZM _ δ = (ZM _ (baseA (puAmalgam h.le))).map (MulAut.conj s⁻¹).toMonoidHom := by
      rw [← zm_smul, ← hsδ, inv_smul_smul]
    rw [e, mem_map_conj, inv_inv] at h1
    exact h1
  · rw [zm_smul]
    exact Subgroup.mem_map_of_mem _ hw.1
  · intro h0
    apply hwJ
    rw [← hCJ, mem_map_conj, inv_inv]
    exact h0

theorem large_symm (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    Large h k (baseA _) δ ↔ Large h k δ (baseA _) := by
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨t, ht, htα⟩ := exists_mem_stab_smul _ hαβadj.symm hβδ
  have htJ := map_jOff_eq_of_smul h ht hl.1 htα
  have htJ' := map_jOff_inv_eq h htJ
  have htβ' : t⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem ht)
  have e : Large h k δ (baseA _) ↔ Large h k (baseA _) (t⁻¹ • baseA (puAmalgam h.le)) := by
    rw [← large_smul h t⁻¹ δ (baseA _), ← htα, inv_smul_smul]
  rw [e]
  constructor
  · intro hlg
    by_contra hsm
    have hβδ₁ : (puAmalgam h.le).treeGraph.Adj (baseB _) (t⁻¹ • baseA (puAmalgam h.le)) := by
      have := (adj_smul _ t⁻¹ _ _).2 hαβadj.symm
      rwa [htβ'] at this
    have hl₁ := case56_smul h (inv_mem ht) htJ' (ν := baseA (puAmalgam h.le)) (l := l)
      ⟨rfl, hl.2⟩
    have := not_large_smul hZc h54 h hmin hb hd hXU hβδ₁ hl₁ hsm ht htJ (smul_inv_smul t _)
    rw [htα] at this
    exact this hlg
  · intro hlg
    by_contra hsm
    have hsδ : t⁻¹ • δ = baseA (puAmalgam h.le) := by rw [← htα, inv_smul_smul]
    exact not_large_smul hZc h54 h hmin hb hd hXU hβδ hl hsm (inv_mem ht) htJ' hsδ hlg

theorem relIndex_bSub_le_relIndex_centralizer (h32 : S32) (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)} (hδM : IsMVtx _ δ)
    (hdαδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2) :
    (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤
      (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _)).relIndex
        (S5.uSub h.le L δ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hUδZ : S5.uSub h.le L δ ≤ ZM _ δ := uSub_le_zm' h δ
  have hUδQ : S5.uSub h.le L δ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    hUδZ.trans (zm_le_qv_of_dist_lt _ hδM (by rw [tdist_comm, hdαδ]; omega))
  have hXL := S5C56.commutator_xm_puTrans_le_uSub h32 h
  have hUαZ : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ ZM _ (baseA (puAmalgam h.le)) :=
    uSub_le_zm' h _
  have hCB : Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) ⊓ S5.uSub h.le L δ ≤
      S5.bSub h.le L (baseA (puAmalgam h.le)) ⊓ S5.uSub h.le L δ := by
    rintro u ⟨huC, huU⟩
    have huX : u ∈ XM _ (baseA (puAmalgam h.le)) :=
      mem_omegaOneCenterOf (hUδQ huU) (fun y hy => Subgroup.mem_centralizer_iff.1 huC y hy)
        (sq_eq_one_of_mem_omegaOneCenterOf (zm_le_xm _ hyp hb0 hδM (hUδZ huU)))
    refine ⟨Subgroup.subset_closure ⟨?_, fun y hy => ?_⟩, huU⟩
    · exact le_iSup₂_of_le (f := fun ρ' (_ : ρ' ∈ {ρ' : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) ρ' ≤ 2}) =>
          Zv (puAmalgam h.le) ρ') δ hdαδ.le (zv_of_isMVtx _ hδM).ge (hUδZ huU)
    · exact hUαZ (hXL (Subgroup.commutator_mem_commutator huX hy))
  have hUδβ : S5.uSub h.le L δ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    hUδQ.trans (qv_le_qv _ hyp hα (adj_baseA_baseB _))
  have : Finite ↥(Qv (puAmalgam h.le) (baseB (puAmalgam h.le))) :=
    finite_qv _ hyp (not_isMVtx_baseB _)
  have : Finite ↥(S5.uSub h.le L δ) :=
    Finite.of_injective (Subgroup.inclusion hUδβ) (Subgroup.inclusion_injective hUδβ)
  rw [← Subgroup.inf_relIndex_right (S5.bSub h.le L (baseA (puAmalgam h.le))),
    ← Subgroup.inf_relIndex_right (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal))]
  exact Subgroup.relIndex_le_of_le_left hCB
    (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)

theorem large_of_lt_relIndex_bSub (h32 : S32) (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)} (hδM : IsMVtx _ δ)
    (hdαδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2)
    (hlt : 2 ^ k < (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ)) :
    Large h k δ (baseA _) :=
  hlt.trans_le (relIndex_bSub_le_relIndex_centralizer h32 h hb hδM hdαδ)

end S512Z

end CFSG.Quasithin.MS93
