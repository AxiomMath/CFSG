module

public import CFSG.Quasithin.MS93.S510Loc
public import CFSG.Quasithin.MS93.S59Base
public import CFSG.Quasithin.MS93.S59Mod

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

section Grp

variable {Γ : Type} [Group Γ]

theorem commutator_iSup_le {ι : Sort*} {K : ι → Subgroup Γ} {A N : Subgroup Γ}
    (hN : ∀ i, K i ≤ Subgroup.normalizer (N : Set Γ)) (hK : ∀ i, ⁅K i, A⁆ ≤ N) :
    ⁅⨆ i, K i, A⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = (y₁ * ⁅y₂, x⁆ * y₁⁻¹) * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 hy₁ _).1 (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, h₁⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (inv_mem (h₁ x hx))
        simpa using this }
  have hS : ⨆ i, K i ≤ S := iSup_le fun i y hy =>
    ⟨hN i hy, fun x hx => hK i (Subgroup.commutator_mem_commutator hy hx)⟩
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hy).2 x hx

theorem le_of_le_sup_commutator {P A S : Subgroup Γ} (hS : Group.IsNilpotent ↥S) (hPS : P ≤ S)
    (hSP : S ≤ Subgroup.normalizer (P : Set Γ)) (hAP : A ≤ P)
    (hSA : S ≤ Subgroup.normalizer (A : Set Γ)) (hle : P ≤ A ⊔ ⁅P, S⁆) : P ≤ A := by
  let f : Subgroup Γ → Subgroup Γ := fun D => ⁅D, S⁆
  let D : ℕ → Subgroup Γ := fun n => f^[n] P
  have hDs : ∀ n, D (n + 1) = ⁅D n, S⁆ := fun n => Function.iterate_succ_apply' f n P
  have hSS : S ≤ Subgroup.normalizer (S : Set Γ) := Subgroup.le_normalizer
  have hDn : ∀ n, S ≤ Subgroup.normalizer ((D n : Subgroup Γ) : Set Γ) := by
    intro n
    induction n with
    | zero => exact hSP
    | succ n ih => rw [hDs]; exact le_normalizer_commutator ih hSS
  have hDP : ∀ n, D n ≤ P := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [hDs]; exact (commutator_le_left_of_le_normalizer (hDn n)).trans ih
  have key : ∀ n, P ≤ A ⊔ D n := by
    intro n
    induction n with
    | zero => exact le_sup_right
    | succ n ih =>
      refine hle.trans (sup_le le_sup_left ((Subgroup.commutator_mono ih le_rfl).trans ?_))
      refine S5B.commutator_sup_le_of_le ?_ ?_ ?_ ?_
      · exact (hAP.trans hPS).trans (le_normalizer_sup hSA (hDn (n + 1)))
      · exact ((hDP n).trans hPS).trans (le_normalizer_sup hSA (hDn (n + 1)))
      · exact (commutator_le_left_of_le_normalizer hSA).trans le_sup_left
      · rw [← hDs]
        exact le_sup_right
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).1 hS
  have hlcs : ∀ m, D m ≤ S.lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact hPS
    | succ m ih =>
      rw [hDs, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih le_rfl
  have hD : D n = ⊥ := by
    have := hlcs n
    rw [hn] at this
    exact le_bot_iff.1 this
  have := key n
  rwa [hD, sup_bot_eq] at this

end Grp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Vertex

theorem exists_puTrans_mul_vtx (h : PUHyp M T L) {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδε : (puAmalgam h.le).treeGraph.Adj δ ε) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ δ) : ∃ l ∈ puTrans h.le L δ, ∃ t ∈ Qv _ ε, g = l * t := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨c, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hε : (puAmalgam h.le).treeGraph.Adj (baseA _) (c⁻¹ • ε) := by
    have := (adj_smul _ c⁻¹ _ _).2 hδε
    rwa [inv_smul_smul] at this
  have hg' : c⁻¹ * g * c ∈ stab _ (baseA (puAmalgam h.le)) := by
    rw [mem_stab_smul] at hg
    exact hg
  obtain ⟨l, hl, t, ht, hlt⟩ := S5B.exists_puTrans_mul h hε hg'
  refine ⟨c * l * c⁻¹, ?_, c * t * c⁻¹, ?_, ?_⟩
  · rw [puTrans_smul h.le hLn]
    exact ⟨l, hl, rfl⟩
  · have e : ε = c • (c⁻¹ • ε) := (smul_inv_smul c ε).symm
    rw [e, qv_smul]
    exact ⟨t, ht, rfl⟩
  · calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      _ = c * l * c⁻¹ * (c * t * c⁻¹) := by rw [hlt]; group

theorem uSub_inf_le_stabCenter (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    S5.uSub h.le L δ ⊓ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ δ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hUM := (sp4Lift_holds G M T L h k F _ _ a hd).2.1
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [S5B.uSub_smul h.le hLn, puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, S510.stabCenter_smul,
    map_conj_le_map_conj_iff, S5B.uSub_baseA h, S5B.puTrans_L_baseA h,
    ← imM_inf_centralizer h.le _ h.L_le, hUM, S5B.stabCenter_baseA]
  exact imM_mono h.le (inf_le_inf_right _ (Uq_le h.L_le))

theorem zm_le_stab_of_dist_le (h : PUHyp M T L) {ν δ : Vtx (puAmalgam h.le)} (hν : IsMVtx _ ν)
    (hd : (puAmalgam h.le).treeGraph.dist ν δ ≤ critDist (puAmalgam h.le)) :
    ZM _ ν ≤ stab _ δ := by
  have hb0 := h.critDist_pos
  rcases Nat.eq_zero_or_pos ((puAmalgam h.le).treeGraph.dist ν δ) with h0 | hpos
  · rw [← (dist_eq_zero_iff _).1 h0]
    exact (zm_le_qv_self _ hν hb0).trans (qv_le_stab _ _)
  · have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ ν 1) :=
      adj_geo_one _ (by rw [SimpleGraph.dist_comm]; exact hpos)
    have hd1 : (puAmalgam h.le).treeGraph.dist ν (geo _ δ ν 1) < critDist (puAmalgam h.le) := by
      rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [SimpleGraph.dist_comm]; omega),
        SimpleGraph.dist_comm]
      omega
    exact (zm_le_qv_of_dist_lt _ hν hd1).trans (qv_le_stab_of_adj _ hadj.symm)

end Vertex

section Config

theorem gamma_facts (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _) :
    IsMVtx _ γ ∧ (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 ∧
      geo _ γ (baseA (puAmalgam h.le)) 1 = baseB _ := by
  have hγ : IsMVtx _ γ := by
    have := isMVtx_iff_of_adj _ hβγ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hd2 := dist_eq_two_of_adj_adj _ (adj_baseA_baseB (puAmalgam h.le)) hβγ (Ne.symm hγα)
  refine ⟨hγ, hd2, (eq_geo_one _ hβγ.symm ?_).symm⟩
  rw [dist_eq_one_of_adj _ (adj_baseA_baseB (puAmalgam h.le)).symm, SimpleGraph.dist_comm, hd2]

theorem tZero_facts (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k) :
    ZM _ ξ ≤ tZero h.le L γ ∧ tZero h.le L γ ≤ stab _ γ ∧ IsPGroup 2 (tZero h.le L γ) ∧
      ¬ tZero h.le L γ ≤ Qv _ γ ∧
      (Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L γ) = 2 ^ k := by
  obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hβ := not_isMVtx_baseB (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hZξ : ZM _ ξ ≤ tZero h.le L γ := by
    refine zm_le_tZero h hb hαβ hβγ hξ.1 ?_ (by rw [SimpleGraph.dist_comm]; omega)
    rw [SimpleGraph.dist_comm]
    omega
  have hTst : tZero h.le L γ ≤ stab _ γ :=
    (tZero_le_qv h.le γ).trans ((qv_le_qv _ h.hyp20 hα hαβ).trans (qv_le_stab_of_adj _ hβγ))
  have hT2 : IsPGroup 2 (tZero h.le L γ) :=
    (isPGroup_qv _ h.hyp20 hβ).to_le ((tZero_le_qv h.le γ).trans (qv_le_qv _ h.hyp20 hα hαβ))
  have hTQ : ¬ tZero h.le L γ ≤ Qv _ γ := fun hle => hξ.2.2 (hZξ.trans hle)
  have hfin : Finite ↥(S5.uSub h.le L γ) := S5B.finite_of_le_qv h hγ
    ((S5B.uSub_le_zm h.le γ).trans (zm_le_qv_self _ hγ h.critDist_pos))
  have h1 : S5.uSub h.le L γ ⊓ S5.bSub h.le L (baseA _) ≤
      Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal) := by
    rw [← Subgroup.le_centralizer_iff]
    exact tZero_le_centralizer h.le γ
  have h2 : Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (ZM _ ξ : Set (puAmalgam h.le).Universal) :=
    Subgroup.centralizer_le hZξ
  have hup : (Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L γ) ≤ 2 ^ k := by
    refine le_trans ?_ hP
    rw [← Subgroup.inf_relIndex_right (S5.bSub h.le L (baseA _)),
      ← Subgroup.inf_relIndex_right (Subgroup.centralizer _)]
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨h1 ⟨hx.2, hx.1⟩, hx.2⟩) ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hlow : 2 ^ k ≤
      (Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L γ) := by
    refine (S5B.le_relIndex_centralizer h hd hγ (hZξ.trans hTst) (hT2.to_le hZξ) hξ.2.2).trans ?_
    rw [← Subgroup.inf_relIndex_right
        (Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal)),
      ← Subgroup.inf_relIndex_right
        (Subgroup.centralizer (ZM _ ξ : Set (puAmalgam h.le).Universal))]
    refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨h2 hx.1, hx.2⟩) ?_
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  exact ⟨hZξ, hTst, hT2, hTQ, le_antisymm hup hlow⟩

theorem hSub_facts (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k) :
    hSub h.le L γ ≤ S5.uSub h.le L γ ∧
      Qv _ (baseB (puAmalgam h.le)) ≤
        Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) ∧
      ¬ hSub h.le L γ ≤
        Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) ∧
      hSub h.le L γ ≤ XM _ (baseA (puAmalgam h.le)) ∧
      ∀ h₀ ∈ hSub h.le L γ,
        h₀ ∉ Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) →
        stab _ γ ⊓ Subgroup.centralizer ({h₀} : Set (puAmalgam h.le).Universal) ≤
          Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) := by
  obtain ⟨hγ, hd2, -⟩ := gamma_facts h hβγ hγα
  obtain ⟨-, hTst, -, -, hrel⟩ := tZero_facts h hb hd hβγ hγα hξ hξα hP
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hβ := not_isMVtx_baseB (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hHU : hSub h.le L γ ≤ S5.uSub h.le L γ :=
    commutator_le_left_of_le_normalizer (hTst.trans (stab_le_normalizer_uSub h γ))
  have hQβ : Qv _ (baseB (puAmalgam h.le)) ≤
      Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal) := by
    intro t ht
    have htγ : t ∈ stab _ γ := qv_le_stab_of_adj _ hβγ ht
    have htα : t ∈ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_isMVtx _ h.hyp20 hα hαβ ht
    obtain ⟨n, hn⟩ := isPGroup_qv _ h.hyp20 hβ ⟨t, ht⟩
    have hn' : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_centralizer_of_normalizer h hd hγ hTst hrel htγ hn' fun e he => ?_
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_tZero h hb hαβ hβγ htα) e).1 he
  have hHL : ¬ hSub h.le L γ ≤
      Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) := by
    intro hle
    have hbot := commutator_eq_bot_of_le h hd hγ hTst hle
    have hUc : S5.uSub h.le L γ ≤
        Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    rw [Subgroup.relIndex_eq_one.2 hUc] at hrel
    have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
    omega
  have hHX : hSub h.le L γ ≤ XM _ (baseA (puAmalgam h.le)) := by
    intro x hx
    have hxU := hHU hx
    have hγα' : (puAmalgam h.le).treeGraph.dist γ (baseA _) < critDist (puAmalgam h.le) := by
      rw [SimpleGraph.dist_comm, hd2]
      exact hb
    have hxQ : x ∈ Qv _ (baseA (puAmalgam h.le)) :=
      zm_le_qv_of_dist_lt _ hγ hγα' (S5B.uSub_le_zm h.le γ hxU)
    have hxC : x ∈ Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hQβ (qv_le_qv _ h.hyp20 hα hαβ hy)) x hx).symm
    have hx2 := (isElemAbelian_xm _ γ).2 x
      (zm_le_xm _ h.hyp20 h.critDist_pos hγ (S5B.uSub_le_zm h.le γ hxU))
    exact Subgroup.subset_closure ⟨⟨hxQ, hxC⟩, hx2⟩
  refine ⟨hHU, hQβ, hHL, hHX, fun h₀ hh₀ hh₀L m hm => ?_⟩
  exact mem_centralizer_of_comm h hd hγ hTst hrel hh₀ hh₀L hm.1
    (Subgroup.mem_centralizer_singleton_iff.1 hm.2)

theorem uSub_not_le_bSub_of_hyp (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k) :
    ¬ S5.uSub h.le L γ ≤ S5.bSub h.le L (baseA _) := by
  intro hle
  obtain ⟨-, -, -, -, hrel⟩ := tZero_facts h hb hd hβγ hγα hξ hξα hP
  have hUc : S5.uSub h.le L γ ≤
      Subgroup.centralizer (tZero h.le L γ : Set (puAmalgam h.le).Universal) := by
    rw [← Subgroup.le_centralizer_iff]
    exact (tZero_le_centralizer h.le γ).trans (Subgroup.centralizer_le (by
      intro x hx
      exact ⟨hx, hle hx⟩))
  rw [Subgroup.relIndex_eq_one.2 hUc] at hrel
  have := Nat.one_lt_two_pow (show k ≠ 0 by have := hd.1; omega)
  omega

theorem hSub_smul (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le))) :
    hSub h.le L (g • γ) = (hSub h.le L γ).map (MulAut.conj g).toMonoidHom := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  rw [hSub, hSub, tZero_smul_eq h hb hαβ hβγ hg, S5B.uSub_smul h.le hLn,
    Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (le_normalizer_tZero h hb hαβ hβγ hg)]

theorem commutator_zm_tZero_smul (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le))) :
    ⁅ZM _ (g • γ), tZero h.le L γ⁆ = (hSub h.le L γ).map (MulAut.conj g).toMonoidHom := by
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg
  have hα' : (puAmalgam h.le).treeGraph.Adj (baseA _) (g • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g _ _).2 hαβ
    rwa [hgα] at this
  have hβγ' : (puAmalgam h.le).treeGraph.Adj (g • baseB (puAmalgam h.le)) (g • γ) :=
    (adj_smul _ g _ _).2 hβγ
  rw [← tZero_smul_eq h hb hαβ hβγ hg, commutator_zm_tZero h hb hα' hβγ', hSub_smul h hb hβγ hg]

end Config

section V

@[expose] def vSub (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  S5.nclStab _ (baseA (puAmalgam hTM)) (ZM _ γ)

omit [Finite G] [Fintype F] in
theorem zm_smul_le_vSub (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM)) {g : (puAmalgam hTM).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam hTM))) : ZM _ (g • γ) ≤ vSub hTM γ := by
  rw [zm_smul]
  exact le_iSup_of_le (⟨g, hg⟩ : ↥(stab _ (baseA (puAmalgam hTM)))) le_rfl

omit [Finite G] [Fintype F] in
theorem vSub_le_iff (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM))
    {K : Subgroup (puAmalgam hTM).Universal} :
    vSub hTM γ ≤ K ↔ ∀ g ∈ stab _ (baseA (puAmalgam hTM)), ZM _ (g • γ) ≤ K := by
  constructor
  · intro hle g hg
    exact (zm_smul_le_vSub hTM γ hg).trans hle
  · intro hK
    refine iSup_le fun g => ?_
    rw [← zm_smul]
    exact hK g g.2

omit [Finite G] [Fintype F] in
theorem stab_le_normalizer_vSub (hTM : T ≤ M) (γ : Vtx (puAmalgam hTM)) :
    stab _ (baseA (puAmalgam hTM)) ≤
      Subgroup.normalizer (vSub hTM γ : Set (puAmalgam hTM).Universal) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  rw [vSub, ← S5B.nclStab_smul, (mem_stab _).1 hx, ← zm_smul]
  refine iSup_le fun g => ?_
  rw [← zm_smul, smul_smul]
  exact zm_smul_le_vSub hTM γ (mul_mem g.2 hx)

theorem vSub_facts (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    (hγα : γ ≠ baseA _) :
    ZM _ (baseA (puAmalgam h.le)) ≤ vSub h.le γ ∧ vSub h.le γ ≤ Vv _ (baseA (puAmalgam h.le)) ∧
      vSub h.le γ ≤ Qv _ (baseA (puAmalgam h.le)) ∧
      vSub h.le γ ≤ Subgroup.centralizer (vSub h.le γ : Set (puAmalgam h.le).Universal) ∧
      (∀ δ, (puAmalgam h.le).treeGraph.dist (baseA _) δ + 2 < critDist (puAmalgam h.le) →
        vSub h.le γ ≤ Qv _ δ) ∧
      (∀ δ, (puAmalgam h.le).treeGraph.dist (baseA _) δ + 2 ≤ critDist (puAmalgam h.le) →
        vSub h.le γ ≤ stab _ δ) := by
  obtain ⟨hγ, hd2, -⟩ := gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hgen : ∀ g ∈ stab _ (baseA (puAmalgam h.le)),
      IsMVtx _ (g • γ) ∧ (puAmalgam h.le).treeGraph.dist (baseA _) (g • γ) = 2 := by
    intro g hg
    refine ⟨(isMVtx_smul _ g γ).2 hγ, ?_⟩
    rw [← (mem_stab _).1 hg, dist_smul]
    exact hd2
  have hQδ : ∀ δ, (puAmalgam h.le).treeGraph.dist (baseA _) δ + 2 < critDist (puAmalgam h.le) →
      vSub h.le γ ≤ Qv _ δ := by
    intro δ hδ
    refine (vSub_le_iff h.le γ).2 fun g hg => ?_
    obtain ⟨hM, hdg⟩ := hgen g hg
    refine zm_le_qv_of_dist_lt _ hM ?_
    have := dist_triangle _ (g • γ) (baseA (puAmalgam h.le)) δ
    rw [SimpleGraph.dist_comm (u := g • γ) (v := baseA _), hdg] at this
    omega
  refine ⟨?_, ?_, hQδ (baseA _) (by simp; omega), ?_, hQδ, ?_⟩
  ·
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨t, ht, rfl⟩ := exists_mem_stab_smul _ hαβ hε
    rw [zh_smul]
    exact (Subgroup.map_mono (zh_le_zm _ hβγ.symm)).trans
      (by rw [← zm_smul]; exact zm_smul_le_vSub h.le γ ht)
  · refine (vSub_le_iff h.le γ).2 fun g hg => ?_
    obtain ⟨hM, hdg⟩ := hgen g hg
    exact S5B.zm_le_vv_of_dist hM hdg.le
  ·
    rw [← Subgroup.le_centralizer_iff]
    refine (vSub_le_iff h.le γ).2 fun g₁ hg₁ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine (vSub_le_iff h.le γ).2 fun g₂ hg₂ => ?_
    obtain ⟨hM₁, hd₁⟩ := hgen g₁ hg₁
    obtain ⟨hM₂, hd₂⟩ := hgen g₂ hg₂
    have hlt : (puAmalgam h.le).treeGraph.dist (g₂ • γ) (g₁ • γ) < critDist (puAmalgam h.le) := by
      have := dist_triangle _ (g₂ • γ) (baseA (puAmalgam h.le)) (g₁ • γ)
      rw [SimpleGraph.dist_comm (u := g₂ • γ) (v := baseA _), hd₁, hd₂] at this
      omega
    exact (zm_le_qv_of_dist_lt _ hM₂ hlt).trans (Subgroup.le_centralizer_iff.1
      (zm_le_centralizer_qv _ h.hyp20 hM₁))
  · intro δ hδ
    refine (vSub_le_iff h.le γ).2 fun g hg => ?_
    obtain ⟨hM, hdg⟩ := hgen g hg
    refine zm_le_stab_of_dist_le h hM ?_
    have := dist_triangle _ (g • γ) (baseA (puAmalgam h.le)) δ
    rw [SimpleGraph.dist_comm (u := g • γ) (v := baseA _), hdg] at this
    omega

end V

end S59

end CFSG.Quasithin.MS93
