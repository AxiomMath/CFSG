module

public import CFSG.Quasithin.MS93.S59RTv
public import CFSG.Quasithin.MS93.S59Set

public section

namespace CFSG.Quasithin.MS93.S59R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Config

theorem uSub_inf_centralizer_eq (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {t : (puAmalgam h.le).Universal} (ht : t ∈ S59.tZero h.le L γ)
    (htU : ¬ S5.uSub h.le L γ ≤ Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)) :
    S5.uSub h.le L γ ⊓ Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) =
      S5.uSub h.le L γ ⊓ S5.bSub h.le L (baseA _) := by
  obtain ⟨hγ, -, -⟩ := S59.gamma_facts h hβγ hγα
  obtain ⟨-, hTst, hT2, -, -⟩ := S59.tZero_facts h hb hd hβγ hγα hξ hξα hP
  have hfin : Finite ↥(S5.uSub h.le L γ) := S5B.finite_of_le_qv h hγ
    ((S5B.uSub_le_zm h.le γ).trans (zm_le_qv_self _ hγ h.critDist_pos))
  have hzp : Subgroup.zpowers t ≤ S59.tZero h.le L γ := (Subgroup.zpowers_le).2 ht
  have hCz : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup _) :
      Set (puAmalgam h.le).Universal) =
      Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hQ : ¬ Subgroup.zpowers t ≤ Qv _ γ := by
    intro hle
    apply htU
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hγ
      (S5B.uSub_le_zm h.le γ hu)) t (hle (Subgroup.mem_zpowers t))).symm
  have hlow := S5B.le_relIndex_centralizer h hd hγ (hzp.trans hTst) (hT2.to_le hzp) hQ
  rw [hCz] at hlow
  have hsub : S5.uSub h.le L γ ⊓ S5.bSub h.le L (baseA _) ≤
      S5.uSub h.le L γ ⊓ Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) := by
    intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 ht.2 x hx)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hsub
    (inf_le_left : S5.uSub h.le L γ ⊓ Subgroup.centralizer ({t} : Set _) ≤ S5.uSub h.le L γ)
  rw [inf_comm (S5.uSub h.le L γ) (S5.bSub h.le L (baseA _)), Subgroup.inf_relIndex_right,
    inf_comm (S5.uSub h.le L γ) (Subgroup.centralizer _), Subgroup.inf_relIndex_right] at hmul
  rw [inf_comm (S5.uSub h.le L γ) (S5.bSub h.le L (baseA _))] at hsub ⊢
  rw [inf_comm (S5.uSub h.le L γ) (Subgroup.centralizer _)] at hsub ⊢
  have hpos : 0 < (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L γ) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have h1 : (S5.bSub h.le L (baseA _) ⊓ S5.uSub h.le L γ).relIndex
      (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) ⊓ S5.uSub h.le L γ) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : 2 * (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L γ) ≤ 2 ^ k := by
      calc 2 * _ ≤ _ * _ := Nat.mul_le_mul_right _ hlt
        _ = _ := hmul
        _ ≤ 2 ^ k := hP
    omega
  have h2 : (S5.bSub h.le L (baseA _) ⊓ S5.uSub h.le L γ).relIndex
      (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) ⊓ S5.uSub h.le L γ) = 1 := by
    have : (S5.bSub h.le L (baseA _) ⊓ S5.uSub h.le L γ).relIndex
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal) ⊓ S5.uSub h.le L γ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have : 1 ≤ (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) := by
        rw [Subgroup.relIndex]
        exact Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
      omega
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) hsub

theorem hSub_le_commutator (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {N : Subgroup (puAmalgam h.le).Universal} (hNT : N ≤ S59.tZero h.le L γ)
    {u : (puAmalgam h.le).Universal} (hu : u ∈ S5.uSub h.le L γ)
    (huB : u ∉ S5.bSub h.le L (baseA _))
    (hNu : 2 ^ k ≤ (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex N) :
    S59.hSub h.le L γ ≤ ⁅S5.uSub h.le L γ, N⁆ := by
  obtain ⟨hγ, -, -⟩ := S59.gamma_facts h hβγ hγα
  obtain ⟨-, hTst, -, -, hrel⟩ := S59.tZero_facts h hb hd hβγ hγα hξ hξα hP
  obtain ⟨-, hQβ, -, -, -⟩ := S59.hSub_facts h hb hd hβγ hγα hξ hξα hP
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  set D := Subgroup.centralizer (S5.uSub h.le L γ : Set (puAmalgam h.le).Universal)
  set T₀ := S59.tZero h.le L γ
  have hTQ : T₀ ≤ Qv _ (baseA (puAmalgam h.le)) := S59.tZero_le_qv h.le γ
  have hTfin : Finite ↥T₀ := S5B.finite_of_le_qv h hα hTQ
  have hCN : Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊓ N = D ⊓ N := by
    apply le_antisymm
    · intro n hn
      refine ⟨?_, hn.2⟩
      by_contra hnD
      have hnU : ¬ S5.uSub h.le L γ ≤
          Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) := by
        intro hle
        apply hnD
        refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hw))
      have heq := uSub_inf_centralizer_eq h hb hd hβγ hγα hξ hξα hP (hNT hn.2) hnU
      have huC : u ∈ S5.uSub h.le L γ ⊓
          Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) :=
        ⟨hu, Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hn.1).symm⟩
      rw [heq] at huC
      exact huB huC.2
    · intro n hn
      refine ⟨?_, hn.2⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hn.1 u hu).symm)
  have hDN : 2 ^ k ≤ D.relIndex N := by
    rw [← Subgroup.inf_relIndex_right, ← hCN, Subgroup.inf_relIndex_right]
    exact hNu
  have hDT : D.relIndex T₀ ≤ 2 ^ k := relIndex_le_of_relIndex h hd hγ hTst hrel
  set S := N ⊔ (D ⊓ T₀)
  have hST : S ≤ T₀ := sup_le hNT inf_le_right
  have hSfin : Finite ↥S := Finite.of_injective (Subgroup.inclusion hST)
    (Subgroup.inclusion_injective hST)
  have hDS : D.relIndex N ≤ D.relIndex S := Subgroup.relIndex_le_of_le_right le_sup_left (by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite)
  have hmul := Subgroup.relIndex_mul_relIndex (D ⊓ T₀) S T₀ le_sup_right hST
  have e1 : (D ⊓ T₀).relIndex S = D.relIndex S := by
    rw [← Subgroup.inf_relIndex_right (D ⊓ T₀) S, ← Subgroup.inf_relIndex_right D S,
      inf_assoc, inf_of_le_right hST]
  rw [e1, Subgroup.inf_relIndex_right] at hmul
  have hS1 : S.relIndex T₀ = 1 := by
    have hpos : S.relIndex T₀ ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have : D.relIndex S * S.relIndex T₀ ≤ 2 ^ k * 1 := by rw [hmul, mul_one]; exact hDT
    have h2 : 2 ^ k * S.relIndex T₀ ≤ 2 ^ k * 1 :=
      (Nat.mul_le_mul_right _ (hDN.trans hDS)).trans this
    have := Nat.le_of_mul_le_mul_left h2 (by positivity)
    omega
  have hTS : T₀ ≤ S := Subgroup.relIndex_eq_one.1 hS1
  have hHc : ⁅S5.uSub h.le L γ, N⁆ ≤ S59.hSub h.le L γ :=
    Subgroup.commutator_mono le_rfl hNT
  have hTc : T₀ ≤ Subgroup.centralizer
      ((⁅S5.uSub h.le L γ, N⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    fun t ht => Subgroup.centralizer_le hHc
      (hQβ (hTQ.trans (qv_le_qv _ h.hyp20 hα hαβ) ht))
  have hTn : T₀ ≤ Subgroup.normalizer
      ((⁅S5.uSub h.le L γ, N⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    hTc.trans (Subgroup.centralizer_le_normalizer _)
  show ⁅S5.uSub h.le L γ, T₀⁆ ≤ ⁅S5.uSub h.le L γ, N⁆
  rw [Subgroup.commutator_comm (S5.uSub h.le L γ) T₀]
  refine (Subgroup.commutator_mono hTS le_rfl).trans ?_
  refine S5B.commutator_sup_le_of_le (hNT.trans hTn) (inf_le_right.trans hTn) ?_ ?_
  · rw [Subgroup.commutator_comm]
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).2 ?_]
    · exact bot_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.1 hx.1 w hw)

theorem commutator_uSub_geo_eq_bot (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    (hH : ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ α'' : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L γ, S5.uSub h.le L (geo _ α'' (baseA (puAmalgam h.le)) 2)⁆ = ⊥ := by
  obtain ⟨hγ, hd2, -⟩ := S59.gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hβ := not_isMVtx_baseB (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hdd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α'' = critDist (puAmalgam h.le) :=
    hc''.2.1
  have hα''M : IsMVtx _ α'' := hc''.isMVtx_right _ h.hyp20
  set σ := geo _ α'' (baseA (puAmalgam h.le)) 2 with hσdef
  have hdα''σ : (puAmalgam h.le).treeGraph.dist α'' σ = 2 :=
    dist_geo _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)
  have hdσα : (puAmalgam h.le).treeGraph.dist σ (baseA _) = critDist (puAmalgam h.le) - 2 := by
    rw [dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdd'']; omega), SimpleGraph.dist_comm,
      hdd'']
  have hσM : IsMVtx _ σ :=
    (isMVtx_geo _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)).2 (iff_of_true hα''M ⟨1, rfl⟩)
  have hσT : ZM _ σ ≤ S59.tZero h.le L γ :=
    S59.zm_le_tZero h hb hαβ hβγ hσM (by rw [SimpleGraph.dist_comm, hdσα]; omega)
      (by rw [SimpleGraph.dist_comm, hdσα]; omega)
  have hUσT : S5.uSub h.le L σ ≤ S59.tZero h.le L γ := (S5B.uSub_le_zm h.le σ).trans hσT
  have hγσ : (puAmalgam h.le).treeGraph.dist γ σ ≤ critDist (puAmalgam h.le) := by
    have t := dist_triangle _ γ (baseA (puAmalgam h.le)) σ
    rw [SimpleGraph.dist_comm (u := γ) (v := baseA _), hd2,
      SimpleGraph.dist_comm (u := baseA _) (v := σ), hdσα] at t
    omega
  have hZγst : ZM _ γ ≤ stab _ σ := S59.zm_le_stab_of_dist_le h hγ hγσ
  by_contra hne
  obtain ⟨n, hnσ, hnU⟩ : ∃ n ∈ S5.uSub h.le L σ, ¬ S5.uSub h.le L γ ≤
      Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) := by
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw n hn
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hall n hn hw)
    rw [Subgroup.mem_bot, commutatorElement_def, hc]
    group
  have hUB := S59.uSub_not_le_bSub_of_hyp h hb hd hβγ hγα hξ hξα hP
  obtain ⟨u, hu, huB⟩ := Set.not_subset.1 hUB
  have heq := uSub_inf_centralizer_eq h hb hd hβγ hγα hξ hξα hP (hUσT hnσ) hnU
  have hun : u ∉ Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) := by
    intro hun
    have : u ∈ S5.uSub h.le L γ ⊓ Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) :=
      ⟨hu, hun⟩
    rw [heq] at this
    exact huB this.2
  have huσ : u ∈ stab _ σ := hZγst (S5B.uSub_le_zm h.le γ hu)
  have huQ : ¬ Subgroup.zpowers u ≤ Qv _ σ := by
    intro hle
    apply hun
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hσM
      (S5B.uSub_le_zm h.le σ hnσ)) u (hle (Subgroup.mem_zpowers u)))
  have huβ : u ∈ Qv _ (baseB (puAmalgam h.le)) :=
    (zm_le_qv_self _ hγ h.critDist_pos).trans (qv_le_qv _ h.hyp20 hγ hβγ.symm)
      (S5B.uSub_le_zm h.le γ hu)
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    (isPGroup_qv _ h.hyp20 hβ).to_le ((Subgroup.zpowers_le).2 huβ)
  have hlow := S5B.le_relIndex_centralizer h hd hσM ((Subgroup.zpowers_le).2 huσ) hu2 huQ
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hlow
  have hHle := hSub_le_commutator h hb hd hβγ hγα hξ hξα hP hUσT hu huB hlow
  apply hH
  refine hHle.trans ?_
  rw [Subgroup.commutator_comm]
  refine (commutator_le_left_of_le_normalizer
    (hZγst.trans (S59.stab_le_normalizer_uSub h σ) |>.trans' (S5B.uSub_le_zm h.le γ))).trans ?_
  refine (S5B.uSub_le_zm h.le σ).trans ((zm_le_centralizer_qv _ h.hyp20 hσM).trans ?_)
  exact Subgroup.centralizer_le (zm_le_qv_of_dist_lt _ hα''M (by rw [hdα''σ]; omega))

theorem commutator_uSub_inf_qv_eq_bot (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    (hUst : S5.uSub h.le L γ ≤ stab _ α'')
    (hAT : critA _ (baseA (puAmalgam h.le)) α'' ≤ S59.tZero h.le L γ)
    (hH : ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ α'' : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L γ, S5.uSub h.le L α'' ⊓ Qv _ (baseA (puAmalgam h.le))⁆ = ⊥ := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hb0 := h.critDist_pos
  have hdd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α'' = critDist (puAmalgam h.le) :=
    hc''.2.1
  have hα''M : IsMVtx _ α'' := hc''.isMVtx_right _ h.hyp20
  set N := S5.uSub h.le L α'' ⊓ Qv _ (baseA (puAmalgam h.le)) with hNdef
  have hNT : N ≤ S59.tZero h.le L γ := by
    refine le_trans (inf_le_inf_right _ ?_) hAT
    exact (S5B.uSub_le_zm h.le α'').trans (zm_le_xm _ h.hyp20 hb0 hα''M)
  have hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α'' 1) :=
    adj_geo_one _ (by omega)
  have hdε : (puAmalgam h.le).treeGraph.dist α'' (geo _ (baseA (puAmalgam h.le)) α'' 1) <
      critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hdd'']
    omega
  have hNC : N = S5.uSub h.le L α'' ⊓
      Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) := by
    apply le_antisymm
    · refine le_inf inf_le_left (inf_le_right.trans ?_)
      exact Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hα)
    · refine le_inf inf_le_left ?_
      refine le_qv_of_le_centralizer _ h.centHyp hα hαε ?_ inf_le_right
      exact inf_le_left.trans ((S5B.uSub_le_zm h.le α'').trans (zm_le_qv_of_dist_lt _ hα''M hdε))
  by_contra hne
  obtain ⟨n, hnN, hnU⟩ : ∃ n ∈ N, ¬ S5.uSub h.le L γ ≤
      Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) := by
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw n hn
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hall n hn hw)
    rw [Subgroup.mem_bot, commutatorElement_def, hc]
    group
  have hUB := S59.uSub_not_le_bSub_of_hyp h hb hd hβγ hγα hξ hξα hP
  obtain ⟨u, hu, huB⟩ := Set.not_subset.1 hUB
  have heq := uSub_inf_centralizer_eq h hb hd hβγ hγα hξ hξα hP (hNT hnN) hnU
  have hnu : n ∉ Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) := by
    intro hnu
    have : u ∈ S5.uSub h.le L γ ⊓ Subgroup.centralizer ({n} : Set (puAmalgam h.le).Universal) :=
      ⟨hu, Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hnu).symm⟩
    rw [heq] at this
    exact huB this.2
  have hZst : ZM _ (baseA (puAmalgam h.le)) ≤ stab _ α'' :=
    S59.zm_le_stab_of_dist_le h hα hdd''.le
  have hdual := relIndex_centralizer_one_or h hd hα''M hZst (hUst hu)
  rw [← hNC] at hdual
  have hNu : 2 ^ k ≤ (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex N := by
    rcases hdual with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.1 h1 hnN) hnu
    · exact h1
  have hHle := hSub_le_commutator h hb hd hβγ hγα hξ hξα hP hNT hu huB hNu
  apply hH
  refine hHle.trans ?_
  rw [Subgroup.commutator_comm]
  refine (Subgroup.commutator_mono (inf_le_left : N ≤ S5.uSub h.le L α'') le_rfl).trans ?_
  refine (commutator_le_left_of_le_normalizer
    (hUst.trans (S59.stab_le_normalizer_uSub h α''))).trans ?_
  refine (S5B.uSub_le_zm h.le α'').trans ((zm_le_centralizer_qv _ h.hyp20 hα''M).trans ?_)
  exact Subgroup.centralizer_le (zm_le_qv_self _ hα''M hb0)

theorem zm_le_centralizer_zm_geo (h : PUHyp M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    (hH : ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ α'' : Set (puAmalgam h.le).Universal)) :
    ZM _ γ ≤ Subgroup.centralizer
      (ZM _ (geo _ α'' (baseA (puAmalgam h.le)) 2) : Set (puAmalgam h.le).Universal) := by
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hU := commutator_uSub_geo_eq_bot h hb2 hd hβγ hγα hξ hξα hP hc'' hH
  obtain ⟨hγ, hd2, -⟩ := S59.gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hdd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α'' = critDist (puAmalgam h.le) :=
    hc''.2.1
  have hα''M : IsMVtx _ α'' := hc''.isMVtx_right _ h.hyp20
  set σ := geo _ α'' (baseA (puAmalgam h.le)) 2 with hσdef
  have hdσα : (puAmalgam h.le).treeGraph.dist σ (baseA _) = critDist (puAmalgam h.le) - 2 := by
    rw [dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdd'']; omega), SimpleGraph.dist_comm,
      hdd'']
  have hσM : IsMVtx _ σ :=
    (isMVtx_geo _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)).2 (iff_of_true hα''M ⟨1, rfl⟩)
  have hσT : ZM _ σ ≤ S59.tZero h.le L γ :=
    S59.zm_le_tZero h hb2 hαβ hβγ hσM (by rw [SimpleGraph.dist_comm, hdσα]; omega)
      (by rw [SimpleGraph.dist_comm, hdσα]; omega)
  have hγσ : (puAmalgam h.le).treeGraph.dist γ σ ≤ critDist (puAmalgam h.le) := by
    have t := dist_triangle _ γ (baseA (puAmalgam h.le)) σ
    rw [SimpleGraph.dist_comm (u := γ) (v := baseA _), hd2,
      SimpleGraph.dist_comm (u := baseA _) (v := σ), hdσα] at t
    omega
  have hσγ1 : 1 ≤ (puAmalgam h.le).treeGraph.dist σ γ := by
    have t := dist_triangle _ σ γ (baseA (puAmalgam h.le))
    rw [hdσα, SimpleGraph.dist_comm (u := γ) (v := baseA _), hd2] at t
    omega
  set ε := geo _ σ γ 1 with hεdef
  have hσε : (puAmalgam h.le).treeGraph.Adj σ ε := adj_geo_one _ hσγ1
  have hγε : (puAmalgam h.le).treeGraph.dist γ ε < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ hσγ1, SimpleGraph.dist_comm]
    omega
  rw [S5B.zm_eq_zh_sup_uSub h hγ hβγ.symm]
  refine sup_le ?_ ?_
  ·
    refine (zh_le_centralizer _ _).trans (Subgroup.centralizer_le ?_)
    exact SetLike.coe_subset_coe.2 (hσT.trans
      ((S59.tZero_le_qv h.le γ).trans (qv_le_qv _ h.hyp20 hα hαβ)))
  · rw [S5B.zm_eq_zh_sup_uSub h hσM hσε, S59.centralizer_sup]
    refine le_inf ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hU)
    refine (S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_of_dist_lt _ hγ hγε).trans ?_)
    exact Subgroup.le_centralizer_iff.1 (zh_le_centralizer _ _)

theorem zm_le_centralizer_uSub_inf_qv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    (hUst : S5.uSub h.le L γ ≤ stab _ α'')
    (hAT : critA _ (baseA (puAmalgam h.le)) α'' ≤ S59.tZero h.le L γ)
    (hH : ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ α'' : Set (puAmalgam h.le).Universal)) :
    ZM _ γ ≤ Subgroup.centralizer ((S5.uSub h.le L α'' ⊓ Qv _ (baseA (puAmalgam h.le)) :
      Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hU := commutator_uSub_inf_qv_eq_bot h hb hd hβγ hγα hξ hξα hP hc'' hUst hAT hH
  obtain ⟨hγ, -, -⟩ := S59.gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  rw [S5B.zm_eq_zh_sup_uSub h hγ hβγ.symm]
  refine sup_le ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hU)
  refine (zh_le_centralizer _ _).trans (Subgroup.centralizer_le ?_)
  exact SetLike.coe_subset_coe.2 (inf_le_right.trans (qv_le_qv _ h.hyp20 hα hαβ))


end Config

end CFSG.Quasithin.MS93.S59R
