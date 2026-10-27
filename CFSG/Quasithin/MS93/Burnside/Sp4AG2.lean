module

public import CFSG.Quasithin.MS93.Burnside.Sp4AMain
import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S34FCore
public import CFSG.Quasithin.MS93.S34FGen
public import CFSG.Quasithin.MS93.S43FC1
public import CFSG.Quasithin.MS93.S4L5KeyFix
public import CFSG.Quasithin.MS93.S4L5KeyTmpl

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] noncomputable def burnsideSp4A_psub (h : PUHyp M T L) (γ δ : Vtx (puAmalgam h.le)) :
    Subgroup (puAmalgam h.le).Universal :=
  Uloc h.le L δ ⊓
    Subgroup.centralizer ((Qv (puAmalgam h.le) γ ⊓ S34F.flat h δ : Subgroup _) : Set _)

theorem burnsideSp4A_psub_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (γ δ : Vtx (puAmalgam h.le)) :
    burnsideSp4A_psub h (g • γ) (g • δ) =
      (burnsideSp4A_psub h γ δ).map (MulAut.conj g).toMonoidHom := by
  rw [burnsideSp4A_psub, burnsideSp4A_psub, uloc_smul h, qv_smul,
    show S34F.flat h (g • δ) = (S34F.flat h δ).map (MulAut.conj g).toMonoidHom from
      puTrans_smul h.le (S34F.flat_subgroupOf_normal h) g δ,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

@[expose] noncomputable def burnsideSp4A_zstar (h : PUHyp M T L) (α : Vtx (puAmalgam h.le)) :
    Subgroup (puAmalgam h.le).Universal :=
  ZM (puAmalgam h.le) α ⊔ ⨆ (γ ∈ (puAmalgam h.le).treeGraph.neighborSet α)
    (δ ∈ (puAmalgam h.le).treeGraph.neighborSet γ), burnsideSp4A_psub h γ δ

@[expose] noncomputable def burnsideSp4A_wsub (h : PUHyp M T L) (β : Vtx (puAmalgam h.le)) :
    Subgroup (puAmalgam h.le).Universal :=
  ⨆ δ ∈ (puAmalgam h.le).treeGraph.neighborSet β, burnsideSp4A_psub h β δ

theorem burnsideSp4A_psub_le_zstar (h : PUHyp M T L) {α γ δ : Vtx (puAmalgam h.le)}
    (hαγ : (puAmalgam h.le).treeGraph.Adj α γ) (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) :
    burnsideSp4A_psub h γ δ ≤ burnsideSp4A_zstar h α :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun γ (_ : γ ∈ (puAmalgam h.le).treeGraph.neighborSet α)
    => ⨆ δ ∈ (puAmalgam h.le).treeGraph.neighborSet γ, burnsideSp4A_psub h γ δ) γ hαγ
    (le_iSup₂_of_le (f := fun δ (_ : δ ∈ (puAmalgam h.le).treeGraph.neighborSet γ) =>
      burnsideSp4A_psub h γ δ) δ hγδ le_rfl))

theorem burnsideSp4A_stab_le_normalizer_zstar (h : PUHyp M T L) (α : Vtx (puAmalgam h.le)) :
    stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (burnsideSp4A_zstar h α : Set (puAmalgam h.le).Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  have hgα : g • α = α := (mem_stab _).mp hg
  rw [burnsideSp4A_zstar, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [← zm_smul, hgα]
    exact le_sup_left
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun δ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hδ => ?_
  rw [← burnsideSp4A_psub_smul]
  refine burnsideSp4A_psub_le_zstar h ?_ ?_
  · have := (adj_smul (puAmalgam h.le) g α γ).mpr hγ
    rwa [hgα] at this
  · exact (adj_smul (puAmalgam h.le) g γ δ).mpr hδ

theorem burnsideSp4A_stab_le_normalizer_wsub (h : PUHyp M T L) (β : Vtx (puAmalgam h.le)) :
    stab (puAmalgam h.le) β ≤
      Subgroup.normalizer (burnsideSp4A_wsub h β : Set (puAmalgam h.le).Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  have hgβ : g • β = β := (mem_stab _).mp hg
  rw [burnsideSp4A_wsub, Subgroup.map_iSup]
  refine iSup_le fun δ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hδ => ?_
  have h1 := burnsideSp4A_psub_smul h g β δ
  rw [hgβ] at h1
  rw [← h1]
  have hδ' : (puAmalgam h.le).treeGraph.Adj β (g • δ) := by
    have := (adj_smul (puAmalgam h.le) g β δ).mpr hδ
    rwa [hgβ] at this
  exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ (puAmalgam h.le).treeGraph.neighborSet β) =>
    burnsideSp4A_psub h β δ) (g • δ) hδ' le_rfl

theorem burnsideSp4A_wsub_le_qv (h : PUHyp M T L) (hb : 1 < critDist (puAmalgam h.le)) :
    burnsideSp4A_wsub h (baseB _) ≤ Qv (puAmalgam h.le) (baseB _) := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  refine iSup₂_le fun δ hδ => ?_
  have hδ' : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hδ'
    tauto
  refine inf_le_left.trans ((S34F.uloc_le_zm' h hδM).trans ?_)
  refine zm_le_qv_of_dist_lt _ hδM ?_
  rw [tdist_comm, dist_eq_one_of_adj _ hδ']
  exact hb

theorem burnsideSp4A_ycrit_le_qv_inf_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) :
    burnsideSp4A_ycrit h ≤ Qv (puAmalgam h.le) (baseB _) ⊓ S34F.flat h δ := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨hc, hμβ⟩ := hμ
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) μ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1
  have hμd : (puAmalgam h.le).treeGraph.dist μ (baseB _) = critDist (puAmalgam h.le) - 1 := by
    rw [tdist_comm, ← hμβ, dist_geo_right (puAmalgam h.le) (by omega), hd]
  refine le_inf (zm_le_qv_of_dist_lt _ hc.1 (by omega)) ?_
  by_cases hZ : ZM (puAmalgam h.le) μ ≤ Qv _ δ
  · exact hZ.trans (S43F.qv_le_flat h hδM)
  · have htri := dist_triangle (puAmalgam h.le) μ (baseB _) δ
    rw [hμd, dist_eq_one_of_adj _ hβδ] at htri
    have hd' : (puAmalgam h.le).treeGraph.dist μ δ = critDist (puAmalgam h.le) := by
      by_contra hne
      exact hZ (zm_le_qv_of_dist_lt _ hc.1 (by omega))
    exact zm_le_flat_sp h hU ⟨hc.1, hd', hZ⟩

@[expose] def burnsideSp4A_G2star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) → IsSp4U M T L → ¬ IsSp4Full M T L →
    ∃ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' ∧
      ⁅burnsideSp4A_zstar h (baseA _), ZM _ α'⁆ ≤
        Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _)

theorem burnsideSp4A_wsub_le_uloc_sup_dloc (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le))
    (hG2 : ⁅burnsideSp4A_zstar h (baseA _), Ltil h.le L (baseA _)⁆ ≤
      Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _)) :
    burnsideSp4A_wsub h (baseB _) ≤ Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) := by
  obtain ⟨m, F, _, _, φ, hm, hcard, hφs, hφ⟩ := IsSp4UEven.exists_natural_flat h hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hUl : Uloc h.le L (baseA _) = imM h.le (Uq M T L) := puTrans_baseA h.le (S4A.Uq_normal h)
  have hDl : Dloc h.le L (baseA _) = imM h.le (Dq M L) := puTrans_baseA h.le (S4A.Dq_normal h)
  have hLt : Ltil h.le L (baseA _) = imM h.le L := puTrans_baseA h.le (S4A.L_normal h)
  have hUD : Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) = imM h.le (Uq M T L ⊔ Dq M L) := by
    rw [hUl, hDl, ← S33.imM_sup h.le (Uq_le h.L_le) (inf_le_left.trans (pCoreOf_le' M))]
  refine iSup₂_le fun δ hδ => ?_
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  have hdδ : (puAmalgam h.le).treeGraph.dist δ (baseA _) ≤ 2 := by
    have htri := dist_triangle (puAmalgam h.le) δ (baseB _) (baseA _)
    rw [tdist_comm _ δ (baseB _), dist_eq_one_of_adj _ hβδ, dist_eq_one_of_adj _ hαβ.symm] at htri
    exact htri
  intro x hx
  have hxZ : x ∈ burnsideSp4A_zstar h (baseA _) := burnsideSp4A_psub_le_zstar h hαβ hβδ hx
  have hxQ : x ∈ Qv (puAmalgam h.le) (baseA _) :=
    zm_le_qv_of_dist_lt _ hδM (by omega) (S34F.uloc_le_zm' h hδM hx.1)
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hxQ
  obtain ⟨w, hwQ, rfl⟩ := hxQ
  replace hwQ : (w : G) ∈ pCoreOf 2 M := hwQ
  have hwL : ∀ l ∈ L, ⁅l, (w : G)⁆ ∈ Uq M T L ⊔ Dq M L := by
    intro l hl
    have hlM : l ∈ M := h.L_le hl
    have hl' : (puAmalgam h.le).ofA ⟨l, hlM⟩ ∈ Ltil h.le L (baseA _) := by
      rw [hLt]
      exact (S33.ofA_mem_imM_iff h.le _).2 hl
    have h1 := hG2 (Subgroup.commutator_mem_commutator hxZ hl')
    rw [hUD, ← map_commutatorElement] at h1
    have h2 := (S33.ofA_mem_imM_iff h.le _).1 h1
    have e : ((⁅w, (⟨l, hlM⟩ : ↥M)⁆ : ↥M) : G) = ⁅(w : G), l⁆ := by
      simp [commutatorElement_def]
    rw [e] at h2
    have h3 : ⁅l, (w : G)⁆ = ⁅(w : G), l⁆⁻¹ := (commutatorElement_inv _ _).symm
    rw [h3]
    exact Subgroup.inv_mem _ h2
  have hYK : S33.pre h.le (burnsideSp4A_ycrit h) ≤ L ⊔ pCoreOf 2 M :=
    S33.pre_le_of_le_imM h (burnsideSp4A_ycrit_le_flat h hU)
  have hYc := burnsideSp4A_ycrit_le_qv_inf_flat h hU hb hβδ
  have hYw : ∀ y ∈ S33.pre h.le (burnsideSp4A_ycrit h), y * (w : G) = (w : G) * y := by
    intro y hy
    obtain ⟨m', hm', rfl⟩ := (S33.mem_pre_iff' h.le).1 hy
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ (hYc hm')
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simpa using h2
  have hwUD := burnsideSp4A_mem_uq_sup_dq h hcard' (by omega) hφs hφ hwQ hwL hYK
    (burnsideSp4A_pCoreOf_le_normalizer_pre_ycrit h) hYw
    (burnsideSp4A_rigid_pre_ycrit burnsideSp4A_lemmaR h hU hcard' (by omega) hφs hφ)
  rw [hUD]
  exact (S33.ofA_mem_imM_iff h.le w).2 hwUD

theorem burnsideSp4A_noNonlinSp_of_g2star (hG : burnsideSp4A_G2star) : NoNonlinSp := by
  intro G _ _ M T L h hmin hb hU hF
  have hUE := S34F.isSp4UEven_of_nonfull h hU hF
  obtain ⟨α', hc, hG2⟩ := hG G M T L h hmin hb hU hF
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hαρ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo (puAmalgam h.le) (baseA _) α' 1) :=
    adj_geo_one _ (by omega)
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hKρ : ZM (puAmalgam h.le) α' ≤ Qv _ (geo (puAmalgam h.le) (baseA _) α' 1) := by
    refine zm_le_qv_of_dist_lt _ hc'.1 ?_
    rw [tdist_comm, dist_geo_right (puAmalgam h.le) (by omega), hd]
    omega
  have hUDn : stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer ((Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) : Subgroup _) :
        Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) _)
      (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) _)
  have hG2' := S34F.commutator_ltil_le_of_commutator_le_gen h hα hαρ
    (burnsideSp4A_stab_le_normalizer_zstar h _) hUDn hG2 hKρ hc'.2.2
  have hW := burnsideSp4A_wsub_le_uloc_sup_dloc h hUE hb hG2'
  have hlift : ∀ l ∈ L, ∀ u ∈ Uq M T L,
      l * u * l⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) → l * u * l⁻¹ = u :=
    fun l hl u hu hlu => IsSp4UEven.lift_flat h hUE (Subgroup.mem_sup_left hl) hu hlu
  have hcen := qv_le_centralizer_of_le_uloc_sup_dloc_lift h hmin hlift
    (burnsideSp4A_wsub_le_qv h (by omega)) (burnsideSp4A_stab_le_normalizer_wsub h _) hW
  have hPα : burnsideSp4A_psub h (baseB _) (baseA _) ≤ burnsideSp4A_wsub h (baseB _) :=
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ (puAmalgam h.le).treeGraph.neighborSet (baseB _)) =>
      burnsideSp4A_psub h (baseB _) δ) (baseA _) hαβ.symm le_rfl
  exact not_le_flat_of_nonfull h hU hF (le_flat_of_qv_le_centralizer_sp h hUE inf_le_left
    inf_le_right (hcen.trans (Subgroup.centralizer_le hPα)))

theorem burnsideSp4A_noNonlinSp4_of_g2star (hG : burnsideSp4A_G2star) : NoNonlinSp4 :=
  (burnsideSp4A_noNonlinSp_of_g2star hG).eq4

theorem burnsideSp4A_noNonlinSpGt4_of_g2star (hG : burnsideSp4A_G2star) : NoNonlinSpGt4 :=
  (burnsideSp4A_noNonlinSp_of_g2star hG).gt4

end CFSG.Quasithin.MS93.S4L
