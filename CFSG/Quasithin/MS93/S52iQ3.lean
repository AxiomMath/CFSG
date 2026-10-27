module

public import CFSG.Quasithin.MS93.S52iCub
public import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S38EBase
public import CFSG.Quasithin.MS93.S33LamM
public import CFSG.Quasithin.MS93.S33SpS5

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S33
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem zm_le_stab_of_dist_le {ρ α : Vtx X} (hρ : IsMVtx X ρ) (hb : 0 < critDist X)
    (hd : X.treeGraph.dist ρ α ≤ critDist X) : ZM X ρ ≤ stab X α := by
  rcases hd.lt_or_eq with hlt | heq
  · exact (zm_le_qv_of_dist_lt X hρ hlt).trans (qv_le_stab X α)
  · have hd1 : 0 < X.treeGraph.dist α ρ := by rw [tdist_comm, heq]; exact hb
    have hadj : X.treeGraph.Adj α (geo X α ρ 1) := adj_geo_one X hd1
    have hlt : X.treeGraph.dist ρ (geo X α ρ 1) < critDist X := by
      rw [tdist_comm, dist_geo_right X (show 1 ≤ X.treeGraph.dist α ρ from hd1), tdist_comm,
        heq]
      omega
    exact (zm_le_qv_of_dist_lt X hρ hlt).trans (PU.qv_le_stab_of_adj X hadj.symm)

end Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem pre_zm_props_of_dist (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam h.le).treeGraph.dist ρ (baseA _) ≤ critDist (puAmalgam h.le)) :
    (∀ x ∈ pre h.le (ZM _ ρ), ∀ y ∈ pre h.le (ZM _ ρ), x * y = y * x) ∧
    (∀ x ∈ pre h.le (ZM _ ρ), x ^ 2 = 1) ∧ ⁅Uq M T L, pre h.le (ZM _ ρ)⁆ ≤ pre h.le (ZM _ ρ) ∧
    imM h.le (pre h.le (ZM _ ρ)) = ZM (puAmalgam h.le) ρ := by
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hZS : ZM (puAmalgam h.le) ρ ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact zm_le_stab_of_dist_le _ hρ hb hd
  have hEim := imM_pre h.le hZS
  have hEA := isElemAbelian_zm _ h20 hb hρ
  refine ⟨pre_comm h.le (isMulCommutative_subgroup_iff.mp hEA.1), pre_sq h.le hEA.2, ?_, hEim⟩
  have hZn : ZM (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) ρ : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_dist_le _ (PU.isMVtx_baseA _) hb (by rw [tdist_comm]; exact hd)).trans
      (stab_le_normalizer_zm _ ρ)
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [← imM_le_imM_iff h.le (commutator_le_of_le hUM (pre_le h.le _)),
    imM_commutator h.le hUM (pre_le h.le _), hEim]
  refine (Subgroup.commutator_mono (imM_mono h.le (Uq_le_Z0q h.L_le)) le_rfl).trans ?_
  rw [← puAmalgam.zm_baseA, Subgroup.commutator_comm]
  exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hZn

theorem vv_eq_iSup_zm {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    (X : GoldAmalgam A C B) {γ : Vtx X} (hγ : IsMVtx X γ) :
    Vv X γ = ⨆ ρ : {ρ : Vtx X // IsMVtx X ρ ∧ X.treeGraph.dist γ ρ ≤ 2}, ZM X ρ.1 := by
  apply le_antisymm
  · rw [S38E.vv_eq_iSup]
    refine iSup_le fun ρ => ?_
    obtain ⟨γ', hγ', hdγ', hle⟩ := S38E.exists_zv_le_zm X hγ ρ.2
    exact hle.trans (le_iSup_of_le (⟨γ', hγ', hdγ'⟩ :
      {ρ : Vtx X // IsMVtx X ρ ∧ X.treeGraph.dist γ ρ ≤ 2}) le_rfl)
  · refine iSup_le fun ρ => ?_
    rw [← zv_of_isMVtx X ρ.2.1]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist γ ρ ≤ 2}) => Zv X ρ)
      ρ.1 ρ.2.2 le_rfl

omit [Finite G] in
theorem vIm_iSup (hTM : T ≤ M) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F)) {ι : Type*}
    (K : ι → Subgroup (puAmalgam hTM).Universal) (hK : ∀ i, K i ≤ imM hTM M) :
    S5.vIm hTM a (⨆ i, K i) = ⨆ i, S5.vIm hTM a (K i) := by
  have hKr : ∀ i, K i ≤ (puAmalgam hTM).ofA.range := fun i => (hK i).trans (imM_self hTM).le
  have e : (⨆ i, K i) = (⨆ i, (K i).comap (puAmalgam hTM).ofA).map (puAmalgam hTM).ofA := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_comap_eq_self (hKr i)).symm
  rw [S5.vIm, e, Subgroup.comap_map_eq_self_of_injective (puAmalgam hTM).ofA_injective,
    Subgroup.map_iSup]
  rfl

theorem relIndex_qv_vv_le (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a)
    (hb : 2 < critDist (puAmalgam h.le)) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hdγ : (puAmalgam h.le).treeGraph.dist γ (baseA _) + 2 ≤ critDist (puAmalgam h.le)) :
    (Qv (puAmalgam h.le) (baseA _)).relIndex (Vv (puAmalgam h.le) γ) ≤ (2 ^ k) ^ 3 := by
  have : CharP F 2 := S5.IsSp4Data.charP hd
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  have hb4 : 4 ≤ critDist (puAmalgam h.le) := by
    obtain ⟨n, hn⟩ := ms21_v _ h20
    omega
  set ι := {ρ : Vtx (puAmalgam h.le) // IsMVtx _ ρ ∧ (puAmalgam h.le).treeGraph.dist γ ρ ≤ 2}
  have hdist : ∀ ρ : ι, (puAmalgam h.le).treeGraph.dist ρ.1 (baseA _) ≤
      critDist (puAmalgam h.le) := fun ρ => by
    have := dist_triangle _ ρ.1 γ (baseA _)
    rw [tdist_comm _ ρ.1 γ] at this
    have := ρ.2.2
    omega
  have hdist2 : ∀ ρ ρ' : ι, (puAmalgam h.le).treeGraph.dist ρ.1 ρ'.1 ≤
      critDist (puAmalgam h.le) := fun ρ ρ' => by
    have := dist_triangle _ ρ.1 γ ρ'.1
    rw [tdist_comm _ ρ.1 γ] at this
    have := ρ.2.2
    have := ρ'.2.2
    omega
  have hV := vv_eq_iSup_zm _ hγ
  have hst : ∀ ρ : ι, ZM (puAmalgam h.le) ρ.1 ≤ imM h.le M := fun ρ => by
    rw [← puAmalgam.stab_baseA]
    exact zm_le_stab_of_dist_le _ ρ.2.1 hb0 (hdist ρ)
  have hVS : Vv (puAmalgam h.le) γ ≤ imM h.le M := by
    rw [hV]
    exact iSup_le hst
  have hV2 : IsPGroup 2 ↥(Vv (puAmalgam h.le) γ) := by
    obtain ⟨ρ, hρ⟩ := exists_adj (puAmalgam h.le) γ
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    exact ((isPGroup_qv _ h20 hρH).to_le (qv_le_qv _ h20 hγ hρ)).to_le (S38E.vv_le_qv _ hb hγ)
  have hpre2 : IsPGroup 2 ↥(pre h.le (Vv (puAmalgam h.le) γ)) := by
    have h1 : IsPGroup 2 ↥((Vv (puAmalgam h.le) γ).comap (puAmalgam h.le).ofA) :=
      hV2.comap_of_injective _ (puAmalgam h.le).ofA_injective
    exact h1.map M.subtype
  have hcard : (Qv (puAmalgam h.le) (baseA _)).relIndex (Vv (puAmalgam h.le) γ) =
      Nat.card ↥(S5.vIm h.le a (Vv (puAmalgam h.le) γ)) := by
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, ← imM_pre h.le hVS,
      relIndex_imM h.le (pre_le h.le _), vIm_eq_map_pre h a, imM_pre h.le hVS,
      ← S5.IsSp4Data.card_imSp_of_isPGroup hd h hpre2 (pre_le h.le _)]
    rfl
  have hnatM : IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) a false 1 := by
    have := hd.2.2.2
    rwa [← h.Uq_inf_Zq] at this
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnatM
  have hAβ := isCoordAct_of_natSp hβα
  set A : ι → Subgroup (MSP.Sp4 F) := fun ρ => S5.vIm h.le a (ZM (puAmalgam h.le) ρ.1) with hAdef
  have hAeq : ∀ ρ : ι, A ρ = ((pre h.le (ZM (puAmalgam h.le) ρ.1)).subgroupOf M).map a :=
    fun ρ => vIm_eq_map_pre h a _
  have hA2 : ∀ ρ : ι, IsPGroup 2 ↥(A ρ) := by
    intro ρ
    obtain ⟨-, hsq, -, -⟩ := pre_zm_props_of_dist h ρ.2.1 (hdist ρ)
    rw [hAeq]
    refine IsPGroup.map (fun x => ⟨1, ?_⟩) a
    exact Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow]
      exact Subtype.ext (by simpa using hsq _ (Subgroup.mem_subgroupOf.1 x.2)))
  have hAq : ∀ ρ : ι, MSP.commSp (A ρ) ≤ MSP.fixSp (A ρ) := by
    intro ρ
    obtain ⟨hab, -, hU, -⟩ := pre_zm_props_of_dist h ρ.2.1 (hdist ρ)
    rw [hAeq]
    exact commSp_le_fixSp_of_quadratic h le_rfl hβ hβker hAβ (pre_le h.le _) hab hU
  have hAn : ∀ ρ ρ' : ι, A ρ ≤ Subgroup.normalizer (A ρ' : Set (MSP.Sp4 F)) := by
    intro ρ ρ'
    rw [hAeq, hAeq]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    have hxZ : (puAmalgam h.le).ofA x ∈ ZM (puAmalgam h.le) ρ.1 :=
      (mem_pre_iff h.le x).1 (Subgroup.mem_subgroupOf.1 hx)
    have hxn : (puAmalgam h.le).ofA x ∈
        Subgroup.normalizer (ZM (puAmalgam h.le) ρ'.1 : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_zm _ ρ'.1 (zm_le_stab_of_dist_le _ ρ.2.1 hb0 (hdist2 ρ ρ') hxZ)
    have key : ∀ y : ↥M, y ∈ (pre h.le (ZM (puAmalgam h.le) ρ'.1)).subgroupOf M ↔
        x * y * x⁻¹ ∈ (pre h.le (ZM (puAmalgam h.le) ρ'.1)).subgroupOf M := by
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_pre_iff h.le, mem_pre_iff h.le,
        map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.1 hxn _
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, (key y).1 hy, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwz⟩
      refine ⟨x⁻¹ * w * x, (key _).2 (by simpa [mul_assoc] using hw), ?_⟩
      rw [map_mul, map_mul, map_inv, hwz]
      group
  have hsup2 : IsPGroup 2 ↥(⨆ ρ, A ρ) := by
    rw [← vIm_iSup h.le a _ hst, ← hV, vIm_eq_map_pre h a]
    exact hpre2.comap_of_injective (M.subtype) M.subtype_injective |>.map a
  rw [hcard, hV, vIm_iSup h.le a _ hst]
  have := card_iSup_le_of_quadratic A hA2 hAq hAn hsup2
  rwa [S5.IsSp4Data.nat_card_eq hd] at this

theorem relIndex_qv_geo_two_vv_le (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a)
    (hb : 2 < critDist (puAmalgam h.le)) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    (Qv (puAmalgam h.le) (geo _ α' (baseA _) 2)).relIndex (Vv (puAmalgam h.le) (baseA _)) ≤
      (2 ^ k) ^ 3 := by
  have h20 := h.hyp20
  have hdα : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1
  have h2 : 2 ≤ (puAmalgam h.le).treeGraph.dist α' (baseA _) := by omega
  have hδ : IsMVtx _ (geo (puAmalgam h.le) α' (baseA _) 2) :=
    (isMVtx_geo _ h2).2 (iff_of_true (hc.isMVtx_right _ h20) even_two)
  obtain ⟨g, hg⟩ := exists_eq_smul_baseA _ hδ
  have hQ : Qv (puAmalgam h.le) (geo _ α' (baseA _) 2) =
      (Qv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [hg, qv_smul]
  have hV : Vv (puAmalgam h.le) (baseA _) =
      (Vv (puAmalgam h.le) (g⁻¹ • baseA _)).map (MulAut.conj g).toMonoidHom := by
    rw [← vi_smul, smul_inv_smul]
  rw [hQ, hV, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  refine relIndex_qv_vv_le h hd hb ((isMVtx_smul _ g⁻¹ _).2 (PU.isMVtx_baseA _)) ?_
  have e : (puAmalgam h.le).treeGraph.dist (g⁻¹ • baseA (puAmalgam h.le)) (baseA _) =
      (puAmalgam h.le).treeGraph.dist (geo _ α' (baseA _) 2) (baseA _) := by
    rw [← dist_smul _ g, smul_inv_smul, ← hg, tdist_comm]
  rw [e, dist_geo_right _ h2, hdα]
  omega

end CFSG.Quasithin.MS93.S52i
